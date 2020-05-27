{-# LANGUAGE CPP #-}

-- | Constructed Product Result analysis. Identifies functions that surely
-- return heap-allocated records on every code path, so that we can eliminate
-- said heap allocation by performing a worker/wrapper split.
--
-- See https://www.microsoft.com/en-us/research/publication/constructed-product-result-analysis-haskell/.
-- CPR analysis should happen after strictness analysis.
-- See Note [Phase ordering].
module GHC.Core.Opt.CprAnal ( cprAnalProgram ) where

#include "HsVersions.h"

import GHC.Prelude

import GHC.Driver.Session
import GHC.Types.Demand
import GHC.Types.Cpr
import GHC.Core
import GHC.Core.Opt.Arity ( splitFunNewTys )
import GHC.Core.Seq
import GHC.Utils.Outputable
import GHC.Types.Var.Env
import GHC.Types.Basic
import GHC.Core.DataCon
import GHC.Types.Id
import GHC.Types.Id.Info
import GHC.Core.Utils   ( dumpIdInfoOfProgram )
import GHC.Core.TyCon
import GHC.Core.Type
import GHC.Core.FamInstEnv
import GHC.Core.Opt.WorkWrap.Utils
import GHC.Utils.Misc
import GHC.Utils.Error  ( dumpIfSet_dyn, DumpFormat (..) )
import GHC.Data.Maybe   ( isJust, isNothing )

import Control.Monad ( guard )
import Data.List

{- Note [Constructed Product Result]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The goal of Constructed Product Result analysis is to identify functions that
surely return heap-allocated records on every code path, so that we can
eliminate said heap allocation by performing a worker/wrapper split.

@swap@ below is such a function:

  swap (a, b) = (b, a)

A @case@ on an application of @swap@, like
@case swap (10, 42) of (a, b) -> a + b@ could cancel away
(by case-of-known-constructor) if we "inlined" @swap@ and simplified. We then
say that @swap@ has the CPR property.

We can't inline recursive functions, but similar reasoning applies there:

  f x n = case n of
    0 -> (x, 0)
    _ -> f (x+1) (n-1)

Inductively, @case f 1 2 of (a, b) -> a + b@ could cancel away the constructed
product with the case. So @f@, too, has the CPR property. But we can't really
"inline" @f@, because it's recursive. Also, non-recursive functions like @swap@
might be too big to inline (or even marked NOINLINE). We still want to exploit
the CPR property, and that is exactly what the worker/wrapper transformation
can do for us:

  $wf x n = case n of
    0 -> case (x, 0) of -> (a, b) -> (# a, b #)
    _ -> case f (x+1) (n-1) of (a, b) -> (# a, b #)
  f x n = case $wf x n of (# a, b #) -> (a, b)

where $wf readily simplifies (by case-of-known-constructor and inlining @f@) to:

  $wf x n = case n of
    0 -> (# x, 0 #)
    _ -> $wf (x+1) (n-1)

Now, a call site like @case f 1 2 of (a, b) -> a + b@ can inline @f@ and
eliminate the heap-allocated pair constructor.

Note [Phase ordering]
~~~~~~~~~~~~~~~~~~~~~
We need to perform strictness analysis before CPR analysis, because that might
unbox some arguments, in turn leading to more constructed products.
Ideally, we would want the following pipeline:

1. Strictness
2. worker/wrapper (for strictness)
3. CPR
4. worker/wrapper (for CPR)

Currently, we omit 2. and anticipate the results of worker/wrapper.
See Note [CPR in a DataAlt case alternative]
and Note [CPR for binders that will be unboxed].
An additional w/w pass would simplify things, but probably add slight overhead.
So currently we have

1. Strictness
2. CPR
3. worker/wrapper (for strictness and CPR)
-}

--
-- * Analysing programs
--

cprAnalProgram :: DynFlags -> FamInstEnvs -> CoreProgram -> IO CoreProgram
cprAnalProgram dflags fam_envs binds = do
  let env            = emptyAnalEnv dflags fam_envs
  let binds_plus_cpr = snd $ mapAccumL cprAnalTopBind env binds
  dumpIfSet_dyn dflags Opt_D_dump_cpr_signatures "Cpr signatures" FormatText $
    dumpIdInfoOfProgram (ppr . cprInfo) binds_plus_cpr
  -- See Note [Stamp out space leaks in demand analysis] in GHC.Core.Opt.DmdAnal
  seqBinds binds_plus_cpr `seq` return binds_plus_cpr

-- Analyse a (group of) top-level binding(s)
cprAnalTopBind :: AnalEnv
               -> CoreBind
               -> (AnalEnv, CoreBind)
cprAnalTopBind env (NonRec id rhs)
  = (env', NonRec id' rhs')
  where
    (id', rhs', env') = cprAnalBind TopLevel env noWidening [] id rhs

cprAnalTopBind env (Rec pairs)
  = (env', Rec pairs')
  where
    (env', pairs') = cprFix TopLevel env [] pairs

--
-- * Analysing expressions
--

-- | Analoguous to the abstract semantic function ⟦_⟧ : Expr -> Env -> A from
-- "Constructed Product Result Analysis for Haskell"
cprAnal, cprAnal'
  :: AnalEnv
  -> [CprType]           -- ^ info about incoming arguments
  -> CoreExpr            -- ^ expression to be denoted by a 'CprType'
  -> (CprType, CoreExpr) -- ^ the updated expression and its 'CprType'

cprAnal env args e = -- pprTraceWith "cprAnal" (\res -> ppr (fst (res)) $$ ppr e) $
                     cprAnal' env args e

cprAnal' _ _ (Lit lit)     = (whnfTermCprType, Lit lit)
cprAnal' _ _ (Type ty)     = (whnfTermCprType, Type ty)      -- Doesn't happen, in fact
cprAnal' _ _ (Coercion co) = (whnfTermCprType, Coercion co)

cprAnal' env args (Var var)   = (cprTransform env args var, Var var)

cprAnal' env args (Cast e co)
  = (cpr_ty, Cast e' co)
  where
    (cpr_ty, e') = cprAnal env args e

cprAnal' env args (Tick t e)
  = (cpr_ty, Tick t e')
  where
    (cpr_ty, e') = cprAnal env args e

cprAnal' env args (App fun (Type ty))
  = (fun_ty, App fun' (Type ty))
  where
    (fun_ty, fun') = cprAnal env args fun

cprAnal' env args (App fun arg)
  = (app_ty, App fun' arg')
  where
    -- TODO: Make incoming info a proper lattice, so that it's clear that we
    --       can always cough up another topCprType
    (arg_ty, arg')      = cprAnal env [] arg
    -- TODO: forgetCPR on arg_ty! We assume CPR according to what WW makes of
    -- the StrictSig and in all other cases, we won't actually get a CPR.
    -- So the CPR of the argument is actually irrelevant. Its termination info
    -- is useful, though. BUT, what about data con apps? There we definietely
    -- want CPR!
    (fun_ty, fun')      = cprAnal env (arg_ty:args) fun
    -- We force arg_ty when entering a lambda or when applying a transformer.
    -- There's no need to force arg_ty after the application, because the
    -- potential divergence from forcing was already unleashed.
    -- Hence arg_str below is unused.
    -- Why unleash in lambda and tranformer rather than here?
    -- We need to unleash in lambda anyway, because there we see the strictness
    -- of the binder (somewhat anticipating how the function will look after
    -- WWing for strictness). We don't have that available here before having
    -- analysed the fun.
    app_ty              = applyCprTy fun_ty
cprAnal' env args (Lam var body)
  | isTyVar var
  , (body_ty, body') <- cprAnal env args body
  = (body_ty, Lam var body')
  | otherwise
  = (lam_ty, Lam var body')
  where
    (arg_ty, body_args)
      | ty:args' <- args = (ty, args')      -- We know things about the argument, for example from a StrictSig or an incoming argument. NB: This can never be an anonymous (non-let-bound) lambda! The simplifier would have eliminated the necessary (App (Lam{} |> co) _) construct.
      | otherwise        = (topCprType, []) -- An anonymous lambda or no info on its argument
    env'                 = extendSigEnv env var (CprSig arg_ty) -- TODO: I think we also need to store assumed argument strictness (which would be all lazy here) in the env
    (body_ty, body')     = cprAnal env' body_args body
    lam_ty               = abstractCprTy body_ty

cprAnal' env args (Case scrut case_bndr ty alts)
  = (res_ty, Case scrut' case_bndr ty alts')
  where
    -- Analyse the scrutinee and additional force the resulting CPR type with
    -- head strictness.
    (scrut_ty, scrut')        = cprAnal env [] scrut
    (whnf_flag, case_bndr_ty) = forceCprTy (getStrDmd seqDmd) scrut_ty
    (alt_tys, alts') = mapAndUnzip (cprAnalAlt env args case_bndr case_bndr_ty) alts
    res_ty           = lubCprTypes alt_tys `bothCprType` whnf_flag

cprAnal' env args (Let (NonRec id rhs) body)
  = (body_ty, Let (NonRec id' rhs') body')
  where
    (id', rhs', env') = cprAnalBind NotTopLevel env noWidening args id rhs
    (body_ty, body')  = cprAnal env' args body

cprAnal' env args (Let (Rec pairs) body)
  = body_ty `seq` (body_ty, Let (Rec pairs') body')
  where
    (env', pairs')   = cprFix NotTopLevel env args pairs
    (body_ty, body') = cprAnal env' args body

cprAnalAlt
  :: AnalEnv
  -> [CprType]      -- ^ info about incoming arguments
  -> Id             -- ^ case binder
  -> CprType        -- ^ info about the case binder
  -> Alt Var        -- ^ current alternative
  -> (CprType, Alt Var)
cprAnalAlt env args case_bndr case_bndr_ty (con@(DataAlt dc),bndrs,rhs)
  -- See 'extendEnvForDataAlt' and Note [CPR in a DataAlt case alternative]
  = (rhs_ty, (con, bndrs, rhs'))
  where
    env_alt        = extendEnvForDataAlt env case_bndr case_bndr_ty dc bndrs
    (rhs_ty, rhs') = cprAnal env_alt args rhs
cprAnalAlt env args case_bndr case_bndr_ty (con,bndrs,rhs)
  = (rhs_ty, (con, bndrs, rhs'))
  where
    env' = extendSigEnv env case_bndr (CprSig case_bndr_ty)
    (rhs_ty, rhs') = cprAnal env' args rhs

--
-- * CPR transformer
--

cprTransform
  :: AnalEnv         -- ^ The analysis environment
  -> [CprType]       -- ^ info about incoming arguments
  -> Id              -- ^ The function
  -> CprType         -- ^ The demand type of the function
cprTransform env args id
  = -- pprTrace "cprTransform" (vcat [ppr id, ppr sig])
    sig
  where
    sig
      -- Local let-bound
      | Just sig <- lookupSigEnv env id
      = cprTransformSig (idStrictness id) sig args
      -- See Note [CPR for expandable unfoldings]
      | Just rhs <- cprExpandUnfolding_maybe id
      = fst $ cprAnal env args rhs
      -- Data constructor
      | Just con <- isDataConWorkId_maybe id
      = cprTransformDataConSig con args
      -- Imported function or data con worker
      | isGlobalId id
      = cprTransformSig (idStrictness id) (idCprInfo id) args
      | otherwise
      = topCprType

--
-- * Bindings
--

--
-- ** Widening
--

type Widening = CprSig -> CprSig

noWidening :: Widening
noWidening = id

-- | A widening operator on 'CprSig' to ensure termination of fixed-point
-- iteration. See Note [Ensuring termination of fixed-point iteration]
depthWidening :: Widening
depthWidening = pruneSig mAX_DEPTH . markDiverging

mAX_DEPTH :: Int
mAX_DEPTH = 4

pruneSig :: Int -> CprSig -> CprSig
pruneSig d (CprSig cpr_ty)
  = CprSig $ cpr_ty { ct_cpr = pruneDeepCpr d (ct_cpr cpr_ty) }

-- TODO: We need the lubCpr with the initial CPR because
--       of functions like iterate, which we would CPR
--       multiple levels deep, thereby changing termination
--       behavior.
markDiverging :: CprSig -> CprSig
markDiverging (CprSig cpr_ty) = CprSig $ cpr_ty { ct_cpr = ct_cpr cpr_ty `lubCpr` divergeCpr }

--
-- ** Analysing a binding (one-round, the non-recursive case)
--

-- | Process the RHS of the binding for a sensible arity, add the CPR signature
-- to the Id, and augment the environment with the signature as well.
cprAnalBind
  :: TopLevelFlag
  -> AnalEnv
  -> Widening -- ^ We want to specify 'depthWidening' in fixed-point iteration
  -> [CprType]
  -> Id
  -> CoreExpr
  -> (Id, CoreExpr, AnalEnv)
cprAnalBind top_lvl env widening args id rhs
  -- See Note [CPR for expandable unfoldings]
  | isJust (cprExpandUnfolding_maybe id)
  = (id, rhs, env)
  | otherwise
  = (id', rhs', env')
  where
    arg_tys             = fst (splitFunNewTys (idType id))
    -- We compute the Termination and CPR transformer based on the strictness
    -- signature. There is no point in pretending that an arg we are strict in
    -- could lead to non-termination, as the signature then trivially
    -- MightDiverge. Instead we assume that call sites make sure to force the
    -- arguments appropriately and unleash the TerminationFlag there.
    assumed_arg_cpr_tys = argCprTypesFromStrictSig (unboxingStrategy env)
                                                   arg_tys
                                                   (idStrictness id)

    -- TODO: Not sure if that special handling of join points is really
    -- necessary. It might even be harmful if the excess 'args' aren't unboxed
    -- and we blindly assume that they have the CPR property! So we should
    -- try out getting rid of this special case and 'args'.
    (rhs_ty, rhs')
      | isJoinId id = cprAnal env (assumed_arg_cpr_tys ++ args) rhs
      | otherwise   = cprAnal env assumed_arg_cpr_tys rhs

    -- possibly trim thunk CPR info
    rhs_ty'
      -- See Note [CPR for thunks]
      | stays_thunk = trimCprTy rhs_ty
      -- See Note [CPR for sum types]
      | returns_sum = trimCprTy rhs_ty
      | otherwise   = rhs_ty

    -- See Note [Arity trimming for CPR signatures]
    dflags          = ae_dflags env
    sig             = widening $ mkCprSigForArity dflags (idArity id) rhs_ty'
    (id', env')     = -- pprTrace "cprAnalBind" (ppr id $$ ppr sig) $
                      (setIdCprInfo id sig, extendSigEnv env id sig)

    -- See Note [CPR for thunks]
    stays_thunk = is_thunk && not_strict
    is_thunk    = idArity id == 0 && not (isJoinId id)
    not_strict  = not (isStrictDmd (idDemandInfo id))
    -- See Note [CPR for sum types]
    (_, ret_ty) = splitPiTys (idType id)
    not_a_prod  = isNothing (deepSplitProductType_maybe (ae_fam_envs env) ret_ty)
    returns_sum = not (isTopLevel top_lvl) && not_a_prod

unboxingStrategy :: AnalEnv -> UnboxingStrategy
unboxingStrategy env ty dmd
  = prj <$> wantToUnbox (ae_fam_envs env) has_inlineable_prag ty dmd
  where
    prj (dmds, DataConAppContext { dcac_dc = dc, dcac_arg_tys = tys_w_str })
      = (dc, map fst tys_w_str, dmds)
    -- Rather than maintaining in AnalEnv whether we are in an INLINEABLE
    -- function, we just assume that we aren't. That flag is only relevant
    -- to Note [Do not unpack class dictionaries], the few unboxing
    -- opportunities on dicts it prohibits are probably irrelevant to CPR.
    has_inlineable_prag = False

cprExpandUnfolding_maybe :: Id -> Maybe CoreExpr
cprExpandUnfolding_maybe id = do
  guard (idArity id == 0)
  -- There are only phase 0 Simplifier runs after CPR analysis
  guard (isActiveIn 0 (idInlineActivation id))
  expandUnfolding_maybe (idUnfolding id)

--
-- ** Analysing recursive bindings
--

-- | Fixed-point iteration
cprFix
  :: TopLevelFlag
  -> AnalEnv                    -- Does not include bindings for this binding
  -> [CprType]
  -> [(Id,CoreExpr)]
  -> (AnalEnv, [(Id,CoreExpr)]) -- Binders annotated with stricness info
cprFix top_lvl env args orig_pairs
  = loop 1 initial_pairs
  where
    init_sig id
      | isJust (cprExpandUnfolding_maybe id) = topCprSig
      | otherwise                            = mkCprSig (idArity id) divergeCpr
    -- See Note [Initialising strictness] in GHC.Core.Opt.DmdAnal
    initial_pairs | ae_virgin env = [(setIdCprInfo id (init_sig id), rhs) | (id, rhs) <- orig_pairs ]
                  | otherwise     = orig_pairs

    -- The fixed-point varies the idCprInfo field of the binders, and terminates if that
    -- annotation does not change any more.
    loop :: Int -> [(Id,CoreExpr)] -> (AnalEnv, [(Id,CoreExpr)])
    loop n pairs
      | found_fixpoint = (final_anal_env, pairs')
      | otherwise      = -- pprTrace "cprFix:loop" (ppr n <+> ppr (map fst pairs)) $
                         loop (n+1) pairs'
      where
        found_fixpoint    = selector pairs' == selector pairs
        selector          = map (idCprInfo . fst)
        first_round       = n == 1
        pairs'            = step first_round pairs
        final_anal_env    = extendSigEnvs env (map fst pairs')

    step :: Bool -> [(Id, CoreExpr)] -> [(Id, CoreExpr)]
    step first_round pairs = pairs'
      where
        -- In all but the first iteration, delete the virgin flag
        start_env | first_round = env
                  | otherwise   = nonVirgin env

        start = extendSigEnvs start_env (map fst pairs)

        (_, pairs') = mapAccumL anal_bind start pairs

        anal_bind env (id,rhs)
          = (env', (id', rhs'))
          where
            -- See Note [Ensuring termination of fixed-point iteration]
            (id', rhs', env') = cprAnalBind top_lvl env depthWidening args id rhs

{- Note [Arity trimming for CPR signatures]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Although it doesn't affect correctness of the analysis per se, we have to trim
CPR signatures to idArity. Here's what might happen if we don't:

  f x = if expensive
          then \y. Box y
          else \z. Box z
  g a b = f a b

The two lambdas will have a CPR type of @1m@ (so construct a product after
applied to one argument). Thus, @f@ will have a CPR signature of @2m@
(constructs a product after applied to two arguments).
But WW will never eta-expand @f@! In this case that would amount to possibly
duplicating @expensive@ work.

(Side note: Even if @f@'s 'idArity' happened to be 2, it would not do so, see
Note [Don't eta expand in w/w].)

So @f@ will not be worker/wrappered. But @g@ also inherited its CPR signature
from @f@'s, so it *will* be WW'd:

  f x = if expensive
          then \y. Box y
          else \z. Box z
  $wg a b = case f a b of Box x -> x
  g a b = Box ($wg a b)

And the case in @g@ can never cancel away, thus we introduced extra reboxing.
Hence we always trim the CPR signature of a binding to idArity.
-}

data AnalEnv
  = AE
  { ae_sigs   :: SigEnv
  -- ^ Current approximation of signatures for local ids
  , ae_virgin :: Bool
  -- ^ True only on every first iteration in a fixed-point
  -- iteration. See Note [Initialising strictness] in "DmdAnal"
  , ae_dflags :: DynFlags
  -- ^ For 'caseBinderCprDepth'.
  , ae_fam_envs :: FamInstEnvs
  -- ^ Needed when expanding type families and synonyms of product types.
  }

type SigEnv = VarEnv CprSig

instance Outputable AnalEnv where
  ppr (AE { ae_sigs = env, ae_virgin = virgin })
    = text "AE" <+> braces (vcat
         [ text "ae_virgin =" <+> ppr virgin
         , text "ae_sigs =" <+> ppr env ])

emptyAnalEnv :: DynFlags -> FamInstEnvs -> AnalEnv
emptyAnalEnv dflags fam_envs
  = AE
  { ae_sigs = emptyVarEnv
  , ae_virgin = True
  , ae_dflags = dflags
  , ae_fam_envs = fam_envs
  }

extendSigEnv :: AnalEnv -> Id -> CprSig -> AnalEnv
extendSigEnv env id sig
  = env { ae_sigs = extendVarEnv (ae_sigs env) id sig }

extendSigEnvList :: AnalEnv -> [(Id, CprSig)] -> AnalEnv
extendSigEnvList env ids_cprs
  = env { ae_sigs = extendVarEnvList (ae_sigs env) ids_cprs }

-- | Extend an environment with the CPR signatures attached to the id
extendSigEnvs :: AnalEnv -> [Id] -> AnalEnv
extendSigEnvs env ids
  = env { ae_sigs = sigs' }
  where
    sigs' = extendVarEnvList (ae_sigs env) [ (id, idCprInfo id) | id <- ids ]

lookupSigEnv :: AnalEnv -> Id -> Maybe CprSig
lookupSigEnv env id = lookupVarEnv (ae_sigs env) id

nonVirgin :: AnalEnv -> AnalEnv
nonVirgin env = env { ae_virgin = False }

extendEnvForDataAlt :: AnalEnv -> Id -> CprType -> DataCon -> [Var] -> AnalEnv
-- See Note [CPR in a DataAlt case alternative]
extendEnvForDataAlt env case_bndr case_bndr_ty dc bndrs
  = extendSigEnv env' case_bndr (CprSig case_bndr_ty')
  where
    tycon          = dataConTyCon dc
    is_product     = isJust (isDataProductTyCon_maybe tycon)
    is_sum         = isJust (isDataSumTyCon_maybe tycon)
    case_bndr_ty'
      | is_product || is_sum = markOptimisticConCprType dc case_bndr_ty
      -- Any of the constructors had existentials. This is a little too
      -- conservative (after all, we only care about the particular data con),
      -- but there is no easy way to write is_sum and this won't happen much.
      | otherwise            = case_bndr_ty
    env'
      | Just fields <- splitConCprTy dc case_bndr_ty'
      , let ids     = filter isId bndrs
      , let cpr_tys = map (CprSig . CprType 0) fields
      = extendSigEnvList env (zipEqual "extendEnvForDataAlt" ids cpr_tys)
      | otherwise
      = env

{- Note [Ensuring termination of fixed-point iteration]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Fixed-point iteration may fail to terminate for a function like repeat:

  repeat x = x : repeat x

In the first  round, we will infer the Cpr 2(-, -).
In the second round, we will infer the Cpr 2(-, 2(-, -)).
And so on.

Hence it is important to apply a /widening/ operator between iterations to
ensure termination. In the case of DmdAnal, that is simply a check on the
number of iterations, defaulting to Top after a certain limit
(See Note [Safe abortion in the fixed-point iteration] in DmdAnal).
In case of CprAnal, we simply prune Cpr and Termination info after each
iteration to a constant depth of mAX_DEPTH.

Note [CPR in a DataAlt case alternative]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In a case alternative, we want to give some of the binders the CPR property.
Specifically

 * The case binder; inside the alternative, the case binder always has
   the CPR property, meaning that a case on it will successfully cancel.
   Example:
        f True  x = case x of y { I# x' -> if x' ==# 3
                                           then y
                                           else I# 8 }
        f False x = I# 3

   By giving 'y' the CPR property, we ensure that 'f' does too, so we get
        f b x = case fw b x of { r -> I# r }
        fw True  x = case x of y { I# x' -> if x' ==# 3 then x' else 8 }
        fw False x = 3

   Of course there is the usual risk of re-boxing: we have 'x' available
   boxed and unboxed, but we return the unboxed version for the wrapper to
   box.  If the wrapper doesn't cancel with its caller, we'll end up
   re-boxing something that we did have available in boxed form.

 * Any strict binders with product type, can use
   Note [CPR for binders that will be unboxed]
   to anticipate worker/wrappering for strictness info.
   But we can go a little further. Consider

      data T = MkT !Int Int

      f2 (MkT x y) | y>0       = f2 (MkT x (y-1))
                   | otherwise = x

   For $wf2 we are going to unbox the MkT *and*, since it is strict, the
   first argument of the MkT; see Note [Add demands for strict constructors].
   But then we don't want box it up again when returning it!  We want
   'f2' to have the CPR property, so we give 'x' the CPR property.

 * It's a bit delicate because we're brittly anticipating worker/wrapper here.
   If the case above is scrutinising something other than an argument the
   original function, we really don't have the unboxed version available.  E.g
      g v = case foo v of
              MkT x y | y>0       -> ...
                      | otherwise -> x
   Here we don't have the unboxed 'x' available.  Hence the
   is_var_scrut test when making use of the strictness annotation.
   Slightly ad-hoc, because even if the scrutinee *is* a variable it
   might not be a onre of the arguments to the original function, or a
   sub-component thereof.  But it's simple, and nothing terrible
   happens if we get it wrong.  e.g. Trac #10694.

Note [CPR for binders that will be unboxed]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If a lambda-bound variable will be unboxed by worker/wrapper (so it must be
demanded strictly), then give it a CPR signature. Here's a concrete example
('f1' in test T10482a), assuming h is strict:

  f1 :: Int -> Int
  f1 x = case h x of
          A -> x
          B -> f1 (x-1)
          C -> x+1

If we notice that 'x' is used strictly, we can give it the CPR
property; and hence f1 gets the CPR property too.  It's sound (doesn't
change strictness) to give it the CPR property because by the time 'x'
is returned (case A above), it'll have been evaluated (by the wrapper
of 'h' in the example).

Moreover, if f itself is strict in x, then we'll pass x unboxed to
f1, and so the boxed version *won't* be available; in that case it's
very helpful to give 'x' the CPR property.

Note that

  * We only want to do this for something that definitely
    has product type, else we may get over-optimistic CPR results
    (e.g. from \x -> x!).

  * This also (approximately) applies to DataAlt field binders;
    See Note [CPR in a DataAlt case alternative].

  * See Note [CPR examples]

Note [CPR for sum types]
~~~~~~~~~~~~~~~~~~~~~~~~
At the moment we do not do CPR for let-bindings that
   * non-top level
   * bind a sum type
Reason: I found that in some benchmarks we were losing let-no-escapes,
which messed it all up.  Example
   let j = \x. ....
   in case y of
        True  -> j False
        False -> j True
If we w/w this we get
   let j' = \x. ....
   in case y of
        True  -> case j' False of { (# a #) -> Just a }
        False -> case j' True of { (# a #) -> Just a }
Notice that j' is not a let-no-escape any more.

However this means in turn that the *enclosing* function
may be CPR'd (via the returned Justs).  But in the case of
sums, there may be Nothing alternatives; and that messes
up the sum-type CPR.

Conclusion: only do this for products.  It's still not
guaranteed OK for products, but sums definitely lose sometimes.

Note [CPR for thunks]
~~~~~~~~~~~~~~~~~~~~~
If the rhs is a thunk, we usually forget the CPR info, because
it is presumably shared (else it would have been inlined, and
so we'd lose sharing if w/w'd it into a function).  E.g.

        let r = case expensive of
                  (a,b) -> (b,a)
        in ...

If we marked r as having the CPR property, then we'd w/w into

        let $wr = \() -> case expensive of
                            (a,b) -> (# b, a #)
            r = case $wr () of
                  (# b,a #) -> (b,a)
        in ...

But now r is a thunk, which won't be inlined, so we are no further ahead.
But consider

        f x = let r = case expensive of (a,b) -> (b,a)
              in if foo r then r else (x,x)

Does f have the CPR property?  Well, no.

However, if the strictness analyser has figured out (in a previous
iteration) that it's strict, then we DON'T need to forget the CPR info.
Instead we can retain the CPR info and do the thunk-splitting transform
(see WorkWrap.splitThunk).

This made a big difference to PrelBase.modInt, which had something like
        modInt = \ x -> let r = ... -> I# v in
                        ...body strict in r...
r's RHS isn't a value yet; but modInt returns r in various branches, so
if r doesn't have the CPR property then neither does modInt
Another case I found in practice (in Complex.magnitude), looks like this:
                let k = if ... then I# a else I# b
                in ... body strict in k ....
(For this example, it doesn't matter whether k is returned as part of
the overall result; but it does matter that k's RHS has the CPR property.)
Left to itself, the simplifier will make a join point thus:
                let $j k = ...body strict in k...
                if ... then $j (I# a) else $j (I# b)
With thunk-splitting, we get instead
                let $j x = let k = I#x in ...body strict in k...
                in if ... then $j a else $j b
This is much better; there's a good chance the I# won't get allocated.

But what about botCpr? Consider
    lvl = error "boom"
    fac -1 = lvl
    fac 0 = 1
    fac n = n * fac (n-1)
fac won't have the CPR property here when we trim every thunk! But the
assumption is that error cases are rarely entered and we are diverging anyway,
so WW doesn't hurt.

Should we also trim CPR on DataCon application bindings?
See Note [CPR for expandable unfoldings]!

Note [CPR for expandable unfoldings]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Long static data structures (whether top-level or not) like

  xs = x1 : xs1
  xs1 = x2 : xs2
  xs2 = x3 : xs3

should not get CPR signatures, because they

  * Never get WW'd, so their CPR signature should be irrelevant after analysis
    (in fact the signature might even be harmful for that reason)
  * Would need to be inlined/expanded to see their constructed product
  * Recording CPR on them blows up interface file sizes and is redundant with
    their unfolding. In case of Nested CPR, this blow-up can be quadratic!

But we can't just stop giving DataCon application bindings the CPR property,
for example

  fac 0 = 1
  fac n = n * fac (n-1)

fac certainly has the CPR property and should be WW'd! But FloatOut will
transform the first clause to

  lvl = 1
  fac 0 = lvl

If lvl doesn't have the CPR property, fac won't either. But lvl doesn't have a
CPR signature to extrapolate into a CPR transformer ('cprTransform'). So
instead we keep on cprAnal'ing through *expandable* unfoldings for these arity
0 bindings via 'cprExpandUnfolding_maybe'.

In practice, GHC generates a lot of (nested) TyCon and KindRep bindings, one
for each data declaration. It's wasteful to attach CPR signatures to each of
them (and intractable in case of Nested CPR).

Also we don't need to analyse RHSs of expandable bindings: The CPR signature of
the binding is never consulted and there may not be let or case expressions
nested inside its RHS. In which case we also don't record a signature in the
local AnalEnv. Doing so would override looking into the unfolding. Why not give
the expandable case in cprTransform a higher priority then? Because then *all*
case binders would get the CPR property, regardless of -fcase-binder-cpr-depth,
because case binders have expandable unfoldings.

Tracked by #18154.

Note [CPR examples]
~~~~~~~~~~~~~~~~~~~~
Here are some examples (stranal/should_compile/T10482a) of the
usefulness of Note [CPR in a DataAlt case alternative].  The main
point: all of these functions can have the CPR property.

    ------- f1 -----------
    -- x is used strictly by h, so it'll be available
    -- unboxed before it is returned in the True branch

    f1 :: Int -> Int
    f1 x = case h x x of
            True  -> x
            False -> f1 (x-1)

    ------- f3 -----------
    -- h is strict in x, so x will be unboxed before it
    -- is rerturned in the otherwise case.

    data T3 = MkT3 Int Int

    f1 :: T3 -> Int
    f1 (MkT3 x y) | h x y     = f3 (MkT3 x (y-1))
                  | otherwise = x
-}
