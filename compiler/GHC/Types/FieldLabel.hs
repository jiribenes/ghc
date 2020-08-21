{-
%
% (c) Adam Gundry 2013-2020
%

This module defines the representation of FieldLabels as stored in
TyCons.  As well as a selector name, these have some extra structure
to support the DuplicateRecordFields extension.

In the normal case (with NoDuplicateRecordFields), a datatype like

    data T = MkT { foo :: Int }

has

    FieldLabel { flLabel        = "foo"
               , flIsOverloaded = False
               , flUpdate       = $upd:foo:MkT
               , flSelector     = foo }.

In particular, the Name of the selector has the same string representation as
the label.  Regarding the flUpdate field, see Note [Updater names].

If DuplicateRecordFields is enabled, however, the same declaration instead gives

    FieldLabel { flLabel        = "foo"
               , flIsOverloaded = True
               , flUpdate       = $upd:foo:MkT
               , flSelector     = $sel:foo:MkT }.

Now the name of the selector ($sel:foo:MkT) does not match the label of
the field (foo).  We must be careful not to show the selector name to
the user!  The point of mangling the selector name is to allow a
module to define the same field label in different datatypes:

    data T = MkT { foo :: Int }
    data U = MkU { foo :: Bool }

Now there will be two FieldLabel values for 'foo', one in T and one in
U.  They share the same label (FieldLabelString), but the selector
functions differ.

See also Note [Representing fields in AvailInfo] in GHC.Types.Avail.

Note [Why selector names include data constructors]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

As explained above, a selector name includes the name of the first
data constructor in the type, so that the same label can appear
multiple times in the same module.  (This is irrespective of whether
the first constructor has that field, for simplicity.)

We use a data constructor name, rather than the type constructor name,
because data family instances do not have a representation type
constructor name generated until relatively late in the typechecking
process.

Of course, datatypes with no constructors cannot have any fields.

Note [Updater names]
~~~~~~~~~~~~~~~~~~~~
As well as the name of the selector for a field label, we sometimes need to
store the name of the updater, which is a pre-generated function for updating a
sole field of a record.  See Note [Record updaters] in GHC.Tc.TyCl.Utils, which
describes how updaters are constructed and used.

However, in some circumstance we do not need the updater name:

 * The renamer uses the selector name to uniquely identify the field, but the
   updater name is irrelevant for renaming, so field labels with only selector
   names appear in AvailInfo and IE.  (Arguably it might be better for the
   renamer not to rely on the selector name like this, but changing it would be
   a major effort.)

 * Record pattern synonyms do not have updaters, but they do contain field
   labels.  (See Note [No updaters for pattern synonyms] in GHC.Tc.TyCl.Utils.)

The FieldLbl type is parameterised over the representations of updater names and
selector names, so we can vary whether updater names are available
(FieldLabelWithUpdate) or not (FieldLabel).

-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}

module GHC.Types.FieldLabel
   ( FieldLabelString
   , FieldLabelEnv
   , FieldLbl(..)
   , FieldLabel
   , FieldLabelWithUpdate
   , mkFieldLabelOccs
   , fieldLabelWithoutUpdate
   , fieldLabelsWithoutUpdates
   )
where

import GHC.Prelude

import GHC.Types.Name.Occurrence
import GHC.Types.Name

import GHC.Data.FastString
import GHC.Data.FastString.Env
import GHC.Utils.Outputable
import GHC.Utils.Binary

import Data.Data

-- | Field labels are just represented as strings;
-- they are not necessarily unique (even within a module)
type FieldLabelString = FastString

-- | A map from labels to all the auxiliary information
type FieldLabelEnv = DFastStringEnv FieldLabelWithUpdate


-- | Representation of a field where we know the name of the selector function,
-- but not the updater.
type FieldLabel = FieldLbl () Name

-- | Representation of a field where we know the names of both the selector and
-- updater functions.
type FieldLabelWithUpdate = FieldLbl Name Name

-- | Fields in an algebraic record type
data FieldLbl update_rep selector_rep = FieldLabel {
      flLabel        :: FieldLabelString, -- ^ User-visible label of the field
      flIsOverloaded :: Bool,             -- ^ Was DuplicateRecordFields on
                                          --   in the defining module for this datatype?
      flUpdate       :: update_rep,       -- ^ Field updater function
                                          -- (See Note [Updater names])
      flSelector     :: selector_rep      -- ^ Record selector function
    }
  deriving (Eq, Functor, Foldable, Traversable)
deriving instance (Data a, Data b) => Data (FieldLbl a b)

instance Outputable b => Outputable (FieldLbl a b) where
    ppr fl = ppr (flLabel fl) <> braces (ppr (flSelector fl))

instance (Binary a, Binary b) => Binary (FieldLbl a b) where
    put_ bh (FieldLabel aa ab ac ad) = do
        put_ bh aa
        put_ bh ab
        put_ bh ac
        put_ bh ad
    get bh = do
        aa <- get bh
        ab <- get bh
        ac <- get bh
        ad <- get bh
        return (FieldLabel aa ab ac ad)


-- | Drop the updater names from a field label (see Note [Updater names]).
fieldLabelWithoutUpdate :: FieldLabelWithUpdate -> FieldLabel
fieldLabelWithoutUpdate fl = fl { flUpdate = () }

-- | Drop the updater names from a list of field labels.
fieldLabelsWithoutUpdates :: [FieldLabelWithUpdate] -> [FieldLabel]
fieldLabelsWithoutUpdates = map fieldLabelWithoutUpdate


-- | Record selector OccNames are built from the underlying field name
-- and the name of the first data constructor of the type, to support
-- duplicate record field names.
-- See Note [Why selector names include data constructors].
mkFieldLabelOccs :: FieldLabelString -> OccName -> Bool -> FieldLbl OccName OccName
mkFieldLabelOccs lbl dc is_overloaded
  = FieldLabel { flLabel = lbl, flIsOverloaded = is_overloaded
               , flUpdate = upd_occ, flSelector = sel_occ }
  where
    str     = ":" ++ unpackFS lbl ++ ":" ++ occNameString dc
    upd_occ = mkRecFldUpdOcc str
    sel_occ | is_overloaded = mkRecFldSelOcc str
            | otherwise     = mkVarOccFS lbl
