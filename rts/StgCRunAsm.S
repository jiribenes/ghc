#include "ghcconfig.h"
#include "rts/Constants.h"

/* If the RTS mini interpreter is used, e.g. for unregisterised builds,
 * then functions StgRun/StgReturn are implemented in file StgCRun.c */
#if !defined(USE_MINIINTERPRETER)

#if defined(powerpc64le_HOST_ARCH)
# if defined(linux_HOST_OS)
/* 64-bit PowerPC ELF V2 ABI Revision 1.4
 *
 * Stack frame organization (see Figure 2.18, ELF V2 ABI Revision 1.4, p 31)
 *
 * +-> Back Chain (points to the prevoius stack frame)
 * |   Floating point register save area (f14-f31)
 * |   General register save area (r14-r31)
 * |   ... unused (optional) save areas (size 0)
 * |   Local variable space
 * |   Parameter save area (8 doublewords)
 * |   ... stack header (TOC, LR, CR)
 * +-- Back chain           <---- SP (r1)
 *
 * We save all callee-saves general purpose registers (r14-r31, _savegpr1_14)
 * and all callee-saves floating point registers (f14-31, _savefpr14) and
 * the return address of the caller (LR), which is saved in the caller's
 * stack frame as required by the ABI. We only modify the CR0 and CR1 fields
 * of the condition register and those are caller-saves, so we don't save CR.
 *
 * StgReturn restores all saved registers from their respective locations
 * on the stack before returning to the caller.
 *
 * There is no need to save the TOC register (r2) because we will return
 * through StgReturn. All calls to StgReturn will be to the global entry
 * point and we compute the TOC from the entry address of StgReturn, which
 * is required to be in r12 by the ABI.
 */
# define STACK_FRAME_SIZE (RESERVED_C_STACK_BYTES+288+15) & ~15
	.file	"StgCRun.c"
	.abiversion 2
	.section	".toc","aw"
	.section	".text"
	.align 2
        .globl StgRun
        .hidden StgRun
        .type StgRun,@function
StgRun:
        .localentry StgRun,.-StgRun
	mflr 0
        addi 12,1,-(8*18)
        bl _savegpr1_14
        bl _savefpr_14
	stdu 1, -(STACK_FRAME_SIZE)(1)
	mr 27, 4
	mtctr 3
	mr 12, 3
	bctr

        .globl StgReturn
        .type StgReturn,@function
StgReturn:
        addis 2,12,.TOC.-StgReturn@ha
        addi 2,2,.TOC.-StgReturn@l
        .localentry StgReturn,.-StgReturn
	mr 3,14
	la 1, STACK_FRAME_SIZE(1)
        addi 12,1,-(8*18)
        bl _restgpr1_14
        b _restfpr_14

	.section	.note.GNU-stack,"",@progbits
# else // linux_HOST_OS
# error Only Linux support for power64 little endian right now.
# endif

#elif defined(powerpc_HOST_ARCH)
# if defined(aix_HOST_OS)
# define STACK_FRAME_SIZE RESERVED_C_STACK_BYTES+224
	.toc
	.csect StgRun[DS]
	.globl StgRun[DS]
	.long .StgRun, TOC[TC0], 0
	.csect .text[PR]
	.globl .StgRun
.StgRun:
	mflr  0
	mr    5,1
	stw   0,8(1)
	stwu  1,-(STACK_FRAME_SIZE)(1)
	stw   2,-224(5)
	stmw 13,-220(5)
	stfd 14,-144(5)
	stfd 15,-136(5)
	stfd 16,-128(5)
	stfd 17,-120(5)
	stfd 18,-112(5)
	stfd 19,-104(5)
	stfd 20,-96(5)
	stfd 21,-88(5)
	stfd 22,-80(5)
	stfd 23,-72(5)
	stfd 24,-64(5)
	stfd 25,-56(5)
	stfd 26,-48(5)
	stfd 27,-40(5)
	stfd 28,-32(5)
	stfd 29,-24(5)
	stfd 30,-16(5)
	stfd 31,-8(5)
	mr   27,4
	mtctr 3
	bctr

	.globl StgReturn
StgReturn:
	mr   3,14
	la   5,(STACK_FRAME_SIZE)(1)
	lwz  2,-224(5)
	lmw 13,-220(5)
	lfd 14,-144(5)
	lfd 15,-136(5)
	lfd 16,-128(5)
	lfd 17,-120(5)
	lfd 18,-112(5)
	lfd 19,-104(5)
	lfd 20,-96(5)
	lfd 21,-88(5)
	lfd 22,-80(5)
	lfd 23,-72(5)
	lfd 24,-64(5)
	lfd 25,-56(5)
	lfd 26,-48(5)
	lfd 27,-40(5)
	lfd 28,-32(5)
	lfd 29,-24(5)
	lfd 30,-16(5)
	lfd 31,-8(5)
	mr   1,5
	lwz  0,8(1)
	mtlr 0
	blr

# endif // aix_HOST_OS

#elif defined(s390x_HOST_ARCH)
# define STACK_FRAME_SIZE (RESERVED_C_STACK_BYTES+160)
	.text
	.align 8
	.globl StgRun
	.type StgRun, @function
StgRun:
	.cfi_startproc
	/* save callee-saved registers */
	stmg %r6,%r14,16(%r15)
	std  %f8,     88(%r15)
	std  %f9,     96(%r15)
	std  %f10,   104(%r15)
	std  %f11,   112(%r15)
	std  %f12,   120(%r15)
	std  %f13,   128(%r15)
	std  %f14,   136(%r15)
	std  %f15,   144(%r15)
	.cfi_offset  6, -144
	.cfi_offset  7, -136
	.cfi_offset  8, -128
	.cfi_offset  9, -120
	.cfi_offset 10, -112
	.cfi_offset 11, -104
	.cfi_offset 12,  -96
	.cfi_offset 13,  -88
	.cfi_offset 14,  -80
	.cfi_offset 15,  -72
	.cfi_offset 24,  -64
	.cfi_offset 28,  -56
	.cfi_offset 25,  -48
	.cfi_offset 29,  -40
	.cfi_offset 26,  -32
	.cfi_offset 30,  -24
	.cfi_offset 27,  -16
	.cfi_offset 31,   -8
	/* allocate stack frame */
	aghi %r15,-STACK_FRAME_SIZE
	.cfi_def_cfa_offset -(STACK_FRAME_SIZE+160)
	/* set STGs BaseReg from S390Xs r3 */
	lgr  %r7,%r3
	/* jump to STG function */
	br   %r2
	.cfi_endproc
	.size StgRun, .-StgRun

	.text
	.align 8
	.globl StgReturn
	.type StgReturn, @function
StgReturn:
	.cfi_startproc
	/* set return value from STGs R1 (S390Xs r11) */
	lgr  %r2,%r11
	/* deallocate stack frame */
	aghi %r15,STACK_FRAME_SIZE
	.cfi_def_cfa_offset (STACK_FRAME_SIZE+160)
	/* restore callee-saved registers */
	lmg  %r6,%r14, 16(%r15)
	ld   %f8,      88(%r15)
	ld   %f9,      96(%r15)
	ld   %f10,    104(%r15)
	ld   %f11,    112(%r15)
	ld   %f12,    120(%r15)
	ld   %f13,    128(%r15)
	ld   %f14,    136(%r15)
	ld   %f15,    144(%r15)
	.cfi_restore  6
	.cfi_restore  7
	.cfi_restore  8
	.cfi_restore  9
	.cfi_restore 10
	.cfi_restore 11
	.cfi_restore 12
	.cfi_restore 13
	.cfi_restore 14
	.cfi_restore 24
	.cfi_restore 28
	.cfi_restore 25
	.cfi_restore 29
	.cfi_restore 26
	.cfi_restore 30
	.cfi_restore 27
	.cfi_restore 31
	.cfi_def_cfa 15, 160
	/* jump back to caller of StgRun() */
	br   %r14
	.cfi_endproc
	.size StgReturn, .-StgReturn

	.section	.note.GNU-stack,"",@progbits
#endif

#endif /* !USE_MINIINTERPRETER */
