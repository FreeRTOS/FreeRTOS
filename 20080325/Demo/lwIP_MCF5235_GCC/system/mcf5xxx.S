/*
 * Lowest level routines for all ColdFire processors. Based on the
 * MCF523x examples from Freescale.
 *
 * Freescale explicitly grants the redistribution and modification
 * of these source files. The complete licensing information is
 * available in the file LICENSE_FREESCALE.TXT.
 *
 * Modifications Copyright (c) 2006 Christian Walter <wolti@sil.at>
 *
 * File: $Id: mcf5xxx.S,v 1.3 2006/09/24 22:50:23 wolti Exp $
 */

  .global asm_set_ipl
  .global _asm_set_ipl
  .global mcf5xxx_wr_cacr
  .global _mcf5xxx_wr_cacr
  .global mcf5xxx_wr_acr0
  .global _mcf5xxx_wr_acr0
  .global mcf5xxx_wr_acr1
  .global _mcf5xxx_wr_acr1
  .global mcf5xxx_wr_acr2
  .global _mcf5xxx_wr_acr2
  .global mcf5xxx_wr_acr3
  .global _mcf5xxx_wr_acr3
  .global mcf5xxx_wr_other_sp
  .global _mcf5xxx_wr_other_sp
  .global mcf5xxx_wr_other_a7
  .global _mcf5xxx_wr_other_a7
  .global mcf5xxx_wr_vbr
  .global _mcf5xxx_wr_vbr
  .global mcf5xxx_wr_macsr
  .global _mcf5xxx_wr_macsr
  .global mcf5xxx_wr_mask
  .global _mcf5xxx_wr_mask
  .global mcf5xxx_wr_acc0
  .global _mcf5xxx_wr_acc0
  .global mcf5xxx_wr_accext01
  .global _mcf5xxx_wr_accext01
  .global mcf5xxx_wr_accext23
  .global _mcf5xxx_wr_accext23
  .global mcf5xxx_wr_acc1
  .global _mcf5xxx_wr_acc1
  .global mcf5xxx_wr_acc2
  .global _mcf5xxx_wr_acc2
  .global mcf5xxx_wr_acc3
  .global _mcf5xxx_wr_acc3
  .global mcf5xxx_wr_sr
  .global _mcf5xxx_wr_sr
  .global mcf5xxx_wr_rambar0
  .global _mcf5xxx_wr_rambar0
  .global mcf5xxx_wr_rambar1
  .global _mcf5xxx_wr_rambar1
  .global mcf5xxx_wr_mbar
  .global _mcf5xxx_wr_mbar
  .global mcf5xxx_wr_mbar0
  .global _mcf5xxx_wr_mbar0
  .global mcf5xxx_wr_mbar1
  .global _mcf5xxx_wr_mbar1

  .text

/********************************************************************/
/*
 * This routines changes the IPL to the value passed into the routine.
 * It also returns the old IPL value back.
 * Calling convention from C:
 *   old_ipl = asm_set_ipl(new_ipl);
 * For the Diab Data C compiler, it passes return value thru D0.
 * Note that only the least significant three bits of the passed
 * value are used.
 */

asm_set_ipl:
_asm_set_ipl:
  link  a6,#-8
  movem.l d6-d7,(sp)

  move.w  sr,d7   /* current sr  */

  move.l  d7,d0   /* prepare return value  */
  andi.l  #0x0700,d0  /* mask out IPL  */
  lsr.l #8,d0   /* IPL   */

  move.l  8(a6),d6  /* get argument  */
  andi.l  #0x07,d6    /* least significant three bits  */
  lsl.l #8,d6   /* move over to make mask  */

  andi.l  #0x0000F8FF,d7  /* zero out current IPL  */
  or.l  d6,d7     /* place new IPL in sr   */
  move.w  d7,sr

  movem.l (sp),d6-d7
  lea   8(sp),sp
  unlk  a6
  rts

/********************************************************************/
/*
 * These routines write to the special purpose registers in the ColdFire
 * core.  Since these registers are write-only in the supervisor model,
 * no corresponding read routines exist.
 */

mcf5xxx_wr_cacr:
_mcf5xxx_wr_cacr:
    move.l  4(sp),d0
    .long   0x4e7b0002      /* movec d0,cacr   */
    nop
    rts

mcf5xxx_wr_acr0:
_mcf5xxx_wr_acr0:
    move.l  4(sp),d0
    .long   0x4e7b0004      /* movec d0,ACR0  */
    nop
    rts

mcf5xxx_wr_acr1:
_mcf5xxx_wr_acr1:
    move.l  4(sp),d0
    .long   0x4e7b0005      /* movec d0,ACR1  */
    nop
    rts

mcf5xxx_wr_acr2:
_mcf5xxx_wr_acr2:
    move.l  4(sp),d0
    .long   0x4e7b0006      /* movec d0,ACR2  */
    nop
    rts

mcf5xxx_wr_acr3:
_mcf5xxx_wr_acr3:
    move.l  4(sp),d0
    .long   0x4e7b0007      /* movec d0,ACR3  */
    nop
    rts

mcf5xxx_wr_other_sp:
_mcf5xxx_wr_other_sp:
mcf5xxx_wr_other_a7:
_mcf5xxx_wr_other_a7:
  move.l  4(sp),d0
  .long 0x4e7b0800    /* movec d0,OTHER_A7 */
  nop
  rts

mcf5xxx_wr_vbr:
_mcf5xxx_wr_vbr:
  move.l  4(sp),d0
  .long 0x4e7b0801    /* movec d0,VBR */
  nop
  rts

mcf5xxx_wr_macsr:
_mcf5xxx_wr_macsr:
    move.l  4(sp),d0
    .long   0x4e7b0804      /* movec d0,MACSR */
    nop
    rts

mcf5xxx_wr_mask:
_mcf5xxx_wr_mask:
    move.l  4(sp),d0
    .long   0x4e7b0805      /* movec d0,MASK  */
    nop
    rts

mcf5xxx_wr_acc0:
_mcf5xxx_wr_acc0:
    move.l  4(sp),d0
    .long   0x4e7b0806      /* movec d0,ACC0  */
    nop
    rts

mcf5xxx_wr_accext01:
_mcf5xxx_wr_accext01:
    move.l  4(sp),d0
    .long   0x4e7b0807      /* movec d0,ACCEXT01  */
    nop
    rts

mcf5xxx_wr_accext23:
_mcf5xxx_wr_accext23:
    move.l  4(sp),d0
    .long   0x4e7b0808      /* movec d0,ACCEXT23  */
    nop
    rts

mcf5xxx_wr_acc1:
_mcf5xxx_wr_acc1:
    move.l  4(sp),d0
    .long   0x4e7b0809      /* movec d0,ACC1  */
    nop
    rts

mcf5xxx_wr_acc2:
_mcf5xxx_wr_acc2:
    move.l  4(sp),d0
    .long   0x4e7b080A      /* movec d0,ACC2  */
    nop
    rts

mcf5xxx_wr_acc3:
_mcf5xxx_wr_acc3:
    move.l  4(sp),d0
    .long   0x4e7b080B      /* movec d0,ACC3  */
    nop
    rts

mcf5xxx_wr_sr:
_mcf5xxx_wr_sr:
  move.l  4(sp),d0
  move.w  d0,SR
  rts

mcf5xxx_wr_rambar0:
_mcf5xxx_wr_rambar0:
    move.l  4(sp),d0
    .long   0x4e7b0C04      /* movec d0,RAMBAR0 */
    nop
    rts

mcf5xxx_wr_rambar1:
_mcf5xxx_wr_rambar1:
    move.l  4(sp),d0
    .long   0x4e7b0C05      /* movec d0,RAMBAR1 */
    nop
    rts

mcf5xxx_wr_mbar:
_mcf5xxx_wr_mbar:
mcf5xxx_wr_mbar0:
_mcf5xxx_wr_mbar0:
    move.l  4(sp),d0
    .long   0x4e7b0C0F      /* movec d0,MBAR0 */
    nop
    rts

mcf5xxx_wr_mbar1:
_mcf5xxx_wr_mbar1:
    move.l  4(sp),d0
    .long   0x4e7b0C0E      /* movec d0,MBAR1 */
    nop
    rts

  .end
/********************************************************************/
