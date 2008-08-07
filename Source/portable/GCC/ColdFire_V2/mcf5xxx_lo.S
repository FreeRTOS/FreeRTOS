
/*
 * File:    mcf5xxx.s
 * Purpose: Lowest level routines for all ColdFire processors.
 *
 * Notes:
 *
 * File provided by FreeScale.
 */

    .global french_cheese

    .text

/********************************************************************
 * This routine is the lowest-level exception handler.
 */
 /*
asm_exception_handler:
_asm_exception_handler:
    lea     -16(SP),SP
    movem.l D0-D1/A0-A1,(SP)
    lea     16(SP),A1
    move.l  A1,-(SP)
    jsr     mcf5xxx_exception_handler
    lea     4(SP),SP
    movem.l (SP),D0-D1/A0-A1
    lea     16(SP),SP
    rte

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

french_cheese:
    link    A6,#-8
    movem.l D6-D7,(SP)

    move.w  SR,D7       /* current sr    */

    move.l  D7,D0       /* prepare return value  */
    andi.l  #0x0700,D0  /* mask out IPL  */
    lsr.l   #8,D0       /* IPL   */

    move.l  8(A6),D6    /* get argument  */
    andi.l  #0x07,D6        /* least significant three bits  */
    lsl.l   #8,D6       /* move over to make mask    */

    andi.l  #0x0000F8FF,D7  /* zero out current IPL  */
    or.l    D6,D7           /* place new IPL in sr   */
    move.w  D7,SR

    movem.l (SP),D6-D7
    lea     8(SP),SP
    unlk    A6
    rts

/********************************************************************/
    .end




#if 0

/*
 * File:    mcf5xxx.s
 * Purpose: Lowest level routines for all ColdFire processors.
 *
 * Notes:
 *
 */

#define mcf5xxx_exception_handler   _mcf5xxx_exception_handler

    .extern mcf5xxx_exception_handler

    //.global asm_exception_handler
    //.global _asm_exception_handler
    .global asm_set_ipl
    .global _asm_set_ipl
    .global mcf5xxx_exe_wdebug
    .global _mcf5xxx_exe_wdebug
    //.global mcf5xxx_wr_cacr
    //.global _mcf5xxx_wr_cacr
    .global mcf5xxx_wr_asid
    .global _mcf5xxx_wr_asid
    .global mcf5xxx_wr_acr0
    .global _mcf5xxx_wr_acr0
    .global mcf5xxx_wr_acr1
    .global _mcf5xxx_wr_acr1
    .global mcf5xxx_wr_acr2
    .global _mcf5xxx_wr_acr2
    .global mcf5xxx_wr_acr3
    .global _mcf5xxx_wr_acr3
    .global mcf5xxx_wr_mmubar
    .global _mcf5xxx_wr_mmubar
    .global mcf5xxx_wr_other_a7
    .global _mcf5xxx_wr_other_a7
   // .global mcf5xxx_wr_vbr
   // .global _mcf5xxx_wr_vbr
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
    .global mcf5xxx_wr_pc
    .global _mcf5xxx_wr_pc
    .global mcf5xxx_wr_rombar0
    .global _mcf5xxx_wr_rombar0
    .global mcf5xxx_wr_rombar1
    .global _mcf5xxx_wr_rombar1
    .global mcf5xxx_wr_rambar0
    .global _mcf5xxx_wr_rambar0
    .global mcf5xxx_wr_rambar1
    .global _mcf5xxx_wr_rambar1
    .global mcf5xxx_wr_mpcr
    .global _mcf5xxx_wr_mpcr
    .global mcf5xxx_wr_secmbar
    .global _mcf5xxx_wr_secmbar
    .global mcf5xxx_wr_mbar
    .global _mcf5xxx_wr_mbar

    .text

/********************************************************************
 * This routine is the lowest-level exception handler.
 */
 /*
asm_exception_handler:
_asm_exception_handler:
    lea     -16(SP),SP
    movem.l D0-D1/A0-A1,(SP)
    lea     16(SP),A1
    move.l  A1,-(SP)
    jsr     mcf5xxx_exception_handler
    lea     4(SP),SP
    movem.l (SP),D0-D1/A0-A1
    lea     16(SP),SP
    rte

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
    link    A6,#-8
    movem.l D6-D7,(SP)

    move.w  SR,D7       /* current sr    */

    move.l  D7,D0       /* prepare return value  */
    andi.l  #0x0700,D0  /* mask out IPL  */
    lsr.l   #8,D0       /* IPL   */

    move.l  8(A6),D6    /* get argument  */
    andi.l  #0x07,D6        /* least significant three bits  */
    lsl.l   #8,D6       /* move over to make mask    */

    andi.l  #0x0000F8FF,D7  /* zero out current IPL  */
    or.l    D6,D7           /* place new IPL in sr   */
    move.w  D7,SR

    movem.l (SP),D6-D7
    lea     8(SP),SP
    unlk    A6
    rts

/********************************************************************/
/*
 * These routines execute special ColdFire instructions
 */

mcf5xxx_exe_wdebug:
_mcf5xxx_exe_wdebug:
    move.l   4(sp),a0
    wdebug.l (a0)
    rts

/********************************************************************/
/*
 * These routines write to the special purpose registers in the ColdFire
 * core.  Since these registers are write-only in the supervisor model,
 * no corresponding read routines exist.
 */

mcf5xxx_wr_sr:
_mcf5xxx_wr_sr:
    move.l  4(SP),D0
    move.w  D0,SR
    rts
/*
mcf5xxx_wr_cacr:
_mcf5xxx_wr_cacr:
    move.l  4(SP),D0
    .long   0x4e7b0002      /* movec d0,cacr */
/*
    nop
    rts
*/
mcf5xxx_wr_asid:
_mcf5xxx_wr_asid:
    move.l  4(SP),D0
    .long   0x4e7b0003      /* movec d0,asid */
    nop
    rts

mcf5xxx_wr_acr0:
_mcf5xxx_wr_acr0:
    move.l  4(SP),D0
    .long   0x4e7b0004      /* movec d0,ACR0 */
    nop
    rts

mcf5xxx_wr_acr1:
_mcf5xxx_wr_acr1:
    move.l  4(SP),D0
    .long   0x4e7b0005      /* movec d0,ACR1 */
    nop
    rts

mcf5xxx_wr_acr2:
_mcf5xxx_wr_acr2:
    move.l  4(SP),D0
    .long   0x4e7b0006      /* movec d0,ACR2 */
    nop
    rts

mcf5xxx_wr_acr3:
_mcf5xxx_wr_acr3:
    move.l  4(SP),D0
    .long   0x4e7b0007      /* movec d0,ACR3 */
    nop
    rts

mcf5xxx_wr_mmubar:
_mcf5xxx_wr_mmubar:
    move.l  4(SP),D0
    .long   0x4e7b0008      /* movec d0,MBAR */
    nop
    rts

mcf5xxx_wr_other_a7:
_mcf5xxx_wr_other_a7:
    move.l  4(SP),D0
    .long   0x4e7b0800      /* movec d0,OTHER_A7 */
    nop
    rts

/*
mcf5xxx_wr_vbr:
_mcf5xxx_wr_vbr:
    move.l  4(SP),D0
    .long   0x4e7b0801      /* movec d0,VBR */
    /*
    nop
    rts
*/
mcf5xxx_wr_macsr:
_mcf5xxx_wr_macsr:
    move.l  4(SP),D0
    .long   0x4e7b0804      /* movec d0,MACSR */
    nop
    rts

mcf5xxx_wr_mask:
_mcf5xxx_wr_mask:
    move.l  4(SP),D0
    .long   0x4e7b0805      /* movec d0,MASK */
    nop
    rts

mcf5xxx_wr_acc0:
_mcf5xxx_wr_acc0:
    move.l  4(SP),D0
    .long   0x4e7b0806      /* movec d0,ACC0 */
    nop
    rts

mcf5xxx_wr_accext01:
_mcf5xxx_wr_accext01:
    move.l  4(SP),D0
    .long   0x4e7b0807      /* movec d0,ACCEXT01 */
    nop
    rts

mcf5xxx_wr_accext23:
_mcf5xxx_wr_accext23:
    move.l  4(SP),D0
    .long   0x4e7b0808      /* movec d0,ACCEXT23 */
    nop
    rts

mcf5xxx_wr_acc1:
_mcf5xxx_wr_acc1:
    move.l  4(SP),D0
    .long   0x4e7b0809      /* movec d0,ACC1 */
    nop
    rts

mcf5xxx_wr_acc2:
_mcf5xxx_wr_acc2:
    move.l  4(SP),D0
    .long   0x4e7b080A      /* movec d0,ACC2 */
    nop
    rts

mcf5xxx_wr_acc3:
_mcf5xxx_wr_acc3:
    move.l  4(SP),D0
    .long   0x4e7b080B      /* movec d0,ACC3 */
    nop
    rts

mcf5xxx_wr_pc:
_mcf5xxx_wr_pc:
    move.l  4(SP),D0
    .long   0x4e7b080F      /* movec d0,PC */
    nop
    rts

mcf5xxx_wr_rombar0:
_mcf5xxx_wr_rombar0:
    move.l  4(SP),D0
    .long   0x4e7b0C00      /* movec d0,ROMBAR0 */
    nop
    rts

mcf5xxx_wr_rombar1:
_mcf5xxx_wr_rombar1:
    move.l  4(SP),D0
    .long   0x4e7b0C01      /* movec d0,ROMBAR1 */
    nop
    rts

mcf5xxx_wr_rambar0:
_mcf5xxx_wr_rambar0:
    move.l  4(SP),D0
    .long   0x4e7b0C04      /* movec d0,RAMBAR0 */
    nop
    rts

mcf5xxx_wr_rambar1:
_mcf5xxx_wr_rambar1:
    move.l  4(SP),D0
    .long   0x4e7b0C05      /* movec d0,RAMBAR1 */
    nop
    rts

mcf5xxx_wr_mpcr:
_mcf5xxx_wr_mpcr:
    move.l  4(SP),D0
    .long   0x4e7b0C0C      /* movec d0,MPCR */
    nop
    rts

mcf5xxx_wr_secmbar:
_mcf5xxx_wr_secmbar:
    move.l  4(SP),D0
    .long   0x4e7b0C0E      /* movec d0,MBAR1   */
    nop
    rts

mcf5xxx_wr_mbar:
_mcf5xxx_wr_mbar:
    move.l  4(SP),D0
    .long   0x4e7b0C0F      /* movec d0,MBAR0   */
    nop
    rts

/********************************************************************/
    .end

#endif
