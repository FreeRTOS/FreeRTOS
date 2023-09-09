/*
 * File:	mcf5225x_lo.s
 * Purpose:	Low-level routines for the MCF5225x.
 *
 * Notes:	
 * 
 * License:     All software covered by license agreement in -
 *              docs/Freescale_Software_License.pdf
 */

#define mcf5225x_init   _mcf5225x_init
#define common_startup  _common_startup
#define cpu_startup     _cpu_startup
#define main	    	_main
#define __IPSBAR        ___IPSBAR   
#define __SRAM          ___SRAM     
#define __FLASH         ___FLASH    
#define __SP_INIT       ___SP_INIT  
 
	.extern __IPSBAR
	.extern __SRAM
	.extern __FLASH
	.extern __SP_INIT
	.extern mcf5225x_init
    .extern common_startup
    .extern cpu_startup
	.extern main

	.global asm_startmeup
	.global _asm_startmeup
	.global d0_reset
	.global _d0_reset
	.global d1_reset
	.global _d1_reset

    .data
    
d0_reset:
_d0_reset:  .long   0
d1_reset:
_d1_reset:  .long   0

	.text

/********************************************************************
 * 
 * This is the main entry point upon hard reset.  The memory map is
 * setup based on linker file definitions, then the higher level
 * system initialization routine is called.  Finally, we jump to the
 * "main" process. 
 */
asm_startmeup:
_asm_startmeup:

    move.w	#0x2700,sr

    /* Save off reset values of D0 and D1 */
    move.l  d0,d6
    move.l  d1,d7
    
    /* Initialize RAMBAR1: locate SRAM and validate it */
	move.l	#__SRAM,d0
	andi.l	#0xFFFF0000,d0
    add.l   #0x21,d0
    movec   d0,RAMBAR1

	/* Locate Stack Pointer */ 
	move.l	#__SP_INIT,sp

    /* Initialize IPSBAR */
	move.l	#__IPSBAR,d0
    add.l   #0x1,d0
	move.l	d0,0x40000000
	
    /* Initialize FLASHBAR */
    move.l  #__FLASH,d0
    cmp.l   #0x00000000,d0
    bne     change_flashbar
    add.l   #0x61,d0
    movec   d0,RAMBAR0

_continue_startup:

	/* Locate Stack Pointer */ 
	move.l	#__SP_INIT,sp

	/* Initialize the system */
	jsr		mcf5225x_init

    /* Common startup code */
    //jsr     common_startup

    /* Save off intial D0 and D1 to RAM */
    move.l  d6,d0_reset
    move.l  d7,d1_reset
    
    /* CPU specific startup code */
	//jsr     cpu_startup

	/* Jump to the main process */
	jsr		main
	
	bra		.
	nop
	nop
	halt

change_flashbar:
    /* 
     * The following sequence is used to set FLASHBAR. Since we may 
     * be executing from Flash, we must put the routine into SRAM for
     * execution and then jump back to Flash using the new address.
     *
     * The following instructions are coded into the SRAM:
     *
     * move.l	#(__FLASH + 0x21),d0
     * movec	d0, RAMBAR0
     * jmp		_continue_startup
     *
     * An arbitrary SRAM address is chosen until the real address
     * can be loaded.
     *
     * This routine is not necessary if the default Flash address
     * (0x00000000) is used.
     *
     * If running in SRAM, change_flashbar should not be executed 
     */

	move.l  #__SRAM,a0

	/* Code "move.l #(__FLASH + 0x21),d0" into SRAM */
	move.w  #0x203C,d0
	move.w  d0,(a0)+
	move.l  #__FLASH,d0
    add.l   #0x21,d0
    move.l  d0,(a0)+
	
	/* Code "movec d0,FLASHBAR" into SRAM */
	move.l  #0x4e7b0C04,d0
	move.l  d0,(a0)+
		
	/* Code "jmp _continue_startup" into SRAM */
	move.w  #0x4EF9,d0
	move.w  d0,(a0)+
	move.l  #_continue_startup,d0
	move.l  d0,(a0)+

	/* Jump to code segment in internal SRAM */
	jmp	    __SRAM

/********************************************************************/

	.end
