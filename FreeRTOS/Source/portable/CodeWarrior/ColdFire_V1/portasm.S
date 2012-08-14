/*
    FreeRTOS V7.2.0 - Copyright (C) 2012 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/*
 * Purpose: Lowest level routines for all ColdFire processors.
 *
 * Notes:
 * 
 * ulPortSetIPL() and mcf5xxx_wr_cacr() copied with permission from FreeScale
 * supplied source files.
 */

    .global ulPortSetIPL
    .global _ulPortSetIPL
    .global mcf5xxx_wr_cacrx
    .global _mcf5xxx_wr_cacrx
    .global vPortYieldISR
    .global _vPortYieldISR
    .global vPortStartFirstTask
    .global _vPortStartFirstTask
    .extern _pxCurrentTCB
    .extern _vPortYieldHandler

    .text

.macro portSAVE_CONTEXT

	lea.l		(-60, sp), sp
	movem.l		d0-a6, (sp)
	move.l		_pxCurrentTCB, a0
	move.l		sp, (a0)

	.endm

.macro portRESTORE_CONTEXT

	move.l		_pxCurrentTCB, a0
	move.l		(a0), sp
	movem.l		(sp), d0-a6
	lea.l		(60, sp), sp
	rte

	.endm

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

ulPortSetIPL:
_ulPortSetIPL:
    link    A6,#-8
    movem.l D6-D7,(SP)

    move.w  SR,D7       /* current sr    */

    move.l  D7,D6       /* prepare return value  */
    andi.l  #0x0700,D6  /* mask out IPL  */
    lsr.l   #8,D6       /* IPL   */

    andi.l  #0x07,D0    /* least significant three bits  */
    lsl.l   #8,D0       /* move over to make mask    */

    andi.l  #0x0000F8FF,D7  /* zero out current IPL  */
    or.l    D0,D7           /* place new IPL in sr   */
    move.w  D7,SR

	move.l	D6, D0		/* Return value in D0. */
    movem.l (SP),D6-D7
    lea     8(SP),SP
    unlk    A6
    rts
/********************************************************************/

mcf5xxx_wr_cacrx:
_mcf5xxx_wr_cacrx:
    move.l  4(sp),d0
    .long   0x4e7b0002  /* movec d0,cacr   */
    nop
    rts

/********************************************************************/

/* Yield interrupt. */
_vPortYieldISR:
vPortYieldISR:
	portSAVE_CONTEXT
	jsr _vPortYieldHandler
	portRESTORE_CONTEXT

/********************************************************************/


vPortStartFirstTask:
_vPortStartFirstTask:
	portRESTORE_CONTEXT

    .end


