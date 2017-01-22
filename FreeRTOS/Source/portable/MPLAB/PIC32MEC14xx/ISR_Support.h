/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

#include "FreeRTOSConfig.h"

#define portCONTEXT_SIZE 132
#define portEPC_STACK_LOCATION 124
#define portSTATUS_STACK_LOCATION 128

#ifdef __LANGUAGE_ASSEMBLY__

/******************************************************************/
.macro	portSAVE_CONTEXT

	/* Make room for the context. First save the current status so it can be
	manipulated, and the cause and EPC registers so their original values are
	captured. */
	mfc0	k0, _CP0_CAUSE
	addiu	sp, sp, -portCONTEXT_SIZE
	mfc0	k1, _CP0_STATUS

	/* Also save s6 and s5 so they can be used.  Any nesting interrupts should
	maintain the values of these registers across the ISR. */
	sw		s6, 44(sp)
	sw		s5, 40(sp)
	sw		k1, portSTATUS_STACK_LOCATION(sp)

	/* Prepare to enable interrupts above the current priority.
	k0 = k0 >> 10. Moves RIPL[17:10] to [7:0] */
	srl		k0, k0, 0xa

	/* Insert bit field. 7 bits k0[6:0] to k1[16:10] */
	ins		k1, k0, 10, 7

	/* Sets CP0.Status.IPL = CP0.Cause.RIPL
	Copy the MSB of the IPL, but it would be an error if it was set anyway. */
	srl		k0, k0, 0x7

	/* MSB of IPL is bit[18] of CP0.Status */
	ins		k1, k0, 18, 1

	/* CP0.Status[5:1] = 0 b[5]=Rsvd, b[4]=UM,
	   b[3]=Rsvd, b[2]=ERL, b[1]=EXL
	   Setting EXL=0 allows higher priority interrupts
	   to preempt this handler */
	ins		k1, zero, 1, 4


	/* s5 is used as the frame pointer. */
	add		s5, zero, sp

	/* Check the nesting count value. */
	la		k0, uxInterruptNesting
	lw		s6, (k0)

	/* If the nesting count is 0 then swap to the the system stack, otherwise
	the system stack is already being used. */
	bne		s6, zero, 1f
	nop

	/* Swap to the system stack. */
	la		sp, xISRStackTop
	lw		sp, (sp)

	/* Increment and save the nesting count. */
1:  addiu   s6, s6, 1
	sw		s6, 0(k0)

	/* s6 holds the EPC value, this is saved after interrupts are re-enabled. */
	mfc0	s6, _CP0_EPC

	/* Re-enable interrupts. */
	mtc0	k1, _CP0_STATUS

	/* Save the context into the space just created.  s6 is saved again
	here as it now contains the EPC value.  No other s registers need be
	saved. */
	sw		ra, 120(s5) /* Return address (RA=R31) */
	sw		s8, 116(s5) /* Frame Pointer (FP=R30) */
	sw		t9, 112(s5)
	sw		t8, 108(s5)
	sw		t7, 104(s5)
	sw		t6, 100(s5)
	sw		t5, 96(s5)
	sw		t4, 92(s5)
	sw		t3, 88(s5)
	sw		t2, 84(s5)
	sw		t1, 80(s5)
	sw		t0, 76(s5)
	sw		a3, 72(s5)
	sw		a2, 68(s5)
	sw		a1, 64(s5)
	sw		a0, 60(s5)
	sw		v1, 56(s5)
	sw		v0, 52(s5)
	sw		s6, portEPC_STACK_LOCATION(s5)
	sw		$1, 16(s5)

	/* MEC14xx does not have DSP, removed 7 words */
	mfhi	s6
	sw		s6, 12(s5)
	mflo	s6
	sw		s6, 8(s5)

	/* Update the task stack pointer value if nesting is zero. */
	la		s6, uxInterruptNesting
	lw		s6, (s6)
	addiu	s6, s6, -1
	bne		s6, zero, 1f
	nop

	/* Save the stack pointer. */
	la		s6, uxSavedTaskStackPointer
	sw		s5, (s6)
1:
	.endm

/******************************************************************/
.macro	portRESTORE_CONTEXT

	/* Restore the stack pointer from the TCB.  This is only done if the
	nesting count is 1. */
	la		s6, uxInterruptNesting
	lw		s6, (s6)
	addiu   s6, s6, -1
	bne		s6, zero, 1f
	nop
	la		s6, uxSavedTaskStackPointer
	lw		s5, (s6)

	/* Restore the context.
	MCHP MEC14xx does not include DSP */
1:
	lw		s6, 8(s5)
	mtlo	s6
	lw		s6, 12(s5)
	mthi	s6
	lw		$1, 16(s5)

	/* s6 is loaded as it was used as a scratch register and therefore saved
	as part of the interrupt context. */
	lw		s6, 44(s5)
	lw		v0, 52(s5)
	lw		v1, 56(s5)
	lw		a0, 60(s5)
	lw		a1, 64(s5)
	lw		a2, 68(s5)
	lw		a3, 72(s5)
	lw		t0, 76(s5)
	lw		t1, 80(s5)
	lw		t2, 84(s5)
	lw		t3, 88(s5)
	lw		t4, 92(s5)
	lw		t5, 96(s5)
	lw		t6, 100(s5)
	lw		t7, 104(s5)
	lw		t8, 108(s5)
	lw		t9, 112(s5)
	lw		s8, 116(s5)
	lw		ra, 120(s5)

	/* Protect access to the k registers, and others. */
	di
	ehb

	/* Decrement the nesting count. */
	la		k0, uxInterruptNesting
	lw		k1, (k0)
	addiu	k1, k1, -1
	sw		k1, 0(k0)

	lw		k0, portSTATUS_STACK_LOCATION(s5)
	lw		k1, portEPC_STACK_LOCATION(s5)

	/* Leave the stack in its original state.  First load sp from s5, then
	restore s5 from the stack. */
	add		sp, zero, s5
	lw		s5, 40(sp)
	addiu   sp, sp, portCONTEXT_SIZE

	mtc0	k0, _CP0_STATUS
	mtc0	k1, _CP0_EPC
	ehb
	eret
	nop

	.endm

#endif /* #ifdef __LANGUAGE_ASSEMBLY__ */

