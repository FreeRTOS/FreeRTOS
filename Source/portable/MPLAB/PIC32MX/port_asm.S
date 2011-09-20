/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/
 
#include <p32xxxx.h>
#include <sys/asm.h>
#include "ISR_Support.h"
 

	.set	nomips16
 	.set 	noreorder
 	
 	.extern pxCurrentTCB
 	.extern vTaskSwitchContext
 	.extern vPortIncrementTick
	.extern xISRStackTop
 	
 	.global vPortStartFirstTask
	.global vPortYieldISR
	.global vT1InterruptHandler


/******************************************************************/

 	.set		noreorder
	.set 		noat
 	.ent		vT1InterruptHandler
	
vT1InterruptHandler:

	portSAVE_CONTEXT

	jal 		vPortIncrementTick
	nop

	portRESTORE_CONTEXT

	.end vT1InterruptHandler

/******************************************************************/

 	.set		noreorder
	.set 		noat
 	.ent		xPortStartScheduler

vPortStartFirstTask:

	/* Simply restore the context of the highest priority task that has been
	created so far. */
	portRESTORE_CONTEXT

	.end xPortStartScheduler



/*******************************************************************/

 	.set		noreorder
	.set 		noat
 	.ent		vPortYieldISR

vPortYieldISR:

	/* Make room for the context. First save the current status so we can 
	manipulate it, and the cause and EPC registers so we capture their 
	original values in case of interrupt nesting. */
	mfc0		k0, _CP0_CAUSE
	addiu		sp,	sp, -portCONTEXT_SIZE
	mfc0		k1, _CP0_STATUS

	/* Also save s6 and s5 so we can use them during this interrupt.  Any
	nesting interrupts should maintain the values of these registers
	across the ISR. */
	sw			s6, 44(sp)
	sw			s5, 40(sp)
	sw			k1, portSTATUS_STACK_LOCATION(sp)

	/* Enable interrupts above the current priority. */
	srl			k0, k0, 0xa
	ins 		k1, k0, 10, 6
	ins			k1, zero, 1, 4

	/* s5 is used as the frame pointer. */
	add			s5, zero, sp

	/* Swap to the system stack.  This is not conditional on the nesting
	count as this interrupt is always the lowest priority and therefore
	the nesting is always 0. */
	la			sp, xISRStackTop
	lw			sp, (sp)

	/* Set the nesting count. */
	la			k0, uxInterruptNesting
	addiu		s6, zero, 1
	sw			s6, 0(k0)

	/* s6 holds the EPC value, this is saved with the rest of the context
	after interrupts are enabled. */
	mfc0 		s6, _CP0_EPC

	/* Re-enable interrupts. */
	mtc0		k1, _CP0_STATUS

	/* Save the context into the space just created.  s6 is saved again
	here as it now contains the EPC value. */
	sw			ra,	120(s5)
	sw			s8, 116(s5)
	sw			t9, 112(s5)
	sw			t8,	108(s5)
	sw			t7,	104(s5)
	sw			t6, 100(s5)
	sw			t5, 96(s5)
	sw			t4, 92(s5)
	sw			t3, 88(s5)
	sw			t2, 84(s5)
	sw			t1, 80(s5)
	sw			t0, 76(s5)
	sw			a3, 72(s5)
	sw			a2, 68(s5)
	sw			a1, 64(s5)
	sw			a0, 60(s5)
	sw			v1, 56(s5)
	sw			v0, 52(s5)
	sw			s7, 48(s5)
	sw			s6, portEPC_STACK_LOCATION(s5)
	/* s5 and s6 has already been saved. */
	sw			s4,	36(s5)
	sw			s3, 32(s5)
	sw			s2, 28(s5)
	sw			s1, 24(s5)
	sw			s0, 20(s5)
	sw			$1, 16(s5)

	/* s7 is used as a scratch register as this should always be saved across
	nesting interrupts. */
	mfhi		s7
	sw			s7, 12(s5)
	mflo		s7
	sw			s7, 8(s5)

	/* Save the stack pointer to the task. */
	la			s7, pxCurrentTCB
	lw			s7, (s7)
	sw			s5, (s7)

	/* Set the interrupt mask to the max priority that can use the API.  The
	yield handler will only be called at configKERNEL_INTERRUPT_PRIORITY which
	is below configMAX_SYSCALL_INTERRUPT_PRIORITY - so this can only ever
	raise the IPL value and never lower it. */
	di
	mfc0		s7, _CP0_STATUS
	ins 		s7, $0, 10, 6
	ori			s6, s7, ( configMAX_SYSCALL_INTERRUPT_PRIORITY << 10 ) | 1

	/* This mtc0 re-enables interrupts, but only above 
	configMAX_SYSCALL_INTERRUPT_PRIORITY. */
	mtc0		s6, _CP0_STATUS

	/* Clear the software interrupt in the core. */
	mfc0		s6, _CP0_CAUSE
	addiu       s4,zero,-257
	and			s6, s6, s4
	mtc0		s6, _CP0_CAUSE

	/* Clear the interrupt in the interrupt controller. */
	la			s6, IFS0CLR
	addiu		s4, zero, 2
	sw			s4, (s6)

	jal			vTaskSwitchContext
	nop

	/* Clear the interrupt mask again.  The saved status value is still in s7. */
	mtc0		s7, _CP0_STATUS

	/* Restore the stack pointer from the TCB. */
	la			s0, pxCurrentTCB
	lw			s0, (s0)
	lw			s5, (s0)

	/* Restore the rest of the context. */
	lw			s0, 8(s5)
	mtlo		s0
	lw			s0, 12(s5)
	mthi		s0
	lw			$1, 16(s5)
	lw			s0, 20(s5)
	lw			s1, 24(s5)
	lw			s2, 28(s5)
	lw			s3, 32(s5)
	lw			s4, 36(s5)
	/* s5 is loaded later. */
	lw			s6, 44(s5)
	lw			s7, 48(s5)
	lw			v0, 52(s5)
	lw			v1, 56(s5)
	lw			a0, 60(s5)
	lw			a1, 64(s5)
	lw			a2, 68(s5)
	lw			a3, 72(s5)
	lw			t0, 76(s5)
	lw			t1, 80(s5)
	lw			t2, 84(s5)
	lw			t3, 88(s5)
	lw			t4, 92(s5)
	lw			t5, 96(s5)
	lw			t6, 100(s5)
	lw			t7, 104(s5)
	lw			t8, 108(s5)
	lw			t9, 112(s5)
	lw			s8, 116(s5)
	lw			ra, 120(s5)

	/* Protect access to the k registers, and others. */
	di

	/* Set nesting back to zero.  As the lowest priority interrupt this
	interrupt cannot have nested. */
	la			k0, uxInterruptNesting
	sw			zero, 0(k0)

	/* Switch back to use the real stack pointer. */
	add			sp, zero, s5

	/* Restore the real s5 value. */
	lw			s5, 40(sp)

	/* Pop the status and epc values. */
	lw			k1, portSTATUS_STACK_LOCATION(sp)
	lw			k0, portEPC_STACK_LOCATION(sp)

	/* Remove stack frame. */
	addiu		sp,	sp,	portCONTEXT_SIZE

	mtc0		k1, _CP0_STATUS	
	mtc0 		k0, _CP0_EPC
	ehb
	eret 
	nop

	.end		vPortYieldISR



