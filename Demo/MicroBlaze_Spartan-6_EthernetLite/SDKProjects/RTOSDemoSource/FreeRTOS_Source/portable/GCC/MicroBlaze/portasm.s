/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.


	FreeRTOS supports many tools and architectures. V7.0.0 is sponsored by:
	Atollic AB - Atollic provides professional embedded systems development
	tools for C/C++ development, code analysis and test automation.
	See http://www.atollic.com


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

	.extern pxCurrentTCB
	.extern XIntc_DeviceInterruptHandler
	.extern vTaskSwitchContext
	.extern uxCriticalNesting
	.extern pulISRStack

	.global _interrupt_handler
	.global VPortYieldASM
	.global vPortStartFirstTask


.macro portSAVE_CONTEXT

	/* Make room for the context on the stack. */
	addik r1, r1, -132

	/* Save r31 so it can then be used as a temporary. */
	swi r31, r1, 4

	/* Copy the msr into r31 - this is stacked later. */
	mfs r31, rmsr

	/* Stack general registers. */
	swi r30, r1, 12
	swi r29, r1, 16
	swi r28, r1, 20
	swi r27, r1, 24
	swi r26, r1, 28
	swi r25, r1, 32
	swi r24, r1, 36
	swi r23, r1, 40
	swi r22, r1, 44
	swi r21, r1, 48
	swi r20, r1, 52
	swi r19, r1, 56
	swi r18, r1, 60
	swi r17, r1, 64
	swi r16, r1, 68
	swi r15, r1, 72
	swi r13, r1, 80
	swi r12, r1, 84
	swi r11, r1, 88
	swi r10, r1, 92
	swi r9, r1, 96
	swi r8, r1, 100
	swi r7, r1, 104
	swi r6, r1, 108
	swi r5, r1, 112
	swi r4, r1, 116
	swi r3, r1, 120
	swi r2, r1, 124

	/* Stack the critical section nesting value. */
	lwi r3, r0, uxCriticalNesting
	swi r3, r1, 128

	/* Save the top of stack value to the TCB. */
	lwi r3, r0, pxCurrentTCB
	sw	r1, r0, r3
	
	.endm

.macro portRESTORE_CONTEXT

	/* Load the top of stack value from the TCB. */
	lwi r3, r0, pxCurrentTCB
	lw	r1, r0, r3	

	/* Restore the general registers. */
	lwi r31, r1, 4		
	lwi r30, r1, 12		
	lwi r29, r1, 16	
	lwi r28, r1, 20	
	lwi r27, r1, 24	
	lwi r26, r1, 28	
	lwi r25, r1, 32	
	lwi r24, r1, 36	
	lwi r23, r1, 40	
	lwi r22, r1, 44	
	lwi r21, r1, 48	
	lwi r20, r1, 52	
	lwi r19, r1, 56	
	lwi r18, r1, 60	
	lwi r17, r1, 64	
	lwi r16, r1, 68	
	lwi r15, r1, 72	
	lwi r14, r1, 76	
	lwi r13, r1, 80	
	lwi r12, r1, 84	
	lwi r11, r1, 88	
	lwi r10, r1, 92	
	lwi r9, r1, 96	
	lwi r8, r1, 100	
	lwi r7, r1, 104
	lwi r6, r1, 108
	lwi r5, r1, 112
	lwi r4, r1, 116
	lwi r2, r1, 124

	/* Reload the rmsr from the stack. */
	lwi r3, r1, 8
	mts rmsr, r3

	/* Load the critical nesting value. */
	lwi r3, r1, 128
	swi r3, r0, uxCriticalNesting

	/* Test the critical nesting value.  If it is non zero then the task last
	exited the running state using a yield.  If it is zero, then the task
	last exited the running state through an interrupt. */
	xori r3, r3, 0
	bnei r3, exit_from_yield

	/* r3 was being used as a temporary.  Now restore its true value from the
	stack. */
	lwi r3, r1, 120

	/* Remove the stack frame. */
	addik r1, r1, 132

	/* Return using rtid so interrupts are re-enabled as this function is
	exited. */
	rtid r14, 0
	or r0, r0, r0

	.endm

	.text
	.align  2

/* This function is used to exit portRESTORE_CONTEXT() if the task being
returned to last left the Running state by calling taskYIELD() (rather than
being preempted by an interrupt. */
exit_from_yield:

	/* r3 was being used as a temporary.  Now restore its true value from the
	stack. */
	lwi r3, r1, 120

	/* Remove the stack frame. */
	addik r1, r1, 132

	/* Return to the task. */
	rtsd r14, 0
	or r0, r0, r0


_interrupt_handler:

	portSAVE_CONTEXT

	/* Stack msr. */
	swi r31, r1, 8

	/* Stack the return address. */
	swi r14, r1, 76

	/* Switch to the ISR stack. */
	lwi r1, r0, pulISRStack

	/* Execute any pending interrupts. */
	bralid r15, XIntc_DeviceInterruptHandler
	or r0, r0, r0

	/* Restore the context of the next task scheduled to execute. */
	portRESTORE_CONTEXT


VPortYieldASM:

	portSAVE_CONTEXT

	/* Stack msr. */
	swi r31, r1, 8

	/* Modify the return address so a return is done to the instruction after
	the call to VPortYieldASM. */
	addi r14, r14, 8
	swi r14, r1, 76

	/* Switch to use the ISR stack. */
	lwi r1, r0, pulISRStack

	/* Select the next task to execute. */
	bralid r15, vTaskSwitchContext
	or r0, r0, r0

	/* Restore the context of the next task scheduled to execute. */
	portRESTORE_CONTEXT

vPortStartFirstTask:

	portRESTORE_CONTEXT
	
	




