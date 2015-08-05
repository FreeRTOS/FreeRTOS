/*
    FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

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

	.extern ulTopOfSystemStack
	.extern ulInterruptNesting

/*-----------------------------------------------------------*/

.macro portFREERTOS_INTERRUPT_ENTRY

	/* Save general purpose registers. */
	pusha

	/* If ulInterruptNesting is zero the rest of the task context will need
	saving and a stack switch might be required. */
	movl	ulInterruptNesting, %eax
	test	%eax, %eax
	jne		2f

	/* Interrupts are not nested, so save the rest of the task context. */
	.if configSUPPORT_FPU == 1

		/* If the task has a buffer allocated to save the FPU context then
		save the FPU context now. */
		movl	pucPortTaskFPUContextBuffer, %eax
		test	%eax, %eax
		je		1f
		fnsave	( %eax ) /* Save FLOP context into ucTempFPUBuffer array. */
		fwait

		1:
		/* Save the address of the FPU context, if any. */
		push	pucPortTaskFPUContextBuffer

	.endif /* configSUPPORT_FPU */

	/* Find the TCB. */
	movl 	pxCurrentTCB, %eax

	/* Stack location is first item in the TCB. */
	movl	%esp, (%eax)

	/* Switch stacks. */
	movl 	ulTopOfSystemStack, %esp
	movl	%esp, %ebp

	2:
	/* Increment nesting count. */
	add 	$1, ulInterruptNesting

.endm
/*-----------------------------------------------------------*/

.macro portINTERRUPT_EPILOGUE

	cli
	sub		$1, ulInterruptNesting

	/* If the nesting has unwound to zero. */
	movl	ulInterruptNesting, %eax
	test	%eax, %eax
	jne		2f

	/* If a yield was requested then select a new TCB now. */
	movl	ulPortYieldPending, %eax
	test	%eax, %eax
	je		1f
	movl	$0, ulPortYieldPending
	call	vTaskSwitchContext

	1:
	/* Stack location is first item in the TCB. */
	movl 	pxCurrentTCB, %eax
	movl	(%eax), %esp

	.if configSUPPORT_FPU == 1

		/* Restore address of task's FPU context buffer. */
		pop 	pucPortTaskFPUContextBuffer

		/* If the task has a buffer allocated in which its FPU context is saved,
		then restore it now. */
		movl	pucPortTaskFPUContextBuffer, %eax
		test	%eax, %eax
		je		1f
		frstor	( %eax )
		1:
	.endif

	2:
	popa

.endm
/*-----------------------------------------------------------*/

.macro portFREERTOS_INTERRUPT_EXIT

	portINTERRUPT_EPILOGUE
	/* EOI. */
	movl	$0x00, (0xFEE000B0)
	iret

.endm
