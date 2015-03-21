/*
    FreeRTOS V8.2.1 - Copyright (C) 2015 Real Time Engineers Ltd.
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

#include <FreeRTOSConfig.h>

	RSEG    CODE:CODE(2)
	thumb

	EXTERN vPortYieldFromISR
	EXTERN pxCurrentTCB
	EXTERN vTaskSwitchContext

	PUBLIC vSetMSP
	PUBLIC xPortPendSVHandler
	PUBLIC vPortSVCHandler
	PUBLIC vPortStartFirstTask
	PUBLIC ulSetInterruptMaskFromISR
	PUBLIC vClearInterruptMaskFromISR

/*-----------------------------------------------------------*/

vSetMSP
	msr msp, r0
	bx lr

/*-----------------------------------------------------------*/

xPortPendSVHandler:
	mrs r0, psp

	ldr	r3, =pxCurrentTCB	/* Get the location of the current TCB. */
	ldr	r2, [r3]

	subs r0, r0, #32		/* Make space for the remaining low registers. */
	str r0, [r2]			/* Save the new top of stack. */
	stmia r0!, {r4-r7}		/* Store the low registers that are not saved automatically. */
	mov r4, r8				/* Store the high registers. */
	mov r5, r9
	mov r6, r10
	mov r7, r11
	stmia r0!, {r4-r7}

	push {r3, r14}
	cpsid i
	bl vTaskSwitchContext
	cpsie i
	pop {r2, r3}			/* lr goes in r3. r2 now holds tcb pointer. */

	ldr r1, [r2]
	ldr r0, [r1]			/* The first item in pxCurrentTCB is the task top of stack. */
	adds r0, r0, #16		/* Move to the high registers. */
	ldmia r0!, {r4-r7}		/* Pop the high registers. */
	mov r8, r4
	mov r9, r5
	mov r10, r6
	mov r11, r7

	msr psp, r0				/* Remember the new top of stack for the task. */

	subs r0, r0, #32		/* Go back for the low registers that are not automatically restored. */
	ldmia r0!, {r4-r7}		/* Pop low registers.  */

	bx r3

/*-----------------------------------------------------------*/

vPortSVCHandler;
	/* This function is no longer used, but retained for backward
	compatibility. */
	bx lr

/*-----------------------------------------------------------*/

vPortStartFirstTask
	/* The MSP stack is not reset as, unlike on M3/4 parts, there is no vector
	table offset register that can be used to locate the initial stack value.
	Not all M0 parts have the application vector table at address 0. */

	ldr	r3, =pxCurrentTCB	/* Obtain location of pxCurrentTCB. */
	ldr r1, [r3]
	ldr r0, [r1]			/* The first item in pxCurrentTCB is the task top of stack. */
	adds r0, #32			/* Discard everything up to r0. */
	msr psp, r0				/* This is now the new top of stack to use in the task. */
	movs r0, #2				/* Switch to the psp stack. */
	msr CONTROL, r0
	pop {r0-r5}				/* Pop the registers that are saved automatically. */
	mov lr, r5				/* lr is now in r5. */
	cpsie i					/* The first task has its context and interrupts can be enabled. */
	pop {pc}				/* Finally, pop the PC to jump to the user defined task code. */

/*-----------------------------------------------------------*/

ulSetInterruptMaskFromISR
	mrs r0, PRIMASK
	cpsid i
	bx lr

/*-----------------------------------------------------------*/

vClearInterruptMaskFromISR
	msr PRIMASK, r0
	bx lr

	END
