/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#include <FreeRTOSConfig.h>

	RSEG    CODE:CODE(2)
	thumb

	EXTERN pxCurrentTCB
	EXTERN vTaskSwitchContext
	EXTERN vPortSVCHandler_C

	PUBLIC xPortPendSVHandler
	PUBLIC vPortSVCHandler
	PUBLIC vPortStartFirstTask
	PUBLIC vPortEnableVFP
	PUBLIC vPortRestoreContextOfFirstTask
	PUBLIC xPortRaisePrivilege

/*-----------------------------------------------------------*/

xPortPendSVHandler:
	mrs r0, psp
	isb
	/* Get the location of the current TCB. */
	ldr	r3, =pxCurrentTCB
	ldr	r2, [r3]

	/* Is the task using the FPU context?  If so, push high vfp registers. */
	tst r14, #0x10
	it eq
	vstmdbeq r0!, {s16-s31}

	/* Save the core registers. */
	mrs r1, control
	stmdb r0!, {r1, r4-r11, r14}

	/* Save the new top of stack into the first member of the TCB. */
	str r0, [r2]

	stmdb sp!, {r0, r3}
	mov r0, #configMAX_SYSCALL_INTERRUPT_PRIORITY
	msr basepri, r0
	dsb
	isb
	bl vTaskSwitchContext
	mov r0, #0
	msr basepri, r0
	ldmia sp!, {r0, r3}

	/* The first item in pxCurrentTCB is the task top of stack. */
	ldr r1, [r3]
	ldr r0, [r1]
	/* Move onto the second item in the TCB... */
	add r1, r1, #4
	/* Region Base Address register. */
	ldr r2, =0xe000ed9c
	/* Read 4 sets of MPU registers. */
	ldmia r1!, {r4-r11}
	/* Write 4 sets of MPU registers. */
	stmia r2!, {r4-r11}
	/* Pop the registers that are not automatically saved on exception entry. */
	ldmia r0!, {r3-r11, r14}
	msr control, r3

	/* Is the task using the FPU context?  If so, pop the high vfp registers
	too. */
	tst r14, #0x10
	it eq
	vldmiaeq r0!, {s16-s31}

	msr psp, r0
	isb

	bx r14


/*-----------------------------------------------------------*/

vPortSVCHandler:
	#ifndef USE_PROCESS_STACK	/* Code should not be required if a main() is using the process stack. */
		tst lr, #4
		ite eq
		mrseq r0, msp
		mrsne r0, psp
	#else
		mrs r0, psp
	#endif
		b vPortSVCHandler_C

/*-----------------------------------------------------------*/

vPortStartFirstTask
	/* Use the NVIC offset register to locate the stack. */
	ldr r0, =0xE000ED08
	ldr r0, [r0]
	ldr r0, [r0]
	/* Set the msp back to the start of the stack. */
	msr msp, r0
	/* Clear the bit that indicates the FPU is in use in case the FPU was used
	before the scheduler was started - which would otherwise result in the
	unnecessary leaving of space in the SVC stack for lazy saving of FPU
	registers. */
	mov r0, #0
	msr control, r0
	/* Call SVC to start the first task. */
	cpsie i
	cpsie f
	dsb
	isb
	svc 0

/*-----------------------------------------------------------*/

vPortRestoreContextOfFirstTask
	/* Use the NVIC offset register to locate the stack. */
	ldr r0, =0xE000ED08
	ldr r0, [r0]
	ldr r0, [r0]
	/* Set the msp back to the start of the stack. */
	msr msp, r0
	/* Restore the context. */
	ldr	r3, =pxCurrentTCB
	ldr r1, [r3]
	/* The first item in the TCB is the task top of stack. */
	ldr r0, [r1]
	/* Move onto the second item in the TCB... */
	add r1, r1, #4
	/* Region Base Address register. */
	ldr r2, =0xe000ed9c
	/* Read 4 sets of MPU registers. */
	ldmia r1!, {r4-r11}
	/* Write 4 sets of MPU registers. */
	stmia r2!, {r4-r11}
	/* Pop the registers that are not automatically saved on exception entry. */
	ldmia r0!, {r3-r11, r14}
	msr control, r3
	/* Restore the task stack pointer. */
	msr psp, r0
	mov r0, #0
	msr	basepri, r0
	bx r14

/*-----------------------------------------------------------*/

vPortEnableVFP
	/* The FPU enable bits are in the CPACR. */
	ldr.w r0, =0xE000ED88
	ldr	r1, [r0]

	/* Enable CP10 and CP11 coprocessors, then save back. */
	orr	r1, r1, #( 0xf << 20 )
	str r1, [r0]
	bx	r14

/*-----------------------------------------------------------*/

xPortRaisePrivilege
	mrs r0, control
	/* Is the task running privileged? */
	tst r0, #1
	itte ne
	/* CONTROL[0]!=0, return false. */
	movne r0, #0
	/* Switch to privileged. */
	svcne 2	/* 2 == portSVC_RAISE_PRIVILEGE */
	/* CONTROL[0]==0, return true. */
	moveq r0, #1
	bx lr


	END

