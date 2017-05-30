;/*
;    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
;    All rights reserved
;
;    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.
;
;    This file is part of the FreeRTOS distribution.
;
;    FreeRTOS is free software; you can redistribute it and/or modify it under
;    the terms of the GNU General Public License (version 2) as published by the
;    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.
;
;    ***************************************************************************
;    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
;    >>!   distribute a combined work that includes FreeRTOS without being   !<<
;    >>!   obliged to provide the source code for proprietary components     !<<
;    >>!   outside of the FreeRTOS kernel.                                   !<<
;    ***************************************************************************
;
;    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
;    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
;    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
;    link: http://www.freertos.org/a00114.html
;
;    ***************************************************************************
;     *                                                                       *
;     *    FreeRTOS provides completely free yet professionally developed,    *
;     *    robust, strictly quality controlled, supported, and cross          *
;     *    platform software that is more than just the market leader, it     *
;     *    is the industry's de facto standard.                               *
;     *                                                                       *
;     *    Help yourself get started quickly while simultaneously helping     *
;     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
;     *    tutorial book, reference manual, or both:                          *
;     *    http://www.FreeRTOS.org/Documentation                              *
;     *                                                                       *
;    ***************************************************************************
;
;    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
;    the FAQ page "My application does not run, what could be wrong?".  Have you
;    defined configASSERT()?
;
;    http://www.FreeRTOS.org/support - In return for receiving this top quality
;    embedded software for free we request you assist our global community by
;    participating in the support forum.
;
;    http://www.FreeRTOS.org/training - Investing in training allows your team to
;    be as productive as possible as early as possible.  Now you can receive
;    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
;    Ltd, and the world's leading authority on the world's leading RTOS.
;
;    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
;    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
;    compatible FAT file system, and our tiny thread aware UDP/IP stack.
;
;    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
;    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.
;
;    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
;    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
;    licenses offer ticketed support, indemnification and commercial middleware.
;
;    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
;    engineered and independently SIL3 certified version for use in safety and
;    mission critical applications that require provable dependability.
;
;    1 tab == 4 spaces!
;*/

	.thumb

	.ref pxCurrentTCB
	.ref vTaskSwitchContext
	.ref ulMaxSyscallInterruptPriority

	.def xPortPendSVHandler
	.def ulPortGetIPSR
	.def vPortSVCHandler
	.def vPortStartFirstTask
	.def vPortEnableVFP

NVICOffsetConst:					.word 	0xE000ED08
CPACRConst:							.word 	0xE000ED88
pxCurrentTCBConst:					.word	pxCurrentTCB
ulMaxSyscallInterruptPriorityConst: .word ulMaxSyscallInterruptPriority

; -----------------------------------------------------------

	.align 4
ulPortGetIPSR: .asmfunc
 	mrs r0, ipsr
 	bx r14
 	.endasmfunc
 ; -----------------------------------------------------------

	.align 4
vPortSetInterruptMask: .asmfunc
	push {r0}
	ldr r0, ulMaxSyscallInterruptPriorityConst
	msr basepri, r0
	pop {r0}
	bx r14
	.endasmfunc
; -----------------------------------------------------------

	.align 4
xPortPendSVHandler: .asmfunc
	mrs r0, psp
	isb

	;/* Get the location of the current TCB. */
	ldr	r3, pxCurrentTCBConst
	ldr	r2, [r3]

	;/* Is the task using the FPU context?  If so, push high vfp registers. */
	tst r14, #0x10
	it eq
	vstmdbeq r0!, {s16-s31}

	;/* Save the core registers. */
	stmdb r0!, {r4-r11, r14}

	;/* Save the new top of stack into the first member of the TCB. */
	str r0, [r2]

	stmdb sp!, {r0, r3}
	ldr r0, ulMaxSyscallInterruptPriorityConst
	ldr r1, [r0]
	msr basepri, r1
	dsb
	isb
	bl vTaskSwitchContext
	mov r0, #0
	msr basepri, r0
	ldmia sp!, {r0, r3}

	;/* The first item in pxCurrentTCB is the task top of stack. */
	ldr r1, [r3]
	ldr r0, [r1]

	;/* Pop the core registers. */
	ldmia r0!, {r4-r11, r14}

	;/* Is the task using the FPU context?  If so, pop the high vfp registers
	;too. */
	tst r14, #0x10
	it eq
	vldmiaeq r0!, {s16-s31}

	msr psp, r0
	isb
	bx r14
	.endasmfunc

; -----------------------------------------------------------

	.align 4
vPortSVCHandler: .asmfunc
	;/* Get the location of the current TCB. */
	ldr	r3, pxCurrentTCBConst
	ldr r1, [r3]
	ldr r0, [r1]
	;/* Pop the core registers. */
	ldmia r0!, {r4-r11, r14}
	msr psp, r0
	isb
	mov r0, #0
	msr	basepri, r0
	bx r14
	.endasmfunc

; -----------------------------------------------------------

	.align 4
vPortStartFirstTask: .asmfunc
	;/* Use the NVIC offset register to locate the stack. */
	ldr r0, NVICOffsetConst
	ldr r0, [r0]
	ldr r0, [r0]
	;/* Set the msp back to the start of the stack. */
	msr msp, r0
	;/* Clear the bit that indicates the FPU is in use in case the FPU was used
	;before the scheduler was started - which would otherwise result in the
	;unnecessary leaving of space in the SVC stack for lazy saving of FPU
	;registers. */
	mov r0, #0
	msr control, r0
	;/* Call SVC to start the first task. */
	cpsie i
	cpsie f
	dsb
	isb
	svc #0
	.endasmfunc

; -----------------------------------------------------------

	.align 4
vPortEnableVFP: .asmfunc
	;/* The FPU enable bits are in the CPACR. */
	ldr.w r0, CPACRConst
	ldr	r1, [r0]

	;/* Enable CP10 and CP11 coprocessors, then save back. */
	orr	r1, r1, #( 0xf << 20 )
	str r1, [r0]
	bx	r14
	.endasmfunc

	.end

; -----------------------------------------------------------

