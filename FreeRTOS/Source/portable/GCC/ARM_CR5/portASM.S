/*
    FreeRTOS V9.0.0rc2 - Copyright (C) 2016 Real Time Engineers Ltd.
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

	.text
	.arm

	.set SYS_MODE,	0x1f
	.set SVC_MODE,	0x13
	.set IRQ_MODE,	0x12

	/* Hardware registers. */
	.extern ulICCIAR
	.extern ulICCEOIR
	.extern ulICCPMR

	/* Variables and functions. */
	.extern ulMaxAPIPriorityMask
	.extern _freertos_vector_table
	.extern pxCurrentTCB
	.extern vTaskSwitchContext
	.extern vApplicationIRQHandler
	.extern ulPortInterruptNesting
	.extern ulPortTaskHasFPUContext

	.global FreeRTOS_IRQ_Handler
	.global FreeRTOS_SWI_Handler
	.global vPortRestoreTaskContext
	.global vPortInstallFreeRTOSVectorTable




.macro portSAVE_CONTEXT

	/* Save the LR and SPSR onto the system mode stack before switching to
	system mode to save the remaining system mode registers. */
	SRSDB	sp!, #SYS_MODE
	CPS		#SYS_MODE
	PUSH	{R0-R12, R14}

	/* Push the critical nesting count. */
	LDR		R2, ulCriticalNestingConst
	LDR		R1, [R2]
	PUSH	{R1}

	/* Does the task have a floating point context that needs saving?  If
	ulPortTaskHasFPUContext is 0 then no. */
	LDR		R2, ulPortTaskHasFPUContextConst
	LDR		R3, [R2]
	CMP		R3, #0

	/* Save the floating point context, if any. */
	FMRXNE  R1,  FPSCR
	VPUSHNE {D0-D15}
	/*VPUSHNE	{D16-D31}*/
	PUSHNE	{R1}

	/* Save ulPortTaskHasFPUContext itself. */
	PUSH	{R3}

	/* Save the stack pointer in the TCB. */
	LDR		R0, pxCurrentTCBConst
	LDR		R1, [R0]
	STR		SP, [R1]

	.endm

; /**********************************************************************/

.macro portRESTORE_CONTEXT

	/* Set the SP to point to the stack of the task being restored. */
	LDR		R0, pxCurrentTCBConst
	LDR		R1, [R0]
	LDR		SP, [R1]

	/* Is there a floating point context to restore?  If the restored
	ulPortTaskHasFPUContext is zero then no. */
	LDR		R0, ulPortTaskHasFPUContextConst
	POP		{R1}
	STR		R1, [R0]
	CMP		R1, #0

	/* Restore the floating point context, if any. */
	POPNE 	{R0}
	/*VPOPNE	{D16-D31}*/
	VPOPNE	{D0-D15}
	VMSRNE  FPSCR, R0

	/* Restore the critical section nesting depth. */
	LDR		R0, ulCriticalNestingConst
	POP		{R1}
	STR		R1, [R0]

	/* Ensure the priority mask is correct for the critical nesting depth. */
	LDR		R2, ulICCPMRConst
	LDR		R2, [R2]
	CMP		R1, #0
	MOVEQ	R4, #255
	LDRNE	R4, ulMaxAPIPriorityMaskConst
	LDRNE	R4, [R4]
	STR		R4, [R2]

	/* Restore all system mode registers other than the SP (which is already
	being used). */
	POP		{R0-R12, R14}

	/* Return to the task code, loading CPSR on the way. */
	RFEIA	sp!

	.endm




/******************************************************************************
 * SVC handler is used to start the scheduler.
 *****************************************************************************/
.align 4
.type FreeRTOS_SWI_Handler, %function
FreeRTOS_SWI_Handler:
	/* Save the context of the current task and select a new task to run. */
	portSAVE_CONTEXT
	LDR R0, vTaskSwitchContextConst
	BLX	R0
	portRESTORE_CONTEXT


/******************************************************************************
 * vPortRestoreTaskContext is used to start the scheduler.
 *****************************************************************************/
.type vPortRestoreTaskContext, %function
vPortRestoreTaskContext:
	/* Switch to system mode. */
	CPS		#SYS_MODE
	portRESTORE_CONTEXT

.align 4
.type FreeRTOS_IRQ_Handler, %function
FreeRTOS_IRQ_Handler:

	/* Return to the interrupted instruction. */
	SUB		lr, lr, #4

	/* Push the return address and SPSR. */
	PUSH	{lr}
	MRS		lr, SPSR
	PUSH	{lr}

	/* Change to supervisor mode to allow reentry. */
	CPS		#SVC_MODE

	/* Push used registers. */
	PUSH	{r0-r4, r12}

	/* Increment nesting count.  r3 holds the address of ulPortInterruptNesting
	for future use.  r1 holds the original ulPortInterruptNesting value for
	future use. */
	LDR		r3, ulPortInterruptNestingConst
	LDR		r1, [r3]
	ADD		r4, r1, #1
	STR		r4, [r3]

	/* Read value from the interrupt acknowledge register, which is stored in r0
	for future parameter and interrupt clearing use. */
	LDR 	r2, ulICCIARConst
	LDR		r2, [r2]
	LDR		r0, [r2]

	/* Ensure bit 2 of the stack pointer is clear.  r2 holds the bit 2 value for
	future use. */
	MOV		r2, sp
	AND		r2, r2, #4
	SUB		sp, sp, r2

	/* Call the interrupt handler. */
	PUSH	{r0-r3, lr}
	LDR		r1, vApplicationIRQHandlerConst
	BLX		r1
	POP		{r0-r3, lr}
	ADD		sp, sp, r2

	CPSID	i
	DSB
	ISB

	/* Write the value read from ICCIAR to ICCEOIR. */
	LDR 	r4, ulICCEOIRConst
	LDR		r4, [r4]
	STR		r0, [r4]

	/* Restore the old nesting count. */
	STR		r1, [r3]

	/* A context switch is never performed if the nesting count is not 0. */
	CMP		r1, #0
	BNE		exit_without_switch

	/* Did the interrupt request a context switch?  r1 holds the address of
	ulPortYieldRequired and r0 the value of ulPortYieldRequired for future
	use. */
	LDR		r1, =ulPortYieldRequired
	LDR		r0, [r1]
	CMP		r0, #0
	BNE		switch_before_exit

exit_without_switch:
	/* No context switch.  Restore used registers, LR_irq and SPSR before
	returning. */
	POP		{r0-r4, r12}
	CPS		#IRQ_MODE
	POP		{LR}
	MSR		SPSR_cxsf, LR
	POP		{LR}
	MOVS	PC, LR

switch_before_exit:
	/* A context swtich is to be performed.  Clear the context switch pending
	flag. */
	MOV		r0, #0
	STR		r0, [r1]

	/* Restore used registers, LR-irq and SPSR before saving the context
	to the task stack. */
	POP		{r0-r4, r12}
	CPS		#IRQ_MODE
	POP		{LR}
	MSR		SPSR_cxsf, LR
	POP		{LR}
	portSAVE_CONTEXT

	/* Call the function that selects the new task to execute.
	vTaskSwitchContext() if vTaskSwitchContext() uses LDRD or STRD
	instructions, or 8 byte aligned stack allocated data.  LR does not need
	saving as a new LR will be loaded by portRESTORE_CONTEXT anyway. */
	LDR		R0, vTaskSwitchContextConst
	BLX		R0

	/* Restore the context of, and branch to, the task selected to execute
	next. */
	portRESTORE_CONTEXT

ulICCIARConst:	.word ulICCIAR
ulICCEOIRConst:	.word ulICCEOIR
ulICCPMRConst: .word ulICCPMR
pxCurrentTCBConst: .word pxCurrentTCB
ulCriticalNestingConst: .word ulCriticalNesting
ulPortTaskHasFPUContextConst: .word ulPortTaskHasFPUContext
ulMaxAPIPriorityMaskConst: .word ulMaxAPIPriorityMask
vTaskSwitchContextConst: .word vTaskSwitchContext
vApplicationIRQHandlerConst: .word vApplicationIRQHandler
ulPortInterruptNestingConst: .word ulPortInterruptNesting

.end





