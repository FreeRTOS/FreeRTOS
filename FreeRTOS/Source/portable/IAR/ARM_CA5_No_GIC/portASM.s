;/*
;    FreeRTOS V8.0.1 - Copyright (C) 2014 Real Time Engineers Ltd.
;    All rights reserved
;
;
;    ***************************************************************************
;     *                                                                       *
;     *    FreeRTOS tutorial books are available in pdf and paperback.        *
;     *    Complete, revised, and edited pdf reference manuals are also       *
;     *    available.                                                         *
;     *                                                                       *
;     *    Purchasing FreeRTOS documentation will not only help you, by       *
;     *    ensuring you get running as quickly as possible and with an        *
;     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
;     *    the FreeRTOS project to continue with its mission of providing     *
;     *    professional grade, cross platform, de facto standard solutions    *
;     *    for microcontrollers - completely free of charge!                  *
;     *                                                                       *
;     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
;     *                                                                       *
;     *    Thank you for using FreeRTOS, and thank you for your support!      *
;     *                                                                       *
;    ***************************************************************************
;
;
;    This file is part of the FreeRTOS distribution.
;
;    FreeRTOS is free software; you can redistribute it and/or modify it under
;    the terms of the GNU General Public License (version 2) as published by the
;    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
;    >>>NOTE<<< The modification to the GPL is included to allow you to
;    distribute a combined work that includes FreeRTOS without being obliged to
;    provide the source code for proprietary components outside of the FreeRTOS
;    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
;    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
;    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;    more details. You should have received a copy of the GNU General Public
;    License and the FreeRTOS license exception along with FreeRTOS; if not it
;    can be viewed here: http://www.freertos.org/a00114.html and also obtained
;    by writing to Richard Barry, contact details for whom are available on the
;    FreeRTOS WEB site.
;
;    1 tab == 4 spaces!
;
;    http://www.FreeRTOS.org - Documentation, latest information, license and
;    contact details.
;
;    http://www.SafeRTOS.com - A version that is certified for use in safety
;    critical systems.
;
;    http://www.OpenRTOS.com - Commercial support, development, porting,
;    licensing and training services.
;*/

	INCLUDE FreeRTOSConfig.h
	INCLUDE portmacro.h

	EXTERN	vTaskSwitchContext
	EXTERN	ulPortYieldRequired
	EXTERN	ulPortInterruptNesting
	EXTERN	vApplicationIRQHandler

	PUBLIC	FreeRTOS_SWI_Handler
	PUBLIC  FreeRTOS_IRQ_Handler
	PUBLIC 	vPortRestoreTaskContext

SYS_MODE			EQU		0x1f
SVC_MODE			EQU		0x13
IRQ_MODE			EQU		0x12

	SECTION .text:CODE:ROOT(2)
	ARM

	INCLUDE portASM.h

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SVC handler is used to yield a task.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
FreeRTOS_SWI_Handler

	PRESERVE8

	; Save the context of the current task and select a new task to run.
	portSAVE_CONTEXT
	LDR R0, =vTaskSwitchContext
	BLX	R0
	portRESTORE_CONTEXT

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; vPortRestoreTaskContext is used to start the scheduler.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
vPortRestoreTaskContext

	PRESERVE8

	; Switch to system mode
	CPS		#SYS_MODE
	portRESTORE_CONTEXT

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; IRQ interrupt handler used when individual priorities cannot be masked
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
FreeRTOS_IRQ_Handler

	PRESERVE8

	; Return to the interrupted instruction.
	SUB		lr, lr, #4

	; Push the return address and SPSR
	PUSH	{lr}
	MRS		lr, SPSR
	PUSH	{lr}

	; Change to supervisor mode to allow reentry.
	CPS		#SVC_MODE

	; Push used registers.
	PUSH	{r0-r4, r12}

	; Increment nesting count.  r3 holds the address of ulPortInterruptNesting
	; for future use.  r1 holds the original ulPortInterruptNesting value for
	; future use.
	LDR		r3, =ulPortInterruptNesting
	LDR		r1, [r3]
	ADD		r4, r1, #1
	STR		r4, [r3]

	; Ensure bit 2 of the stack pointer is clear.  r2 holds the bit 2 value for
	; future use.
	MOV		r2, sp
	AND		r2, r2, #4
	SUB		sp, sp, r2

	; Obtain the address of the interrupt handler, then pass it into the ISR
	; callback.
	PUSH	{r0-r3, lr}
	LDR		r1, =configINTERRUPT_VECTOR_ADDRESS
	LDR		r0, [r1]
	LDR		r1, =vApplicationIRQHandler
	BLX		r1
	POP		{r0-r3, lr}
	ADD		sp, sp, r2

	CPSID	i

	; Write to the EOI register
	LDR 	r4, =configEOI_ADDRESS
	STR		r0, [r4]

	; Restore the old nesting count
	STR		r1, [r3]

	; A context switch is never performed if the nesting count is not 0
	CMP		r1, #0
	BNE		exit_without_switch

	; Did the interrupt request a context switch?  r1 holds the address of
	; ulPortYieldRequired and r0 the value of ulPortYieldRequired for future
	; use.
	LDR		r1, =ulPortYieldRequired
	LDR		r0, [r1]
	CMP		r0, #0
	BNE		switch_before_exit

exit_without_switch
	; No context switch.  Restore used registers, LR_irq and SPSR before
	; returning.
	POP		{r0-r4, r12}
	CPS		#IRQ_MODE
	POP		{LR}
	MSR		SPSR_cxsf, LR
	POP		{LR}
	MOVS	PC, LR

switch_before_exit
	; A context switch is to be performed.  Clear the context switch pending
	; flag.
	MOV		r0, #0
	STR		r0, [r1]

	; Restore used registers, LR-irq and SPSR before saving the context
	; to the task stack.
	POP		{r0-r4, r12}
	CPS		#IRQ_MODE
	POP		{LR}
	MSR		SPSR_cxsf, LR
	POP		{LR}
	portSAVE_CONTEXT

	; Call the function that selects the new task to execute.
	; vTaskSwitchContext() if vTaskSwitchContext() uses LDRD or STRD
	; instructions, or 8 byte aligned stack allocated data.  LR does not need
	; saving as a new LR will be loaded by portRESTORE_CONTEXT anyway.
	LDR		r0, =vTaskSwitchContext
	BLX		r0

	; Restore the context of, and branch to, the task selected to execute next.
	portRESTORE_CONTEXT


	END




