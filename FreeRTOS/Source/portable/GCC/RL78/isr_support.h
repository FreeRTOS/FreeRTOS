/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
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

/* Variables used by scheduler */
	.extern    _pxCurrentTCB
	.extern    _usCriticalNesting

/*
 * portSAVE_CONTEXT MACRO
 * Saves the context of the general purpose registers, CS and ES (only in far
 * memory mode) registers the usCriticalNesting Value and the Stack Pointer
 * of the active Task onto the task stack
 */
	.macro portSAVE_CONTEXT

	SEL 	RB0

	/* Save AX Register to stack. */
	PUSH	AX
	PUSH	HL
	/* Save CS register. */
	MOV 	A, CS
	XCH		A, X
	/* Save ES register. */
	MOV		A, ES
	PUSH	AX
	/* Save the remaining general purpose registers from bank 0. */
	PUSH	DE
	PUSH	BC
	/* Save the other register banks - only necessary in the GCC port. */
	SEL		RB1
	PUSH	AX
	PUSH	BC
	PUSH	DE
	PUSH	HL
	SEL		RB2
	PUSH	AX
	PUSH	BC
	PUSH	DE
	PUSH	HL
	/* Registers in bank 3 are for ISR use only so don't need saving. */
	SEL		RB0
	/* Save the usCriticalNesting value. */
	MOVW	AX, !_usCriticalNesting
	PUSH	AX
	/* Save the Stack pointer. */
	MOVW	AX, !_pxCurrentTCB
	MOVW	HL, AX
	MOVW	AX, SP
	MOVW	[HL], AX
	/* Switch stack pointers. */
	movw sp,#_stack /* Set stack pointer */

	.endm


/*
 * portRESTORE_CONTEXT MACRO
 * Restores the task Stack Pointer then use this to restore usCriticalNesting,
 * general purpose registers and the CS and ES (only in far memory mode)
 * of the selected task from the task stack
 */
.macro portRESTORE_CONTEXT MACRO
	SEL		RB0
	/* Restore the Stack pointer. */
	MOVW	AX, !_pxCurrentTCB
	MOVW	HL, AX
	MOVW	AX, [HL]
	MOVW	SP, AX
	/* Restore usCriticalNesting value. */
	POP		AX
	MOVW	!_usCriticalNesting, AX
	/* Restore the alternative register banks - only necessary in the GCC
	port.  Register bank 3 is dedicated for interrupts use so is not saved or
	restored. */
	SEL		RB2
	POP		HL
	POP		DE
	POP		BC
	POP		AX
	SEL		RB1
	POP		HL
	POP		DE
	POP		BC
	POP		AX
	SEL		RB0
	/* Restore the necessary general purpose registers. */
	POP		BC
	POP		DE
	/* Restore the ES register. */
	POP		AX
	MOV		ES, A
	/* Restore the CS register. */
	XCH		A, X
	MOV		CS, A
	/* Restore general purpose register HL. */
	POP		HL
	/* Restore AX. */
	POP		AX

	.endm

