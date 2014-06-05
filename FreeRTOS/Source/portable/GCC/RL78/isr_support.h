/*
    FreeRTOS V8.0.1 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

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

