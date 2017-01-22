/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
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


#include <xc.h>
#include <sys/asm.h>


 	.global	vRegTest1
 	.global vRegTest2

/* Reg test macro helper. Test a register for a known value branching to
error_loop if not correct otherwise continuing on */
.macro	portREG_TEST work_reg, test_reg, test_value
	.set	micromips
	.set	noreorder
	.set	noat

	/* Check each register maintains the value assigned to it for the lifetime
	of the task. */
	addiu	\work_reg, $0, 0x00
	addiu	\work_reg, \test_reg, -\test_value
	beq		\work_reg, $0, 1f
	nop
	/* The register value was not that expected.  Jump to the error loop so the
	cycle counter stops incrementing. */
	b	error_loop
	nop
1:
	.endm


	.set	micromips
	.set	noreorder
	.set 	noat
	.ent	error_loop

/* Reg test tasks call the error loop when they find an error.  Sitting in the
tight error loop prevents them incrementing their ulRegTestnCycles counter, and
so allows the check softwate timer to know an error has been found. */
error_loop:
	b	error_loop
	nop

	.end error_loop


	.set	micromips
	.set	noreorder
	.set 	noat
	.ent	vRegTest1

vRegTest1:
	/* Fill the registers with known values. */
	addiu	$1, $0, 0x11
	addiu	$2, $0, 0x12
	addiu	$3, $0, 0x13
	/* $4 contains the address of the loop counter - don't mess with $4. */
	addiu	$5, $0, 0x15
	addiu	$6, $0, 0x16
	addiu	$7, $0, 0x17
	addiu	$8, $0, 0x18
	addiu	$9, $0, 0x19
	addiu	$10, $0, 0x110
	addiu	$11, $0, 0x111
	addiu	$12, $0, 0x112
	addiu	$13, $0, 0x113
	addiu	$14, $0, 0x114
	addiu	$15, $0, 0x115
	addiu	$16, $0, 0x116
	addiu	$17, $0, 0x117
	addiu	$18, $0, 0x118
	addiu	$19, $0, 0x119
	addiu	$20, $0, 0x120
	addiu	$21, $0, 0x121
	addiu	$23, $0, 0x123
	addiu	$24, $0, 0x124
	addiu	$25, $0, 0x125
	addiu	$30, $0, 0x130
	addiu	$22, $0, 0x131

vRegTest1Loop:
	portREG_TEST	$22, $1, 0x11
	portREG_TEST	$22, $2, 0x12
	portREG_TEST	$22, $3, 0x13
	portREG_TEST	$22, $5, 0x15
	portREG_TEST	$22, $6, 0x16
	portREG_TEST	$22, $7, 0x17
	portREG_TEST	$22, $8, 0x18
	portREG_TEST	$22, $9, 0x19
	portREG_TEST	$22, $10, 0x110
	portREG_TEST	$22, $11, 0x111
	portREG_TEST	$22, $12, 0x112
	portREG_TEST	$22, $13, 0x113
	portREG_TEST	$22, $14, 0x114
	portREG_TEST	$22, $15, 0x115
	portREG_TEST	$22, $16, 0x116
	portREG_TEST	$22, $17, 0x117
	portREG_TEST	$22, $18, 0x118
	portREG_TEST	$22, $19, 0x119
	portREG_TEST	$22, $20, 0x120
	portREG_TEST	$22, $21, 0x121
	portREG_TEST	$22, $23, 0x123
	portREG_TEST	$22, $24, 0x124
	portREG_TEST	$22, $25, 0x125
	portREG_TEST	$22, $30, 0x130

	/* No errors detected.  Increment the loop count so the check timer knows
	this task is still running without error, then loop back to do it all
	again.  The address of the loop counter is in $4. */
	lw		$22, 0( $4 )
	addiu	$22, $22, 0x01
	sw		$22, 0( $4 )
	b		vRegTest1Loop
	nop

	.end	vRegTest1


	.set	micromips
	.set	noreorder
	.set 	noat
	.ent	vRegTest2

vRegTest2:
	addiu	$1, $0, 0x21
	addiu	$2, $0, 0x22
	addiu	$3, $0, 0x23
	/* $4 contains the address of the loop counter - don't mess with $4. */
	addiu	$5, $0, 0x25
	addiu	$6, $0, 0x26
	addiu	$7, $0, 0x27
	addiu	$8, $0, 0x28
	addiu	$9, $0, 0x29
	addiu	$10, $0, 0x210
	addiu	$11, $0, 0x211
	addiu	$12, $0, 0x212
	addiu	$13, $0, 0x213
	addiu	$14, $0, 0x214
	addiu	$15, $0, 0x215
	addiu	$16, $0, 0x216
	addiu	$17, $0, 0x217
	addiu	$18, $0, 0x218
	addiu	$19, $0, 0x219
	addiu	$20, $0, 0x220
	addiu	$21, $0, 0x221
	addiu	$23, $0, 0x223
	addiu	$24, $0, 0x224
	addiu	$25, $0, 0x225
	addiu	$30, $0, 0x230
	addiu	$22, $0, 0x231

vRegTest2Loop:
	portREG_TEST	$22, $1, 0x21
	portREG_TEST	$22, $2, 0x22
	portREG_TEST	$22, $3, 0x23
	portREG_TEST	$22, $5, 0x25
	portREG_TEST	$22, $6, 0x26
	portREG_TEST	$22, $7, 0x27
	portREG_TEST	$22, $8, 0x28
	portREG_TEST	$22, $9, 0x29
	portREG_TEST	$22, $10, 0x210
	portREG_TEST	$22, $11, 0x211
	portREG_TEST	$22, $12, 0x212
	portREG_TEST	$22, $13, 0x213
	portREG_TEST	$22, $14, 0x214
	portREG_TEST	$22, $15, 0x215
	portREG_TEST	$22, $16, 0x216
	portREG_TEST	$22, $17, 0x217
	portREG_TEST	$22, $18, 0x218
	portREG_TEST	$22, $19, 0x219
	portREG_TEST	$22, $20, 0x220
	portREG_TEST	$22, $21, 0x221
	portREG_TEST	$22, $23, 0x223
	portREG_TEST	$22, $24, 0x224
	portREG_TEST	$22, $25, 0x225
	portREG_TEST	$22, $30, 0x230

	/* No errors detected.  Increment the loop count so the check timer knows
	this task is still running without error, then loop back to do it all
	again.  The address of the loop counter is in $4. */
	lw		$22, 0( $4 )
	addiu	$22, $22, 0x01
	sw		$22, 0( $4 )
	b		vRegTest2Loop
	nop

	.end	vRegTest2



