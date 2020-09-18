/*
 * FreeRTOS Kernel V10.4.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


#include <xc.h>
#include <sys/asm.h>

	.set	nomips16
 	.set 	noreorder


 	.global	vRegTest1
 	.global vRegTest2

	.set	noreorder
	.set 	noat
	.ent	error_loop

/* Reg test tasks call the error loop when they find an error.  Sitting in the
tight error loop prevents them incrementing their ulRegTestnCycles counter, and
so allows the check softwate timer to know an error has been found. */
error_loop:
	b		.
	nop

	.end error_loop


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
	mthi	$22
	addiu	$22, $0, 0x132
	mtlo	$22

vRegTest1Loop:
	/* Check each register maintains the value assigned to it for the lifetime
	of the task. */
	addiu	$22, $0, 0x00
	addiu	$22, $1, -0x11
	beq		$22, $0, .+16
	nop
	/* The register value was not that expected.  Jump to the error loop so the
	cycle counter stops incrementing. */
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $2, -0x12
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $3, -0x13
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $5, -0x15
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $6, -0x16
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $7, -0x17
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $8, -0x18
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $9, -0x19
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $10, -0x110
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $11, -0x111
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $12, -0x112
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $13, -0x113
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $14, -0x114
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $15, -0x115
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $16, -0x116
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $17, -0x117
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $18, -0x118
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $19, -0x119
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $20, -0x120
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $21, -0x121
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $23, -0x123
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $24, -0x124
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $25, -0x125
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $30, -0x130
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mfhi	$22
	addiu	$22, $22, -0x131
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mflo	$22, $ac1
	addiu	$22, $22, -0x132
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	/* No errors detected.  Increment the loop count so the check timer knows
	this task is still running without error, then loop back to do it all
	again.  The address of the loop counter is in $4. */
	lw		$22, 0( $4 )
	addiu	$22, $22, 0x01
	sw		$22, 0( $4 )
	b		vRegTest1Loop
	nop

	.end	vRegTest1


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
	mthi	$22
	addiu	$22, $0, 0x232
	mtlo	$22

vRegTest2Loop:
	addiu	$22, $0, 0x00
	addiu	$22, $1, -0x21
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $2, -0x22
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $3, -0x23
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $5, -0x25
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $6, -0x26
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $7, -0x27
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $8, -0x28
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $9, -0x29
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $10, -0x210
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $11, -0x211
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $12, -0x212
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $13, -0x213
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $14, -0x214
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $15, -0x215
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $16, -0x216
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $17, -0x217
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $18, -0x218
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $19, -0x219
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $20, -0x220
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $21, -0x221
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $23, -0x223
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $24, -0x224
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $25, -0x225
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	addiu	$22, $0, 0x00
	addiu	$22, $30, -0x230
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mfhi	$22
	addiu	$22, $22, -0x231
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mflo	$22, $ac1
	addiu	$22, $22, -0x232
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	/* No errors detected.  Increment the loop count so the check timer knows
	this task is still running without error, then loop back to do it all
	again.  The address of the loop counter is in $4. */
	lw		$22, 0( $4 )
	addiu	$22, $22, 0x01
	sw		$22, 0( $4 )
	b		vRegTest2Loop
	nop

	.end	vRegTest2



