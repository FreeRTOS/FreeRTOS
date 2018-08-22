/*
 * FreeRTOS Kernel V10.1.0
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


#include <xc.h>
#include <sys/asm.h>
#include "FreeRTOSConfig.h"

	.set	nomips16
	.set 	noreorder


	.global	vRegTest1
	.global vRegTest2

/************************************************************************/
/* Reg test macro helper. Test a register for a known value branching to
error_loop if not correct otherwise continuing on */
.macro	portREG_TEST work_reg, test_reg, test_value

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

/************************************************************************/
/* FPU reg test macro helper, Test an FPU register for a known value branching to
error_loop if not correct otherwise continuing on */
	#if ( __mips_hard_float == 1)  && ( configUSE_TASK_FPU_SUPPORT == 1 )
.macro	portFPU_REG_TEST work_reg, test_reg, test_value
	/* get the lower 32 bit value from the FPU and compare to the test value */
	mfc1	\work_reg, \test_reg
	addiu	\work_reg, \work_reg, -\test_value
	beq		\work_reg, $0, 1f
	nop

	/* The register values was not that expected. Jump to the error loop */
	b	error_loop
	nop
1:
	.endm
	#endif


/************************************************************************/
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
	.set	noat
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
	mthi	$22, $ac1
	addiu	$22, $0, 0x132
	mtlo	$22, $ac1
	addiu	$22, $0, 0x133
	mthi	$22, $ac2
	addiu	$22, $0, 0x134
	mtlo	$22, $ac2
	addiu	$22, $0, 0x135
	mthi	$22, $ac3
	addiu	$22, $0, 0x136
	mtlo	$22, $ac3

	/* Test the FPU registers if they are present on the part. */
	#if ( __mips_hard_float == 1 ) && ( configUSE_TASK_FPU_SUPPORT == 1 )
	addiu	$22, $0, 0x180
	mtc1	$22, $f0
	addiu	$22, $0, 0x181
	mtc1	$22, $f1
	addiu	$22, $0, 0x182
	mtc1	$22, $f2
	addiu	$22, $0, 0x183
	mtc1	$22, $f3
	addiu	$22, $0, 0x184
	mtc1	$22, $f4
	addiu	$22, $0, 0x185
	mtc1	$22, $f5
	addiu	$22, $0, 0x186
	mtc1	$22, $f6
	addiu	$22, $0, 0x187
	mtc1	$22, $f7
	addiu	$22, $0, 0x188
	mtc1	$22, $f8
	addiu	$22, $0, 0x189
	mtc1	$22, $f9
	addiu	$22, $0, 0x18A
	mtc1	$22, $f10
	addiu	$22, $0, 0x18B
	mtc1	$22, $f11
	addiu	$22, $0, 0x18C
	mtc1	$22, $f12
	addiu	$22, $0, 0x18D
	mtc1	$22, $f13
	addiu	$22, $0, 0x18E
	mtc1	$22, $f14
	addiu	$22, $0, 0x18F
	mtc1	$22, $f15
	addiu	$22, $0, 0x190
	mtc1	$22, $f16
	addiu	$22, $0, 0x191
	mtc1	$22, $f17
	addiu	$22, $0, 0x192
	mtc1	$22, $f18
	addiu	$22, $0, 0x193
	mtc1	$22, $f19
	addiu	$22, $0, 0x194
	mtc1	$22, $f20
	addiu	$22, $0, 0x195
	mtc1	$22, $f21
	addiu	$22, $0, 0x196
	mtc1	$22, $f22
	addiu	$22, $0, 0x197
	mtc1	$22, $f23
	addiu	$22, $0, 0x198
	mtc1	$22, $f24
	addiu	$22, $0, 0x199
	mtc1	$22, $f25
	addiu	$22, $0, 0x19A
	mtc1	$22, $f26
	addiu	$22, $0, 0x19B
	mtc1	$22, $f27
	addiu	$22, $0, 0x19C
	mtc1	$22, $f28
	addiu	$22, $0, 0x19D
	mtc1	$22, $f29
	addiu	$22, $0, 0x19E
	mtc1	$22, $f30
	addiu	$22, $0, 0x19F
	mtc1	$22, $f31
	#endif

vRegTest1Loop:
	portREG_TEST	$22, $1, 0x11
	portREG_TEST	$22, $2, 0x12
	portREG_TEST	$22, $3, 0x13
	/* Do not test r4 as we are using it as a loop counter */
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
	/* Do not test r22, used as a helper */
	portREG_TEST	$22, $23, 0x123
	portREG_TEST	$22, $24, 0x124
	portREG_TEST	$22, $25, 0x125
	portREG_TEST	$22, $30, 0x130

	mfhi		$22, $ac1
	addiu		$22, $22, -0x131
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mflo		$22, $ac1
	addiu		$22, $22, -0x132
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mfhi		$22, $ac2
	addiu		$22, $22, -0x133
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mflo		$22, $ac2
	addiu		$22, $22, -0x134
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mfhi		$22, $ac3
	addiu		$22, $22, -0x135
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mflo		$22, $ac3
	addiu		$22, $22, -0x136
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	/* Test the FPU registers if they are present on the part. */
	#if ( __mips_hard_float == 1 ) && ( configUSE_TASK_FPU_SUPPORT == 1 )
		portFPU_REG_TEST    $22, $f0, 0x180
		portFPU_REG_TEST    $22, $f1, 0x181
		portFPU_REG_TEST    $22, $f2, 0x182
		portFPU_REG_TEST    $22, $f3, 0x183
		portFPU_REG_TEST    $22, $f4, 0x184
		portFPU_REG_TEST    $22, $f5, 0x185
		portFPU_REG_TEST    $22, $f6, 0x186
		portFPU_REG_TEST    $22, $f7, 0x187
		portFPU_REG_TEST    $22, $f8, 0x188
		portFPU_REG_TEST    $22, $f9, 0x189
		portFPU_REG_TEST    $22, $f10, 0x18A
		portFPU_REG_TEST    $22, $f11, 0x18B
		portFPU_REG_TEST    $22, $f12, 0x18C
		portFPU_REG_TEST    $22, $f13, 0x18D
		portFPU_REG_TEST    $22, $f14, 0x18E
		portFPU_REG_TEST    $22, $f15, 0x18F
		portFPU_REG_TEST    $22, $f16, 0x190
		portFPU_REG_TEST    $22, $f17, 0x191
		portFPU_REG_TEST    $22, $f18, 0x192
		portFPU_REG_TEST    $22, $f19, 0x193
		portFPU_REG_TEST    $22, $f20, 0x194
		portFPU_REG_TEST    $22, $f21, 0x195
		portFPU_REG_TEST    $22, $f22, 0x196
		portFPU_REG_TEST    $22, $f23, 0x197
		portFPU_REG_TEST    $22, $f24, 0x198
		portFPU_REG_TEST    $22, $f25, 0x199
		portFPU_REG_TEST    $22, $f26, 0x19A
		portFPU_REG_TEST    $22, $f27, 0x19B
		portFPU_REG_TEST    $22, $f28, 0x19C
		portFPU_REG_TEST    $22, $f29, 0x19D
		portFPU_REG_TEST    $22, $f30, 0x19E
		portFPU_REG_TEST    $22, $f31, 0x19F
	#endif

	/* No errors detected.  Increment the loop count so the check timer knows
	this task is still running without error, then loop back to do it all
	again.  The address of the loop counter is in $4. */
	lw		$22, 0( $4 )
	addiu		$22, $22, 0x01
	sw		$22, 0( $4 )
	b		vRegTest1Loop
	nop

	.end	vRegTest1

/************************************************************************/
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
	mthi	$22, $ac1
	addiu	$22, $0, 0x232
	mtlo	$22, $ac1
	addiu	$22, $0, 0x233
	mthi	$22, $ac2
	addiu	$22, $0, 0x234
	mtlo	$22, $ac2
	addiu	$22, $0, 0x235
	mthi	$22, $ac3
	addiu	$22, $0, 0x236
	mtlo	$22, $ac3

	/* Test the FPU registers if they are present on the part. */
	#if ( __mips_hard_float == 1 ) && ( configUSE_TASK_FPU_SUPPORT == 1 )
	addiu	$22, $0, 0x280
	mtc1	$22, $f0
	addiu	$22, $0, 0x281
	mtc1	$22, $f1
	addiu	$22, $0, 0x282
	mtc1	$22, $f2
	addiu	$22, $0, 0x283
	mtc1	$22, $f3
	addiu	$22, $0, 0x284
	mtc1	$22, $f4
	addiu	$22, $0, 0x285
	mtc1	$22, $f5
	addiu	$22, $0, 0x286
	mtc1	$22, $f6
	addiu	$22, $0, 0x287
	mtc1	$22, $f7
	addiu	$22, $0, 0x288
	mtc1	$22, $f8
	addiu	$22, $0, 0x289
	mtc1	$22, $f9
	addiu	$22, $0, 0x28A
	mtc1	$22, $f10
	addiu	$22, $0, 0x28B
	mtc1	$22, $f11
	addiu	$22, $0, 0x28C
	mtc1	$22, $f12
	addiu	$22, $0, 0x28D
	mtc1	$22, $f13
	addiu	$22, $0, 0x28E
	mtc1	$22, $f14
	addiu	$22, $0, 0x28F
	mtc1	$22, $f15
	addiu	$22, $0, 0x290
	mtc1	$22, $f16
	addiu	$22, $0, 0x291
	mtc1	$22, $f17
	addiu	$22, $0, 0x292
	mtc1	$22, $f18
	addiu	$22, $0, 0x293
	mtc1	$22, $f19
	addiu	$22, $0, 0x294
	mtc1	$22, $f20
	addiu	$22, $0, 0x295
	mtc1	$22, $f21
	addiu	$22, $0, 0x296
	mtc1	$22, $f22
	addiu	$22, $0, 0x297
	mtc1	$22, $f23
	addiu	$22, $0, 0x298
	mtc1	$22, $f24
	addiu	$22, $0, 0x299
	mtc1	$22, $f25
	addiu	$22, $0, 0x29A
	mtc1	$22, $f26
	addiu	$22, $0, 0x29B
	mtc1	$22, $f27
	addiu	$22, $0, 0x29C
	mtc1	$22, $f28
	addiu	$22, $0, 0x29D
	mtc1	$22, $f29
	addiu	$22, $0, 0x29E
	mtc1	$22, $f30
	addiu	$22, $0, 0x29F
	mtc1	$22, $f31
	#endif

vRegTest2Loop:
	portREG_TEST	$22, $1, 0x21
	portREG_TEST	$22, $2, 0x22
	portREG_TEST	$22, $3, 0x23
	/* Do not test r4 as we are using it as a loop counter */
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
	/* Do not test r22, used as a helper */
	portREG_TEST	$22, $23, 0x223
	portREG_TEST	$22, $24, 0x224
	portREG_TEST	$22, $25, 0x225
	portREG_TEST	$22, $30, 0x230

	mfhi	$22, $ac1
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

	mfhi	$22, $ac2
	addiu	$22, $22, -0x233
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mflo	$22, $ac2
	addiu	$22, $22, -0x234
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mfhi	$22, $ac3
	addiu	$22, $22, -0x235
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	mflo	$22, $ac3
	addiu	$22, $22, -0x236
	beq		$22, $0, .+16
	nop
	b		error_loop
	nop

	/* Test the FPU registers if they are present on the part. */
	#if ( __mips_hard_float == 1 ) && ( configUSE_TASK_FPU_SUPPORT == 1 )
		portFPU_REG_TEST    $22, $f0, 0x280
		portFPU_REG_TEST    $22, $f1, 0x281
		portFPU_REG_TEST    $22, $f2, 0x282
		portFPU_REG_TEST    $22, $f3, 0x283
		portFPU_REG_TEST    $22, $f4, 0x284
		portFPU_REG_TEST    $22, $f5, 0x285
		portFPU_REG_TEST    $22, $f6, 0x286
		portFPU_REG_TEST    $22, $f7, 0x287
		portFPU_REG_TEST    $22, $f8, 0x288
		portFPU_REG_TEST    $22, $f9, 0x289
		portFPU_REG_TEST    $22, $f10, 0x28A
		portFPU_REG_TEST    $22, $f11, 0x28B
		portFPU_REG_TEST    $22, $f12, 0x28C
		portFPU_REG_TEST    $22, $f13, 0x28D
		portFPU_REG_TEST    $22, $f14, 0x28E
		portFPU_REG_TEST    $22, $f15, 0x28F
		portFPU_REG_TEST    $22, $f16, 0x290
		portFPU_REG_TEST    $22, $f17, 0x291
		portFPU_REG_TEST    $22, $f18, 0x292
		portFPU_REG_TEST    $22, $f19, 0x293
		portFPU_REG_TEST    $22, $f20, 0x294
		portFPU_REG_TEST    $22, $f21, 0x295
		portFPU_REG_TEST    $22, $f22, 0x296
		portFPU_REG_TEST    $22, $f23, 0x297
		portFPU_REG_TEST    $22, $f24, 0x298
		portFPU_REG_TEST    $22, $f25, 0x299
		portFPU_REG_TEST    $22, $f26, 0x29A
		portFPU_REG_TEST    $22, $f27, 0x29B
		portFPU_REG_TEST    $22, $f28, 0x29C
		portFPU_REG_TEST    $22, $f29, 0x29D
		portFPU_REG_TEST    $22, $f30, 0x29E
		portFPU_REG_TEST    $22, $f31, 0x29F
	#endif

	/* No errors detected.  Increment the loop count so the check timer knows
	this task is still running without error, then loop back to do it all
	again.  The address of the loop counter is in $4. */
	lw		$22, 0( $4 )
	addiu	$22, $22, 0x01
	sw		$22, 0( $4 )
	b		vRegTest2Loop
	nop

	.end	vRegTest2



