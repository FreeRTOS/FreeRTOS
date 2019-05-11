/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

	.global vRegTest1Implementation
	.global vRegTest2Implementation
	.extern ullRegTest1LoopCounter
	.extern ullRegTest2LoopCounter

	.text

	/* This function is explained in the comments at the top of main-full.c. */
.type vRegTest1Implementation, %function
vRegTest1Implementation:

	/* Fill each general purpose register with a known value. */
	mov		x0, #0xff
	mov		x1, #0x01
	mov		x2, #0x02
	mov		x3, #0x03
	mov		x4, #0x04
	mov		x5, #0x05
	mov		x6, #0x06
	mov		x7, #0x07
	mov		x8, #0x08
	mov		x9, #0x09
	mov		x10, #0x10
	mov		x11, #0x11
	mov		x12, #0x12
	mov		x13, #0x13
	mov		x14, #0x14
	mov		x15, #0x15
	mov		x16, #0x16
	mov		x17, #0x17
	mov		x18, #0x18
	mov		x19, #0x19
	mov		x20, #0x20
	mov		x21, #0x21
	mov		x22, #0x22
	mov		x23, #0x23
	mov		x24, #0x24
	mov		x25, #0x25
	mov		x26, #0x26
	mov		x27, #0x27
	mov		x28, #0x28
	mov		x29, #0x29
	mov		x30, #0x30

	/* Fill each FPU register with a known value. */
	fmov	v0.d[1], x0
	fmov	d1, x1
	fmov	d2, x2
	fmov	d3, x3
	fmov	d4, x4
	fmov	d5, x5
	fmov	d6, x6
	fmov	d7, x7
	fmov	d8, x8
	fmov	d9, x9
	fmov	d10, x10
	fmov	d11, x11
	fmov	d12, x12
	fmov	d13, x13
	fmov	d14, x14
	fmov	d15, x15
	fmov	d16, x16
	fmov	d17, x17
	fmov	d18, x18
	fmov	d19, x19
	fmov	d20, x20
	fmov	d21, x21
	fmov	d22, x22
	fmov	d23, x23
	fmov	d24, x24
	fmov	d25, x25
	fmov	d26, x26
	fmov	d27, x27
	fmov	d28, x28
	fmov	d29, x29
	fmov	v30.d[1], x30
	fmov	d31, xzr

	/* Loop, checking each itteration that each register still contains the
	expected value. */
reg1_loop:
	/* Yield to increase test coverage */
	SMC 0

	/* Test each general purpose register to check that it still contains the
	expected known value, jumping to reg1_error_loop if any register contains
	an unexpected value. */
	cmp		x0, #0xFF
	bne		reg1_error_loop
	cmp		x1, #0x01
	bne		reg1_error_loop
	cmp		x2, #0x02
	bne		reg1_error_loop
	cmp		x3, #0x03
	bne		reg1_error_loop
	cmp		x4, #0x04
	bne		reg1_error_loop
	cmp		x5, #0x05
	bne		reg1_error_loop
	cmp		x6, #0x06
	bne		reg1_error_loop
	cmp		x7, #0x07
	bne		reg1_error_loop
	cmp		x8, #0x08
	bne		reg1_error_loop
	cmp		x9, #0x09
	bne		reg1_error_loop
	cmp		x10, #0x10
	bne		reg1_error_loop
	cmp		x11, #0x11
	bne		reg1_error_loop
	cmp		x12, #0x12
	bne		reg1_error_loop
	cmp		x13, #0x13
	bne		reg1_error_loop
	cmp		x14, #0x14
	bne		reg1_error_loop
	cmp		x15, #0x15
	bne		reg1_error_loop
	cmp		x16, #0x16
	bne		reg1_error_loop
	cmp		x17, #0x17
	bne		reg1_error_loop
	cmp		x18, #0x18
	bne		reg1_error_loop
	cmp		x19, #0x19
	bne		reg1_error_loop
	cmp		x20, #0x20
	bne		reg1_error_loop
	cmp		x21, #0x21
	bne		reg1_error_loop
	cmp		x22, #0x22
	bne		reg1_error_loop
	cmp		x23, #0x23
	bne		reg1_error_loop
	cmp		x24, #0x24
	bne		reg1_error_loop
	cmp		x25, #0x25
	bne		reg1_error_loop
	cmp		x26, #0x26
	bne		reg1_error_loop
	cmp		x27, #0x27
	bne		reg1_error_loop
	cmp		x28, #0x28
	bne		reg1_error_loop
	cmp		x29, #0x29
	bne		reg1_error_loop
	cmp		x30, #0x30
	bne		reg1_error_loop

	/* Check every floating point register to ensure it contains the expected
	value.  First save the registers clobbered by the test. */
	stp 	x0, x1, [sp,#-0x10]!

	fmov	x0, v0.d[1]
	cmp		x0, 0xff
	bne		reg1_error_loop
	fmov	x0, d1
	cmp		x0, 0x01
	bne		reg1_error_loop
	fmov	x0, d2
	cmp		x0, 0x02
	bne		reg1_error_loop
	fmov	x0, d3
	cmp		x0, 0x03
	bne		reg1_error_loop
	fmov	x0, d4
	cmp		x0, 0x04
	bne		reg1_error_loop
	fmov	x0, d5
	cmp		x0, 0x05
	bne		reg1_error_loop
	fmov	x0, d6
	cmp		x0, 0x06
	bne		reg1_error_loop
	fmov	x0, d7
	cmp		x0, 0x07
	bne		reg1_error_loop
	fmov	x0, d8
	cmp		x0, 0x08
	bne		reg1_error_loop
	fmov	x0, d9
	cmp		x0, 0x09
	bne		reg1_error_loop
	fmov	x0, d10
	cmp		x0, 0x10
	bne		reg1_error_loop
	fmov	x0, d11
	cmp		x0, 0x11
	bne		reg1_error_loop
	fmov	x0, d12
	cmp		x0, 0x12
	bne		reg1_error_loop
	fmov	x0, d13
	cmp		x0, 0x13
	bne		reg1_error_loop
	fmov	x0, d14
	cmp		x0, 0x14
	bne		reg1_error_loop
	fmov	x0, d15
	cmp		x0, 0x15
	bne		reg1_error_loop
	fmov	x0, d16
	cmp		x0, 0x16
	bne		reg1_error_loop
	fmov	x0, d17
	cmp		x0, 0x17
	bne		reg1_error_loop
	fmov	x0, d18
	cmp		x0, 0x18
	bne		reg1_error_loop
	fmov	x0, d19
	cmp		x0, 0x19
	bne		reg1_error_loop
	fmov	x0, d20
	cmp		x0, 0x20
	bne		reg1_error_loop
	fmov	x0, d21
	cmp		x0, 0x21
	bne		reg1_error_loop
	fmov	x0, d22
	cmp		x0, 0x22
	bne		reg1_error_loop
	fmov	x0, d23
	cmp		x0, 0x23
	bne		reg1_error_loop
	fmov	x0, d24
	cmp		x0, 0x24
	bne		reg1_error_loop
	fmov	x0, d25
	cmp		x0, 0x25
	bne		reg1_error_loop
	fmov	x0, d26
	cmp		x0, 0x26
	bne		reg1_error_loop
	fmov	x0, d27
	cmp		x0, 0x27
	bne		reg1_error_loop
	fmov	x0, d28
	cmp		x0, 0x28
	bne		reg1_error_loop
	fmov	x0, d29
	cmp		x0, 0x29
	bne		reg1_error_loop
	fmov	x0, v30.d[1]
	cmp		x0, 0x30
	bne		reg1_error_loop
	fmov	x0, d31
	cmp		x0, 0x00
	bne		reg1_error_loop

	/* Restore the registers clobbered by the test. */
	ldp 	x0, x1, [sp], #0x10

	/* Everything passed, increment the loop counter. */
	stp 	x0, x1, [sp,#-0x10]!
	ldr		x0, =ullRegTest1LoopCounter
	ldr 	x1, [x0]
	adds 	x1, x1, #1
	str 	x1, [x0]
	ldp 	x0, x1, [sp], #0x10

	/* Start again. */
	b reg1_loop

reg1_error_loop:
	/* If this line is hit then there was an error in a core register value.
	The loop ensures the loop counter stops incrementing. */
	b reg1_error_loop
	nop

/*-----------------------------------------------------------*/

.type vRegTest2Implementation, %function
vRegTest2Implementation:

	/* Fill each general purpose register with a known value. */
	mov		x0, #0xff0
	mov		x1, #0x010
	mov		x2, #0x020
	mov		x3, #0x030
	mov		x4, #0x040
	mov		x5, #0x050
	mov		x6, #0x060
	mov		x7, #0x070
	mov		x8, #0x080
	mov		x9, #0x090
	mov		x10, #0x100
	mov		x11, #0x110
	mov		x12, #0x120
	mov		x13, #0x130
	mov		x14, #0x140
	mov		x15, #0x150
	mov		x16, #0x160
	mov		x17, #0x170
	mov		x18, #0x180
	mov		x19, #0x190
	mov		x20, #0x200
	mov		x21, #0x210
	mov		x22, #0x220
	mov		x23, #0x230
	mov		x24, #0x240
	mov		x25, #0x250
	mov		x26, #0x260
	mov		x27, #0x270
	mov		x28, #0x280
	mov		x29, #0x290
	mov		x30, #0x300

	/* Fill each FPU register with a known value. */
	fmov	d0, x0
	fmov	d1, x1
	fmov	d2, x2
	fmov	d3, x3
	fmov	d4, x4
	fmov	d5, x5
	fmov	d6, x6
	fmov	d7, x7
	fmov	d8, x8
	fmov	d9, x9
	fmov	v10.d[1], x10
	fmov	d11, x11
	fmov	d12, x12
	fmov	d13, x13
	fmov	d14, x14
	fmov	d15, x15
	fmov	d16, x16
	fmov	d17, x17
	fmov	d18, x18
	fmov	d19, x19
	fmov	d20, x20
	fmov	d21, x21
	fmov	d22, x22
	fmov	d23, x23
	fmov	d24, x24
	fmov	d25, x25
	fmov	d26, x26
	fmov	v27.d[1], x27
	fmov	d28, x28
	fmov	d29, x29
	fmov	d30, x30
	fmov	d31, x0

	/* Loop, checking each itteration that each register still contains the
	expected value. */
reg2_loop:

	/* Test each general purpose register to check that it still contains the
	expected known value, jumping to reg2_error_loop if any register contains
	an unexpected value. */
	cmp		x0, #0xFF0
	bne		reg2_error_loop
	cmp		x1, #0x010
	bne		reg2_error_loop
	cmp		x2, #0x020
	bne		reg2_error_loop
	cmp		x3, #0x030
	bne		reg2_error_loop
	cmp		x4, #0x040
	bne		reg2_error_loop
	cmp		x5, #0x050
	bne		reg2_error_loop
	cmp		x6, #0x060
	bne		reg2_error_loop
	cmp		x7, #0x070
	bne		reg2_error_loop
	cmp		x8, #0x080
	bne		reg2_error_loop
	cmp		x9, #0x090
	bne		reg2_error_loop
	cmp		x10, #0x100
	bne		reg2_error_loop
	cmp		x11, #0x110
	bne		reg2_error_loop
	cmp		x12, #0x120
	bne		reg2_error_loop
	cmp		x13, #0x130
	bne		reg2_error_loop
	cmp		x14, #0x140
	bne		reg2_error_loop
	cmp		x15, #0x150
	bne		reg2_error_loop
	cmp		x16, #0x160
	bne		reg2_error_loop
	cmp		x17, #0x170
	bne		reg2_error_loop
	cmp		x18, #0x180
	bne		reg2_error_loop
	cmp		x19, #0x190
	bne		reg2_error_loop
	cmp		x20, #0x200
	bne		reg2_error_loop
	cmp		x21, #0x210
	bne		reg2_error_loop
	cmp		x22, #0x220
	bne		reg2_error_loop
	cmp		x23, #0x230
	bne		reg2_error_loop
	cmp		x24, #0x240
	bne		reg2_error_loop
	cmp		x25, #0x250
	bne		reg2_error_loop
	cmp		x26, #0x260
	bne		reg2_error_loop
	cmp		x27, #0x270
	bne		reg2_error_loop
	cmp		x28, #0x280
	bne		reg2_error_loop
	cmp		x29, #0x290
	bne		reg2_error_loop
	cmp		x30, #0x300
	bne		reg2_error_loop

	/* Check every floating point register to ensure it contains the expected
	value.  First save the registers clobbered by the test. */
	stp 	x0, x1, [sp,#-0x10]!

	fmov	x0, d0
	cmp		x0, 0xff0
	bne		reg1_error_loop
	fmov	x0, d1
	cmp		x0, 0x010
	bne		reg1_error_loop
	fmov	x0, d2
	cmp		x0, 0x020
	bne		reg1_error_loop
	fmov	x0, d3
	cmp		x0, 0x030
	bne		reg1_error_loop
	fmov	x0, d4
	cmp		x0, 0x040
	bne		reg1_error_loop
	fmov	x0, d5
	cmp		x0, 0x050
	bne		reg1_error_loop
	fmov	x0, d6
	cmp		x0, 0x060
	bne		reg1_error_loop
	fmov	x0, d7
	cmp		x0, 0x070
	bne		reg1_error_loop
	fmov	x0, d8
	cmp		x0, 0x080
	bne		reg1_error_loop
	fmov	x0, d9
	cmp		x0, 0x090
	bne		reg1_error_loop
	fmov	x0, v10.d[1]
	cmp		x0, 0x100
	bne		reg1_error_loop
	fmov	x0, d11
	cmp		x0, 0x110
	bne		reg1_error_loop
	fmov	x0, d12
	cmp		x0, 0x120
	bne		reg1_error_loop
	fmov	x0, d13
	cmp		x0, 0x130
	bne		reg1_error_loop
	fmov	x0, d14
	cmp		x0, 0x140
	bne		reg1_error_loop
	fmov	x0, d15
	cmp		x0, 0x150
	bne		reg1_error_loop
	fmov	x0, d16
	cmp		x0, 0x160
	bne		reg1_error_loop
	fmov	x0, d17
	cmp		x0, 0x170
	bne		reg1_error_loop
	fmov	x0, d18
	cmp		x0, 0x180
	bne		reg1_error_loop
	fmov	x0, d19
	cmp		x0, 0x190
	bne		reg1_error_loop
	fmov	x0, d20
	cmp		x0, 0x200
	bne		reg1_error_loop
	fmov	x0, d21
	cmp		x0, 0x210
	bne		reg1_error_loop
	fmov	x0, d22
	cmp		x0, 0x220
	bne		reg1_error_loop
	fmov	x0, d23
	cmp		x0, 0x230
	bne		reg1_error_loop
	fmov	x0, d24
	cmp		x0, 0x240
	bne		reg1_error_loop
	fmov	x0, d25
	cmp		x0, 0x250
	bne		reg1_error_loop
	fmov	x0, d26
	cmp		x0, 0x260
	bne		reg1_error_loop
	fmov	x0, v27.d[1]
	cmp		x0, 0x270
	bne		reg1_error_loop
	fmov	x0, d28
	cmp		x0, 0x280
	bne		reg1_error_loop
	fmov	x0, d29
	cmp		x0, 0x290
	bne		reg1_error_loop
	fmov	x0, d30
	cmp		x0, 0x300
	bne		reg1_error_loop
	fmov	x0, d31
	cmp		x0, 0xff0
	bne		reg1_error_loop

	/* Restore the registers clobbered by the test. */
	ldp 	x0, x1, [sp], #0x10

	/* Everything passed, increment the loop counter. */
	stp 	x0, x1, [sp,#-0x10]!
	ldr		x0, =ullRegTest2LoopCounter
	ldr 	x1, [x0]
	adds 	x1, x1, #1
	str 	x1, [x0]
	ldp 	x0, x1, [sp], #0x10

	/* Start again. */
	b reg2_loop

reg2_error_loop:
	/* If this line is hit then there was an error in a core register value.
	The loop ensures the loop counter stops incrementing. */
	b reg2_error_loop
	nop

	.end

