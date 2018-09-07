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

	.global vRegTest1Implementation
	.global vRegTest2Implementation
	.extern ulRegTest1LoopCounter
	.extern ulRegTest2LoopCounter

	.text
	.arm

	/* This function is explained in the comments at the top of main-full.c. */
.type vRegTest1Implementation, %function
vRegTest1Implementation:

	/* Fill each general purpose register with a known value. */
	mov		r0,  #0xFF
	mov		r1,  #0x11
	mov		r2,  #0x22
	mov		r3,  #0x33
	mov     r4,  #0x44
	mov     r5,  #0x55
	mov     r6,  #0x66
	mov     r7,  #0x77
	mov     r8,  #0x88
	mov     r9,  #0x99
	mov     r10, #0xAA
	mov     r11, #0xBB
	mov     r12, #0xCC
	mov		r14, #0xEE

	/* Fill each FPU register with a known value. */
	vmov 	d0, r0, r1
	vmov 	d1, r2, r3
	vmov 	d2, r4, r5
	vmov 	d3, r6, r7
	vmov 	d4, r8, r9
	vmov 	d5, r10, r11
	vmov 	d6, r0, r1
	vmov 	d7, r2, r3
	vmov 	d8, r4, r5
	vmov 	d9, r6, r7
	vmov 	d10, r8, r9
	vmov 	d11, r10, r11
	vmov 	d12, r0, r1
	vmov 	d13, r2, r3
	vmov 	d14, r4, r5
	vmov 	d15, r6, r7

	vmov 	d16, r0, r1
	vmov 	d17, r2, r3
	vmov 	d18, r4, r5
	vmov 	d19, r6, r7
	vmov 	d20, r8, r9
	vmov 	d21, r10, r11
	vmov 	d22, r0, r1
	vmov 	d23, r2, r3
	vmov 	d24, r4, r5
	vmov 	d25, r6, r7
	vmov 	d26, r8, r9
	vmov 	d27, r10, r11
	vmov 	d28, r0, r1
	vmov 	d29, r2, r3
	vmov 	d30, r4, r5
	vmov 	d31, r6, r7

	/* Loop, checking each iteration that each register still contains the
	expected value. */
reg1_loop:
	/* Yield to increase test coverage */
	svc 0

	/* Check all the VFP registers still contain the values set above.
	First save registers that are clobbered by the test. */
	push { r0-r1 }

	vmov 	r0, r1, d0
	cmp 	r0, #0xFF
	bne 	reg1_error_loopf
	cmp 	r1, #0x11
	bne 	reg1_error_loopf
	vmov 	r0, r1, d1
	cmp 	r0, #0x22
	bne 	reg1_error_loopf
	cmp 	r1, #0x33
	bne 	reg1_error_loopf
	vmov 	r0, r1, d2
	cmp 	r0, #0x44
	bne 	reg1_error_loopf
	cmp 	r1, #0x55
	bne 	reg1_error_loopf
	vmov 	r0, r1, d3
	cmp 	r0, #0x66
	bne 	reg1_error_loopf
	cmp 	r1, #0x77
	bne 	reg1_error_loopf
	vmov 	r0, r1, d4
	cmp 	r0, #0x88
	bne 	reg1_error_loopf
	cmp 	r1, #0x99
	bne 	reg1_error_loopf
	vmov 	r0, r1, d5
	cmp 	r0, #0xAA
	bne 	reg1_error_loopf
	cmp 	r1, #0xBB
	bne 	reg1_error_loopf
	vmov 	r0, r1, d6
	cmp 	r0, #0xFF
	bne 	reg1_error_loopf
	cmp 	r1, #0x11
	bne 	reg1_error_loopf
	vmov 	r0, r1, d7
	cmp 	r0, #0x22
	bne 	reg1_error_loopf
	cmp 	r1, #0x33
	bne 	reg1_error_loopf
	vmov 	r0, r1, d8
	cmp 	r0, #0x44
	bne 	reg1_error_loopf
	cmp 	r1, #0x55
	bne 	reg1_error_loopf
	vmov 	r0, r1, d9
	cmp 	r0, #0x66
	bne 	reg1_error_loopf
	cmp 	r1, #0x77
	bne 	reg1_error_loopf
	vmov 	r0, r1, d10
	cmp 	r0, #0x88
	bne 	reg1_error_loopf
	cmp 	r1, #0x99
	bne 	reg1_error_loopf
	vmov 	r0, r1, d11
	cmp 	r0, #0xAA
	bne 	reg1_error_loopf
	cmp 	r1, #0xBB
	bne 	reg1_error_loopf
	vmov 	r0, r1, d12
	cmp 	r0, #0xFF
	bne 	reg1_error_loopf
	cmp 	r1, #0x11
	bne 	reg1_error_loopf
	vmov 	r0, r1, d13
	cmp 	r0, #0x22
	bne 	reg1_error_loopf
	cmp 	r1, #0x33
	bne 	reg1_error_loopf
	vmov 	r0, r1, d14
	cmp 	r0, #0x44
	bne 	reg1_error_loopf
	cmp 	r1, #0x55
	bne 	reg1_error_loopf
	vmov 	r0, r1, d15
	cmp 	r0, #0x66
	bne 	reg1_error_loopf
	cmp 	r1, #0x77
	bne 	reg1_error_loopf

	vmov 	r0, r1, d16
	cmp 	r0, #0xFF
	bne 	reg1_error_loopf
	cmp 	r1, #0x11
	bne 	reg1_error_loopf
	vmov 	r0, r1, d17
	cmp 	r0, #0x22
	bne 	reg1_error_loopf
	cmp 	r1, #0x33
	bne 	reg1_error_loopf
	vmov 	r0, r1, d18
	cmp 	r0, #0x44
	bne 	reg1_error_loopf
	cmp 	r1, #0x55
	bne 	reg1_error_loopf
	vmov 	r0, r1, d19
	cmp 	r0, #0x66
	bne 	reg1_error_loopf
	cmp 	r1, #0x77
	bne 	reg1_error_loopf
	vmov 	r0, r1, d20
	cmp 	r0, #0x88
	bne 	reg1_error_loopf
	cmp 	r1, #0x99
	bne 	reg1_error_loopf
	vmov 	r0, r1, d21
	cmp 	r0, #0xAA
	bne 	reg1_error_loopf
	cmp 	r1, #0xBB
	bne 	reg1_error_loopf
	vmov 	r0, r1, d22
	cmp 	r0, #0xFF
	bne 	reg1_error_loopf
	cmp 	r1, #0x11
	bne 	reg1_error_loopf
	vmov 	r0, r1, d23
	cmp 	r0, #0x22
	bne 	reg1_error_loopf
	cmp 	r1, #0x33
	bne 	reg1_error_loopf
	vmov 	r0, r1, d24
	cmp 	r0, #0x44
	bne 	reg1_error_loopf
	cmp 	r1, #0x55
	bne 	reg1_error_loopf
	vmov 	r0, r1, d25
	cmp 	r0, #0x66
	bne 	reg1_error_loopf
	cmp 	r1, #0x77
	bne 	reg1_error_loopf
	vmov 	r0, r1, d26
	cmp 	r0, #0x88
	bne 	reg1_error_loopf
	cmp 	r1, #0x99
	bne 	reg1_error_loopf
	vmov 	r0, r1, d27
	cmp 	r0, #0xAA
	bne 	reg1_error_loopf
	cmp 	r1, #0xBB
	bne 	reg1_error_loopf
	vmov 	r0, r1, d28
	cmp 	r0, #0xFF
	bne 	reg1_error_loopf
	cmp 	r1, #0x11
	bne 	reg1_error_loopf
	vmov 	r0, r1, d29
	cmp 	r0, #0x22
	bne 	reg1_error_loopf
	cmp 	r1, #0x33
	bne 	reg1_error_loopf
	vmov 	r0, r1, d30
	cmp 	r0, #0x44
	bne 	reg1_error_loopf
	cmp 	r1, #0x55
	bne 	reg1_error_loopf
	vmov 	r0, r1, d31
	cmp 	r0, #0x66
	bne 	reg1_error_loopf
	cmp 	r1, #0x77
	bne 	reg1_error_loopf

	/* Restore the registers that were clobbered by the test. */
	pop 	{r0-r1}

	/* VFP register test passed.  Jump to the core register test. */
	b 		reg1_loopf_pass

reg1_error_loopf:
	/* If this line is hit then a VFP register value was found to be
	incorrect. */
	b reg1_error_loopf

reg1_loopf_pass:

	/* Test each general purpose register to check that it still contains the
	expected known value, jumping to reg1_error_loop if any register contains
	an unexpected value. */
	cmp		r0, #0xFF
	bne		reg1_error_loop
	cmp		r1, #0x11
	bne		reg1_error_loop
	cmp		r2, #0x22
	bne		reg1_error_loop
	cmp		r3, #0x33
	bne		reg1_error_loop
	cmp		r4, #0x44
	bne		reg1_error_loop
	cmp		r5, #0x55
	bne		reg1_error_loop
	cmp		r6, #0x66
	bne		reg1_error_loop
	cmp		r7, #0x77
	bne		reg1_error_loop
	cmp		r8, #0x88
	bne		reg1_error_loop
	cmp		r9, #0x99
	bne		reg1_error_loop
	cmp		r10, #0xAA
	bne		reg1_error_loop
	cmp		r11, #0xBB
	bne		reg1_error_loop
	cmp		r12, #0xCC
	bne		reg1_error_loop
	cmp		r14, #0xEE
	bne		reg1_error_loop

	/* Everything passed, increment the loop counter. */
	push { r0-r1 }
	ldr	r0, =ulRegTest1LoopCounter
	ldr r1, [r0]
	adds r1, r1, #1
	str r1, [r0]
	pop { r0-r1 }

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

	/* Put a known value in each register. */
	mov		r0,  #0xFF000000
	mov		r1,  #0x11000000
	mov		r2,  #0x22000000
	mov		r3,  #0x33000000
	mov     r4,  #0x44000000
	mov     r5,  #0x55000000
	mov     r6,  #0x66000000
	mov     r7,  #0x77000000
	mov     r8,  #0x88000000
	mov     r9,  #0x99000000
	mov     r10, #0xAA000000
	mov     r11, #0xBB000000
	mov     r12, #0xCC000000
	mov     r14, #0xEE000000

	/* Likewise the floating point registers */
	vmov 	d0, r0, r1
	vmov 	d1, r2, r3
	vmov 	d2, r4, r5
	vmov 	d3, r6, r7
	vmov 	d4, r8, r9
	vmov 	d5, r10, r11
	vmov 	d6, r0, r1
	vmov 	d7, r2, r3
	vmov 	d8, r4, r5
	vmov 	d9, r6, r7
	vmov 	d10, r8, r9
	vmov 	d11, r10, r11
	vmov 	d12, r0, r1
	vmov 	d13, r2, r3
	vmov 	d14, r4, r5
	vmov 	d15, r6, r7

	vmov 	d16, r0, r1
	vmov 	d17, r2, r3
	vmov 	d18, r4, r5
	vmov 	d19, r6, r7
	vmov 	d20, r8, r9
	vmov 	d21, r10, r11
	vmov 	d22, r0, r1
	vmov 	d23, r2, r3
	vmov 	d24, r4, r5
	vmov 	d25, r6, r7
	vmov 	d26, r8, r9
	vmov 	d27, r10, r11
	vmov 	d28, r0, r1
	vmov 	d29, r2, r3
	vmov 	d30, r4, r5
	vmov 	d31, r6, r7

	/* Loop, checking each iteration that each register still contains the
	expected value. */
reg2_loop:
	/* Check all the VFP registers still contain the values set above.
	First save registers that are clobbered by the test. */
	push 	{ r0-r1 }

	vmov 	r0, r1, d0
	cmp 	r0, #0xFF000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x11000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d1
	cmp 	r0, #0x22000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x33000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d2
	cmp 	r0, #0x44000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x55000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d3
	cmp 	r0, #0x66000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x77000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d4
	cmp 	r0, #0x88000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x99000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d5
	cmp 	r0, #0xAA000000
	bne 	reg2_error_loopf
	cmp 	r1, #0xBB000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d6
	cmp 	r0, #0xFF000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x11000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d7
	cmp 	r0, #0x22000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x33000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d8
	cmp 	r0, #0x44000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x55000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d9
	cmp 	r0, #0x66000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x77000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d10
	cmp 	r0, #0x88000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x99000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d11
	cmp 	r0, #0xAA000000
	bne 	reg2_error_loopf
	cmp 	r1, #0xBB000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d12
	cmp 	r0, #0xFF000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x11000000
	bne 	reg2_error_loopf
	vmov	r0, r1, d13
	cmp 	r0, #0x22000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x33000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d14
	cmp 	r0, #0x44000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x55000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d15
	cmp 	r0, #0x66000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x77000000
	bne 	reg2_error_loopf

	vmov 	r0, r1, d16
	cmp 	r0, #0xFF000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x11000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d17
	cmp 	r0, #0x22000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x33000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d18
	cmp 	r0, #0x44000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x55000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d19
	cmp 	r0, #0x66000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x77000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d20
	cmp 	r0, #0x88000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x99000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d21
	cmp 	r0, #0xAA000000
	bne 	reg2_error_loopf
	cmp 	r1, #0xBB000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d22
	cmp 	r0, #0xFF000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x11000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d23
	cmp 	r0, #0x22000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x33000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d24
	cmp 	r0, #0x44000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x55000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d25
	cmp 	r0, #0x66000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x77000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d26
	cmp 	r0, #0x88000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x99000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d27
	cmp 	r0, #0xAA000000
	bne 	reg2_error_loopf
	cmp 	r1, #0xBB000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d28
	cmp 	r0, #0xFF000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x11000000
	bne 	reg2_error_loopf
	vmov	r0, r1, d29
	cmp 	r0, #0x22000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x33000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d30
	cmp 	r0, #0x44000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x55000000
	bne 	reg2_error_loopf
	vmov 	r0, r1, d31
	cmp 	r0, #0x66000000
	bne 	reg2_error_loopf
	cmp 	r1, #0x77000000
	bne 	reg2_error_loopf

	/* Restore the registers that were clobbered by the test. */
	pop 	{r0-r1}

	/* VFP register test passed.  Jump to the core register test. */
	b 		reg2_loopf_pass

reg2_error_loopf:
	/* If this line is hit then a VFP register value was found to be
	incorrect. */
	b 		reg2_error_loopf

reg2_loopf_pass:

	cmp		r0, #0xFF000000
	bne		reg2_error_loop
	cmp		r1, #0x11000000
	bne		reg2_error_loop
	cmp		r2, #0x22000000
	bne		reg2_error_loop
	cmp		r3, #0x33000000
	bne		reg2_error_loop
	cmp		r4, #0x44000000
	bne		reg2_error_loop
	cmp		r5, #0x55000000
	bne		reg2_error_loop
	cmp		r6, #0x66000000
	bne		reg2_error_loop
	cmp		r7, #0x77000000
	bne		reg2_error_loop
	cmp		r8, #0x88000000
	bne		reg2_error_loop
	cmp		r9, #0x99000000
	bne		reg2_error_loop
	cmp		r10, #0xAA000000
	bne		reg2_error_loop
	cmp		r11, #0xBB000000
	bne		reg2_error_loop
	cmp		r12, #0xCC000000
	bne		reg2_error_loop
	cmp     r14, #0xEE000000
	bne		reg2_error_loop

	/* Everything passed, increment the loop counter. */
	push 	{ r0-r1 }
	ldr		r0, =ulRegTest2LoopCounter
	ldr 	r1, [r0]
	adds 	r1, r1, #1
	str 	r1, [r0]
	pop 	{ r0-r1 }

	/* Start again. */
	b 		reg2_loop

reg2_error_loop:
	/* If this line is hit then there was an error in a core register value.
	The loop ensures the loop counter stops incrementing. */
	b 		reg2_error_loop
	nop


	.end

