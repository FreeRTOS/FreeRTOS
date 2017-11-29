/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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

	RSEG    CODE:CODE(2)
	thumb

	EXTERN ulRegTest1LoopCounter
	EXTERN ulRegTest2LoopCounter

	PUBLIC vRegTest1Task
	PUBLIC vRegTest2Task

/*-----------------------------------------------------------*/
vRegTest1Task

	/* Fill the core registers with known values.  This is only done once. */
	movs r1, #101
	movs r2, #102
	movs r3, #103
	movs r4, #104
	movs r5, #105
	movs r6, #106
	movs r7, #107
	movs r0, #108
	mov	 r8, r0
	movs r0, #109
	mov  r9, r0
	movs r0, #110
	mov	 r10, r0
	movs r0, #111
	mov	 r11, r0
	movs r0, #112
	mov  r12, r0
	movs r0, #100

reg1_loop
	/* Repeatedly check that each register still contains the value written to
	it when the task started. */
	cmp	r0, #100
	bne	reg1_error_loop
	cmp	r1, #101
	bne	reg1_error_loop
	cmp	r2, #102
	bne	reg1_error_loop
	cmp r3, #103
	bne	reg1_error_loop
	cmp	r4, #104
	bne	reg1_error_loop
	cmp	r5, #105
	bne	reg1_error_loop
	cmp	r6, #106
	bne	reg1_error_loop
	cmp	r7, #107
	bne	reg1_error_loop
	movs r0, #108
	cmp	r8, r0
	bne	reg1_error_loop
	movs r0, #109
	cmp	r9, r0
	bne	reg1_error_loop
	movs r0, #110
	cmp	r10, r0
	bne	reg1_error_loop
	movs r0, #111
	cmp	r11, r0
	bne	reg1_error_loop
	movs r0, #112
	cmp	r12, r0
	bne	reg1_error_loop

	/* Everything passed, increment the loop counter. */
	push { r1 }
	ldr	r0, =ulRegTest1LoopCounter
	ldr r1, [r0]
	adds r1, r1, #1
	str r1, [r0]
	pop { r1 }

	/* Start again. */
	movs r0, #100
	b reg1_loop

reg1_error_loop
	/* If this line is hit then there was an error in a core register value.
	The loop ensures the loop counter stops incrementing. */
	b reg1_error_loop
	nop



vRegTest2Task

	/* Fill the core registers with known values.  This is only done once. */
	movs r1, #1
	movs r2, #2
	movs r3, #3
	movs r4, #4
	movs r5, #5
	movs r6, #6
	movs r7, #7
	movs r0, #8
	mov	r8, r0
	movs r0, #9
	mov r9, r0
	movs r0, #10
	mov	r10, r0
	movs r0, #11
	mov	r11, r0
	movs r0, #12
	mov r12, r0
	movs r0, #10

reg2_loop
	/* Repeatedly check that each register still contains the value written to
	it when the task started. */
	cmp	r0, #10
	bne	reg2_error_loop
	cmp	r1, #1
	bne	reg2_error_loop
	cmp	r2, #2
	bne	reg2_error_loop
	cmp r3, #3
	bne	reg2_error_loop
	cmp	r4, #4
	bne	reg2_error_loop
	cmp	r5, #5
	bne	reg2_error_loop
	cmp	r6, #6
	bne	reg2_error_loop
	cmp	r7, #7
	bne	reg2_error_loop
	movs r0, #8
	cmp	r8, r0
	bne	reg2_error_loop
	movs r0, #9
	cmp	r9, r0
	bne	reg2_error_loop
	movs r0, #10
	cmp	r10, r0
	bne	reg2_error_loop
	movs r0, #11
	cmp	r11, r0
	bne	reg2_error_loop
	movs r0, #12
	cmp	r12, r0
	bne	reg2_error_loop

	/* Everything passed, increment the loop counter. */
	push { r1 }
	ldr	r0, =ulRegTest2LoopCounter
	ldr r1, [r0]
	adds r1, r1, #1
	str r1, [r0]
	pop { r1 }

	/* Start again. */
	movs r0, #10
	b reg2_loop

reg2_error_loop
	/* If this line is hit then there was an error in a core register value.
	The loop ensures the loop counter stops incrementing. */
	b reg2_error_loop
	nop

	END
