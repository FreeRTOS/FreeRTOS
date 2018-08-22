;/*
; * FreeRTOS Kernel V10.1.0
; * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
; *
; * Permission is hereby granted, free of charge, to any person obtaining a copy of
; * this software and associated documentation files (the "Software"), to deal in
; * the Software without restriction, including without limitation the rights to
; * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
; * the Software, and to permit persons to whom the Software is furnished to do so,
; * subject to the following conditions:
; *
; * The above copyright notice and this permission notice shall be included in all
; * copies or substantial portions of the Software.
; *
; * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
; * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
; * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
; * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
; * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
; *
; * http://www.FreeRTOS.org
; * http://aws.amazon.com/freertos
; *
; * 1 tab == 4 spaces!
; */


	.thumb

	.ref ulRegTest1LoopCounter
	.ref ulRegTest2LoopCounter

	.def vRegTest1Implementation
	.def vRegTest2Implementation

ulRegTest1LoopCounterConst:	.word	ulRegTest1LoopCounter
ulRegTest2LoopCounterConst:	.word	ulRegTest2LoopCounter
ulNVIC_INT_CTRL:			.word 	0xe000ed04
;/*-----------------------------------------------------------*/
	.align 4
vRegTest1Implementation: .asmfunc

	;/* Fill the core registers with known values. */
	mov r0, #100
	mov r1, #101
	mov r2, #102
	mov r3, #103
	mov	r4, #104
	mov	r5, #105
	mov	r6, #106
	mov r7, #107
	mov	r8, #108
	mov	r9, #109
	mov	r10, #110
	mov	r11, #111
	mov r12, #112

reg1_loop:

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
	cmp	r8, #108
	bne	reg1_error_loop
	cmp	r9, #109
	bne	reg1_error_loop
	cmp	r10, #110
	bne	reg1_error_loop
	cmp	r11, #111
	bne	reg1_error_loop
	cmp	r12, #112
	bne	reg1_error_loop

	;/* Everything passed, increment the loop counter. */
	push { r0-r1 }
	ldr	r0, ulRegTest1LoopCounterConst
	ldr r1, [r0]
	adds r1, r1, #1
	str r1, [r0]
	pop { r0-r1 }

	;/* Start again. */
	b reg1_loop

reg1_error_loop:
	;/* If this line is hit then there was an error in a core register value.
	;The loop ensures the loop counter stops incrementing. */
	b reg1_error_loop
	.endasmfunc

;/*-----------------------------------------------------------*/

	.align 4
vRegTest2Implementation: .asmfunc

	;/* Set all the core registers to known values. */
	mov r0, #-1
	mov r1, #1
	mov r2, #2
	mov r3, #3
	mov	r4, #4
	mov	r5, #5
	mov	r6, #6
	mov r7, #7
	mov	r8, #8
	mov	r9, #9
	mov	r10, #10
	mov	r11, #11
	mov r12, #12


reg2_loop:

	cmp	r0, #-1
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
	cmp	r8, #8
	bne	reg2_error_loop
	cmp	r9, #9
	bne	reg2_error_loop
	cmp	r10, #10
	bne	reg2_error_loop
	cmp	r11, #11
	bne	reg2_error_loop
	cmp	r12, #12
	bne	reg2_error_loop

	;/* Increment the loop counter to indicate this test is still functioning
	;correctly. */
	push { r0-r1 }
	ldr	r0, ulRegTest2LoopCounterConst
	ldr r1, [r0]
	adds r1, r1, #1
	str r1, [r0]

	;/* Yield to increase test coverage. */
	movs r0, #0x01
	ldr r1, ulNVIC_INT_CTRL
	lsl r0, r0, #28 ;/* Shift to PendSV bit */
	str r0, [r1]
	dsb

	pop { r0-r1 }

	;/* Start again. */
	b reg2_loop

reg2_error_loop:
	;/* If this line is hit then there was an error in a core register value.
	;This loop ensures the loop counter variable stops incrementing. */
	b reg2_error_loop

;/*-----------------------------------------------------------*/

	.end
