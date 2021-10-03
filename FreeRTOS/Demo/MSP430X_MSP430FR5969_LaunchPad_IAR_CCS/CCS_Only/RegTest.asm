;
;/*
; * FreeRTOS V202107.00
; * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

; * The definition of the "register test" tasks, as described at the top of
; * main.c

	.include data_model.h

	.if $DEFINED( __LARGE_DATA_MODEL__ )
		.define "cmp.a", cmp_x
		.define "incx.w", inc_x
	.else
		.define "cmp.w", cmp_x
		.define "inc.w", inc_x
	.endif


	.global usRegTest1LoopCounter
	.global usRegTest2LoopCounter
	.global vPortYield
	
	.def vRegTest1Implementation
	.def vRegTest2Implementation

	.text
	
	.align 2
vRegTest1Implementation: .asmfunc

	; Fill each general purpose register with a known value.
	mov_x	#0x4444, r4
	mov_x	#0x5555, r5
	mov_x	#0x6666, r6
	mov_x	#0x7777, r7
	mov_x	#0x8888, r8
	mov_x	#0x9999, r9
	mov_x	#0xaaaa, r10
	mov_x	#0xbbbb, r11
	mov_x	#0xcccc, r12
	mov_x	#0xdddd, r13
	mov_x	#0xeeee, r14
	mov_x	#0xffff, r15
	
prvRegTest1Loop:

	; Test each general purpose register to check that it still contains the
	; expected known value, jumping to vRegTest1Error if any register contains
	; an unexpected value.
	cmp_x	#0x4444, r4
	jne		vRegTest1Error
	cmp_x	#0x5555, r5
	jne		vRegTest1Error
	cmp_x	#0x6666, r6
	jne		vRegTest1Error
	cmp_x	#0x7777, r7
	jne		vRegTest1Error
	cmp_x	#0x8888, r8
	jne		vRegTest1Error
	cmp_x	#0x9999, r9
	jne		vRegTest1Error
	cmp_x	#0xaaaa, r10
	jne		vRegTest1Error
	cmp_x	#0xbbbb, r11
	jne		vRegTest1Error
	cmp_x	#0xcccc, r12
	jne		vRegTest1Error
	cmp_x	#0xdddd, r13
	jne		vRegTest1Error
	cmp_x	#0xeeee, r14
	jne		vRegTest1Error
	cmp_x	#0xffff, r15
	jne		vRegTest1Error
	
	; This task is still running without jumping to vRegTest1Error, so increment
	; the loop counter so the check task knows the task is running error free.
	inc_x	&usRegTest1LoopCounter
	
	; Loop again, performing the same tests.
	jmp		prvRegTest1Loop
	nop
	
vRegTest1Error:
	jmp vRegTest1Error
	nop
	.endasmfunc	
; -----------------------------------------------------------

; See the comments in vRegTest1Implementation.  This task is the same, it just uses
; different values in its registers.
	.align 2
vRegTest2Implementation: .asmfunc

	mov_x	#0x4441, r4
	mov_x	#0x5551, r5
	mov_x	#0x6661, r6
	mov_x	#0x7771, r7
	mov_x	#0x8881, r8
	mov_x	#0x9991, r9
	mov_x	#0xaaa1, r10
	mov_x	#0xbbb1, r11
	mov_x	#0xccc1, r12
	mov_x	#0xddd1, r13
	mov_x	#0xeee1, r14
	mov_x	#0xfff1, r15
	
prvRegTest2Loop:

	cmp_x	#0x4441, r4
	jne		vRegTest2Error
	cmp_x	#0x5551, r5
	jne		vRegTest2Error
	cmp_x	#0x6661, r6
	jne		vRegTest2Error
	cmp_x	#0x7771, r7
	jne		vRegTest2Error
	cmp_x	#0x8881, r8
	jne		vRegTest2Error
	cmp_x	#0x9991, r9
	jne		vRegTest2Error
	cmp_x	#0xaaa1, r10
	jne		vRegTest2Error
	cmp_x	#0xbbb1, r11
	jne		vRegTest2Error
	cmp_x	#0xccc1, r12
	jne		vRegTest2Error
	cmp_x	#0xddd1, r13
	jne		vRegTest2Error
	cmp_x	#0xeee1, r14
	jne		vRegTest2Error
	cmp_x	#0xfff1, r15
	jne		vRegTest2Error
	
	; Also perform a manual yield, just to increase the scope of the test.
	call_x 	#vPortYield
	
	inc_x	&usRegTest2LoopCounter
	jmp		prvRegTest2Loop
	nop

	
vRegTest2Error:
	jmp vRegTest2Error
	nop
	.endasmfunc
; /*-----------------------------------------------------------

     		
	.end
		
