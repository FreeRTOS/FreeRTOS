;/*
; * FreeRTOS Kernel V10.0.0
; * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
; *
; * Permission is hereby granted, free of charge, to any person obtaining a copy of
; * this software and associated documentation files (the "Software"), to deal in
; * the Software without restriction, including without limitation the rights to
; * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
; * the Software, and to permit persons to whom the Software is furnished to do so,
; * subject to the following conditions:
; *
; * The above copyright notice and this permission notice shall be included in all
; * copies or substantial portions of the Software. If you wish to use our Amazon
; * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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

;-------------------------------------------------
;
		.def	vRegTestTask1
		.ref	ulRegTest1Counter

		.if (__TI_VFP_SUPPORT__)
			.ref vPortTaskUsesFPU
		.endif ;__TI_VFP_SUPPORT__

		.text
		.arm

vRegTestTask1:
	.if (__TI_VFP_SUPPORT__)
		; Let the port layer know that this task needs its FPU context saving.
		BL		vPortTaskUsesFPU
	.endif

		; Fill each general purpose register with a known value.
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

	.if (__TI_VFP_SUPPORT__)
		; Fill each FPU register with a known value.
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
	.endif


vRegTestLoop1:

		; Force yeild
		swi		#0

	.if (__TI_VFP_SUPPORT__)
		; Check all the VFP registers still contain the values set above.
		; First save registers that are clobbered by the test.
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

		; Restore the registers that were clobbered by the test.
		pop 	{r0-r1}

		; VFP register test passed.  Jump to the core register test.
		b 		reg1_loopf_pass

reg1_error_loopf:
		; If this line is hit then a VFP register value was found to be
		; incorrect.
		b reg1_error_loopf

reg1_loopf_pass:

	.endif ;__TI_VFP_SUPPORT__

		; Test each general purpose register to check that it still contains the
		; expected known value, jumping to vRegTestError1 if any register contains
		; an unexpected value.
		cmp		r0, #0xFF
		bne		vRegTestError1
		cmp		r1, #0x11
		bne		vRegTestError1
		cmp		r2, #0x22
		bne		vRegTestError1
		cmp		r3, #0x33
		bne		vRegTestError1
		cmp		r4, #0x44
		bne		vRegTestError1
		cmp		r5, #0x55
		bne		vRegTestError1
		cmp		r6, #0x66
		bne		vRegTestError1
		cmp		r7, #0x77
		bne		vRegTestError1
		cmp		r8, #0x88
		bne		vRegTestError1
		cmp		r9, #0x99
		bne		vRegTestError1
		cmp		r10, #0xAA
		bne		vRegTestError1
		cmp		r11, #0xBB
		bne		vRegTestError1
		cmp		r12, #0xCC
		bne		vRegTestError1
		cmp		r14, #0xEE
		bne		vRegTestError1

		; This task is still running without jumping to vRegTestError1, so increment
		; the loop counter so the check task knows the task is running error free.
		stmfd   sp!, { r0-r1 }
		ldr		r0, Count1Const
		ldr		r1, [r0]
		add		r1, r1, #1
		str     r1, [r0]
		ldmfd   sp!, { r0-r1 }

		; Loop again, performing the same tests.
		b		vRegTestLoop1

Count1Const	.word	ulRegTest1Counter

vRegTestError1:
		b       vRegTestError1


;-------------------------------------------------
;
		.def	vRegTestTask2
		.ref	ulRegTest2Counter
		.text
		.arm
;
vRegTestTask2:
	.if (__TI_VFP_SUPPORT__)
		; Let the port layer know that this task needs its FPU context saving.
		BL		vPortTaskUsesFPU
	.endif

		; Fill each general purpose register with a known value.
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

	.if (__TI_VFP_SUPPORT__)

		; Fill each FPU register with a known value.
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
	.endif

vRegTestLoop2:

	.if (__TI_VFP_SUPPORT__)
		; Check all the VFP registers still contain the values set above.
		; First save registers that are clobbered by the test.
		push { r0-r1 }

		vmov r0, r1, d0
		cmp r0, #0xFF000000
		bne reg2_error_loopf
		cmp r1, #0x11000000
		bne reg2_error_loopf
		vmov r0, r1, d1
		cmp r0, #0x22000000
		bne reg2_error_loopf
		cmp r1, #0x33000000
		bne reg2_error_loopf
		vmov r0, r1, d2
		cmp r0, #0x44000000
		bne reg2_error_loopf
		cmp r1, #0x55000000
		bne reg2_error_loopf
		vmov r0, r1, d3
		cmp r0, #0x66000000
		bne reg2_error_loopf
		cmp r1, #0x77000000
		bne reg2_error_loopf
		vmov r0, r1, d4
		cmp r0, #0x88000000
		bne reg2_error_loopf
		cmp r1, #0x99000000
		bne reg2_error_loopf
		vmov r0, r1, d5
		cmp r0, #0xAA000000
		bne reg2_error_loopf
		cmp r1, #0xBB000000
		bne reg2_error_loopf
		vmov r0, r1, d6
		cmp r0, #0xFF000000
		bne reg2_error_loopf
		cmp r1, #0x11000000
		bne reg2_error_loopf
		vmov r0, r1, d7
		cmp r0, #0x22000000
		bne reg2_error_loopf
		cmp r1, #0x33000000
		bne reg2_error_loopf
		vmov r0, r1, d8
		cmp r0, #0x44000000
		bne reg2_error_loopf
		cmp r1, #0x55000000
		bne reg2_error_loopf
		vmov r0, r1, d9
		cmp r0, #0x66000000
		bne reg2_error_loopf
		cmp r1, #0x77000000
		bne reg2_error_loopf
		vmov r0, r1, d10
		cmp r0, #0x88000000
		bne reg2_error_loopf
		cmp r1, #0x99000000
		bne reg2_error_loopf
		vmov r0, r1, d11
		cmp r0, #0xAA000000
		bne reg2_error_loopf
		cmp r1, #0xBB000000
		bne reg2_error_loopf
		vmov r0, r1, d12
		cmp r0, #0xFF000000
		bne reg2_error_loopf
		cmp r1, #0x11000000
		bne reg2_error_loopf
		vmov r0, r1, d13
		cmp r0, #0x22000000
		bne reg2_error_loopf
		cmp r1, #0x33000000
		bne reg2_error_loopf
		vmov r0, r1, d14
		cmp r0, #0x44000000
		bne reg2_error_loopf
		cmp r1, #0x55000000
		bne reg2_error_loopf
		vmov r0, r1, d15
		cmp r0, #0x66000000
		bne reg2_error_loopf
		cmp r1, #0x77000000
		bne reg2_error_loopf

		; Restore the registers that were clobbered by the test.
		pop {r0-r1}

		; VFP register test passed.  Jump to the core register test.
		b reg2_loopf_pass

reg2_error_loopf:
		; If this line is hit then a VFP register value was found to be
		; incorrect.
		b 	reg2_error_loopf

reg2_loopf_pass:

	.endif ;__TI_VFP_SUPPORT__

		; Test each general purpose register to check that it still contains the
		; expected known value, jumping to vRegTestError2 if any register contains
		; an unexpected value.
		cmp		r0, #0xFF000000
		bne		vRegTestError2
		cmp		r1, #0x11000000
		bne		vRegTestError2
		cmp		r2, #0x22000000
		bne		vRegTestError2
		cmp		r3, #0x33000000
		bne		vRegTestError2
		cmp		r4, #0x44000000
		bne		vRegTestError2
		cmp		r5, #0x55000000
		bne		vRegTestError2
		cmp		r6, #0x66000000
		bne		vRegTestError2
		cmp		r7, #0x77000000
		bne		vRegTestError2
		cmp		r8, #0x88000000
		bne		vRegTestError2
		cmp		r9, #0x99000000
		bne		vRegTestError2
		cmp		r10, #0xAA000000
		bne		vRegTestError2
		cmp		r11, #0xBB000000
		bne		vRegTestError2
		cmp		r12, #0xCC000000
		bne		vRegTestError2
		cmp     r14, #0xEE000000
		bne		vRegTestError2

		; This task is still running without jumping to vRegTestError2, so increment
		; the loop counter so the check task knows the task is running error free.
		stmfd   sp!, { r0-r1 }
		ldr		r0, Count2Const
		ldr		r1, [r0]
		add		r1, r1, #1
		str     r1, [r0]
		ldmfd   sp!, { r0-r1 }

		; Loop again, performing the same tests.
		b		vRegTestLoop2

Count2Const	.word	ulRegTest2Counter

vRegTestError2:
		b       vRegTestError2

;-------------------------------------------------



