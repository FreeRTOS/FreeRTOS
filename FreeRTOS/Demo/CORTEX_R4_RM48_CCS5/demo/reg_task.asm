;-------------------------------------------------
;
		.def	vRegTestTask1
		.ref	usRegTest1Counter
		.text
		.arm
;
vRegTestTask1:
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
	
regTestLoop1:
		; Force yeild
		swi		#0

		; Test each general purpose register to check that it still contains the
		; expected known value, jumping to vRegTest1Error if any register contains
		; an unexpected value.
		cmp		r0, #0xFF
		bne		regTestError1		
		cmp		r1, #0x11
		bne		regTestError1		
		cmp		r2, #0x22
		bne		regTestError1		
		cmp		r3, #0x33
		bne		regTestError1		
		cmp		r4, #0x44
		bne		regTestError1		
		cmp		r5, #0x55
		bne		regTestError1		
		cmp		r6, #0x66
		bne		regTestError1		
		cmp		r7, #0x77
		bne		regTestError1		
		cmp		r8, #0x88
		bne		regTestError1		
		cmp		r9, #0x99
		bne		regTestError1		
		cmp		r10, #0xAA
		bne		regTestError1		
		cmp		r11, #0xBB
		bne		regTestError1		
		cmp		r12, #0xCC
		bne		regTestError1		
		cmp		r14, #0xEE
		bne		regTestError1		
	
		; This task is still running without jumping to vRegTest1Error, so increment
		; the loop counter so the check task knows the task is running error free.
		stmfd   sp!, { r0-r1 }
		ldr		r0, count1
		ldr		r1, [r0]
		add		r1, r1, #1
		str     r1, [r0]
		ldmfd   sp!, { r0-r1 }
		
		; Loop again, performing the same tests.
		b		regTestLoop1

count1	.word	usRegTest1Counter
	
regTestError1:
		b       regTestError1


;-------------------------------------------------
;
		.def	vRegTestTask2
		.ref	usRegTest2Counter
		.text
		.arm
;
vRegTestTask2:
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
	
regTestLoop2:
		; Force yeild
		swi		#0

		; Test each general purpose register to check that it still contains the
		; expected known value, jumping to vRegTest1Error if any register contains
		; an unexpected value.
		cmp		r0, #0xFF000000
		bne		regTestError2		
		cmp		r1, #0x11000000
		bne		regTestError2	
		cmp		r2, #0x22000000
		bne		regTestError2	
		cmp		r3, #0x33000000
		bne		regTestError2	
		cmp		r4, #0x44000000
		bne		regTestError2	
		cmp		r5, #0x55000000
		bne		regTestError2	
		cmp		r6, #0x66000000
		bne		regTestError2	
		cmp		r7, #0x77000000
		bne		regTestError2	
		cmp		r8, #0x88000000
		bne		regTestError2	
		cmp		r9, #0x99000000
		bne		regTestError2	
		cmp		r10, #0xAA000000
		bne		regTestError2	
		cmp		r11, #0xBB000000
		bne		regTestError2	
		cmp		r12, #0xCC000000
		bne		regTestError2	
		cmp     r14, #0xEE000000
		bne		regTestError2	
	
		; This task is still running without jumping to vRegTest1Error, so increment
		; the loop counter so the check task knows the task is running error free.
		stmfd   sp!, { r0-r1 }
		ldr		r0, count2
		ldr		r1, [r0]
		add		r1, r1, #1
		str     r1, [r0]
		ldmfd   sp!, { r0-r1 }
		
		; Loop again, performing the same tests.
		b		regTestLoop2

count2	.word	usRegTest2Counter
	
regTestError2:
		b       regTestError2

;-------------------------------------------------
	
	
	
