;/*
;    FreeRTOS V7.2.0 - Copyright (C) 2012 Real Time Engineers Ltd.
;
;
;    ***************************************************************************
;     *                                                                       *
;     *    FreeRTOS tutorial books are available in pdf and paperback.        *
;     *    Complete, revised, and edited pdf reference manuals are also       *
;     *    available.                                                         *
;     *                                                                       *
;     *    Purchasing FreeRTOS documentation will not only help you, by       *
;     *    ensuring you get running as quickly as possible and with an        *
;     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
;     *    the FreeRTOS project to continue with its mission of providing     *
;     *    professional grade, cross platform, de facto standard solutions    *
;     *    for microcontrollers - completely free of charge!                  *
;     *                                                                       *
;     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
;     *                                                                       *
;     *    Thank you for using FreeRTOS, and thank you for your support!      *
;     *                                                                       *
;    ***************************************************************************
;
;
;    This file is part of the FreeRTOS distribution.
;
;    FreeRTOS is free software; you can redistribute it and/or modify it under
;    the terms of the GNU General Public License (version 2) as published by the
;    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
;    >>>NOTE<<< The modification to the GPL is included to allow you to
;    distribute a combined work that includes FreeRTOS without being obliged to
;    provide the source code for proprietary components outside of the FreeRTOS
;    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
;    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
;    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;    more details. You should have received a copy of the GNU General Public
;    License and the FreeRTOS license exception along with FreeRTOS; if not it
;    can be viewed here: http://www.freertos.org/a00114.html and also obtained
;    by writing to Richard Barry, contact details for whom are available on the
;    FreeRTOS WEB site.
;
;    1 tab == 4 spaces!
;    
;    ***************************************************************************
;     *                                                                       *
;     *    Having a problem?  Start by reading the FAQ "My application does   *
;     *    not run, what could be wrong?                                      *
;     *                                                                       *
;     *    http://www.FreeRTOS.org/FAQHelp.html                               *
;     *                                                                       *
;    ***************************************************************************
;
;    
;    http://www.FreeRTOS.org - Documentation, training, latest information, 
;    license and contact details.
;    
;    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
;    including FreeRTOS+Trace - an indispensable productivity tool.
;
;    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
;    the code with commercial support, indemnification, and middleware, under 
;    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
;    provide a safety engineered and independently SIL3 certified version under 
;    the SafeRTOS brand: http://www.SafeRTOS.com.
;*/

;-------------------------------------------------
;
		.def	vRegTestTask1
		.ref	ulRegTest1Counter
		.text
		.arm

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
	
vRegTestLoop1:

		; Force yeild
		swi		#0

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
	
vRegTestLoop2:

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
	
	
	
