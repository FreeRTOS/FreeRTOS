;/*
;    FreeRTOS V8.2.0 - Copyright (C) 2014 Real Time Engineers Ltd.
;
;    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
;    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.
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
;
;    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
;    distribute a combined work that includes FreeRTOS without being obliged to
;    provide the source code for proprietary components outside of the FreeRTOS
;    kernel.
;
;    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
;    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
;    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
;    details. You should have received a copy of the GNU General Public License
;    and the FreeRTOS license exception along with FreeRTOS; if not itcan be
;    viewed here: http://www.freertos.org/a00114.html and also obtained by
;    writing to Real Time Engineers Ltd., contact details for whom are available
;    on the FreeRTOS WEB site.
;
;    1 tab == 4 spaces!
;
;    ***************************************************************************
;     *                                                                       *
;     *    Having a problem?  Start by reading the FAQ "My application does   *
;     *    not run, what could be wrong?"                                     *
;     *                                                                       *
;     *    http://www.FreeRTOS.org/FAQHelp.html                               *
;     *                                                                       *
;    ***************************************************************************
;
;
;    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
;    license and Real Time Engineers Ltd. contact details.
;
;    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
;    including FreeRTOS+Trace - an indispensable productivity tool, and our new
;    fully thread aware and reentrant UDP/IP stack.
;
;    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
;    Integrity Systems, who sell the code with commercial support,
;    indemnification and middleware, under the OpenRTOS brand.
;
;    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
;    engineered and independently SIL3 certified version for use in safety and
;    mission critical applications that require provable dependability.
;*/

	EXPORT vRegTest1Implementation
	EXPORT vRegTest2Implementation

	; This file is built with IAR and ARM compilers.  When the ARM compiler
	; is used the compiler options must define __IASMARM__ as 0 using the
	; --predefine "__IASMARM__ SETA 0" command line option.  When compiling
	; with IAR __IASMARM__ is automatically set to 1 so no additional assembler
	; options are required.
	SECTION .text:CODE:ROOT(2)
	ARM

	; This function is explained in the comments at the top of main-full.c.
vRegTest1Implementation

	PRESERVE8
	IMPORT ulRegTest1LoopCounter

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

	; Loop, checking each itteration that each register still contains the
	; expected value.
reg1_loop
	; Yield to increase test coverage
	svc 0

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

reg1_error_loopf
	; If this line is hit then a VFP register value was found to be
	; incorrect.
	b reg1_error_loopf

reg1_loopf_pass

	; Test each general purpose register to check that it still contains the
	; expected known value, jumping to reg1_error_loop if any register contains
	; an unexpected value.
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

	; Everything passed, increment the loop counter.
	push { r0-r1 }
	ldr	r0, =ulRegTest1LoopCounter
	ldr r1, [r0]
	adds r1, r1, #1
	str r1, [r0]
	pop { r0-r1 }

	; Start again.
	b reg1_loop

reg1_error_loop
	; If this line is hit then there was an error in a core register value.
	; The loop ensures the loop counter stops incrementing.
	b reg1_error_loop
	nop

;/*-----------------------------------------------------------*/

vRegTest2Implementation

	PRESERVE8
	IMPORT ulRegTest2LoopCounter

	; Put a known value in each register.
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

	; Likewise the floating point registers
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

	; Loop, checking each itteration that each register still contains the
	; expected value.
reg2_loop
	; Check all the VFP registers still contain the values set above.
	; First save registers that are clobbered by the test.
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

	; Restore the registers that were clobbered by the test.
	pop 	{r0-r1}

	; VFP register test passed.  Jump to the core register test.
	b 		reg2_loopf_pass

reg2_error_loopf
	; If this line is hit then a VFP register value was found to be
	; incorrect.
	b 		reg2_error_loopf

reg2_loopf_pass

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

	; Everything passed, increment the loop counter.
	push 	{ r0-r1 }
	ldr		r0, =ulRegTest2LoopCounter
	ldr 	r1, [r0]
	adds 	r1, r1, #1
	str 	r1, [r0]
	pop 	{ r0-r1 }

	; Start again.
	b 		reg2_loop

reg2_error_loop
	; If this line is hit then there was an error in a core register value.
	; The loop ensures the loop counter stops incrementing.
	b 		reg2_error_loop
	nop


	END
