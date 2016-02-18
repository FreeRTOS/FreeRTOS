/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

	PUBLIC vRegTest1Implementation
	PUBLIC vRegTest2Implementation
	EXTERN ulRegTest1LoopCounter
	EXTERN ulRegTest2LoopCounter

	SECTION intvec:CODE:ROOT(2)
    ARM

	/* This function is explained in the comments at the top of main-full.c. */
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


	END

