/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
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

/* 
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register maintains its expected value for the lifetime of the
 * task.  Each task uses a different set of values.  The reg test tasks execute
 * with a very low priority, so get preempted very frequently.  A register
 * containing an unexpected value is indicative of an error in the context
 * switching mechanism.
 */
 
void vRegTest1Task( void ) __attribute__((naked));
void vRegTest2Task( void ) __attribute__((naked));

void vRegTest1Task( void )
{
	__asm volatile
	(
		".extern ulRegTest1LoopCounter		\n"
		"									\n"
		"	/* Fill the core registers with known values. */ \n"
		"	movs r1, #101					\n"
		"	movs r2, #102					\n"
		"	movs r3, #103					\n"
		"	movs r4, #104					\n"
		"	movs r5, #105					\n"
		"	movs r6, #106					\n"
		"	movs r7, #107					\n"
		"	movs r0, #108					\n"
		"	mov	 r8, r0						\n"
		"	movs r0, #109					\n"
		"	mov  r9, r0						\n"
		"	movs r0, #110					\n"
		"	mov	 r10, r0					\n"
		"	movs r0, #111					\n"
		"	mov	 r11, r0					\n"
		"	movs r0, #112					\n"
		"	mov  r12, r0					\n"
		"	movs r0, #100					\n"
		"									\n"
		"reg1_loop:							\n"
		"									\n"
		"	cmp	r0, #100					\n"
		"	bne	reg1_error_loop				\n"
		"	cmp	r1, #101					\n"
		"	bne	reg1_error_loop				\n"
		"	cmp	r2, #102					\n"
		"	bne	reg1_error_loop				\n"
		"	cmp r3, #103					\n"
		"	bne	reg1_error_loop				\n"
		"	cmp	r4, #104					\n"
		"	bne	reg1_error_loop				\n"
		"	cmp	r5, #105					\n"
		"	bne	reg1_error_loop				\n"
		"	cmp	r6, #106					\n"
		"	bne	reg1_error_loop				\n"
		"	cmp	r7, #107					\n"
		"	bne	reg1_error_loop				\n"
		"	movs r0, #108					\n"
		"	cmp	r8, r0						\n"
		"	bne	reg1_error_loop				\n"
		"	movs r0, #109					\n"
		"	cmp	r9, r0						\n"
		"	bne	reg1_error_loop				\n"
		"	movs r0, #110					\n"
		"	cmp	r10, r0						\n"
		"	bne	reg1_error_loop				\n"
		"	movs r0, #111					\n"
		"	cmp	r11, r0						\n"
		"	bne	reg1_error_loop				\n"
		"	movs r0, #112					\n"
		"	cmp	r12, r0						\n"
		"	bne	reg1_error_loop				\n"
		"									\n"
		"	/* Everything passed, increment the loop counter. */ \n"
		"	push { r1 }						\n"
		"	ldr	r0, =ulRegTest1LoopCounter	\n"
		"	ldr r1, [r0]					\n"
		"	add r1, r1, #1					\n"
		"	str r1, [r0]					\n"
		"									\n"
		"	/* Yield to increase test coverage. */ \n"
		"	movs r0, #0x01					\n"
		"	ldr r1, =0xe000ed04 			\n" /*NVIC_INT_CTRL */
		"	lsl r0, #28 					\n" /* Shift to PendSV bit */
		"	str r0, [r1]					\n"
		"	dsb								\n"
		"	pop { r1 }						\n"
		"									\n"
		"	/* Start again. */				\n"
		"	movs r0, #100					\n"
		"	b reg1_loop						\n"
		"									\n"
		"reg1_error_loop:					\n"
		"	/* If this line is hit then there was an error in a core register value. 	\n"
		"	The loop ensures the loop counter stops incrementing. */					\n"
		"	b reg1_error_loop				\n"
		"	nop								\n"
	);
}
/*-----------------------------------------------------------*/

void vRegTest2Task( void )
{
	__asm volatile
	(
		".extern ulRegTest2LoopCounter		\n"
		"									\n"
		"	/* Fill the core registers with known values. */ \n"
		"	movs r1, #1						\n"
		"	movs r2, #2						\n"
		"	movs r3, #3						\n"
		"	movs r4, #4						\n"
		"	movs r5, #5						\n"
		"	movs r6, #6						\n"
		"	movs r7, #7						\n"
		"	movs r0, #8						\n"
		"	movs r8, r0						\n"
		"	movs r0, #9						\n"
		"	mov  r9, r0						\n"
		"	movs r0, #10					\n"
		"	mov	 r10, r0					\n"
		"	movs r0, #11					\n"
		"	mov	 r11, r0					\n"
		"	movs r0, #12					\n"
		"	mov  r12, r0					\n"
		"	movs r0, #10					\n"
		"									\n"
		"reg2_loop:							\n"
		"									\n"
		"	cmp	r0, #10						\n"
		"	bne	reg2_error_loop				\n"
		"	cmp	r1, #1						\n"
		"	bne	reg2_error_loop				\n"
		"	cmp	r2, #2						\n"
		"	bne	reg2_error_loop				\n"
		"	cmp r3, #3						\n"
		"	bne	reg2_error_loop				\n"
		"	cmp	r4, #4						\n"
		"	bne	reg2_error_loop				\n"
		"	cmp	r5, #5						\n"
		"	bne	reg2_error_loop				\n"
		"	cmp	r6, #6						\n"
		"	bne	reg2_error_loop				\n"
		"	cmp	r7, #7						\n"
		"	bne	reg2_error_loop				\n"
		"	movs r0, #8						\n"
		"	cmp	r8, r0						\n"
		"	bne	reg2_error_loop				\n"
		"	movs r0, #9						\n"
		"	cmp	r9, r0						\n"
		"	bne	reg2_error_loop				\n"
		"	movs r0, #10					\n"
		"	cmp	r10, r0						\n"
		"	bne	reg2_error_loop				\n"
		"	movs r0, #11					\n"
		"	cmp	r11, r0						\n"
		"	bne	reg2_error_loop				\n"
		"	movs r0, #12					\n"
		"	cmp	r12, r0						\n"
		"	bne	reg2_error_loop				\n"
		"									\n"
		"	/* Everything passed, increment the loop counter. */ \n"
		"	push { r1 }						\n"
		"	ldr	r0, =ulRegTest2LoopCounter	\n"
		"	ldr r1, [r0]					\n"
		"	add r1, r1, #1					\n"
		"	str r1, [r0]					\n"
		"	pop { r1 }						\n"
		"									\n"
		"	/* Start again. */				\n"
		"	movs r0, #10					\n"
		"	b reg2_loop						\n"
		"									\n"
		"reg2_error_loop:					\n"
		"	/* If this line is hit then there was an error in a core register value. 	\n"
		"	The loop ensures the loop counter stops incrementing. */					\n"
		"	b reg2_error_loop				\n"
		"	nop								\n"
	);
}
/*-----------------------------------------------------------*/




