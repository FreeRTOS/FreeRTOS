/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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




