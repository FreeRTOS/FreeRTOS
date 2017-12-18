/*
 * FreeRTOS Kernel V10.0.1
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

#include "FreeRTOS.h"
#include "task.h"

/*
 * Two test tasks that fill the CPU registers with known values before
 * continuously looping round checking that each register still contains its
 * expected value.  Both tasks use a separate set of values, with an incorrect
 * value being found at any time being indicative of an error in the context
 * switch mechanism.  One of the tasks uses a yield instruction to increase the
 * test coverage.  The nature of these tasks necessitates that they are written
 * in assembly code.
 */
static void vRegTest1( void *pvParameters );
static void vRegTest2( void *pvParameters );

/* Counters used to ensure the tasks are still running. */
static volatile unsigned long ulRegTest1Counter = 0UL, ulRegTest2Counter = 0UL;

/*-----------------------------------------------------------*/

void vStartRegTestTasks( void )
{
	xTaskCreate( vRegTest1, "RTest1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegTest2, "RTest1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

static void vRegTest1( void *pvParameters )
{
	__asm volatile
	(
		"	mov		r2, #0x02							\n" /* Fill the registers with known values, r0 is always 0 and r1 is the stack pointer. */
		"	mov		r3, #0x03							\n"
		"	mov		r4, #0x04							\n"
		"	mov		r5, #0x05							\n"
		"	mov		r6, #0x06							\n"
		"	mov		r7, #0x07							\n"
		"	mov		r8, #0x08							\n"
		"	mov		r9, #0x09							\n"
		"	mov		r10, #0x0a							\n"
		"	mov		r11, #0x0b							\n"
		"	mov		r12, #0x0c							\n"
		"	mov		r13, #0x0d							\n"
		"	mov		r14, #0x0e							\n"
		"	mov		r15, #0x0f							\n"
		"												\n"
		"reg_check_loop_1:								\n"
		"	trap	#31									\n"
		"	cmp		r2, #0x02							\n" /* Check that each register still contains the expected value, jump to an infinite loop if an error is found. */
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r3, #0x03							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r4, #0x04							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r5, #0x05							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r6, #0x06							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r7, #0x07							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r8, #0x08							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r9, #0x09							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r10, #0x0a							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r11, #0x0b							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r12, #0x0c							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r13, #0x0d							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r14, #0x0e							\n"
		"	bne.s	reg_check_error_1					\n"
		"	cmp		r15, #0x0f							\n"
		"	bne.s	reg_check_error_1					\n"
		"												\n"
		"	ld		r2, [r0]+short(ulRegTest1Counter)	\n" /* Increment the loop counter to show that this task is still running error free. */
		"	add		r2, #1								\n"
		"	st		r2, [r0]+short(ulRegTest1Counter)	\n"
		"	mov		r2, #0x02							\n"
		"												\n"
		"	bra.s	reg_check_loop_1					\n" /* Do it all again. */
		"												\n"
		"reg_check_error_1:								\n"
			"bra.s		.								\n"
	);
}
/*-----------------------------------------------------------*/

static void vRegTest2( void *pvParameters )
{
	__asm volatile
	(
		"	mov		r2, #0x12							\n" /* Fill the registers with known values, r0 is always 0 and r1 is the stack pointer. */
		"	mov		r3, #0x13							\n"
		"	mov		r4, #0x14							\n"
		"	mov		r5, #0x15							\n"
		"	mov		r6, #0x16							\n"
		"	mov		r7, #0x17							\n"
		"	mov		r8, #0x18							\n"
		"	mov		r9, #0x19							\n"
		"	mov		r10, #0x1a							\n"
		"	mov		r11, #0x1b							\n"
		"	mov		r12, #0x1c							\n"
		"	mov		r13, #0x1d							\n"
		"	mov		r14, #0x1e							\n"
		"	mov		r15, #0x1f							\n"
		"												\n"
		"reg_check_loop_2:								\n"
		"	cmp		r2, #0x12							\n" /* Check that each register still contains the expected value, jump to an infinite loop if an error is found. */
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r3, #0x13							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r4, #0x14							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r5, #0x15							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r6, #0x16							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r7, #0x17							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r8, #0x18							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r9, #0x19							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r10, #0x1a							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r11, #0x1b							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r12, #0x1c							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r13, #0x1d							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r14, #0x1e							\n"
		"	bne.s	reg_check_error_2					\n"
		"	cmp		r15, #0x1f							\n"
		"	bne.s	reg_check_error_2					\n"
		"												\n"
		"	ld		r2, [r0]+short(ulRegTest2Counter)	\n" /* Increment the loop counter to show that this task is still running error free. */
		"	add		r2, #1								\n"
		"	st		r2, [r0]+short(ulRegTest2Counter)	\n"
		"	mov		r2, #0x12							\n"
		"												\n"
		"	bra.s	reg_check_loop_2					\n" /* Do it all again. */
		"												\n"
		"reg_check_error_2:								\n"
			"bra.s		.								\n"
	);
}
/*-----------------------------------------------------------*/

portBASE_TYPE xAreRegTestTasksStillRunning( void )
{
static unsigned long ulLastCounter1 = 0UL, ulLastCounter2 = 0UL;
long lReturn;

	/* Check that both loop counters are still incrementing, indicating that
	both reg test tasks are still running error free. */
	if( ulLastCounter1 == ulRegTest1Counter )
	{
		lReturn = pdFAIL;
	}
	else if( ulLastCounter2 == ulRegTest2Counter )
	{
		lReturn = pdFAIL;
	}
	else
	{
		lReturn = pdPASS;
	}

	ulLastCounter1 = ulRegTest1Counter;
	ulLastCounter2 = ulRegTest2Counter;

	return lReturn;
}
