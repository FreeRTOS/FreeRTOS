/*
    FreeRTOS V6.0.4 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

#include "FreeRTOS.h"
#include "task.h"

static void vRegTest1( void *pvParameters );// __attribute__((naked));
static void vRegTest2( void *pvParameters );// __attribute__((naked));

static volatile unsigned long ulRegTest1Counter = 0UL, ulRegTest2Counter = 0UL;

void vStartRegTestTasks( void )
{
	xTaskCreate( vRegTest1, ( signed char * ) "RTest1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegTest2, ( signed char * ) "RTest1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
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














