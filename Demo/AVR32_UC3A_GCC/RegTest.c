/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

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
	xTaskCreate( vRegTest1, ( signed char * ) "RTest1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
//	xTaskCreate( vRegTest2, ( signed char * ) "RTest2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

static void vRegTest1( void *pvParameters )
{
	__asm__ __volatile__
	(
		/* Fill the registers with known values. */
		"	mov		r0, 0							\n"
		"	mov		r1, 1							\n"
		"	mov		r2, 2							\n"
		"	mov		r3, 3							\n"
		"	mov		r4, 4							\n"
		"	mov		r5, 5							\n"
		"	mov		r6, 6							\n" /* r7 is the frame pointer. */
		"	mov		r10, 10							\n"
		"	mov		r11, 11							\n"
		"	mov		r12, 12							\n" /* r13 is the stack pointer, and r14 the link register. */
		"											\n"
		"reg_check_loop_1:							\n"
		"											\n"
		"	mov		r8, 8							\n" /* Reset the registers that are likely to be clobbered when incrementing the check variable. */
		"	mov		r9, 9							\n"
		"											\n"
		"	cp.w	r0, 0							\n"
		"	brne	reg_check_error_1				\n"
		"	cp.w	r1, 1							\n"
		"	brne	reg_check_error_1				\n"
		"	cp.w	r2, 2							\n" /* Check that each register still contains the expected value, jump to an infinite loop if an error is found. */
		"	brne	reg_check_error_1				\n"
		"	cp.w	r3, 3							\n"
		"	brne	reg_check_error_1				\n"
		"	cp.w	r4, 4							\n"
		"	brne	reg_check_error_1				\n"
		"	cp.w	r5, 5							\n"
		"	brne	reg_check_error_1				\n"
		"	cp.w	r6, 6							\n"
		"	brne	reg_check_error_1				\n"
		"	cp.w	r8, 8							\n"
		"	brne	reg_check_error_1				\n"
		"	cp.w	r9, 9							\n"
		"	brne	reg_check_error_1				\n"
		"	cp.w	r10, 10							\n"
		"	brne	reg_check_error_1				\n"
		"	cp.w	r11, 11							\n"
		"	brne	reg_check_error_1				\n"
		"	cp.w	r12, 12							\n"
		"	brne	reg_check_error_1				\n"
		"											\n"
		"	ld.w 	r8, ulRegTest1CounterConst		\n"
		"	ld.w  	r8, r8[ 0x00 ]					\n"
		"	sub   	r9, r8, -1						\n"
		"	ld.w 	r8, ulRegTest1CounterConst		\n"
		"	st.w	r8[ 0x00 ], r9					\n"
		"											\n"
		"	bral	reg_check_loop_1				\n"
		"											\n"
		"reg_check_error_1:							\n"
		"	bral	.								\n" /* If an error is discovered, just loop here so the check variable stops incrementing. */
		"											\n"
		"ulRegTest1CounterConst: .word ulRegTest1Counter	\n"
	);
}

/*-----------------------------------------------------------*/

#if 0
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
		"	cp.w		r2, #0x12							\n" /* Check that each register still contains the expected value, jump to an infinite loop if an error is found. */
		"	brne		reg_check_error_2					\n"
		"	cp.w		r3, #0x13							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r4, #0x14							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r5, #0x15							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r6, #0x16							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r7, #0x17							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r8, #0x18							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r9, #0x19							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r10, #0x1a							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r11, #0x1b							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r12, #0x1c							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r13, #0x1d							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r14, #0x1e							\n"
		"	brne		reg_check_error_2					\n"
		"	cp.w		r15, #0x1f							\n"
		"	brne		reg_check_error_2					\n"
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
#endif

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
//	else if( ulLastCounter2 == ulRegTest2Counter )
//	{
//		lReturn = pdFAIL;
//	}
	else
	{
		lReturn = pdPASS;
	}

	ulLastCounter1 = ulRegTest1Counter;
	ulLastCounter2 = ulRegTest2Counter;

	return lReturn;
}














