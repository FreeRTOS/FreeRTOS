/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/******************************************************************************
 * NOTE 1:  This project provides two demo applications.  A simple blinky style
 * project, and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting in main.c is used to select
 * between the two.  See the notes on using mainCREATE_SIMPLE_BLINKY_DEMO_ONLY
 * in main.c.  This file implements the comprehensive test and demo version.
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * full demo.  Generic functions, such FreeRTOS hook functions, and functions
 * required to configure the hardware, are defined in main.c.
 ******************************************************************************
 *
 * main_full() creates all the demo application tasks and a software timer, then
 * starts the scheduler.  The web documentation provides more details of the
 * standard demo application tasks, which provide no particular functionality,
 * but do provide a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Reg test" tasks - These fill both the core and floating point registers with
 * known values, then check that each register maintains its expected value for
 * the lifetime of the task.  Each task uses a different set of values.  The reg
 * test tasks execute with a very low priority, so get preempted very
 * frequently.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism.
 *
 * "Check" timer - The check software timer period is initially set to three
 * seconds.  The callback function associated with the check software timer
 * checks that all the standard demo tasks, and the register check tasks, are
 * not only still executing, but are executing without reporting any errors.  If
 * the check software timer discovers that a task has either stalled, or
 * reported an error, then it changes its own execution period from the initial
 * three seconds, to just 200ms.  The check software timer callback function
 * also toggles the single LED each time it is called.  This provides a visual
 * indication of the system status:  If the LED toggles every three seconds,
 * then no issues have been discovered.  If the LED toggles every 200ms, then
 * an issue has been discovered with at least one task.
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"

/* Standard demo application includes. */
#include "flop.h"
#include "semtest.h"
#include "dynamic.h"
#include "blocktim.h"
#include "countsem.h"
#include "GenQTest.h"
#include "recmutex.h"

/* Priorities for the demo application tasks. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1UL )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainCREATOR_TASK_PRIORITY			( tskIDLE_PRIORITY + 3UL )
#define mainFLOP_TASK_PRIORITY				( tskIDLE_PRIORITY )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_PERIOD_MS )

/*-----------------------------------------------------------*/

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * Register check tasks, and the tasks used to write over and check the contents
 * of the FPU registers, as described at the top of this file.  The nature of
 * these files necessitates that they are written in an assembly file.
 */
static void prvRegTest1Task( void *pvParameters ) __attribute__((naked));
static void prvRegTest2Task( void *pvParameters ) __attribute__((naked));

/*-----------------------------------------------------------*/

/* The following two variables are used to communicate the status of the
register check tasks to the check software timer.  If the variables keep
incrementing, then the register check tasks has not discovered any errors.  If
a variable stops incrementing, then an error has been found. */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

/*-----------------------------------------------------------*/

void main_full( void )
{
TimerHandle_t xCheckTimer = NULL;

	/* Start all the other standard demo/test tasks.  The have not particular
	functionality, but do demonstrate how to use the FreeRTOS API and test the
	kernel port. */
	vStartDynamicPriorityTasks();
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartRecursiveMutexTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartMathTasks( mainFLOP_TASK_PRIORITY );

	/* Create the register check tasks, as described at the top of this
	file */
	xTaskCreate( prvRegTest1Task, "Reg1", configMINIMAL_STACK_SIZE, ( void * ) NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTest2Task, "Reg2", configMINIMAL_STACK_SIZE, ( void * ) NULL, tskIDLE_PRIORITY, NULL );

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( "CheckTimer",					/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
								pdTRUE,							/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,					/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback			/* The callback function that inspects the status of all the other tasks. */
							  );

	if( xCheckTimer != NULL )
	{
		xTimerStart( xCheckTimer, mainDONT_BLOCK );
	}

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
unsigned long ulErrorFound = pdFALSE;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none have detected an error. */

	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if ( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if ( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	/* Check that the register test 1 task is still running. */
	if( ulLastRegTest1Value == ulRegTest1LoopCounter )
	{
		ulErrorFound = pdTRUE;
	}
	ulLastRegTest1Value = ulRegTest1LoopCounter;

	/* Check that the register test 2 task is still running. */
	if( ulLastRegTest2Value == ulRegTest2LoopCounter )
	{
		ulErrorFound = pdTRUE;
	}
	ulLastRegTest2Value = ulRegTest2LoopCounter;

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every mainCHECK_TIMER_PERIOD_MS milliseconds then
	everything is ok.  A faster toggle indicates an error. */
	configTOGGLE_LED();

	/* Have any errors been latch in ulErrorFound?  If so, shorten the
	period of the check timer to mainERROR_CHECK_TIMER_PERIOD_MS milliseconds.
	This will result in an increase in the rate at which mainCHECK_LED
	toggles. */
	if( ulErrorFound != pdFALSE )
	{
		if( lChangedTimerPeriodAlready == pdFALSE )
		{
			lChangedTimerPeriodAlready = pdTRUE;

			/* This call to xTimerChangePeriod() uses a zero block time.
			Functions called from inside of a timer callback function must
			*never* attempt	to block. */
			xTimerChangePeriod( xTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
		}
	}
}
/*-----------------------------------------------------------*/

/* This is a naked function. */
static void prvRegTest1Task( void *pvParameters )
{
	__asm volatile
	(
		"	/* Fill the core registers with known values. */		\n"
		"	mov r0, #100											\n"
		"	mov r1, #101											\n"
		"	mov r2, #102											\n"
		"	mov r3, #103											\n"
		"	mov	r4, #104											\n"
		"	mov	r5, #105											\n"
		"	mov	r6, #106											\n"
		"	mov r7, #107											\n"
		"	mov	r8, #108											\n"
		"	mov	r9, #109											\n"
		"	mov	r10, #110											\n"
		"	mov	r11, #111											\n"
		"	mov r12, #112											\n"
		"															\n"
		"	/* Fill the VFP registers with known values. */			\n"
		"	vmov d0, r0, r1											\n"
		"	vmov d1, r2, r3											\n"
		"	vmov d2, r4, r5											\n"
		"	vmov d3, r6, r7											\n"
		"	vmov d4, r8, r9											\n"
		"	vmov d5, r10, r11										\n"
		"	vmov d6, r0, r1											\n"
		"	vmov d7, r2, r3											\n"
		"	vmov d8, r4, r5											\n"
		"	vmov d9, r6, r7											\n"
		"	vmov d10, r8, r9										\n"
		"	vmov d11, r10, r11										\n"
		"	vmov d12, r0, r1										\n"
		"	vmov d13, r2, r3										\n"
		"	vmov d14, r4, r5										\n"
		"	vmov d15, r6, r7										\n"
		"															\n"
		"reg1_loop:													\n"
		"	/* Check all the VFP registers still contain the values set above.\n"
		"	First save registers that are clobbered by the test. */	\n"
		"	push { r0-r1 }											\n"
		"															\n"
		"	vmov r0, r1, d0											\n"
		"	cmp r0, #100											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #101											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d1											\n"
		"	cmp r0, #102											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #103											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d2											\n"
		"	cmp r0, #104											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #105											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d3											\n"
		"	cmp r0, #106											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #107											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d4											\n"
		"	cmp r0, #108											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #109											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d5											\n"
		"	cmp r0, #110											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #111											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d6											\n"
		"	cmp r0, #100											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #101											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d7											\n"
		"	cmp r0, #102											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #103											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d8											\n"
		"	cmp r0, #104											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #105											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d9											\n"
		"	cmp r0, #106											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #107											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d10										\n"
		"	cmp r0, #108											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #109											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d11										\n"
		"	cmp r0, #110											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #111											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d12										\n"
		"	cmp r0, #100											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #101											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d13										\n"
		"	cmp r0, #102											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #103											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d14										\n"
		"	cmp r0, #104											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #105											\n"
		"	bne reg1_error_loopf									\n"
		"	vmov r0, r1, d15										\n"
		"	cmp r0, #106											\n"
		"	bne reg1_error_loopf									\n"
		"	cmp r1, #107											\n"
		"	bne reg1_error_loopf									\n"
		"															\n"
		"	/* Restore the registers that were clobbered by the test. */\n"
		"	pop {r0-r1}												\n"
		"															\n"
		"	/* VFP register test passed.  Jump to the core register test. */\n"
		"	b reg1_loopf_pass										\n"
		"															\n"
		"reg1_error_loopf:											\n"
		"	/* If this line is hit then a VFP register value was found to be\n"
		"	incorrect. */											\n"
		"	b reg1_error_loopf										\n"
		"															\n"
		"reg1_loopf_pass:											\n"
		"															\n"
		"	cmp	r0, #100											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r1, #101											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r2, #102											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp r3, #103											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r4, #104											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r5, #105											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r6, #106											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r7, #107											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r8, #108											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r9, #109											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r10, #110											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r11, #111											\n"
		"	bne	reg1_error_loop										\n"
		"	cmp	r12, #112											\n"
		"	bne	reg1_error_loop										\n"
		"															\n"
		"	/* Everything passed, increment the loop counter. */	\n"
		"	push { r0-r1 }											\n"
		"	ldr	r0, =ulRegTest1LoopCounter							\n"
		"	ldr r1, [r0]											\n"
		"	adds r1, r1, #1											\n"
		"	str r1, [r0]											\n"
		"	pop { r0-r1 }											\n"
		"															\n"
		"	/* Start again. */										\n"
		"	b reg1_loop												\n"
		"															\n"
		"reg1_error_loop:											\n"
		"	/* If this line is hit then there was an error in a core register value.\n"
		"	The loop ensures the loop counter stops incrementing. */\n"
		"	b reg1_error_loop										\n"
		"	nop														"
	);
}
/*-----------------------------------------------------------*/

/* This is a naked function. */
static void prvRegTest2Task( void *pvParameters )
{
	__asm volatile
	(
		"	/* Set all the core registers to known values. */		\n"
		"	mov r0, #-1												\n"
		"	mov r1, #1												\n"
		"	mov r2, #2												\n"
		"	mov r3, #3												\n"
		"	mov	r4, #4												\n"
		"	mov	r5, #5												\n"
		"	mov	r6, #6												\n"
		"	mov r7, #7												\n"
		"	mov	r8, #8												\n"
		"	mov	r9, #9												\n"
		"	mov	r10, #10											\n"
		"	mov	r11, #11											\n"
		"	mov r12, #12											\n"
		"															\n"
		"	/* Set all the VFP to known values. */					\n"
		"	vmov d0, r0, r1											\n"
		"	vmov d1, r2, r3											\n"
		"	vmov d2, r4, r5											\n"
		"	vmov d3, r6, r7											\n"
		"	vmov d4, r8, r9											\n"
		"	vmov d5, r10, r11										\n"
		"	vmov d6, r0, r1											\n"
		"	vmov d7, r2, r3											\n"
		"	vmov d8, r4, r5											\n"
		"	vmov d9, r6, r7											\n"
		"	vmov d10, r8, r9										\n"
		"	vmov d11, r10, r11										\n"
		"	vmov d12, r0, r1										\n"
		"	vmov d13, r2, r3										\n"
		"	vmov d14, r4, r5										\n"
		"	vmov d15, r6, r7										\n"
		"															\n"
		"reg2_loop:													\n"
		"															\n"
		"	/* Check all the VFP registers still contain the values set above.\n"
		"	First save registers that are clobbered by the test. */	\n"
		"	push { r0-r1 }											\n"
		"															\n"
		"	vmov r0, r1, d0											\n"
		"	cmp r0, #-1												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #1												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d1											\n"
		"	cmp r0, #2												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #3												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d2											\n"
		"	cmp r0, #4												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #5												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d3											\n"
		"	cmp r0, #6												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #7												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d4											\n"
		"	cmp r0, #8												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #9												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d5											\n"
		"	cmp r0, #10												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #11												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d6											\n"
		"	cmp r0, #-1												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #1												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d7											\n"
		"	cmp r0, #2												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #3												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d8											\n"
		"	cmp r0, #4												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #5												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d9											\n"
		"	cmp r0, #6												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #7												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d10										\n"
		"	cmp r0, #8												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #9												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d11										\n"
		"	cmp r0, #10												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #11												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d12										\n"
		"	cmp r0, #-1												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #1												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d13										\n"
		"	cmp r0, #2												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #3												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d14										\n"
		"	cmp r0, #4												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #5												\n"
		"	bne reg2_error_loopf									\n"
		"	vmov r0, r1, d15										\n"
		"	cmp r0, #6												\n"
		"	bne reg2_error_loopf									\n"
		"	cmp r1, #7												\n"
		"	bne reg2_error_loopf									\n"
		"															\n"
		"	/* Restore the registers that were clobbered by the test. */\n"
		"	pop {r0-r1}												\n"
		"															\n"
		"	/* VFP register test passed.  Jump to the core register test. */\n"
		"	b reg2_loopf_pass										\n"
		"															\n"
		"reg2_error_loopf:											\n"
		"	/* If this line is hit then a VFP register value was found to be\n"
		"	incorrect. */											\n"
		"	b reg2_error_loopf										\n"
		"															\n"
		"reg2_loopf_pass:											\n"
		"															\n"
		"	cmp	r0, #-1												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r1, #1												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r2, #2												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp r3, #3												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r4, #4												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r5, #5												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r6, #6												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r7, #7												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r8, #8												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r9, #9												\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r10, #10											\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r11, #11											\n"
		"	bne	reg2_error_loop										\n"
		"	cmp	r12, #12											\n"
		"	bne	reg2_error_loop										\n"
		"															\n"
		"	/* Increment the loop counter to indicate this test is still functioning\n"
		"	correctly. */											\n"
		"	push { r0-r1 }											\n"
		"	ldr	r0, =ulRegTest2LoopCounter							\n"
		"	ldr r1, [r0]											\n"
		"	adds r1, r1, #1											\n"
		"	str r1, [r0]											\n"
		"															\n"
		"	/* Yield to increase test coverage. */ 					\n"
		"	movs r0, #0x01											\n"
		"	ldr r1, =0xe000ed04 									\n" /*NVIC_INT_CTRL */
		"	lsl r0, #28 											\n" /* Shift to PendSV bit */
		"	str r0, [r1]											\n"
		"	dsb														\n"
		"	pop { r0-r1 }											\n"
		"															\n"
		"	/* Start again. */										\n"
		"	b reg2_loop												\n"
		"															\n"
		"reg2_error_loop:											\n"
		"	/* If this line is hit then there was an error in a core register value.\n"
		"	This loop ensures the loop counter variable stops incrementing. */\n"
		"	b reg2_error_loop										\n"
		"	nop														\n"
	);
}
