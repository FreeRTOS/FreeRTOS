/*
 * FreeRTOS Kernel V10.3.0
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


/*
 * This file demonstrates the use of FreeRTOS-MPU.  It creates tasks in both
 * User mode and Privileged mode, and using both the xTaskCreate() and
 * xTaskCreateRestricted() API functions.  The purpose of each created task is
 * documented in the comments above the task function prototype (in this file),
 * with the task behaviour demonstrated and documented within the task function
 * itself.
 *
 * In addition a queue is used to demonstrate passing data between
 * protected/restricted tasks as well as passing data between an interrupt and
 * a protected/restricted task.  A software timer is also used.
 *
 * The system status is printed to ITM channel 0, where it can be viewed in the
 * Keil serial/debug window (a compatible SW debug interface is required).
 */

/* Microchip includes. */
#include "common.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"
#include "timers.h"
#include "event_groups.h"

/*-----------------------------------------------------------*/

/* Misc constants. */
#define mainDONT_BLOCK					( 0 )

/* GCC specifics. */
#define mainALIGN_TO( x )				__attribute__((aligned(x)))

/* Hardware register addresses. */
#define mainVTOR 						( * ( volatile uint32_t * ) 0xE000ED08 )

/* The period of the timer must be less than the rate at which
configPRINT_SYSTEM_STATUS messages are sent to the check task - otherwise the
check task will think the timer has stopped. */
#define mainTIMER_PERIOD				pdMS_TO_TICKS( 200 )

/* The name of the task that is deleted by the Idle task is used in a couple of
places, so is #defined. */
#define mainTASK_TO_DELETE_NAME			"DeleteMe"

/*-----------------------------------------------------------*/
/* Prototypes for functions that implement tasks. -----------*/
/*-----------------------------------------------------------*/

/*
 * NOTE:  The filling and checking of the registers in the following two tasks
 *        is only actually performed when the GCC compiler is used.  Use of the
 *        queue to communicate with the check task is done with all compilers.
 *
 * Prototype for the first two register test tasks, which execute in User mode.
 * Amongst other things, these fill the CPU registers (other than the FPU
 * registers) with known values before checking that the registers still contain
 * the expected values.  Each of the two tasks use different values so an error
 * in the context switch mechanism can be caught.  Both tasks execute at the
 * idle priority so will get preempted regularly.  Each task repeatedly sends a
 * message on a queue to a 'check' task so the check task knows the register
 * check task is still executing and has not detected any errors.  If an error
 * is detected within the task the task is simply deleted so it no longer sends
 * messages.
 *
 * For demonstration and test purposes, both tasks obtain access to the queue
 * handle in different ways; vRegTest1Implementation() is created in Privileged
 * mode and copies the queue handle to its local stack before setting itself to
 * User mode, and vRegTest2Implementation() receives the task handle using its
 * parameter.
 */
extern void vRegTest1Implementation( void *pvParameters );
extern void vRegTest2Implementation( void *pvParameters );

/*
 * The second two register test tasks are similar to the first two, but do test
 * the floating point registers, execute in Privileged mode, and signal their
 * execution status to the 'check' task by incrementing a loop counter on each
 * iteration instead of sending a message on a queue.  The loop counters use a
 * memory region to which the User mode 'check' task has read access.
 *
 * The functions ending 'Implementation' are called by the register check tasks.
 */
static void prvRegTest3Task( void *pvParameters );
extern void vRegTest3Implementation( void );
static void prvRegTest4Task( void *pvParameters );
extern void vRegTest4Implementation( void );

/*
 * Prototype for the check task.  The check task demonstrates various features
 * of the MPU before entering a loop where it waits for messages to arrive on a
 * queue.
 *
 * Two types of messages can be processes:
 *
 * 1) "I'm Alive" messages sent from the first two register test tasks and a
 *    software timer callback, as described above.
 *
 * 2) "Print Status commands" sent periodically by the tick hook function (and
 *    therefore from within an interrupt) which commands the check task to write
 *    either pass or fail to the terminal, depending on the status of the reg
 *    test tasks.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Prototype for a task created in User mode using the original vTaskCreate()
 * API function.  The task demonstrates the characteristics of such a task,
 * before simply deleting itself.
 */
static void prvOldStyleUserModeTask( void *pvParameters );

/*
 * Prototype for a task created in Privileged mode using the original
 * vTaskCreate() API function.  The task demonstrates the characteristics of
 * such a task, before simply deleting itself.
 */
static void prvOldStylePrivilegedModeTask( void *pvParameters );

/*
 * A task that exercises the API of various RTOS objects before being deleted by
 * the Idle task.  This is done for MPU API code coverage test purposes.
 */
static void prvTaskToDelete( void *pvParameters );

/*
 * Functions called by prvTaskToDelete() to exercise the MPU API.
 */
static void prvExerciseEventGroupAPI( void );
static void prvExerciseSemaphoreAPI( void );
static void prvExerciseTaskNotificationAPI( void );

/*
 * Just configures any clocks and IO necessary.
 */
static void prvSetupHardware( void );

/*
 * Simply deletes the calling task.  The function is provided only because it
 * is simpler to call from asm code than the normal vTaskDelete() API function.
 * It has the noinline attribute because it is called from asm code.
 */
void vMainDeleteMe( void ) __attribute__((noinline));

/*
 * Used by the first two reg test tasks and a software timer callback function
 * to send messages to the check task.  The message just lets the check task
 * know that the tasks and timer are still functioning correctly.  If a reg test
 * task detects an error it will delete itself, and in so doing prevent itself
 * from sending any more 'I'm Alive' messages to the check task.
 */
void vMainSendImAlive( QueueHandle_t xHandle, uint32_t ulTaskNumber );

/*
 * The check task is created with access to three memory regions (plus its
 * stack).  Each memory region is configured with different parameters and
 * prvTestMemoryRegions() demonstrates what can and cannot be accessed for each
 * region.  prvTestMemoryRegions() also demonstrates a task that was created
 * as a privileged task settings its own privilege level down to that of a user
 * task.
 */
static void prvTestMemoryRegions( void );

/*
 * Callback function used with the timer that uses the queue to send messages
 * to the check task.
 */
static void prvTimerCallback( TimerHandle_t xExpiredTimer );

/*
 * Simple routine to print a string to ITM for viewing in the Keil serial debug
 * viewer.
 */
static void prvITMPrintString( const char *pcString );

/*-----------------------------------------------------------*/

/* The handle of the queue used to communicate between tasks and between tasks
and interrupts.  Note that this is a global scope variable that falls outside of
any MPU region.  As such other techniques have to be used to allow the tasks
to gain access to the queue.  See the comments in the tasks themselves for
further information. */
QueueHandle_t xGlobalScopeCheckQueue = NULL;

/* Holds the handle of a task that is deleted in the idle task hook - this is
done for code coverage test purposes only. */
static TaskHandle_t xTaskToDelete = NULL;

/* The timer that periodically sends data to the check task on the queue. */
static TimerHandle_t xTimer = NULL;

#if defined ( __GNUC__ )
	extern uint32_t __FLASH_segment_start__[];
	extern uint32_t __FLASH_segment_end__[];
	extern uint32_t __SRAM_segment_start__[];
	extern uint32_t __SRAM_segment_end__[];
	extern uint32_t __privileged_functions_start__[];
	extern uint32_t __privileged_functions_end__[];
	extern uint32_t __privileged_data_start__[];
	extern uint32_t __privileged_data_end__[];
	extern uint32_t __privileged_functions_actual_end__[];
	extern uint32_t __privileged_data_actual_end__[];
#else
	const uint32_t * __FLASH_segment_start__ = ( uint32_t * ) 0xE0000UL;
	const uint32_t * __FLASH_segment_end__ = ( uint32_t * ) 0x100000UL;
	const uint32_t * __SRAM_segment_start__ = ( uint32_t * ) 0x100000UL;
	const uint32_t * __SRAM_segment_end__ = ( uint32_t * ) 0x120000;
	const uint32_t * __privileged_functions_start__ = ( uint32_t * ) 0xE0000UL;
	const uint32_t * __privileged_functions_end__ = ( uint32_t * ) 0xE4000UL;
	const uint32_t * __privileged_data_start__ = ( uint32_t * ) 0x100000UL;
	const uint32_t * __privileged_data_end__ = ( uint32_t * ) 0x100200UL;
#endif
/*-----------------------------------------------------------*/
/* Data used by the 'check' task. ---------------------------*/
/*-----------------------------------------------------------*/

/* Define the constants used to allocate the check task stack.  Note that the
stack size is defined in words, not bytes. */
#define mainCHECK_TASK_STACK_SIZE_WORDS	128
#define mainCHECK_TASK_STACK_ALIGNMENT ( mainCHECK_TASK_STACK_SIZE_WORDS * sizeof( portSTACK_TYPE ) )

/* Declare the stack that will be used by the check task.  The kernel will
 automatically create an MPU region for the stack.  The stack alignment must
 match its size, so if 128 words are reserved for the stack then it must be
 aligned to ( 128 * 4 ) bytes. */
static portSTACK_TYPE xCheckTaskStack[ mainCHECK_TASK_STACK_SIZE_WORDS ] mainALIGN_TO( mainCHECK_TASK_STACK_ALIGNMENT );

/* Declare three arrays - an MPU region will be created for each array
using the TaskParameters_t structure below.  THIS IS JUST TO DEMONSTRATE THE
MPU FUNCTIONALITY, the data is not used by the check tasks primary function
of monitoring the reg test tasks and printing out status information.

Note that the arrays allocate slightly more RAM than is actually assigned to
the MPU region.  This is to permit writes off the end of the array to be
detected even when the arrays are placed in adjacent memory locations (with no
gaps between them).  The align size must be a power of two. */
#define mainREAD_WRITE_ARRAY_SIZE 130
#define mainREAD_WRITE_ALIGN_SIZE 128
char cReadWriteArray[ mainREAD_WRITE_ARRAY_SIZE ] mainALIGN_TO( mainREAD_WRITE_ALIGN_SIZE );

#define mainREAD_ONLY_ARRAY_SIZE 260
#define mainREAD_ONLY_ALIGN_SIZE 256
char cReadOnlyArray[ mainREAD_ONLY_ARRAY_SIZE ] mainALIGN_TO( mainREAD_ONLY_ALIGN_SIZE );

#define mainPRIVILEGED_ONLY_ACCESS_ARRAY_SIZE 130
#define mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE 128
char cPrivilegedOnlyAccessArray[ mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE ] mainALIGN_TO( mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE );

/* The following two variables are used to communicate the status of the second
two register check tasks (tasks 3 and 4) to the check task.  If the variables
keep incrementing, then the register check tasks have not discovered any errors.
If a variable stops incrementing, then an error has been found.  The variables
overlay the array that the check task has access to so they can be read by the
check task without causing a memory fault.  The check task has the highest
priority so will have finished with the array before the register test tasks
start to access it. */
volatile uint32_t *pulRegTest3LoopCounter = ( uint32_t * ) &( cReadWriteArray[ 0 ] ), *pulRegTest4LoopCounter = ( uint32_t * ) &( cReadWriteArray[ 4 ] );

/* Fill in a TaskParameters_t structure to define the check task - this is the
structure passed to the xTaskCreateRestricted() function. */
static const TaskParameters_t xCheckTaskParameters =
{
	prvCheckTask,								/* pvTaskCode - the function that implements the task. */
	"Check",									/* pcName */
	mainCHECK_TASK_STACK_SIZE_WORDS,			/* usStackDepth - defined in words, not bytes. */
	( void * ) 0x12121212,						/* pvParameters - this value is just to test that the parameter is being passed into the task correctly. */
	( tskIDLE_PRIORITY + 1 ) | portPRIVILEGE_BIT,/* uxPriority - this is the highest priority task in the system.  The task is created in privileged mode to demonstrate accessing the privileged only data. */
	xCheckTaskStack,							/* puxStackBuffer - the array to use as the task stack, as declared above. */

	/* xRegions - In this case the xRegions array is used to create MPU regions
	for all three of the arrays declared directly above.  Each MPU region is
	created with different parameters.  Again, THIS IS JUST TO DEMONSTRATE THE
	MPU FUNCTIONALITY, the data is not used by the check tasks primary function
	of monitoring the reg test tasks and printing out status information.*/
	{
		/* Base address					Length									Parameters */
		{ cReadWriteArray,				mainREAD_WRITE_ALIGN_SIZE,				portMPU_REGION_READ_WRITE },
		{ cReadOnlyArray,				mainREAD_ONLY_ALIGN_SIZE,				portMPU_REGION_READ_ONLY },
		{ cPrivilegedOnlyAccessArray,	mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE,	portMPU_REGION_PRIVILEGED_READ_WRITE }
	}
};



/*-----------------------------------------------------------*/
/* Data used by the 'reg test' tasks. -----------------------*/
/*-----------------------------------------------------------*/

/* Define the constants used to allocate the reg test task stacks.  Note that
that stack size is defined in words, not bytes. */
#define mainREG_TEST_STACK_SIZE_WORDS	128
#define mainREG_TEST_STACK_ALIGNMENT	( mainREG_TEST_STACK_SIZE_WORDS * sizeof( portSTACK_TYPE ) )

/* Declare the stacks that will be used by the reg test tasks.  The kernel will
automatically create an MPU region for the stack.  The stack alignment must
match its size, so if 128 words are reserved for the stack then it must be
aligned to ( 128 * 4 ) bytes. */
static portSTACK_TYPE xRegTest1Stack[ mainREG_TEST_STACK_SIZE_WORDS ] mainALIGN_TO( mainREG_TEST_STACK_ALIGNMENT );
static portSTACK_TYPE xRegTest2Stack[ mainREG_TEST_STACK_SIZE_WORDS ] mainALIGN_TO( mainREG_TEST_STACK_ALIGNMENT );

/* Fill in a TaskParameters_t structure per reg test task to define the tasks. */
static const TaskParameters_t xRegTest1Parameters =
{
	vRegTest1Implementation,							/* pvTaskCode - the function that implements the task. */
	"RegTest1",									/* pcName			*/
	mainREG_TEST_STACK_SIZE_WORDS,				/* usStackDepth		*/
	( void * ) configREG_TEST_TASK_1_PARAMETER,	/* pvParameters - this value is just to test that the parameter is being passed into the task correctly. */
	tskIDLE_PRIORITY | portPRIVILEGE_BIT,		/* uxPriority - note that this task is created with privileges to demonstrate one method of passing a queue handle into the task. */
	xRegTest1Stack,								/* puxStackBuffer - the array to use as the task stack, as declared above. */
	{											/* xRegions - this task does not use any non-stack data hence all members are zero. */
		/* Base address		Length		Parameters */
		{ 0x00,				0x00,			0x00 },
		{ 0x00,				0x00,			0x00 },
		{ 0x00,				0x00,			0x00 }
	}
};
/*-----------------------------------------------------------*/

static TaskParameters_t xRegTest2Parameters =
{
	vRegTest2Implementation,				/* pvTaskCode - the function that implements the task. */
	"RegTest2",						/* pcName			*/
	mainREG_TEST_STACK_SIZE_WORDS,	/* usStackDepth		*/
	( void * ) NULL,				/* pvParameters	- this task uses the parameter to pass in a queue handle, but the queue is not created yet. */
	tskIDLE_PRIORITY,				/* uxPriority		*/
	xRegTest2Stack,					/* puxStackBuffer - the array to use as the task stack, as declared above. */
	{								/* xRegions - this task does not use any non-stack data hence all members are zero. */
		/* Base address		Length		Parameters */
		{ 0x00,				0x00,			0x00 },
		{ 0x00,				0x00,			0x00 },
		{ 0x00,				0x00,			0x00 }
	}
};

/*-----------------------------------------------------------*/

/*-----------------------------------------------------------*/
/* Configures the task that is deleted. ---------------------*/
/*-----------------------------------------------------------*/

/* Define the constants used to allocate the stack of the task that is
deleted.  Note that that stack size is defined in words, not bytes. */
#define mainDELETE_TASK_STACK_SIZE_WORDS	128
#define mainTASK_TO_DELETE_STACK_ALIGNMENT	( mainDELETE_TASK_STACK_SIZE_WORDS * sizeof( portSTACK_TYPE ) )

/* Declare the stack that will be used by the task that gets deleted.  The
kernel will automatically create an MPU region for the stack.  The stack
alignment must match its size, so if 128 words are reserved for the stack
then it must be aligned to ( 128 * 4 ) bytes. */
static portSTACK_TYPE xDeleteTaskStack[ mainDELETE_TASK_STACK_SIZE_WORDS ] mainALIGN_TO( mainTASK_TO_DELETE_STACK_ALIGNMENT );

static TaskParameters_t xTaskToDeleteParameters =
{
	prvTaskToDelete,					/* pvTaskCode - the function that implements the task. */
	mainTASK_TO_DELETE_NAME,			/* pcName */
	mainDELETE_TASK_STACK_SIZE_WORDS,	/* usStackDepth */
	( void * ) NULL,					/* pvParameters - this task uses the parameter to pass in a queue handle, but the queue is not created yet. */
	tskIDLE_PRIORITY + 1,				/* uxPriority */
	xDeleteTaskStack,					/* puxStackBuffer - the array to use as the task stack, as declared above. */
	{									/* xRegions - this task does not use any non-stack data hence all members are zero. */
		/* Base address		Length		Parameters */
		{ 0x00,				0x00,			0x00 },
		{ 0x00,				0x00,			0x00 },
		{ 0x00,				0x00,			0x00 }
	}
};

/*-----------------------------------------------------------*/

int main( void )
{
	prvSetupHardware();

	prvITMPrintString( "Starting\r\n" );

	/* Create the queue used to pass "I'm alive" messages to the check task. */
	xGlobalScopeCheckQueue = xQueueCreate( 1, sizeof( uint32_t ) );

	/* One check task uses the task parameter to receive the queue handle.
	This allows the file scope variable to be accessed from within the task.
	The pvParameters member of xRegTest2Parameters can only be set after the
	queue has been created so is set here. */
	xRegTest2Parameters.pvParameters = xGlobalScopeCheckQueue;

	/* Create three test tasks.  Handles to the created tasks are not required,
	hence the second parameter is NULL. */
	xTaskCreateRestricted( &xRegTest1Parameters, NULL );
    xTaskCreateRestricted( &xRegTest2Parameters, NULL );
	xTaskCreateRestricted( &xCheckTaskParameters, NULL );

	/* Create a task that does nothing but ensure some of the MPU API functions
	can be called correctly, then get deleted.  This is done for code coverage
	test purposes only.  The task's handle is saved in xTaskToDelete so it can
	get deleted in the idle task hook. */
	xTaskCreateRestricted( &xTaskToDeleteParameters, &xTaskToDelete );

	/* Create the tasks that are created using the original xTaskCreate() API
	function. */
	xTaskCreate(	prvOldStyleUserModeTask,	/* The function that implements the task. */
					"Task1",					/* Text name for the task. */
					100,						/* Stack depth in words. */
					NULL,						/* Task parameters. */
					3,							/* Priority and mode (user in this case). */
					NULL						/* Handle. */
				);

	xTaskCreate(	prvOldStylePrivilegedModeTask,	/* The function that implements the task. */
					"Task2",						/* Text name for the task. */
					100,							/* Stack depth in words. */
					NULL,							/* Task parameters. */
					( 3 | portPRIVILEGE_BIT ),		/* Priority and mode. */
					NULL							/* Handle. */
				);

	/* Create the third and fourth register check tasks, as described at the top
	of this file. */
	xTaskCreate( prvRegTest3Task, "Reg3", configMINIMAL_STACK_SIZE, configREG_TEST_TASK_3_PARAMETER, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTest4Task, "Reg4", configMINIMAL_STACK_SIZE, configREG_TEST_TASK_4_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* Create and start the software timer. */
	xTimer = xTimerCreate( "Timer", 			/* Test name for the timer. */
							mainTIMER_PERIOD, 	/* Period of the timer. */
							pdTRUE,				/* The timer will auto-reload itself. */
							( void * ) 0,		/* The timer's ID is used to count the number of times it expires - initialise this to 0. */
							prvTimerCallback );	/* The function called when the timer expires. */
	configASSERT( xTimer );
	xTimerStart( xTimer, mainDONT_BLOCK );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* Will only get here if there was insufficient memory to create the idle
	task. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
/* This task is created in privileged mode so can access the file scope
queue variable.  Take a stack copy of this before the task is set into user
mode.  Once that task is in user mode the file scope queue variable will no
longer be accessible but the stack copy will. */
QueueHandle_t xQueue = xGlobalScopeCheckQueue;
int32_t lMessage;
uint32_t ulStillAliveCounts[ 3 ] = { 0 };
const char *pcStatusMessage = "PASS\r\n";
uint32_t ulLastRegTest3CountValue = 0, ulLastRegTest4Value = 0;

/* The register test tasks that also test the floating point registers increment
a counter on each iteration of their loop.  The counters are inside the array
that this task has access to. */
volatile uint32_t *pulOverlaidCounter3 = ( uint32_t * ) &( cReadWriteArray[ 0 ] ), *pulOverlaidCounter4 = ( uint32_t * ) &( cReadWriteArray[ 4 ] );

	/* Just to remove compiler warning. */
	( void ) pvParameters;

	/* Demonstrate how the various memory regions can and can't be accessed.
	The task privilege level is set down to user mode within this function. */
	prvTestMemoryRegions();

	/* Clear overlaid reg test counters before entering the loop below. */
	*pulOverlaidCounter3 = 0UL;
	*pulOverlaidCounter4 = 0UL;

	/* This loop performs the main function of the task, which is blocking
	on a message queue then processing each message as it arrives. */
	for( ;; )
	{
		/* Wait for the next message to arrive. */
		xQueueReceive( xQueue, &lMessage, portMAX_DELAY );

		switch( lMessage )
		{
			case configREG_TEST_1_STILL_EXECUTING	:
			case configREG_TEST_2_STILL_EXECUTING	:
			case configTIMER_STILL_EXECUTING		:
					/* Message from the first or second register check task, or
					the timer callback function.  Increment the count of the
					number of times the message source has sent the message as
					the message source must still be executed. */
					( ulStillAliveCounts[ lMessage ] )++;
					break;

			case configPRINT_SYSTEM_STATUS		:
					/* Message from tick hook, time to print out the system
					status.  If messages have stopped arriving from either of
					the first two reg test task or the timer callback then the
					status must be set to fail. */
					if( ( ulStillAliveCounts[ 0 ] == 0 ) || ( ulStillAliveCounts[ 1 ] == 0 ) || ( ulStillAliveCounts[ 2 ] == 0 ) )
					{
						/* One or both of the test tasks are no longer sending
						'still alive' messages. */
						pcStatusMessage = "FAIL\r\n";
					}
					else
					{
						/* Reset the count of 'still alive' messages. */
						memset( ( void * ) ulStillAliveCounts, 0x00, sizeof( ulStillAliveCounts ) );
					}

					/* Check that the register test 3 task is still incrementing
					its counter, and therefore still running. */
					if( ulLastRegTest3CountValue == *pulOverlaidCounter3 )
					{
						pcStatusMessage = "FAIL\r\n";
					}
					ulLastRegTest3CountValue = *pulOverlaidCounter3;

					/* Check that the register test 4 task is still incrementing
					its counter, and therefore still running. */
					if( ulLastRegTest4Value == *pulOverlaidCounter4 )
					{
						pcStatusMessage = "FAIL\r\n";
					}
					ulLastRegTest4Value = *pulOverlaidCounter4;

					/**** print pcStatusMessage here. ****/
					prvITMPrintString( pcStatusMessage );
					break;

		default :
					/* Something unexpected happened.  Delete this task so the
					error is apparent (no output will be displayed). */
					vMainDeleteMe();
					break;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvTestMemoryRegions( void )
{
int32_t x;
char cTemp;

	/* The check task (from which this function is called) is created in the
	Privileged mode.  The privileged array can be both read from and written
	to while this task is privileged. */
	cPrivilegedOnlyAccessArray[ 0 ] = 'a';
	if( cPrivilegedOnlyAccessArray[ 0 ] != 'a' )
	{
		/* Something unexpected happened.  Delete this task so the error is
		apparent (no output will be displayed). */
		vMainDeleteMe();
	}

	/* Writing off the end of the RAM allocated to this task will *NOT* cause a
	protection fault because the task is still executing in a privileged mode.
	Uncomment the following to test. */
	/*cPrivilegedOnlyAccessArray[ mainPRIVILEGED_ONLY_ACCESS_ALIGN_SIZE ] = 'a';*/

	/* Now set the task into user mode. */
	portSWITCH_TO_USER_MODE();

	/* Accessing the privileged only array will now cause a fault.  Uncomment
	the following line to test. */
	/*cPrivilegedOnlyAccessArray[ 0 ] = 'a';*/

	/* The read/write array can still be successfully read and written. */
	for( x = 0; x < mainREAD_WRITE_ALIGN_SIZE; x++ )
	{
		cReadWriteArray[ x ] = 'a';
		if( cReadWriteArray[ x ] != 'a' )
		{
			/* Something unexpected happened.  Delete this task so the error is
			apparent (no output will be displayed). */
			vMainDeleteMe();
		}
	}

	/* But attempting to read or write off the end of the RAM allocated to this
	task will cause a fault.  Uncomment either of the following two lines to
	test. */
	/* cReadWriteArray[ 0 ] = cReadWriteArray[ -1 ]; */
	/* cReadWriteArray[ mainREAD_WRITE_ALIGN_SIZE ] = 0x00; */

	/* The read only array can be successfully read... */
	for( x = 0; x < mainREAD_ONLY_ALIGN_SIZE; x++ )
	{
		cTemp = cReadOnlyArray[ x ];
	}

	/* ...but cannot be written.  Uncomment the following line to test. */
	/* cReadOnlyArray[ 0 ] = 'a'; */

	/* Writing to the first and last locations in the stack array should not
	cause a protection fault.  Note that doing this will cause the kernel to
	detect a stack overflow if configCHECK_FOR_STACK_OVERFLOW is greater than
	1, hence the test is commented out by default. */
	/* xCheckTaskStack[ 0 ] = 0;
	xCheckTaskStack[ mainCHECK_TASK_STACK_SIZE_WORDS - 1 ] = 0; */

	/* Writing off either end of the stack array should cause a protection
	fault, uncomment either of the following two lines to test. */
	/* xCheckTaskStack[ -1 ] = 0; */
	/* xCheckTaskStack[ mainCHECK_TASK_STACK_SIZE_WORDS ] = 0; */

	( void ) cTemp;
}
/*-----------------------------------------------------------*/

static void prvExerciseEventGroupAPI( void )
{
EventGroupHandle_t xEventGroup;
EventBits_t xBits;
const EventBits_t xBitsToWaitFor = ( EventBits_t ) 0xff, xBitToClear = ( EventBits_t ) 0x01;

	/* Exercise some event group functions. */
	xEventGroup = xEventGroupCreate();
	configASSERT( xEventGroup );

	/* No bits should be set. */
	xBits = xEventGroupWaitBits( xEventGroup, xBitsToWaitFor, pdTRUE, pdFALSE, mainDONT_BLOCK );
	configASSERT( xBits == ( EventBits_t ) 0 );

	/* Set bits and read back to ensure the bits were set. */
	xEventGroupSetBits( xEventGroup, xBitsToWaitFor );
	xBits = xEventGroupGetBits( xEventGroup );
	configASSERT( xBits == xBitsToWaitFor );

	/* Clear a bit and read back again using a different API function. */
	xEventGroupClearBits( xEventGroup, xBitToClear );
	xBits = xEventGroupSync( xEventGroup, 0x00, xBitsToWaitFor, mainDONT_BLOCK );
	configASSERT( xBits == ( xBitsToWaitFor & ~xBitToClear ) );

	/* Finished with the event group. */
	vEventGroupDelete( xEventGroup );
}
/*-----------------------------------------------------------*/

static void prvExerciseSemaphoreAPI( void )
{
SemaphoreHandle_t xSemaphore;
const UBaseType_t uxMaxCount = 5, uxInitialCount = 0;

	/* Most of the semaphore API is common to the queue API and is already being
	used.  This function uses a few semaphore functions that are unique to the
	RTOS objects, rather than generic and used by queues also.

	First create and use a counting semaphore. */
	xSemaphore = xSemaphoreCreateCounting( uxMaxCount, uxInitialCount );
	configASSERT( xSemaphore );

	/* Give the semaphore a couple of times and ensure the count is returned
	correctly. */
	xSemaphoreGive( xSemaphore );
	xSemaphoreGive( xSemaphore );
	configASSERT( uxSemaphoreGetCount( xSemaphore ) == 2 );
	vSemaphoreDelete( xSemaphore );

	/* Create a recursive mutex, and ensure the mutex holder and count are
	returned returned correctly. */
	xSemaphore = xSemaphoreCreateRecursiveMutex();
	configASSERT( uxSemaphoreGetCount( xSemaphore ) == 1 );
	configASSERT( xSemaphore );
	xSemaphoreTakeRecursive( xSemaphore, mainDONT_BLOCK );
	xSemaphoreTakeRecursive( xSemaphore, mainDONT_BLOCK );
	configASSERT( xSemaphoreGetMutexHolder( xSemaphore ) == xTaskGetCurrentTaskHandle() );
	configASSERT( xSemaphoreGetMutexHolder( xSemaphore ) == xTaskGetHandle( mainTASK_TO_DELETE_NAME ) );
	xSemaphoreGiveRecursive( xSemaphore );
	configASSERT( uxSemaphoreGetCount( xSemaphore ) == 0 );
	xSemaphoreGiveRecursive( xSemaphore );
	configASSERT( uxSemaphoreGetCount( xSemaphore ) == 1 );
	configASSERT( xSemaphoreGetMutexHolder( xSemaphore ) == NULL );
	vSemaphoreDelete( xSemaphore );

	/* Create a normal mutex, and sure the mutex holder and count are returned
	returned correctly. */
	xSemaphore = xSemaphoreCreateMutex();
	configASSERT( xSemaphore );
	xSemaphoreTake( xSemaphore, mainDONT_BLOCK );
	xSemaphoreTake( xSemaphore, mainDONT_BLOCK );
	configASSERT( uxSemaphoreGetCount( xSemaphore ) == 0 ); /* Not recursive so can only be 1. */
	configASSERT( xSemaphoreGetMutexHolder( xSemaphore ) == xTaskGetCurrentTaskHandle() );
	xSemaphoreGive( xSemaphore );
	configASSERT( uxSemaphoreGetCount( xSemaphore ) == 1 );
	configASSERT( xSemaphoreGetMutexHolder( xSemaphore ) == NULL );
	vSemaphoreDelete( xSemaphore );
}
/*-----------------------------------------------------------*/

static void prvExerciseTaskNotificationAPI( void )
{
uint32_t ulNotificationValue;
BaseType_t xReturned;

	/* The task should not yet have a notification pending. */
	xReturned = xTaskNotifyWait( 0, 0, &ulNotificationValue, mainDONT_BLOCK );
	configASSERT( xReturned == pdFAIL );
	configASSERT( ulNotificationValue == 0UL );

	/* Exercise the 'give' and 'take' versions of the notification API. */
	xTaskNotifyGive( xTaskGetCurrentTaskHandle() );
	xTaskNotifyGive( xTaskGetCurrentTaskHandle() );
	ulNotificationValue = ulTaskNotifyTake( pdTRUE, mainDONT_BLOCK );
	configASSERT( ulNotificationValue == 2 );

	/* Exercise the 'notify' and 'clear' API. */
	ulNotificationValue = 20;
	xTaskNotify( xTaskGetCurrentTaskHandle(), ulNotificationValue, eSetValueWithOverwrite );
	ulNotificationValue = 0;
	xReturned = xTaskNotifyWait( 0, 0, &ulNotificationValue, mainDONT_BLOCK );
	configASSERT( xReturned == pdPASS );
	configASSERT( ulNotificationValue == 20 );
	xTaskNotify( xTaskGetCurrentTaskHandle(), ulNotificationValue, eSetValueWithOverwrite );
	xReturned = xTaskNotifyStateClear( NULL );
	configASSERT( xReturned == pdTRUE ); /* First time a notification was pending. */
	xReturned = xTaskNotifyStateClear( NULL );
	configASSERT( xReturned == pdFALSE ); /* Second time the notification was already clear. */
}
/*-----------------------------------------------------------*/

static void prvTaskToDelete( void *pvParameters )
{
	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* Check the enter and exit critical macros are working correctly.  If the
	SVC priority is below configMAX_SYSCALL_INTERRUPT_PRIORITY then this will
	fault. */
	taskENTER_CRITICAL();
	taskEXIT_CRITICAL();

	/* Exercise the API of various RTOS objects. */
	prvExerciseEventGroupAPI();
	prvExerciseSemaphoreAPI();
	prvExerciseTaskNotificationAPI();

	/* For code coverage test purposes it is deleted by the Idle task. */
	configASSERT( uxTaskGetStackHighWaterMark( NULL ) > 0 );
	vTaskSuspend( NULL );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile const uint32_t *pul;
volatile uint32_t ulReadData;

	/* The idle task, and therefore this function, run in Supervisor mode and
	can therefore access all memory.  Try reading from corners of flash and
	RAM to ensure a memory fault does not occur.

	Start with the edges of the privileged data area. */
	pul = __privileged_data_start__;
	ulReadData = *pul;
	pul = __privileged_data_end__ - 1;
	ulReadData = *pul;

	/* Next the standard SRAM area. */
	pul = __SRAM_segment_end__ - 1;
	ulReadData = *pul;

	/* And the standard Flash area - the start of which is marked for
	privileged access only. */
	pul = __FLASH_segment_start__;
	ulReadData = *pul;
	pul = __FLASH_segment_end__ - 1;
	ulReadData = *pul;

	/* Reading off the end of Flash or SRAM space should cause a fault.
	Uncomment one of the following two pairs of lines to test. */

	/* pul = __FLASH_segment_end__ + 4;
	ulReadData = *pul; */

	/* pul = __SRAM_segment_end__ + 1;
	ulReadData = *pul; */

	/* One task is created purely so it can be deleted - done for code coverage
	test purposes. */
	if( xTaskToDelete != NULL )
	{
		vTaskDelete( xTaskToDelete );
		xTaskToDelete = NULL;
	}

	( void ) ulReadData;
}
/*-----------------------------------------------------------*/

static void prvOldStyleUserModeTask( void *pvParameters )
{
const volatile uint32_t *pulStandardPeripheralRegister = ( volatile uint32_t * ) 0x40000000;
volatile const uint32_t *pul;
volatile uint32_t ulReadData;

/* The following lines are commented out to prevent the unused variable
compiler warnings when the tests that use the variable are also commented out. */
/* extern uint32_t __privileged_functions_start__[]; */
/* const volatile uint32_t *pulSystemPeripheralRegister = ( volatile uint32_t * ) 0xe000e014; */

	( void ) pvParameters;

	/* This task is created in User mode using the original xTaskCreate() API
	function.  It should have access to all Flash and RAM except that marked
	as Privileged access only.  Reading from the start and end of the non-
	privileged RAM should not cause a problem (the privileged RAM is the first
	block at the bottom of the RAM memory). */
	pul = __privileged_data_end__ + 1;
	ulReadData = *pul;
	pul = __SRAM_segment_end__ - 1;
	ulReadData = *pul;

	/* Likewise reading from the start and end of the non-privileged Flash
	should not be a problem (the privileged Flash is the first block at the
	bottom of the Flash memory). */
	pul = __privileged_functions_end__ + 1;
	ulReadData = *pul;
	pul = __FLASH_segment_end__ - 1;
	ulReadData = *pul;

	/* Standard peripherals are accessible. */
	ulReadData = *pulStandardPeripheralRegister;

	/* System peripherals are not accessible.  Uncomment the following line
	to test.  Also uncomment the declaration of pulSystemPeripheralRegister
	at the top of this function.
	ulReadData = *pulSystemPeripheralRegister; */

	/* Reading from anywhere inside the privileged Flash or RAM should cause a
	fault.  This can be tested by uncommenting any of the following pairs of
	lines.  Also uncomment the declaration of __privileged_functions_start__
	at the top of this function. */

	/* pul = __privileged_functions_start__;
	ulReadData = *pul; */

	/*pul = __privileged_functions_end__ - 1;
	ulReadData = *pul;*/

	/*pul = __privileged_data_start__;
	ulReadData = *pul;*/

	/*pul = __privileged_data_end__ - 1;
	ulReadData = *pul;*/

	/* Must not just run off the end of a task function, so delete this task.
	Note that because this task was created using xTaskCreate() the stack was
	allocated dynamically and I have not included any code to free it again. */
	vTaskDelete( NULL );

	( void ) ulReadData;
}
/*-----------------------------------------------------------*/

static void prvOldStylePrivilegedModeTask( void *pvParameters )
{
volatile const uint32_t *pul;
volatile uint32_t ulReadData;
const volatile uint32_t *pulSystemPeripheralRegister = ( volatile uint32_t * ) 0xe000e014; /* Systick */
/*const volatile uint32_t *pulStandardPeripheralRegister = ( volatile uint32_t * ) 0x40000000;*/

	( void ) pvParameters;

	/* This task is created in Privileged mode using the original xTaskCreate()
	API	function.  It should have access to all Flash and RAM including that
	marked as Privileged access only.  So reading from the start and end of the
	non-privileged RAM should not cause a problem (the privileged RAM is the
	first block at the bottom of the RAM memory). */
	pul = __privileged_data_end__ + 1;
	ulReadData = *pul;
	pul = __SRAM_segment_end__ - 1;
	ulReadData = *pul;

	/* Likewise reading from the start and end of the non-privileged Flash
	should not be a problem (the privileged Flash is the first block at the
	bottom of the Flash memory). */
	pul = __privileged_functions_end__ + 1;
	ulReadData = *pul;
	pul = __FLASH_segment_end__ - 1;
	ulReadData = *pul;

	/* Reading from anywhere inside the privileged Flash or RAM should also
	not be a problem. */
	pul = __privileged_functions_start__;
	ulReadData = *pul;
	pul = __privileged_functions_end__ - 1;
	ulReadData = *pul;
	pul = __privileged_data_start__;
	ulReadData = *pul;
	pul = __privileged_data_end__ - 1;
	ulReadData = *pul;

	/* Finally, accessing both System and normal peripherals should both be
	possible. */
	ulReadData = *pulSystemPeripheralRegister;
	/*ulReadData = *pulStandardPeripheralRegister;*/

	/* Must not just run off the end of a task function, so delete this task.
	Note that because this task was created using xTaskCreate() the stack was
	allocated dynamically and I have not included any code to free it again. */
	vTaskDelete( NULL );

	( void ) ulReadData;
}
/*-----------------------------------------------------------*/

void vMainDeleteMe( void )
{
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

void vMainSendImAlive( QueueHandle_t xHandle, uint32_t ulTaskNumber )
{
	if( xHandle != NULL )
	{
		xQueueSend( xHandle, &ulTaskNumber, mainDONT_BLOCK );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	extern void SystemInit( void );
	extern uint32_t __Vectors[];

	/* Assuming downloading code via the debugger - so ensure the hardware
	is using the vector table downloaded with the application. */
	mainVTOR = ( uint32_t ) __Vectors;

	#if ( ( configASSERT_DEFINED == 1 ) && ( defined ( __GNUC__ ) ) )
	{
		/* Sanity check linker configuration sizes sections adequately. */
		const uint32_t ulPrivilegedFunctionsActualEnd = ( uint32_t ) __privileged_functions_actual_end__;
		const uint32_t ulPrivilegedDataActualEnd = ( uint32_t ) __privileged_data_actual_end__;
		const uint32_t ulPrivilegedFunctionsEnd = ( uint32_t ) __privileged_functions_end__;
		const uint32_t ulPrivilegedDataEnd = ( uint32_t ) __privileged_data_end__;

		configASSERT( ulPrivilegedFunctionsActualEnd < ulPrivilegedFunctionsEnd );
		configASSERT( ulPrivilegedDataActualEnd < ulPrivilegedDataEnd );

		/* Clear the privileged data to 0 as the C start up code is only set to
		clear the non-privileged bss. */
		memset( ( void * ) __privileged_data_start__, 0x00, ( size_t ) __privileged_data_actual_end__ - ( size_t ) __privileged_data_start__ );
	}
	#endif

	SystemInit();
	SystemCoreClockUpdate();
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static uint32_t ulCallCount = 0;
const uint32_t ulCallsBetweenSends = pdMS_TO_TICKS( 5000 );
const uint32_t ulMessage = configPRINT_SYSTEM_STATUS;
portBASE_TYPE xDummy;

	/* If configUSE_TICK_HOOK is set to 1 then this function will get called
	from each RTOS tick.  It is called from the tick interrupt and therefore
	will be executing in the privileged state. */

	ulCallCount++;

	/* Is it time to print out the pass/fail message again? */
	if( ulCallCount >= ulCallsBetweenSends )
	{
		ulCallCount = 0;

		/* Send a message to the check task to command it to check that all
		the tasks are still running then print out the status.

		This is running in an ISR so has to use the "FromISR" version of
		xQueueSend().  Because it is in an ISR it is running with privileges
		so can access xGlobalScopeCheckQueue directly. */
		xQueueSendFromISR( xGlobalScopeCheckQueue, &ulMessage, &xDummy );
	}
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	/* If configCHECK_FOR_STACK_OVERFLOW is set to either 1 or 2 then this
	function will automatically get called if a task overflows its stack. */
	( void ) pxTask;
	( void ) pcTaskName;
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* If configUSE_MALLOC_FAILED_HOOK is set to 1 then this function will
	be called automatically if a call to pvPortMalloc() fails.  pvPortMalloc()
	is called automatically when a task, queue or semaphore is created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvTimerCallback( TimerHandle_t xExpiredTimer )
{
uint32_t ulCount;

	/* The count of the number of times this timer has expired is saved in the
	timer's ID.  Obtain the current count. */
	ulCount = ( uint32_t ) pvTimerGetTimerID( xTimer );

	/* Increment the count, and save it back into the timer's ID. */
	ulCount++;
	vTimerSetTimerID( xTimer, ( void * ) ulCount );

	/* Let the check task know the timer is still running. */
	vMainSendImAlive( xGlobalScopeCheckQueue, configTIMER_STILL_EXECUTING );
}
/*-----------------------------------------------------------*/

/* configUSE_STATIC_ALLOCATION is set to 1, so the application must provide an
implementation of vApplicationGetIdleTaskMemory() to provide the memory that is
used by the Idle task. */
void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer, StackType_t **ppxIdleTaskStackBuffer, uint32_t *pulIdleTaskStackSize )
{
/* If the buffers to be provided to the Idle task are declared inside this
function then they must be declared static - otherwise they will be allocated on
the stack and so not exists after this function exits. */
static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

	/* Pass out a pointer to the StaticTask_t structure in which the Idle task's
	state will be stored. */
	*ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

	/* Pass out the array that will be used as the Idle task's stack. */
	*ppxIdleTaskStackBuffer = uxIdleTaskStack;

	/* Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
	Note that, as the array is necessarily of type StackType_t,
	configMINIMAL_STACK_SIZE is specified in words, not bytes. */
	*pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}
/*-----------------------------------------------------------*/

/* configUSE_STATIC_ALLOCATION and configUSE_TIMERS are both set to 1, so the
application must provide an implementation of vApplicationGetTimerTaskMemory()
to provide the memory that is used by the Timer service task. */
void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer, StackType_t **ppxTimerTaskStackBuffer, uint32_t *pulTimerTaskStackSize )
{
/* If the buffers to be provided to the Timer task are declared inside this
function then they must be declared static - otherwise they will be allocated on
the stack and so not exists after this function exits. */
static StaticTask_t xTimerTaskTCB;
static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];

	/* Pass out a pointer to the StaticTask_t structure in which the Timer
	task's state will be stored. */
	*ppxTimerTaskTCBBuffer = &xTimerTaskTCB;

	/* Pass out the array that will be used as the Timer task's stack. */
	*ppxTimerTaskStackBuffer = uxTimerTaskStack;

	/* Pass out the size of the array pointed to by *ppxTimerTaskStackBuffer.
	Note that, as the array is necessarily of type StackType_t,
	configMINIMAL_STACK_SIZE is specified in words, not bytes. */
	*pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}
/*-----------------------------------------------------------*/

static void prvITMPrintString( const char *pcString )
{
	while( *pcString != 0x00 )
	{
		ITM_SendChar( *pcString );
		pcString++;
	}
}
/*-----------------------------------------------------------*/

static void prvRegTest3Task( void *pvParameters )
{
	/* Although the regtest task is written in assembler, its entry point is
	written in C for convenience of checking the task parameter is being passed
	in correctly. */
	if( pvParameters == configREG_TEST_TASK_3_PARAMETER )
	{
		/* Start the part of the test that is written in assembler. */
		vRegTest3Implementation();
	}

	/* The following line will only execute if the task parameter is found to
	be incorrect.  The check task will detect that the regtest loop counter is
	not being incremented and flag an error. */
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvRegTest4Task( void *pvParameters )
{
	/* Although the regtest task is written in assembler, its entry point is
	written in C for convenience of checking the task parameter is being passed
	in correctly. */
	if( pvParameters == configREG_TEST_TASK_4_PARAMETER )
	{
		/* Start the part of the test that is written in assembler. */
		vRegTest4Implementation();
	}

	/* The following line will only execute if the task parameter is found to
	be incorrect.  The check task will detect that the regtest loop counter is
	not being incremented and flag an error. */
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

