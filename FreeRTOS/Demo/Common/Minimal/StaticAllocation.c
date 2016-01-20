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
 * Demonstrates how to create FreeRTOS objects using pre-allocated memory,
 * rather than the normal dynamically allocated memory.
 *
 * Two buffers are required by a task - one that is used by the task as its
 * stack, and one that holds the task's control block (TCB).
 * prvStaticallyAllocatedCreator() creates and deletes tasks with all
 * possible combinations of statically allocated and dynamically allocated
 * stacks and TCBs.
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo program include files. */
#include "StaticAllocation.h"

/* Exclude the entire file if configSUPPORT_STATIC_ALLOCATION is 0. */
#if( configSUPPORT_STATIC_ALLOCATION == 1 )

/* The priority at which the task that performs the tests is created. */
#define staticTASK_PRIORITY					( tskIDLE_PRIORITY + 2 )

/* The length of the queue, in items, not bytes, used in the queue static
allocation tests. */
#define staticQUEUE_LENGTH_IN_ITEMS			( 5 )

/* A block time of 0 simply means "don't block". */
#define staticDONT_BLOCK					( ( TickType_t ) 0 )

/* Binary semaphores have a maximum count of 1. */
#define staticBINARY_SEMAPHORE_MAX_COUNT	( 1 )


/*-----------------------------------------------------------*/

/*
 * A task that is created and deleted multiple times, using both statically and
 * dynamically allocated stack and TCB.
 */
static void prvStaticallyAllocatedTask( void *pvParameters );

/*
 * The task that repeatedly creates and deletes statically allocated tasks, and
 * other RTOS objects.
 */
static void prvStaticallyAllocatedCreator( void *pvParameters );

/*
 * Utility function to create pseudo random numbers.
 */
static UBaseType_t prvRand( void );

/*
 * A function that demonstrates and tests the xTaskCreateStatic() API function
 * by creating and then deleting tasks with both dynamically and statically
 * allocated TCBs and stacks.
 */
static void prvCreateAndDeleteStaticallyAllocatedTasks( void );

/*
 * A function that demonstrates and tests the xQueueCreateStatic() API function
 * by creating and then deleting queues with both dynamically and statically
 * allocated queue structures and queue storage areas.
 */
static void prvCreateAndDeleteStaticallyAllocatedQueues( void );

/*
 * A function that demonstrates and tests the xSemaphoreCreateBinaryStatic() API
 * macro by creating and then deleting binary semaphores with both dynamically
 * and statically allocated semaphore structures.
 */
static void prvCreateAndDeleteStaticallyAllocatedBinarySemaphores( void );

/*
 * A function that demonstrates and tests the xSemaphoreCreateMutexStatic() API
 * macro by creating and then deleting mutexes with both dynamically and
 * statically allocated semaphore structures.
 */
static void prvCreateAndDeleteStaticallyAllocatedMutexes( void );

/*
 * A function that demonstrates and tests the xSemaphoreCreateCountingStatic()
 * API macro by creating and then deleting counting semaphores with both
 * dynamically and statically allocated semaphore structures.
 */
static void prvCreateAndDeleteStaticallyAllocatedCountingSemaphores( void );

/*
 * A function that demonstrates and tests the
 * xSemaphoreCreateRecursiveMutexStatic() API macro by creating and then
 * deleting recursive mutexes with both dynamically and statically allocated
 * semaphore structures.
 */
static void prvCreateAndDeleteStaticallyAllocatedRecursiveMutexes( void );

/*
 * The task that creates and deletes other tasks has to delay occasionally to
 * ensure lower priority tasks are not starved of processing time.  A pseudo
 * random delay time is used just to add a little bit of randomisation into the
 * execution pattern.  prvGetNextDelayTime() generates the pseudo random delay.
 */
static TickType_t prvGetNextDelayTime( void );

/*
 * Checks the basic operation of a queue after it has been created.
 */
static void prvCheckQueueFunction( QueueHandle_t xQueue );

/*
 * Checks the basic operation of a recursive mutex after it has been created.
 */
static void prvCheckRecursiveSemaphoreFunction( SemaphoreHandle_t xSemaphore );

/*
 * Checks the basic operation of a binary semaphore after it has been created.
 */
static void prvCheckSemaphoreFunction( SemaphoreHandle_t xSemaphore, UBaseType_t uxMaxCount );

/*-----------------------------------------------------------*/

/* StaticTCB_t is a publicly accessible structure that has the same size and
alignment requirements as the real TCB structure.  It is provided as a mechanism
for applications to know the size of the TCB (which is dependent on the
architecture and configuration file settings) without breaking the strict data
hiding policy by exposing the real TCB.  This StaticTCB_t variable is passed
into the xTaskCreateStatic() function that creates the
prvStaticallyAllocatedCreator() task, and will hold the TCB of the created
tasks. */
static StaticTCB_t xCreatorTaskTCBBuffer;

/* This is the stack that will be used by the prvStaticallyAllocatedCreator()
task, which is itself created using statically allocated buffers (so without any
dynamic memory allocation). */
static StackType_t uxCreatorTaskStackBuffer[ configMINIMAL_STACK_SIZE ];

/* Used by the pseudo random number generating function. */
static uint32_t ulNextRand = 0;

/* Used so a check task can ensure this test is still executing, and not
stalled. */
static volatile UBaseType_t uxCycleCounter = 0;

/* A variable that gets set to pdTRUE if an error is detected. */
static BaseType_t xErrorOccurred = pdFALSE;

/*-----------------------------------------------------------*/

void vStartStaticallyAllocatedTasks( void  )
{
	/* Create a single task, which then repeatedly creates and deletes the
	task implemented by prvStaticallyAllocatedTask() at various different
	priorities, and both with and without statically allocated TCB and stack. */
	xTaskCreateStatic( prvStaticallyAllocatedCreator,	/* The function that implements the task being created. */
					   "StatCreate",						/* Text name for the task - not used by the RTOS, its just to assist debugging. */
					   configMINIMAL_STACK_SIZE,			/* Size of the buffer passed in as the stack - in words, not bytes! */
					   NULL,								/* Parameter passed into the task - not used in this case. */
					   staticTASK_PRIORITY,					/* Priority of the task. */
					   NULL,								/* Handle of the task being created, not used in this case. */
					   &( uxCreatorTaskStackBuffer[ 0 ] ),  /* The buffer to use as the task's stack. */
					   &xCreatorTaskTCBBuffer );			/* The variable that will hold the task's TCB. */

	/* Pseudo seed the random number generator. */
	ulNextRand = ( uint32_t ) prvRand;
}
/*-----------------------------------------------------------*/

static void prvStaticallyAllocatedCreator( void *pvParameters )
{
	/* Avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Loop, running functions that create and delete the various objects
		that can be optionally created using either static or dynamic memory
		allocation. */
		prvCreateAndDeleteStaticallyAllocatedTasks();
		prvCreateAndDeleteStaticallyAllocatedQueues();
		prvCreateAndDeleteStaticallyAllocatedBinarySemaphores();
		prvCreateAndDeleteStaticallyAllocatedCountingSemaphores();
		prvCreateAndDeleteStaticallyAllocatedMutexes();
		prvCreateAndDeleteStaticallyAllocatedRecursiveMutexes();
	}
}
/*-----------------------------------------------------------*/

static void prvCheckSemaphoreFunction( SemaphoreHandle_t xSemaphore, UBaseType_t uxMaxCount )
{
BaseType_t xReturned;
UBaseType_t x;
const TickType_t xShortBlockTime = pdMS_TO_TICKS( 10 );
TickType_t xTickCount;

	/* The binary semaphore should start 'empty', so a call to xSemaphoreTake()
	should fail. */
	xTickCount = xTaskGetTickCount();
	xReturned = xSemaphoreTake( xSemaphore, xShortBlockTime );

	if( ( xTaskGetTickCount() - xTickCount) < xShortBlockTime )
	{
		/* Did not block on the semaphore as long as expected. */
		xErrorOccurred = pdTRUE;
	}

	if( xReturned != pdFAIL )
	{
		xErrorOccurred = pdTRUE;
	}

	/* Should be possible to 'give' the semaphore up to a maximum of uxMaxCount
	times. */
	for( x = 0; x < uxMaxCount; x++ )
	{
		xReturned = xSemaphoreGive( xSemaphore );

		if( xReturned == pdFAIL )
		{
			xErrorOccurred = pdTRUE;
		}
	}

	/* Giving the semaphore again should fail, as it is 'full'. */
	xReturned = xSemaphoreGive( xSemaphore );

	if( xReturned != pdFAIL )
	{
		xErrorOccurred = pdTRUE;
	}

	configASSERT( uxSemaphoreGetCount( xSemaphore ) == uxMaxCount );

	/* Should now be possible to 'take' the semaphore up to a maximum of
	uxMaxCount times without blocking. */
	for( x = 0; x < uxMaxCount; x++ )
	{
		xReturned = xSemaphoreTake( xSemaphore, staticDONT_BLOCK );

		if( xReturned == pdFAIL )
		{
			xErrorOccurred = pdTRUE;
		}
	}

	/* Back to the starting condition, where the semaphore should not be
	available. */
	xTickCount = xTaskGetTickCount();
	xReturned = xSemaphoreTake( xSemaphore, xShortBlockTime );

	if( ( xTaskGetTickCount() - xTickCount) < xShortBlockTime )
	{
		/* Did not block on the semaphore as long as expected. */
		xErrorOccurred = pdTRUE;
	}

	if( xReturned != pdFAIL )
	{
		xErrorOccurred = pdTRUE;
	}

	configASSERT( uxSemaphoreGetCount( xSemaphore ) == 0 );
}
/*-----------------------------------------------------------*/

static void prvCheckQueueFunction( QueueHandle_t xQueue )
{
uint64_t ull, ullRead;
BaseType_t xReturned, xLoop;

	/* This test is done twice to ensure the queue storage area wraps. */
	for( xLoop = 0; xLoop < 2; xLoop++ )
	{
		/* A very basic test that the queue can be written to and read from as
		expected.  First the queue should be empty. */
		xReturned = xQueueReceive( xQueue, &ull, staticDONT_BLOCK );
		if( xReturned != errQUEUE_EMPTY )
		{
			xErrorOccurred = pdTRUE;
		}

		/* Now it should be possible to write to the queue staticQUEUE_LENGTH_IN_ITEMS
		times. */
		for( ull = 0; ull < staticQUEUE_LENGTH_IN_ITEMS; ull++ )
		{
			xReturned = xQueueSend( xQueue, &ull, staticDONT_BLOCK );
			if( xReturned != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}
		}

		/* Should not now be possible to write to the queue again. */
		xReturned = xQueueSend( xQueue, &ull, staticDONT_BLOCK );
		if( xReturned != errQUEUE_FULL )
		{
			xErrorOccurred = pdTRUE;
		}

		/* Now read back from the queue to ensure the data read back matches that
		written. */
		for( ull = 0; ull < staticQUEUE_LENGTH_IN_ITEMS; ull++ )
		{
			xReturned = xQueueReceive( xQueue, &ullRead, staticDONT_BLOCK );

			if( xReturned != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}

			if( ullRead != ull )
			{
				xErrorOccurred = pdTRUE;
			}
		}

		/* The queue should be empty again. */
		xReturned = xQueueReceive( xQueue, &ull, staticDONT_BLOCK );
		if( xReturned != errQUEUE_EMPTY )
		{
			xErrorOccurred = pdTRUE;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvCheckRecursiveSemaphoreFunction( SemaphoreHandle_t xSemaphore )
{
const BaseType_t xLoops = 5;
BaseType_t x, xReturned;

	/* A very basic test that the recursive semaphore behaved like a recursive
	semaphore. First the semaphore should not be able to be given, as it has not
	yet been taken. */
	xReturned = xSemaphoreGiveRecursive( xSemaphore );

	if( xReturned != pdFAIL )
	{
		xErrorOccurred = pdTRUE;
	}

	/* Now it should be possible to take the mutex a number of times. */
	for( x = 0; x < xLoops; x++ )
	{
		xReturned = xSemaphoreTakeRecursive( xSemaphore, staticDONT_BLOCK );

		if( xReturned != pdPASS )
		{
			xErrorOccurred = pdTRUE;
		}
	}

	/* Should be possible to give the semaphore the same number of times as it
	was given in the loop above. */
	for( x = 0; x < xLoops; x++ )
	{
		xReturned = xSemaphoreGiveRecursive( xSemaphore );

		if( xReturned != pdPASS )
		{
			xErrorOccurred = pdTRUE;
		}
	}

	/* No more gives should be possible though. */
	xReturned = xSemaphoreGiveRecursive( xSemaphore );

	if( xReturned != pdFAIL )
	{
		xErrorOccurred = pdTRUE;
	}
}
/*-----------------------------------------------------------*/

static void prvCreateAndDeleteStaticallyAllocatedCountingSemaphores( void )
{
SemaphoreHandle_t xSemaphore;
const UBaseType_t uxMaxCount = ( UBaseType_t ) 10;

/* StaticSemaphore_t is a publicly accessible structure that has the same size
and alignment requirements as the real semaphore structure.  It is provided as a
mechanism for applications to know the size of the semaphore (which is dependent
on the architecture and configuration file settings) without breaking the strict
data hiding policy by exposing the real semaphore internals.  This
StaticSemaphore_t variable is passed into the xSemaphoreCreateCountingStatic()
function calls within this function.  NOTE: In most usage scenarios now it is
faster and more memory efficient to use a direct to task notification instead of
a counting semaphore.  http://www.freertos.org/RTOS-task-notifications.html */
static StaticSemaphore_t xSemaphoreBuffer; /* Static so it doesn't use too much stack space. */

	/* Create the semaphore.  xSemaphoreCreateCountingStatic() has one more
	parameter than the usual xSemaphoreCreateCounting() function.  The paraemter
	is a pointer to the pre-allocated StaticSemaphore_t structure, which will
	hold information on the semaphore in an anonymous way.  If the pointer is
	passed as NULL then the structure will be allocated dynamically, just as
	when xSemaphoreCreateCounting() is called. */
	xSemaphore = xSemaphoreCreateCountingStatic( uxMaxCount, 0, &xSemaphoreBuffer );

	/* The semaphore handle should equal the static semaphore structure passed
	into the xSemaphoreCreateBinaryStatic() function. */
	configASSERT( xSemaphore == ( SemaphoreHandle_t ) &xSemaphoreBuffer );

	/* Ensure the semaphore passes a few sanity checks as a valid semaphore. */
	prvCheckSemaphoreFunction( xSemaphore, uxMaxCount );

	/* Delete the semaphore again so the buffers can be reused. */
	vSemaphoreDelete( xSemaphore );


	/* The semaphore created above had a statically allocated semaphore
	structure.  Repeat the above using NULL as the third
	xSemaphoreCreateCountingStatic() parameter so the semaphore structure is
	instead allocated dynamically. */
	xSemaphore = xSemaphoreCreateCountingStatic( uxMaxCount, 0, NULL );

	/* Ensure the semaphore passes a few sanity checks as a valid semaphore. */
	prvCheckSemaphoreFunction( xSemaphore, uxMaxCount );

	/* Delete the semaphore again so the buffers can be reused. */
	vSemaphoreDelete( xSemaphore );

	/* Ensure lower priority tasks get CPU time. */
	vTaskDelay( prvGetNextDelayTime() );

	/* Just to show the check task that this task is still executing. */
	uxCycleCounter++;
}
/*-----------------------------------------------------------*/

static void prvCreateAndDeleteStaticallyAllocatedRecursiveMutexes( void )
{
SemaphoreHandle_t xSemaphore;

/* StaticSemaphore_t is a publicly accessible structure that has the same size
and alignment requirements as the real semaphore structure.  It is provided as a
mechanism for applications to know the size of the semaphore (which is dependent
on the architecture and configuration file settings) without breaking the strict
data hiding policy by exposing the real semaphore internals.  This
StaticSemaphore_t variable is passed into the
xSemaphoreCreateRecursiveMutexStatic() function calls within this function. */
static StaticSemaphore_t xSemaphoreBuffer; /* Static so it doesn't use too much stack space. */

	/* Create the semaphore.  xSemaphoreCreateRecursiveMutexStatic() has one
	more parameter than the usual xSemaphoreCreateRecursiveMutex() function.
	The parameter is a pointer to the pre-allocated StaticSemaphore_t structure,
	which will hold information on the semaphore in an anonymous way.  If the
	pointer is passed as NULL then the structure will be allocated dynamically,
	just as	when xSemaphoreCreateRecursiveMutex() is called. */
	xSemaphore = xSemaphoreCreateRecursiveMutexStatic( &xSemaphoreBuffer );

	/* The semaphore handle should equal the static semaphore structure passed
	into the xSemaphoreCreateBinaryStatic() function. */
	configASSERT( xSemaphore == ( SemaphoreHandle_t ) &xSemaphoreBuffer );

	/* Ensure the semaphore passes a few sanity checks as a valid
	recursive semaphore. */
	prvCheckRecursiveSemaphoreFunction( xSemaphore );

	/* Delete the semaphore again so the buffers can be reused. */
	vSemaphoreDelete( xSemaphore );


	/* The semaphore created above had a statically allocated semaphore
	structure.  Repeat the above using NULL as the
	xSemaphoreCreateRecursiveMutexStatic() parameter so the semaphore structure
	is instead allocated dynamically. */
	xSemaphore = xSemaphoreCreateRecursiveMutexStatic( NULL );

	/* Ensure the semaphore passes a few sanity checks as a valid semaphore. */
	prvCheckRecursiveSemaphoreFunction( xSemaphore );

	/* Delete the semaphore again so the buffers can be reused. */
	vSemaphoreDelete( xSemaphore );

	/* Ensure lower priority tasks get CPU time. */
	vTaskDelay( prvGetNextDelayTime() );

	/* Just to show the check task that this task is still executing. */
	uxCycleCounter++;
}
/*-----------------------------------------------------------*/

static void prvCreateAndDeleteStaticallyAllocatedQueues( void )
{
QueueHandle_t xQueue;

/* StaticQueue_t is a publicly accessible structure that has the same size and
alignment requirements as the real queue structure.  It is provided as a
mechanism for applications to know the size of the queue (which is dependent on
the architecture and configuration file settings) without breaking the strict
data hiding policy by exposing the real queue internals.  This StaticQueue_t
variable is passed into the xQueueCreateStatic() function calls within this
function. */
static StaticQueue_t xStaticQueue;

/* The queue storage area must be large enough to hold the maximum number of
items it is possible for the queue to hold at any one time, which equals the
queue length (in items, not bytes) multiplied by the size of each item.  In this
case the queue will hold staticQUEUE_LENGTH_IN_ITEMS 64-bit items.  See
http://www.freertos.org/Embedded-RTOS-Queues.html */
static uint8_t ucQueueStorageArea[ staticQUEUE_LENGTH_IN_ITEMS * sizeof( uint64_t ) ];

	/* Create the queue.  xQueueCreateStatic() has two more parameters than the
	usual xQueueCreate() function.  The first new paraemter is a pointer to the
	pre-allocated queue storage area.  The second new parameter is a pointer to
	the StaticQueue_t structure that will hold the queue state information in
	an anonymous way.  If either pointer is passed as NULL then the respective
	data will be allocated dynamically as if xQueueCreate() had been called. */
	xQueue = xQueueCreateStatic( staticQUEUE_LENGTH_IN_ITEMS, /* The maximum number of items the queue can hold. */
								 sizeof( uint64_t ), /* The size of each item. */
								 ucQueueStorageArea, /* The buffer used to hold items within the queue. */
								 &xStaticQueue );	 /* The static queue structure that will hold the state of the queue. */

	/* The queue handle should equal the static queue structure passed into the
	xQueueCreateStatic() function. */
	configASSERT( xQueue == ( QueueHandle_t ) &xStaticQueue );

	/* Ensure the queue passes a few sanity checks as a valid queue. */
	prvCheckQueueFunction( xQueue );

	/* Delete the queue again so the buffers can be reused. */
	vQueueDelete( xQueue );


	/* The queue created above had a statically allocated queue storage area and
	queue structure.  Repeat the above with three more times - with different
	combinations of static and dynamic allocation. */

	xQueue = xQueueCreateStatic( staticQUEUE_LENGTH_IN_ITEMS, /* The maximum number of items the queue can hold. */
								 sizeof( uint64_t ), /* The size of each item. */
								 NULL,				 /* Allocate the buffer used to hold items within the queue dynamically. */
								 &xStaticQueue );	 /* The static queue structure that will hold the state of the queue. */

	configASSERT( xQueue == ( QueueHandle_t ) &xStaticQueue );
	prvCheckQueueFunction( xQueue );
	vQueueDelete( xQueue );

	/* Ensure lower priority tasks get CPU time. */
	vTaskDelay( prvGetNextDelayTime() );

	/* Just to show the check task that this task is still executing. */
	uxCycleCounter++;

	xQueue = xQueueCreateStatic( staticQUEUE_LENGTH_IN_ITEMS, /* The maximum number of items the queue can hold. */
								 sizeof( uint64_t ), /* The size of each item. */
								 ucQueueStorageArea, /* The buffer used to hold items within the queue. */
								 NULL );			 /* The queue structure is allocated dynamically. */

	prvCheckQueueFunction( xQueue );
	vQueueDelete( xQueue );

	xQueue = xQueueCreateStatic( staticQUEUE_LENGTH_IN_ITEMS, /* The maximum number of items the queue can hold. */
								 sizeof( uint64_t ), /* The size of each item. */
								 NULL,				 /* Allocate the buffer used to hold items within the queue dynamically. */
								 NULL );			 /* The queue structure is allocated dynamically. */

	prvCheckQueueFunction( xQueue );
	vQueueDelete( xQueue );

	/* Ensure lower priority tasks get CPU time. */
	vTaskDelay( prvGetNextDelayTime() );

	/* Just to show the check task that this task is still executing. */
	uxCycleCounter++;
}
/*-----------------------------------------------------------*/

static void prvCreateAndDeleteStaticallyAllocatedMutexes( void )
{
SemaphoreHandle_t xSemaphore;
BaseType_t xReturned;

/* StaticSemaphore_t is a publicly accessible structure that has the same size
and alignment requirements as the real semaphore structure.  It is provided as a
mechanism for applications to know the size of the semaphore (which is dependent
on the architecture and configuration file settings) without breaking the strict
data hiding policy by exposing the real semaphore internals.  This
StaticSemaphore_t variable is passed into the xSemaphoreCreateMutexStatic()
function calls within this function. */
static StaticSemaphore_t xSemaphoreBuffer; /* Static so it doesn't use too much stack space. */

	/* Create the semaphore.  xSemaphoreCreateMutexStatic() has one more
	parameter than the usual xSemaphoreCreateMutex() function.  The paraemter
	is a pointer to the pre-allocated StaticSemaphore_t structure, which will
	hold information on the semaphore in an anonymous way.  If the pointer is
	passed as NULL then the structure will be allocated dynamically, just as
	when xSemaphoreCreateMutex() is called. */
	xSemaphore = xSemaphoreCreateMutexStatic( &xSemaphoreBuffer );

	/* The semaphore handle should equal the static semaphore structure passed
	into the xSemaphoreCreateMutexStatic() function. */
	configASSERT( xSemaphore == ( SemaphoreHandle_t ) &xSemaphoreBuffer );

	/* Take the mutex so the mutex is in the state expected by the
	prvCheckSemaphoreFunction() function. */
	xReturned = xSemaphoreTake( xSemaphore, staticDONT_BLOCK );

	if( xReturned != pdPASS )
	{
		xErrorOccurred = pdTRUE;
	}

	/* Ensure the semaphore passes a few sanity checks as a valid semaphore. */
	prvCheckSemaphoreFunction( xSemaphore, staticBINARY_SEMAPHORE_MAX_COUNT );

	/* Delete the semaphore again so the buffers can be reused. */
	vSemaphoreDelete( xSemaphore );


	/* The semaphore created above had a statically allocated semaphore
	structure.  Repeat the above using NULL as the xSemaphoreCreateMutexStatic()
	parameter so the semaphore structure is instead allocated dynamically. */
	xSemaphore = xSemaphoreCreateMutexStatic( NULL );

	/* Take the mutex so the mutex is in the state expected by the
	prvCheckSemaphoreFunction() function. */
	xReturned = xSemaphoreTake( xSemaphore, staticDONT_BLOCK );

	if( xReturned != pdPASS )
	{
		xErrorOccurred = pdTRUE;
	}

	/* Ensure the semaphore passes a few sanity checks as a valid semaphore. */
	prvCheckSemaphoreFunction( xSemaphore, staticBINARY_SEMAPHORE_MAX_COUNT );

	/* Delete the semaphore again so the buffers can be reused. */
	vSemaphoreDelete( xSemaphore );

	/* Ensure lower priority tasks get CPU time. */
	vTaskDelay( prvGetNextDelayTime() );

	/* Just to show the check task that this task is still executing. */
	uxCycleCounter++;
}
/*-----------------------------------------------------------*/

static void prvCreateAndDeleteStaticallyAllocatedBinarySemaphores( void )
{
SemaphoreHandle_t xSemaphore;

/* StaticSemaphore_t is a publicly accessible structure that has the same size
and alignment requirements as the real semaphore structure.  It is provided as a
mechanism for applications to know the size of the semaphore (which is dependent
on the architecture and configuration file settings) without breaking the strict
data hiding policy by exposing the real semaphore internals.  This
StaticSemaphore_t variable is passed into the xSemaphoreCreateBinaryStatic()
function calls within this function.  NOTE: In most usage scenarios now it is
faster and more memory efficient to use a direct to task notification instead of
a binary semaphore.  http://www.freertos.org/RTOS-task-notifications.html */
static StaticSemaphore_t xSemaphoreBuffer; /* Static so it doesn't use too much stack space. */

	/* Create the semaphore.  xSemaphoreCreateBinaryStatic() has one more
	parameter than the usual xSemaphoreCreateBinary() function.  The paraemter
	is a pointer to the pre-allocated StaticSemaphore_t structure, which will
	hold information on the semaphore in an anonymous way.  If the pointer is
	passed as NULL then the structure will be allocated dynamically, just as
	when xSemaphoreCreateBinary() is called. */
	xSemaphore = xSemaphoreCreateBinaryStatic( &xSemaphoreBuffer );

	/* The semaphore handle should equal the static semaphore structure passed
	into the xSemaphoreCreateBinaryStatic() function. */
	configASSERT( xSemaphore == ( SemaphoreHandle_t ) &xSemaphoreBuffer );

	/* Ensure the semaphore passes a few sanity checks as a valid semaphore. */
	prvCheckSemaphoreFunction( xSemaphore, staticBINARY_SEMAPHORE_MAX_COUNT );

	/* Delete the semaphore again so the buffers can be reused. */
	vSemaphoreDelete( xSemaphore );


	/* The semaphore created above had a statically allocated semaphore
	structure.  Repeat the above using NULL as the xSemaphoreCreateBinaryStatic()
	parameter so the semaphore structure is instead allocated dynamically. */
	xSemaphore = xSemaphoreCreateBinaryStatic( NULL );

	/* Ensure the semaphore passes a few sanity checks as a valid semaphore. */
	prvCheckSemaphoreFunction( xSemaphore, staticBINARY_SEMAPHORE_MAX_COUNT );

	/* Delete the semaphore again so the buffers can be reused. */
	vSemaphoreDelete( xSemaphore );



	/* There isn't a static version of the old and deprecated
	vSemaphoreCreateBinary() macro (because its deprecated!), but check it is
	still functioning correctly when configSUPPORT_STATIC_ALLOCATION is set to
	1. */
	vSemaphoreCreateBinary( xSemaphore );

	/* The macro starts with the binary semaphore available, but the test
	function expects it to be unavailable. */
	if( xSemaphoreTake( xSemaphore, staticDONT_BLOCK ) == pdFAIL )
	{
		xErrorOccurred = pdTRUE;
	}

	prvCheckSemaphoreFunction( xSemaphore, staticBINARY_SEMAPHORE_MAX_COUNT );
	vSemaphoreDelete( xSemaphore );

	/* Ensure lower priority tasks get CPU time. */
	vTaskDelay( prvGetNextDelayTime() );

	/* Just to show the check task that this task is still executing. */
	uxCycleCounter++;
}
/*-----------------------------------------------------------*/

static void prvCreateAndDeleteStaticallyAllocatedTasks( void )
{
TaskHandle_t xCreatedTask;
BaseType_t xReturned;

/* The variable that will hold the TCB of tasks created by this function.  See
the comments above the declaration of the xCreatorTaskTCBBuffer variable for
more information. */
static StaticTCB_t xTCBBuffer; /* Static so it does not use too much stack space. */

/* This buffer that will be used as the stack of tasks created by this function.
See the comments above the declaration of the uxCreatorTaskStackBuffer[] array
above for more information. */
static StackType_t uxStackBuffer[ configMINIMAL_STACK_SIZE ];

	/* Create the task.  xTaskCreateStatic() has two more parameters than
	the usual xTaskCreate() function.  The first new parameter is a pointer to
	the pre-allocated stack.  The second new parameter is a pointer to the
	StaticTCB_t structure that will hold the task's TCB.  If either pointer is
	passed as NULL then the respective object will be allocated dynamically as
	if xTaskCreate() had been called. */
	xReturned = xTaskCreateStatic(
						prvStaticallyAllocatedTask, /* Function that implements the task. */
						"Static",					/* Human readable name for the task. */
						configMINIMAL_STACK_SIZE,	/* Task's stack size, in words (not bytes!). */
						NULL,						/* Parameter to pass into the task. */
						tskIDLE_PRIORITY,			/* The priority of the task. */
						&xCreatedTask,				/* Handle of the task being created. */
						&( uxStackBuffer[ 0 ] ),	/* The buffer to use as the task's stack. */
						&xTCBBuffer );				/* The variable that will hold that task's TCB. */

	/* Check the task was created correctly, then delete the task. */
	configASSERT( xReturned == pdPASS );
	if( xReturned != pdPASS )
	{
		xErrorOccurred = pdTRUE;
	}
	vTaskDelete( xCreatedTask );

	/* Ensure lower priority tasks get CPU time. */
	vTaskDelay( prvGetNextDelayTime() );

	/* Create and delete the task a few times again - testing both static and
	dynamic allocation for the stack and TCB. */
	xReturned = xTaskCreateStatic(
						prvStaticallyAllocatedTask, /* Function that implements the task. */
						"Static",					/* Human readable name for the task. */
						configMINIMAL_STACK_SIZE,	/* Task's stack size, in words (not bytes!). */
						NULL,						/* Parameter to pass into the task. */
						staticTASK_PRIORITY + 1,	/* The priority of the task. */
						&xCreatedTask,				/* Handle of the task being created. */
						NULL,						/* This time, dynamically allocate the stack. */
						&xTCBBuffer );				/* The variable that will hold that task's TCB. */

	configASSERT( xReturned == pdPASS );
	if( xReturned != pdPASS )
	{
		xErrorOccurred = pdTRUE;
	}
	vTaskDelete( xCreatedTask );

	/* Just to show the check task that this task is still executing. */
	uxCycleCounter++;

	/* Ensure lower priority tasks get CPU time. */
	vTaskDelay( prvGetNextDelayTime() );

	xReturned = xTaskCreateStatic(
						prvStaticallyAllocatedTask, /* Function that implements the task. */
						"Static",					/* Human readable name for the task. */
						configMINIMAL_STACK_SIZE,	/* Task's stack size, in words (not bytes!). */
						NULL,						/* Parameter to pass into the task. */
						staticTASK_PRIORITY - 1,	/* The priority of the task. */
						&xCreatedTask,				/* Handle of the task being created. */
						&( uxStackBuffer[ 0 ] ),	/* The buffer to use as the task's stack. */
						NULL );						/* This time dynamically allocate the TCB. */

	configASSERT( xReturned == pdPASS );
	if( xReturned != pdPASS )
	{
		xErrorOccurred = pdTRUE;
	}
	vTaskDelete( xCreatedTask );

	/* Ensure lower priority tasks get CPU time. */
	vTaskDelay( prvGetNextDelayTime() );

	xReturned = xTaskCreateStatic(
						prvStaticallyAllocatedTask, /* Function that implements the task. */
						"Static",					/* Human readable name for the task. */
						configMINIMAL_STACK_SIZE,	/* Task's stack size, in words (not bytes!). */
						NULL,						/* Parameter to pass into the task. */
						staticTASK_PRIORITY,		/* The priority of the task. */
						&xCreatedTask,				/* Handle of the task being created. */
						NULL,						/* This time dynamically allocate the stack and TCB. */
						NULL );						/* This time dynamically allocate the stack and TCB. */

	configASSERT( xReturned == pdPASS );
	if( xReturned != pdPASS )
	{
		xErrorOccurred = pdTRUE;
	}
	vTaskDelete( xCreatedTask );

	/* Ensure lower priority tasks get CPU time. */
	vTaskDelay( prvGetNextDelayTime() );

	/* Just to show the check task that this task is still executing. */
	uxCycleCounter++;
}
/*-----------------------------------------------------------*/

static void prvStaticallyAllocatedTask( void *pvParameters )
{
	( void ) pvParameters;

	/* The created task doesn't do anything - just waits to get deleted. */
	vTaskSuspend( NULL );
}
/*-----------------------------------------------------------*/

static UBaseType_t prvRand( void )
{
const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL;

	/* Utility function to generate a pseudo random number. */
	ulNextRand = ( ulMultiplier * ulNextRand ) + ulIncrement;
	return( ( ulNextRand >> 16UL ) & 0x7fffUL );
}
/*-----------------------------------------------------------*/

static TickType_t prvGetNextDelayTime( void )
{
TickType_t xNextDelay;
const TickType_t xMaxDelay = pdMS_TO_TICKS( ( TickType_t ) 150 );
const TickType_t xMinDelay = pdMS_TO_TICKS( ( TickType_t ) 75 );
const TickType_t xTinyDelay = pdMS_TO_TICKS( ( TickType_t ) 2 );

	/* Generate the next delay time.  This is kept within a narrow band so as
	not to disturb the timing of other tests - but does add in some pseudo
	randomisation into the tests. */
	do
	{
		xNextDelay = prvRand() % xMaxDelay;

		/* Just in case this loop is executed lots of times. */
		vTaskDelay( xTinyDelay );

	} while ( xNextDelay < xMinDelay );

	return xNextDelay;
}
/*-----------------------------------------------------------*/

BaseType_t xAreStaticAllocationTasksStillRunning( void )
{
static UBaseType_t uxLastCycleCounter = 0;
BaseType_t xReturn;

	if( uxCycleCounter == uxLastCycleCounter )
	{
		xErrorOccurred = pdTRUE;
	}
	else
	{
		uxLastCycleCounter = uxCycleCounter;
	}

	if( xErrorOccurred != pdFALSE )
	{
		xReturn = pdFAIL;
	}
	else
	{
		xReturn = pdPASS;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

/* Exclude the entire file if configSUPPORT_STATIC_ALLOCATION is 0. */
#endif /* configSUPPORT_STATIC_ALLOCATION == 1 */
