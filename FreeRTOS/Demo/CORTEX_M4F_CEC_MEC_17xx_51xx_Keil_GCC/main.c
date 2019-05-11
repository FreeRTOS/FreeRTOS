/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * This is a simple example that creates two tasks and one queue.  One task
 * periodically sends a value to the other, which then prints out a message.
 * Normally such a simple example would toggle an LED, so the message that is
 * printed out is "toggle".
 *
 * The demo configures the kernel to be as simple as possible; FreeRTOSConfig.h
 * excludes most features, including dynamic memory allocation.
 */

/* Microchip includes. */
#include "common.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Priorities at which the tasks are created. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The rate at which data is sent to the queue.  The 200ms value is converted
to ticks using the portTICK_PERIOD_MS constant. */
#define mainQUEUE_SEND_FREQUENCY_MS			( pdMS_TO_TICKS( 1000UL ) )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added, meaning the send task should always find
the queue empty. */
#define mainQUEUE_LENGTH_IN_ITEMS			( 1 )

/*-----------------------------------------------------------*/

/*
 * Configures the clocks ready to run the demo.
 */
static void prvSetupHardware( void );

/*
 * Simple routine to print a string to ITM for viewing in the Keil serial debug
 * viewer.
 */
static void prvITMPrintString( const char *pcString );

/*
 * The tasks as described in the comments at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* configSUPPORT_STATIC_ALLOCATION is 1 and configSUPPORT_DYNAMIC_ALLOCATION is
0 so the queue structure and the queue storage area can only be statically
allocated.  See http://TBD for more information.
The queue storage area is dimensioned to hold just one 32-bit value. */
static StaticQueue_t xStaticQueue;
static uint8_t ucQueueStorageArea[ mainQUEUE_LENGTH_IN_ITEMS * sizeof( uint32_t ) ];

/* Holds the handle of the created queue. */
static QueueHandle_t xQueue = NULL;

/* configSUPPORT_STATIC_ALLOCATION is 1 and configSUPPORT_DYNAMIC_ALLOCATION is
0 so the task structure and the stacks used by the tasks can only be statically
allocated.  See http://TBD for more information. */
StaticTask_t xRxTCBBuffer, xTxTCBBuffer;
static StackType_t uxRxStackBuffer[ configMINIMAL_STACK_SIZE ], uxTxStackBuffer[ configMINIMAL_STACK_SIZE ];

/*-----------------------------------------------------------*/

int main( void )
{
	/* Set up the hardware ready to run the demo. */
	prvSetupHardware();
	prvITMPrintString( "Starting\r\n" );

	/* Create the queue.  xQueueCreateStatic() has two more parameters than the
	xQueueCreate() function.  The first new parameter is a pointer to the
	pre-allocated queue storage area.  The second new parameter is a pointer to
	the StaticQueue_t structure that will hold the queue state information in
	an anonymous way. */
	xQueue = xQueueCreateStatic( mainQUEUE_LENGTH_IN_ITEMS, /* The maximum number of items the queue can hold. */
								 sizeof( uint32_t ), 		/* The size of each item. */
								 ucQueueStorageArea, 		/* The buffer used to hold items within the queue. */
								 &xStaticQueue );	 		/* The static queue structure that will hold the state of the queue. */

	/* Create the two tasks as described in the comments at the top of this
	file. */
	xTaskCreateStatic(	prvQueueReceiveTask, 			/* Function that implements the task. */
						"Rx",							/* Human readable name for the task. */
						configMINIMAL_STACK_SIZE,		/* Task's stack size, in words (not bytes!). */
						NULL,							/* Parameter to pass into the task. */
						mainQUEUE_RECEIVE_TASK_PRIORITY,/* The priority of the task. */
						&( uxRxStackBuffer[ 0 ] ),		/* The buffer to use as the task's stack. */
						&xRxTCBBuffer );				/* The variable that will hold that task's TCB. */

	xTaskCreateStatic(	prvQueueSendTask, 				/* Function that implements the task. */
						"Tx",							/* Human readable name for the task. */
						configMINIMAL_STACK_SIZE,		/* Task's stack size, in words (not bytes!). */
						NULL,							/* Parameter to pass into the task. */
						mainQUEUE_SEND_TASK_PRIORITY,	/* The priority of the task. */
						&( uxTxStackBuffer[ 0 ] ),		/* The buffer to use as the task's stack. */
						&xTxTCBBuffer );				/* The variable that will hold that task's TCB. */

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* If dynamic memory allocation was used then the following code line would
	be reached if there was insufficient heap memory available to create either
	the timer or idle tasks.  As this project is using static memory allocation
	then the following line should never be reached. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
TickType_t xNextWakeTime;
const unsigned long ulValueToSend = 100UL;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again.
		The block time is specified in ticks, the constant used converts ticks
		to ms.  While in the Blocked state this task will not consume any CPU
		time. */
		vTaskDelayUntil( &xNextWakeTime, mainQUEUE_SEND_FREQUENCY_MS );

		/* Send to the queue - causing the queue receive task to unblock and
		toggle the LED.  0 is used as the block time so the sending operation
		will not block - it shouldn't need to block as the queue should always
		be empty at this point in the code. */
		xQueueSend( xQueue, &ulValueToSend, 0U );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
unsigned long ulReceivedValue;

	for( ;; )
	{
		/* Wait until something arrives in the queue - this task will block
		indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
		FreeRTOSConfig.h. */
		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

		/*  To get here something must have been received from the queue, but
		is it the expected value?  If it is, toggle the LED. */
		if( ulReceivedValue == 100UL )
		{
			/* Output a string in lieu of using an LED. */
			prvITMPrintString( "Toggle!\r\n" );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	SystemInit();
	SystemCoreClockUpdate();
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

