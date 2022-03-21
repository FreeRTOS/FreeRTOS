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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* FreeRTOS kernel includes. */
#include <FreeRTOS.h>
#include <task.h>
#include <queue.h>

#include <stdio.h>

#include "riscv-virt.h"

/* Priorities used by the tasks. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The rate at which data is sent to the queue.  The 200ms value is converted
to ticks using the pdMS_TO_TICKS() macro. */
#define mainQUEUE_SEND_FREQUENCY_MS			pdMS_TO_TICKS( 1000 )

/* The maximum number items the queue can hold.  The priority of the receiving
task is above the priority of the sending task, so the receiving task will
preempt the sending task and remove the queue items each time the sending task
writes to the queue.  Therefore the queue will never have more than one item in
it at any time, and even with a queue length of 1, the sending task will never
find the queue full. */
#define mainQUEUE_LENGTH					( 1 )

/*-----------------------------------------------------------*/

/* The queue used by both tasks. */
static QueueHandle_t xQueue = NULL;

/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
	TickType_t xNextWakeTime;
	unsigned long ulValueToSend = 0UL;

	/* Remove compiler warning about unused parameter. */
	( void ) pvParameters;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, mainQUEUE_SEND_FREQUENCY_MS );

		ulValueToSend++;

		char buf[40];
		sprintf( buf, "%d: %s: send %ld", xGetCoreID(),
				pcTaskGetName( xTaskGetCurrentTaskHandle() ),
				ulValueToSend );
		vSendString( buf );

		/* 0 is used as the block time so the sending operation will not block -
		 * it shouldn't need to block as the queue should always be empty at
		 * this point in the code. */
		xQueueSend( xQueue, &ulValueToSend, 0U );
	}
}

/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
	/* Remove compiler warning about unused parameter. */
	( void ) pvParameters;

	for( ;; )
	{

		unsigned long ulReceivedValue;
		/* Wait until something arrives in the queue - this task will block
		indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
		FreeRTOSConfig.h. */
		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

		/*  To get here something must have been received from the queue. */
		char buf[40];
		sprintf( buf, "%d: %s: received %ld", xGetCoreID(),
				pcTaskGetName( xTaskGetCurrentTaskHandle() ),
				ulReceivedValue );
		vSendString( buf );
	}
}

/*-----------------------------------------------------------*/

int main_blinky( void )
{
	vSendString( "Hello FreeRTOS!" );

	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );

	if( xQueue != NULL )
	{
		/* Start the two tasks as described in the comments at the top of this
		file. */
		xTaskCreate( prvQueueReceiveTask, "Rx", configMINIMAL_STACK_SIZE * 2U, NULL,
					mainQUEUE_RECEIVE_TASK_PRIORITY, NULL );
		xTaskCreate( prvQueueSendTask, "Tx", configMINIMAL_STACK_SIZE * 2U, NULL,
					mainQUEUE_SEND_TASK_PRIORITY, NULL );
	}

	vTaskStartScheduler();

	return 0;
}
