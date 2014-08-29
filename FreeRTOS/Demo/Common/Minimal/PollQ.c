/*
    FreeRTOS V8.1.1 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

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

/*
 * This version of PollQ. c is for use on systems that have limited stack
 * space and no display facilities.  The complete version can be found in
 * the Demo/Common/Full directory.
 *
 * Creates two tasks that communicate over a single queue.  One task acts as a
 * producer, the other a consumer.
 *
 * The producer loops for three iteration, posting an incrementing number onto the
 * queue each cycle.  It then delays for a fixed period before doing exactly the
 * same again.
 *
 * The consumer loops emptying the queue.  Each item removed from the queue is
 * checked to ensure it contains the expected value.  When the queue is empty it
 * blocks for a fixed period, then does the same again.
 *
 * All queue access is performed without blocking.  The consumer completely empties
 * the queue each time it runs so the producer should never find the queue full.
 *
 * An error is flagged if the consumer obtains an unexpected value or the producer
 * find the queue is full.
 */

/*
Changes from V2.0.0

	+ Delay periods are now specified using variables and constants of
	  TickType_t rather than uint32_t.
*/

#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo program include files. */
#include "PollQ.h"

#define pollqSTACK_SIZE			configMINIMAL_STACK_SIZE
#define pollqQUEUE_SIZE			( 10 )
#define pollqPRODUCER_DELAY		( ( TickType_t ) 200 / portTICK_PERIOD_MS )
#define pollqCONSUMER_DELAY		( pollqPRODUCER_DELAY - ( TickType_t ) ( 20 / portTICK_PERIOD_MS ) )
#define pollqNO_DELAY			( ( TickType_t ) 0 )
#define pollqVALUES_TO_PRODUCE	( ( BaseType_t ) 3 )
#define pollqINITIAL_VALUE		( ( BaseType_t ) 0 )

/* The task that posts the incrementing number onto the queue. */
static portTASK_FUNCTION_PROTO( vPolledQueueProducer, pvParameters );

/* The task that empties the queue. */
static portTASK_FUNCTION_PROTO( vPolledQueueConsumer, pvParameters );

/* Variables that are used to check that the tasks are still running with no
errors. */
static volatile BaseType_t xPollingConsumerCount = pollqINITIAL_VALUE, xPollingProducerCount = pollqINITIAL_VALUE;

/*-----------------------------------------------------------*/

void vStartPolledQueueTasks( UBaseType_t uxPriority )
{
static QueueHandle_t xPolledQueue;

	/* Create the queue used by the producer and consumer. */
	xPolledQueue = xQueueCreate( pollqQUEUE_SIZE, ( UBaseType_t ) sizeof( uint16_t ) );

	/* vQueueAddToRegistry() adds the queue to the queue registry, if one is
	in use.  The queue registry is provided as a means for kernel aware 
	debuggers to locate queues and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is 
	defined to be less than 1. */
	vQueueAddToRegistry( xPolledQueue, "Poll_Test_Queue" );

	/* Spawn the producer and consumer. */
	xTaskCreate( vPolledQueueConsumer, "QConsNB", pollqSTACK_SIZE, ( void * ) &xPolledQueue, uxPriority, ( TaskHandle_t * ) NULL );
	xTaskCreate( vPolledQueueProducer, "QProdNB", pollqSTACK_SIZE, ( void * ) &xPolledQueue, uxPriority, ( TaskHandle_t * ) NULL );
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vPolledQueueProducer, pvParameters )
{
uint16_t usValue = ( uint16_t ) 0;
BaseType_t xError = pdFALSE, xLoop;

	for( ;; )
	{		
		for( xLoop = 0; xLoop < pollqVALUES_TO_PRODUCE; xLoop++ )
		{
			/* Send an incrementing number on the queue without blocking. */
			if( xQueueSend( *( ( QueueHandle_t * ) pvParameters ), ( void * ) &usValue, pollqNO_DELAY ) != pdPASS )
			{
				/* We should never find the queue full so if we get here there
				has been an error. */
				xError = pdTRUE;
			}
			else
			{
				if( xError == pdFALSE )
				{
					/* If an error has ever been recorded we stop incrementing the
					check variable. */
					portENTER_CRITICAL();
						xPollingProducerCount++;
					portEXIT_CRITICAL();
				}

				/* Update the value we are going to post next time around. */
				usValue++;
			}
		}

		/* Wait before we start posting again to ensure the consumer runs and
		empties the queue. */
		vTaskDelay( pollqPRODUCER_DELAY );
	}
}  /*lint !e818 Function prototype must conform to API. */
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vPolledQueueConsumer, pvParameters )
{
uint16_t usData, usExpectedValue = ( uint16_t ) 0;
BaseType_t xError = pdFALSE;

	for( ;; )
	{		
		/* Loop until the queue is empty. */
		while( uxQueueMessagesWaiting( *( ( QueueHandle_t * ) pvParameters ) ) )
		{
			if( xQueueReceive( *( ( QueueHandle_t * ) pvParameters ), &usData, pollqNO_DELAY ) == pdPASS )
			{
				if( usData != usExpectedValue )
				{
					/* This is not what we expected to receive so an error has
					occurred. */
					xError = pdTRUE;

					/* Catch-up to the value we received so our next expected
					value should again be correct. */
					usExpectedValue = usData;
				}
				else
				{
					if( xError == pdFALSE )
					{
						/* Only increment the check variable if no errors have
						occurred. */
						portENTER_CRITICAL();
							xPollingConsumerCount++;
						portEXIT_CRITICAL();
					}
				}

				/* Next time round we would expect the number to be one higher. */
				usExpectedValue++;
			}
		}

		/* Now the queue is empty we block, allowing the producer to place more
		items in the queue. */
		vTaskDelay( pollqCONSUMER_DELAY );
	}
} /*lint !e818 Function prototype must conform to API. */
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running with no errors. */
BaseType_t xArePollingQueuesStillRunning( void )
{
BaseType_t xReturn;

	/* Check both the consumer and producer poll count to check they have both
	been changed since out last trip round.  We do not need a critical section
	around the check variables as this is called from a higher priority than
	the other tasks that access the same variables. */
	if( ( xPollingConsumerCount == pollqINITIAL_VALUE ) ||
		( xPollingProducerCount == pollqINITIAL_VALUE )
	  )
	{
		xReturn = pdFALSE;
	}
	else
	{
		xReturn = pdTRUE;
	}

	/* Set the check variables back down so we know if they have been
	incremented the next time around. */
	xPollingConsumerCount = pollqINITIAL_VALUE;
	xPollingProducerCount = pollqINITIAL_VALUE;

	return xReturn;
}
