/*
	FreeRTOS.org V5.0.2 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

/*
 * This file defines one of the more complex set of demo/test tasks.  They are
 * designed to stress test the queue implementation though pseudo simultaneous 
 * multiple reads and multiple writes from both tasks of varying priority and 
 * interrupts.  The interrupts are prioritised such to ensure that nesting 
 * occurs (for those ports that support it).
 *
 * The test ensures that, while being accessed from three tasks and two 
 * interrupts, all the data sent to the queues is also received from
 * the same queue, and that no duplicate items are either sent or received.
 * The tests also ensure that a low priority task is never able to successfully
 * read from or write to a queue when a task of higher priority is attempting
 * the same operation.
 */

/* Standard includes. */
#include <string.h>

/* SafeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo app includes. */
#include "IntQueue.h"
#include "IntQueueTimer.h"

/* Priorities used by test tasks. */
#define intqHIGHER_PRIORITY		1
#define intqLOWER_PRIORITY		0

/* The number of values to send/receive before checking that all values were
processed as expected. */
#define intqNUM_VALUES_TO_LOG	( 200 )
#define intqSHORT_DELAY			( 75 )

/* The value by which the value being sent to or received from a queue should
increment past intqNUM_VALUES_TO_LOG before we check that all values have been
sent/received correctly.  This is done to ensure that all tasks and interrupts
accessing the queue have completed their accesses with the 
intqNUM_VALUES_TO_LOG range. */
#define intqVALUE_OVERRUN		( 50 )

/* The delay used by the polling task.  A short delay is used for code 
coverage. */
#define intqONE_TICK_DELAY		( 1 )

/* Each task and interrupt is given a unique identifier.  This value is used to 
identify which task sent or received each value.  The identifier is also used 
to distinguish between two tasks that are running the same task function. */
#define intqHIGH_PRIORITY_TASK1	( ( unsigned portBASE_TYPE ) 1 )
#define intqHIGH_PRIORITY_TASK2	( ( unsigned portBASE_TYPE ) 2 )
#define intqLOW_PRIORITY_TASK	( ( unsigned portBASE_TYPE ) 3 )
#define intqFIRST_INTERRUPT		( ( unsigned portBASE_TYPE ) 4 )
#define intqSECOND_INTERRUPT	( ( unsigned portBASE_TYPE ) 5 )
#define intqQUEUE_LENGTH		( ( unsigned portBASE_TYPE ) 10 )

/* At least intqMIN_ACCEPTABLE_TASK_COUNT values should be sent to/received
from each queue by each task, otherwise an error is detected. */
#define intqMIN_ACCEPTABLE_TASK_COUNT		( 5 )

/* Send the next value to the queue that is normally empty.  This is called
from within the interrupts. */
#define timerNORMALLY_EMPTY_TX()																							\
	if( xQueueIsQueueFullFromISR( xNormallyEmptyQueue ) != pdTRUE )															\
	{																														\
	unsigned portBASE_TYPE uxSavedInterruptStatus;																			\
		uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();															\
		{																													\
			xQueueSendFromISR( xNormallyEmptyQueue, ( void * ) &uxValueForNormallyEmptyQueue, &xHigherPriorityTaskWoken );	\
			uxValueForNormallyEmptyQueue++;																					\
		}																													\
		portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus );														\
	}																														\

/* Send the next value to the queue that is normally full.  This is called
from within the interrupts. */
#define timerNORMALLY_FULL_TX()																								\
	if( xQueueIsQueueFullFromISR( xNormallyFullQueue ) != pdTRUE )															\
	{																														\
	unsigned portBASE_TYPE uxSavedInterruptStatus;																			\
		uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();															\
		{																													\
			xQueueSendFromISR( xNormallyFullQueue, ( void * ) &uxValueForNormallyFullQueue, &xHigherPriorityTaskWoken ); 	\
			uxValueForNormallyFullQueue++;																					\
		}																													\
		portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus );														\
	}																														\

/* Receive a value from the normally empty queue.  This is called from within 
an interrupt. */
#define timerNORMALLY_EMPTY_RX()																			\
	if( xQueueReceiveFromISR( xNormallyEmptyQueue, &uxRxedValue, &xHigherPriorityTaskWoken ) != pdPASS )	\
	{																										\
		prvQueueAccessLogError( __LINE__ );																	\
	}																										\
	else																									\
	{																										\
		prvRecordValue_NormallyEmpty( uxRxedValue, intqSECOND_INTERRUPT );									\
	}

/* Receive a value from the normally full queue.  This is called from within 
an interrupt. */
#define timerNORMALLY_FULL_RX()																				\
	if( xQueueReceiveFromISR( xNormallyFullQueue, &uxRxedValue, &xHigherPriorityTaskWoken ) == pdPASS )		\
	{																										\
		prvRecordValue_NormallyFull( uxRxedValue, intqSECOND_INTERRUPT );									\
	}																										\


/*-----------------------------------------------------------*/

/* The two queues used by the test. */
static xQueueHandle xNormallyEmptyQueue, xNormallyFullQueue;

/* Variables used to detect a stall in one of the tasks. */
static unsigned portBASE_TYPE uxHighPriorityLoops1 = 0, uxHighPriorityLoops2 = 0, uxLowPriorityLoops1 = 0, uxLowPriorityLoops2 = 0;

/* Any unexpected behaviour sets xErrorStatus to fail and log the line that
caused the error in xErrorLine. */
static portBASE_TYPE xErrorStatus = pdPASS;
static unsigned portBASE_TYPE xErrorLine = ( unsigned portBASE_TYPE ) 0;

/* Used for sequencing between tasks. */
static portBASE_TYPE xWasSuspended = pdFALSE;

/* The values that are sent to the queues.  An incremented value is sent each
time to each queue. */
volatile unsigned portBASE_TYPE uxValueForNormallyEmptyQueue = 0, uxValueForNormallyFullQueue = 0;

/* A handle to some of the tasks is required so they can be suspended/resumed. */
xTaskHandle xHighPriorityNormallyEmptyTask1, xHighPriorityNormallyEmptyTask2, xHighPriorityNormallyFullTask1, xHighPriorityNormallyFullTask2;

/* When a value is received in a queue the value is ticked off in the array
the array position of the value is set to a the identifier of the task or 
interrupt that accessed the queue.  This way missing or duplicate values can be 
detected. */
static unsigned portCHAR ucNormallyEmptyReceivedValues[ intqNUM_VALUES_TO_LOG ] = { 0 };
static unsigned portCHAR ucNormallyFullReceivedValues[ intqNUM_VALUES_TO_LOG ] = { 0 };

/* The test tasks themselves. */
static void prvLowerPriorityNormallyEmptyTask( void *pvParameters );
static void prvLowerPriorityNormallyFullTask( void *pvParameters );
static void prvHigherPriorityNormallyEmptyTask( void *pvParameters );
static void prv1stHigherPriorityNormallyFullTask( void *pvParameters );
static void prv2ndHigherPriorityNormallyFullTask( void *pvParameters );

/* Used to mark the positions within the ucNormallyEmptyReceivedValues and
ucNormallyFullReceivedValues arrays, while checking for duplicates. */
static void prvRecordValue_NormallyEmpty( unsigned portBASE_TYPE uxValue, unsigned portBASE_TYPE uxSource );
static void prvRecordValue_NormallyFull( unsigned portBASE_TYPE uxValue, unsigned portBASE_TYPE uxSource );

/* Logs the line on which an error occurred. */
static void prvQueueAccessLogError( unsigned portBASE_TYPE uxLine );

/*-----------------------------------------------------------*/

void vStartInterruptQueueTasks( void )
{
	/* Start the test tasks. */
	xTaskCreate( prvHigherPriorityNormallyEmptyTask, ( signed portCHAR * ) "H1QRx", configMINIMAL_STACK_SIZE, ( void * ) intqHIGH_PRIORITY_TASK1, intqHIGHER_PRIORITY, &xHighPriorityNormallyEmptyTask1 );
	xTaskCreate( prvHigherPriorityNormallyEmptyTask, ( signed portCHAR * ) "H2QRx", configMINIMAL_STACK_SIZE, ( void * ) intqHIGH_PRIORITY_TASK2, intqHIGHER_PRIORITY, &xHighPriorityNormallyEmptyTask2 );
	xTaskCreate( prvLowerPriorityNormallyEmptyTask, ( signed portCHAR * ) "LQRx", configMINIMAL_STACK_SIZE, NULL, intqLOWER_PRIORITY, NULL );
	xTaskCreate( prv1stHigherPriorityNormallyFullTask, ( signed portCHAR * ) "H1QTx", configMINIMAL_STACK_SIZE, ( void * ) intqHIGH_PRIORITY_TASK1, intqHIGHER_PRIORITY, &xHighPriorityNormallyFullTask1 );
	xTaskCreate( prv2ndHigherPriorityNormallyFullTask, ( signed portCHAR * ) "H1QTx", configMINIMAL_STACK_SIZE, ( void * ) intqHIGH_PRIORITY_TASK2, intqHIGHER_PRIORITY, &xHighPriorityNormallyFullTask2 );
	xTaskCreate( prvLowerPriorityNormallyFullTask, ( signed portCHAR * ) "LQRx", configMINIMAL_STACK_SIZE, NULL, intqLOWER_PRIORITY, NULL );

	/* Create the queues that are accessed by multiple tasks and multiple 
	interrupts. */
	xNormallyFullQueue = xQueueCreate( intqQUEUE_LENGTH, ( unsigned portBASE_TYPE ) sizeof( unsigned portBASE_TYPE ) );
	xNormallyEmptyQueue = xQueueCreate( intqQUEUE_LENGTH, ( unsigned portBASE_TYPE ) sizeof( unsigned portBASE_TYPE ) );

	/* vQueueAddToRegistry() adds the queue to the queue registry, if one is
	in use.  The queue registry is provided as a means for kernel aware 
	debuggers to locate queues and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is 
	defined to be less than 1. */
	vQueueAddToRegistry( xNormallyFullQueue, ( signed portCHAR * ) "NormallyFull" );
	vQueueAddToRegistry( xNormallyEmptyQueue, ( signed portCHAR * ) "NormallyEmpty" );

}
/*-----------------------------------------------------------*/

static void prvRecordValue_NormallyFull( unsigned portBASE_TYPE uxValue, unsigned portBASE_TYPE uxSource )
{
	if( uxValue < intqNUM_VALUES_TO_LOG )
	{
		/* We don't expect to receive the same value twice, so if the value
		has already been marked as received an error has occurred. */
		if( ucNormallyFullReceivedValues[ uxValue ] != 0x00 )
		{
			prvQueueAccessLogError( __LINE__ );
		}
		
		/* Log that this value has been received. */
		ucNormallyFullReceivedValues[ uxValue ] = uxSource;
	}
}
/*-----------------------------------------------------------*/

static void prvRecordValue_NormallyEmpty( unsigned portBASE_TYPE uxValue, unsigned portBASE_TYPE uxSource )
{
	if( uxValue < intqNUM_VALUES_TO_LOG )
	{
		/* We don't expect to receive the same value twice, so if the value
		has already been marked as received an error has occurred. */
		if( ucNormallyEmptyReceivedValues[ uxValue ] != 0x00 )
		{
			prvQueueAccessLogError( __LINE__ );
		}
		
		/* Log that this value has been received. */
		ucNormallyEmptyReceivedValues[ uxValue ] = uxSource;
	}
}
/*-----------------------------------------------------------*/

static void prvQueueAccessLogError( unsigned portBASE_TYPE uxLine )
{
	/* Latch the line number that caused the error. */
	xErrorLine = uxLine;
	xErrorStatus = pdFAIL;
}
/*-----------------------------------------------------------*/

static void prvHigherPriorityNormallyEmptyTask( void *pvParameters )
{
unsigned portBASE_TYPE uxRxed, ux, uxTask1, uxTask2;

	/* The timer should not be started until after the scheduler has started. 
	More than one task is running this code so we check the parameter value
	to determine which task should start the timer. */
	if( ( unsigned portBASE_TYPE ) pvParameters == intqHIGH_PRIORITY_TASK1 )
	{
		vInitialiseTimerForIntQueueTest();
	}

	for( ;; )
	{
		/* Block waiting to receive a value from the normally empty queue.
		Interrupts will write to the queue so we should receive a value. */
		if( xQueueReceive( xNormallyEmptyQueue, &uxRxed, intqSHORT_DELAY ) != pdPASS )
		{
			prvQueueAccessLogError( __LINE__ );
		}
		else
		{
			/* Note which value was received so we can check all expected
			values are received and no values are duplicated. */
			prvRecordValue_NormallyEmpty( uxRxed, ( unsigned portBASE_TYPE ) pvParameters );
		}
		
		/* Ensure the other task running this code gets a chance to execute. */
		taskYIELD();
		
		if( ( unsigned portBASE_TYPE ) pvParameters == intqHIGH_PRIORITY_TASK1 )
		{
			/* Have we received all the expected values? */
			if( uxValueForNormallyEmptyQueue > ( intqNUM_VALUES_TO_LOG + intqVALUE_OVERRUN ) )
			{
				vTaskSuspend( xHighPriorityNormallyEmptyTask2 );
				
				uxTask1 = 0;
				uxTask2 = 0;
		
				/* Loop through the array, checking that both tasks have
				placed values into the array, and that no values are missing. */
				for( ux = 0; ux < intqNUM_VALUES_TO_LOG; ux++ )
				{
					if( ucNormallyEmptyReceivedValues[ ux ] == 0 )
					{
						/* A value is missing. */
						prvQueueAccessLogError( __LINE__ );
					}
					else
					{
						if( ucNormallyEmptyReceivedValues[ ux ] == intqHIGH_PRIORITY_TASK1 )
						{
							/* Value was placed into the array by task 1. */
							uxTask1++;
						}
						else if( ucNormallyEmptyReceivedValues[ ux ] == intqHIGH_PRIORITY_TASK2 )
						{
							/* Value was placed into the array by task 2. */
							uxTask2++;
						}
					}
				}
				
				if( uxTask1 < intqMIN_ACCEPTABLE_TASK_COUNT )
				{
					/* Only task 2 seemed to log any values. */
					prvQueueAccessLogError( __LINE__ );
				}
				
				if( uxTask2 < intqMIN_ACCEPTABLE_TASK_COUNT  )
				{
					/* Only task 1 seemed to log any values. */
					prvQueueAccessLogError( __LINE__ );
				}

				/* Clear the array again, ready to start a new cycle. */
				memset( ucNormallyEmptyReceivedValues, 0x00, sizeof( ucNormallyEmptyReceivedValues ) );
				
				uxHighPriorityLoops1++;
				uxValueForNormallyEmptyQueue = 0;

				/* Suspend ourselves, allowing the lower priority task to 
				actually receive something from the queue.  Until now it
				will have been prevented from doing so by the higher
				priority tasks.  The lower priority task will resume us
				if it receives something.  We will then resume the other
				higher priority task. */
				vTaskSuspend( NULL );		
				vTaskResume( xHighPriorityNormallyEmptyTask2 );
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvLowerPriorityNormallyEmptyTask( void *pvParameters )
{
unsigned portBASE_TYPE uxValue, uxRxed;
portBASE_TYPE xQueueStatus;

	/* The parameters are not being used so avoid compiler warnings. */
	( void ) pvParameters;
	
	for( ;; )
	{	
		if( ( xQueueStatus = xQueueReceive( xNormallyEmptyQueue, &uxRxed, intqONE_TICK_DELAY ) ) != errQUEUE_EMPTY )
		{
			/* We should only obtain a value when the high priority task is
			suspended. */
			if( xTaskIsTaskSuspended( xHighPriorityNormallyEmptyTask1 ) == pdFALSE )
			{
				prvQueueAccessLogError( __LINE__ );
			}

			prvRecordValue_NormallyEmpty( uxRxed, intqLOW_PRIORITY_TASK );
			
			/* Wake the higher priority task again. */
			vTaskResume( xHighPriorityNormallyEmptyTask1 );
			uxLowPriorityLoops1++;
		}
		else
		{
			/* Raise our priority while we send so we can preempt the higher
			priority task, and ensure we get the Tx value into the queue. */
			vTaskPrioritySet( NULL, intqHIGHER_PRIORITY + 1 );
			
			portENTER_CRITICAL();
			{
				uxValue = uxValueForNormallyEmptyQueue;
				uxValueForNormallyEmptyQueue++;
			}
			portEXIT_CRITICAL();
			
			if( xQueueSend( xNormallyEmptyQueue, &uxValue, portMAX_DELAY ) != pdPASS )
			{
				prvQueueAccessLogError( __LINE__ );
			}
			
			vTaskPrioritySet( NULL, intqLOWER_PRIORITY );
		}
	}
}
/*-----------------------------------------------------------*/

static void prv1stHigherPriorityNormallyFullTask( void *pvParameters )
{
unsigned portBASE_TYPE uxValueToTx, ux;
portBASE_TYPE xQueueStatus;

	/* The parameters are not being used so avoid compiler warnings. */
	( void ) pvParameters;
	
	/* Make sure the queue starts full or near full.  >> 1 as there are two
	high priority tasks. */
	for( ux = 0; ux < ( intqQUEUE_LENGTH >> 1 ); ux++ )
	{
		portENTER_CRITICAL();
		{
			uxValueToTx = uxValueForNormallyFullQueue;
			uxValueForNormallyFullQueue++;
		}
		portEXIT_CRITICAL();

		xQueueSend( xNormallyFullQueue, &uxValueToTx, intqSHORT_DELAY );		
	}

	for( ;; )
	{
		portENTER_CRITICAL();
		{
			uxValueToTx = uxValueForNormallyFullQueue;
			uxValueForNormallyFullQueue++;
		}
		portEXIT_CRITICAL();

		if( ( xQueueStatus = xQueueSend( xNormallyFullQueue, &uxValueToTx, intqSHORT_DELAY ) ) != pdPASS )
		{
			/* intqHIGH_PRIORITY_TASK2 is never suspended so we would not 
			expect it to ever time out. */
			prvQueueAccessLogError( __LINE__ );
		}

		/* Allow the other task running this code to run. */
		taskYIELD();
		
		/* Have all the expected values been sent to the queue? */
		if( uxValueToTx > ( intqNUM_VALUES_TO_LOG + intqVALUE_OVERRUN ) )
		{
			/* Make sure the other high priority task completes its send of
			any values below intqNUM_VALUE_TO_LOG. */
			vTaskDelay( intqSHORT_DELAY );
			
			vTaskSuspend( xHighPriorityNormallyFullTask2 );
			
			if( xWasSuspended == pdTRUE )
			{
				/* We would have expected the other high priority task to have
				set this back to false by now. */
				prvQueueAccessLogError( __LINE__ );
			}
			
			/* Set the suspended flag so an error is not logged if the other
			task recognises a time out when it is unsuspended. */
			xWasSuspended = pdTRUE;
	
			for( ux = 0; ux < intqNUM_VALUES_TO_LOG; ux++ )
			{
				if( ucNormallyFullReceivedValues[ ux ] == 0 )
				{
					/* A value was missing. */
					prvQueueAccessLogError( __LINE__ );
				}
			}				

			/* Reset the array ready for the next cycle. */
			memset( ucNormallyFullReceivedValues, 0x00, sizeof( ucNormallyFullReceivedValues ) );				
			
			uxHighPriorityLoops2++;
			uxValueForNormallyFullQueue = 0;

			/* Suspend ourselves, allowing the lower priority task to 
			actually receive something from the queue.  Until now it
			will have been prevented from doing so by the higher
			priority tasks.  The lower priority task will resume us
			if it receives something.  We will then resume the other
			higher priority task. */
			vTaskSuspend( NULL );	
			vTaskResume( xHighPriorityNormallyFullTask2 );
		}
	}
}
/*-----------------------------------------------------------*/

static void prv2ndHigherPriorityNormallyFullTask( void *pvParameters )
{
unsigned portBASE_TYPE uxValueToTx, ux;
portBASE_TYPE xQueueStatus;

	/* The parameters are not being used so avoid compiler warnings. */
	( void ) pvParameters;
	
	/* Make sure the queue starts full or near full.  >> 1 as there are two
	high priority tasks. */
	for( ux = 0; ux < ( intqQUEUE_LENGTH >> 1 ); ux++ )
	{
		portENTER_CRITICAL();
		{
			uxValueToTx = uxValueForNormallyFullQueue;
			uxValueForNormallyFullQueue++;
		}
		portEXIT_CRITICAL();

		xQueueSend( xNormallyFullQueue, &uxValueToTx, intqSHORT_DELAY );		
	}

	for( ;; )
	{
		portENTER_CRITICAL();
		{
			uxValueToTx = uxValueForNormallyFullQueue;
			uxValueForNormallyFullQueue++;
		}
		portEXIT_CRITICAL();

		if( ( xQueueStatus = xQueueSend( xNormallyFullQueue, &uxValueToTx, intqSHORT_DELAY ) ) != pdPASS )
		{
			if( xWasSuspended != pdTRUE )
			{
				/* It is ok to time out if the task has been suspended. */
				prvQueueAccessLogError( __LINE__ );
			}
		}

		xWasSuspended = pdFALSE;
		
		taskYIELD();
	}
}
/*-----------------------------------------------------------*/

static void prvLowerPriorityNormallyFullTask( void *pvParameters )
{
unsigned portBASE_TYPE uxValue, uxTxed = 9999;
portBASE_TYPE xQueueStatus;

	/* The parameters are not being used so avoid compiler warnings. */
	( void ) pvParameters;
	
	for( ;; )
	{	
		if( ( xQueueStatus = xQueueSend( xNormallyFullQueue, &uxTxed, intqONE_TICK_DELAY ) ) != errQUEUE_FULL )
		{
			/* We would only expect to succeed when the higher priority task
			is suspended. */
			if( xTaskIsTaskSuspended( xHighPriorityNormallyFullTask1 ) == pdFALSE )
			{
				prvQueueAccessLogError( __LINE__ );
			}

			vTaskResume( xHighPriorityNormallyFullTask1 );
			uxLowPriorityLoops2++;
		}
		else
		{
			/* Raise our priority while we receive so we can preempt the higher
			priority task, and ensure we get the value from the queue. */
			vTaskPrioritySet( NULL, intqHIGHER_PRIORITY + 1 );
			
			if( xQueueReceive( xNormallyFullQueue, &uxValue, portMAX_DELAY ) != pdPASS )
			{
				prvQueueAccessLogError( __LINE__ );
			}
			else
			{
				prvRecordValue_NormallyFull( uxValue, intqLOW_PRIORITY_TASK );
			}
			
			vTaskPrioritySet( NULL, intqLOWER_PRIORITY );
		}
	}
}
/*-----------------------------------------------------------*/

portBASE_TYPE xFirstTimerHandler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE, uxRxedValue;
static unsigned portBASE_TYPE uxNextOperation = 0;

	/* Called from a timer interrupt.  Perform various read and write
	accesses on the queues. */

	uxNextOperation++;
	
	if( uxNextOperation & ( unsigned portBASE_TYPE ) 0x01 )
	{
		timerNORMALLY_EMPTY_TX();
		timerNORMALLY_EMPTY_TX();	
		timerNORMALLY_EMPTY_TX();
	}
	else
	{
		timerNORMALLY_FULL_RX();
		timerNORMALLY_FULL_RX();
		timerNORMALLY_FULL_RX();
	}
	
	return xHigherPriorityTaskWoken;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSecondTimerHandler( void )
{
unsigned portBASE_TYPE uxRxedValue;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
static unsigned portBASE_TYPE uxNextOperation = 0;

	/* Called from a timer interrupt.  Perform various read and write
	accesses on the queues. */

	uxNextOperation++;
	
	if( uxNextOperation & ( unsigned portBASE_TYPE ) 0x01 )
	{
		timerNORMALLY_EMPTY_TX();
		timerNORMALLY_EMPTY_TX();

		timerNORMALLY_EMPTY_RX();
		timerNORMALLY_EMPTY_RX();
	}
	else
	{	
		timerNORMALLY_FULL_RX();
		timerNORMALLY_FULL_TX();
		timerNORMALLY_FULL_TX();
		timerNORMALLY_FULL_TX();
		timerNORMALLY_FULL_TX();
	}
	
	return xHigherPriorityTaskWoken;
}
/*-----------------------------------------------------------*/


portBASE_TYPE xAreIntQueueTasksStillRunning( void )
{
static unsigned portBASE_TYPE uxLastHighPriorityLoops1 = 0, uxLastHighPriorityLoops2 = 0, uxLastLowPriorityLoops1 = 0, uxLastLowPriorityLoops2 = 0;
	
	/* xErrorStatus can be set outside of this function.  This function just
	checks that all the tasks are still cycling. */

	if( uxHighPriorityLoops1 == uxLastHighPriorityLoops1 )
	{
		/* The high priority 1 task has stalled. */
		prvQueueAccessLogError( __LINE__ );
	}
	
	uxLastHighPriorityLoops1 = uxHighPriorityLoops1;
	
	if( uxHighPriorityLoops2 == uxLastHighPriorityLoops2 )
	{
		/* The high priority 2 task has stalled. */
		prvQueueAccessLogError( __LINE__ );
	}
	
	uxLastHighPriorityLoops2 = uxHighPriorityLoops2;
	
	if( uxLowPriorityLoops1 == uxLastLowPriorityLoops1 )
	{
		/* The low priority 1 task has stalled. */
		prvQueueAccessLogError( __LINE__ );
	}

	uxLastLowPriorityLoops1 = uxLowPriorityLoops1;

	if( uxLowPriorityLoops2 == uxLastLowPriorityLoops2 )
	{
		/* The low priority 2 task has stalled. */
		prvQueueAccessLogError( __LINE__ );
	}

	uxLastLowPriorityLoops2 = uxLowPriorityLoops2;

	return xErrorStatus;
}

