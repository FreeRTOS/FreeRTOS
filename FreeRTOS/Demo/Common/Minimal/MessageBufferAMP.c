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

/*
 * An example that mimics a message buffer being used to pass data from one core
 * to another.  The core that sends the data is referred to as core A.  The core
 * that receives the data is referred to as core B.  The task implemented by
 * prvCoreATask() runs on core A.  Two instances of the task implemented by
 * prvCoreBTasks() run on core B.  prvCoreATask() sends messages via message
 * buffers to both instances of prvCoreBTasks(), one message buffer per channel.
 * A third message buffer is used to pass the handle of the message buffer
 * written to by core A to an interrupt service routine that is triggered by
 * core A but executes on core B.
 *
 * The example relies on the FreeRTOS provided default implementation of
 * sbSEND_COMPLETED() being overridden by an implementation in FreeRTOSConfig.h
 * that writes the handle of the message buffer that contains data into the
 * control message buffer, then generates an interrupt in core B.  The necessary
 * implementation is provided in this file and can be enabled by adding the
 * following to FreeRTOSConfig.h:
 *
 * #define sbSEND_COMPLETED( pxStreamBuffer ) vGenerateCoreBInterrupt( pxStreamBuffer )
 *
 * Core to core communication via message buffer requires the message buffers
 * to be at an address known to both cores within shared memory.
 *
 * Note that, while this example uses three message buffers, the same
 * functionality can be implemented using a single message buffer by using the
 * same design pattern described on the link below for queues, but using message
 * buffers instead.  It is actually simpler with a message buffer as variable
 * length data can be written into the message buffer directly:
 * http://www.freertos.org/Pend-on-multiple-rtos-objects.html#alternative_design_pattern
 */

/* Standard includes. */
#include "stdio.h"
#include "string.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "message_buffer.h"

/* Demo app includes. */
#include "MessageBufferAMP.h"

/* Enough for 3 4 byte pointers, including the additional 4 bytes per message
overhead of message buffers. */
#define mbaCONTROL_MESSAGE_BUFFER_SIZE ( 24 )

/* Enough four 4 8 byte strings, plus the additional 4 bytes per message
overhead of message buffers. */
#define mbaTASK_MESSAGE_BUFFER_SIZE ( 60 )

/* The number of instances of prvCoreBTasks that are created. */
#define mbaNUMBER_OF_CORE_B_TASKS	2

/* A block time of 0 simply means, don't block. */
#define mbaDONT_BLOCK				0

/* Macro that mimics an interrupt service routine executing by simply calling
the routine inline. */
#define mbaGENERATE_CORE_B_INTERRUPT() prvCoreBInterruptHandler()

/*-----------------------------------------------------------*/

/*
 * Implementation of the task that, on a real dual core device, would run on
 * core A and send message to tasks running on core B.
 */
static void prvCoreATask( void *pvParameters );

/*
 * Implementation of the task that, on a real dual core device, would run on
 * core B and receive message from core A.  The demo creates two instances of
 * this task.
 */
static void prvCoreBTasks( void *pvParameters );

/*
 * The function that, on a real dual core device, would handle inter-core
 * interrupts, but in this case is just called inline.
 */
static void prvCoreBInterruptHandler( void );

/*-----------------------------------------------------------*/

/* The message buffers used to pass data from core A to core B. */
static MessageBufferHandle_t xCoreBMessageBuffers[ mbaNUMBER_OF_CORE_B_TASKS ];

/* The control message buffer.  This is used to pass the handle of the message
message buffer that holds application data into the core to core interrupt
service routine. */
static MessageBufferHandle_t xControlMessageBuffer;

/* Counters used to indicate to the check that the tasks are still executing. */
static uint32_t ulCycleCounters[ mbaNUMBER_OF_CORE_B_TASKS ];

/* Set to pdFALSE if any errors are detected.  Used to inform the check task
that something might be wrong. */
BaseType_t xDemoStatus = pdPASS;

/*-----------------------------------------------------------*/

void vStartMessageBufferAMPTasks( configSTACK_DEPTH_TYPE xStackSize )
{
BaseType_t x;

	xControlMessageBuffer = xMessageBufferCreate( mbaCONTROL_MESSAGE_BUFFER_SIZE );

	xTaskCreate( prvCoreATask,		/* The function that implements the task. */
				 "AMPCoreA",		/* Human readable name for the task. */
				 xStackSize,		/* Stack size (in words!). */
				 NULL,				/* Task parameter is not used. */
				 tskIDLE_PRIORITY,	/* The priority at which the task is created. */
				 NULL );			/* No use for the task handle. */

	for( x = 0; x < mbaNUMBER_OF_CORE_B_TASKS; x++ )
	{
		xCoreBMessageBuffers[ x ] = xMessageBufferCreate( mbaTASK_MESSAGE_BUFFER_SIZE );
		configASSERT( xCoreBMessageBuffers[ x ] );

		/* Pass the loop counter into the created task using the task's
		parameter.  The task then uses the value as an index into the
		ulCycleCounters and xCoreBMessageBuffers arrays. */
		xTaskCreate( prvCoreBTasks,
					 "AMPCoreB1",
					 xStackSize,
					 ( void * ) x,
					 tskIDLE_PRIORITY + 1,
					 NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvCoreATask( void *pvParameters )
{
BaseType_t x;
uint32_t ulNextValue = 0;
const TickType_t xDelay = pdMS_TO_TICKS( 250 );
char cString[ 15 ]; /* At least large enough to hold "4294967295\0" (0xffffffff). */

	/* Remove warning about unused parameters. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Create the next string to send.  The value is incremented on each
		loop iteration, and the length of the string changes as the number of
		digits in the value increases. */
		sprintf( cString, "%lu", ( unsigned long ) ulNextValue );

		/* Send the value from this (pseudo) Core A to the tasks on the (pseudo)
		Core B via the message buffers.  This will result in sbSEND_COMPLETED()
		being executed, which in turn will write the handle of the message
		buffer written to into xControlMessageBuffer then generate an interrupt
		in core B. */
		for( x = 0; x < mbaNUMBER_OF_CORE_B_TASKS; x++ )
		{
			xMessageBufferSend( /* The message buffer to write to. */
								xCoreBMessageBuffers[ x ],
								/* The source of the data to send. */
								( void * ) cString,
								/* The length of the data to send. */
								strlen( cString ),
								/* The block time, should the buffer be full. */
								mbaDONT_BLOCK );
		}

		/* Delay before repeating with a different and potentially different
		length string. */
		vTaskDelay( xDelay );
		ulNextValue++;
	}
}
/*-----------------------------------------------------------*/

static void prvCoreBTasks( void *pvParameters )
{
BaseType_t x;
size_t xReceivedBytes;
uint32_t ulNextValue = 0;
char cExpectedString[ 15 ]; /* At least large enough to hold "4294967295\0" (0xffffffff). */
char cReceivedString[ 15 ];

	/* The index into the xCoreBMessageBuffers and ulLoopCounter arrays is
	passed into this task using the task's parameter. */
	x = ( BaseType_t ) pvParameters;
	configASSERT( x < mbaNUMBER_OF_CORE_B_TASKS );

	for( ;; )
	{
		/* Create the string that is expected to be received this time round. */
		sprintf( cExpectedString, "%lu", ( unsigned long ) ulNextValue );

		/* Wait to receive the next message from core A. */
		memset( cReceivedString, 0x00, sizeof( cReceivedString ) );
		xReceivedBytes = xMessageBufferReceive( /* The message buffer to receive from. */
												xCoreBMessageBuffers[ x ],
												/* Location to store received data. */
												cReceivedString,
												/* Maximum number of bytes to receive. */
												sizeof( cReceivedString ),
												/* Ticks to wait if buffer is empty. */
												portMAX_DELAY );

		/* Check the number of bytes received was as expected. */
		configASSERT( xReceivedBytes == strlen( cExpectedString ) );
		( void ) xReceivedBytes; /* Incase configASSERT() is not defined. */

		/* If the received string matches that expected then increment the loop
		counter so the check task knows this task is still running. */
		if( strcmp( cReceivedString, cExpectedString ) == 0 )
		{
			( ulCycleCounters[ x ] )++;
		}
		else
		{
			xDemoStatus = pdFAIL;
		}

		/* Expect the next string in sequence the next time around. */
		ulNextValue++;
	}
}
/*-----------------------------------------------------------*/

/* Called by the reimplementation of sbSEND_COMPLETED(), which can be defined
as follows in FreeRTOSConfig.h:
#define sbSEND_COMPLETED( pxStreamBuffer ) vGenerateCoreBInterrupt( pxStreamBuffer )
*/
void vGenerateCoreBInterrupt( void * xUpdatedMessageBuffer )
{
MessageBufferHandle_t xUpdatedBuffer = ( MessageBufferHandle_t ) xUpdatedMessageBuffer;

	/* If sbSEND_COMPLETED() has been implemented as above, then this function
	is called from within xMessageBufferSend().  As this function also calls
	xMessageBufferSend() itself it is necessary to guard against a recursive
	call.  If the message buffer just updated is the message buffer written to
	by this function, then this is a recursive call, and the function can just
	exit without taking further action. */
	if( xUpdatedBuffer != xControlMessageBuffer )
	{
		/* Use xControlMessageBuffer to pass the handle of the message buffer
		written to by core A to the interrupt handler about to be generated in
		core B. */
		xMessageBufferSend( xControlMessageBuffer, &xUpdatedBuffer, sizeof( xUpdatedBuffer ), mbaDONT_BLOCK );

		/* This is where the interrupt would be generated.  In this case it is
		not a genuine interrupt handler that executes, just a standard function
		call. */
		mbaGENERATE_CORE_B_INTERRUPT();
	}
}
/*-----------------------------------------------------------*/

/* Handler for the interrupts that are triggered on core A but execute on core
B. */
static void prvCoreBInterruptHandler( void )
{
MessageBufferHandle_t xUpdatedMessageBuffer;
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	/* xControlMessageBuffer contains the handle of the message buffer that
	contains data. */
	if( xMessageBufferReceive( xControlMessageBuffer,
							   &xUpdatedMessageBuffer,
							   sizeof( xUpdatedMessageBuffer ),
							   mbaDONT_BLOCK ) == sizeof( xUpdatedMessageBuffer ) )
	{
		/* Call the API function that sends a notification to any task that is
		blocked on the xUpdatedMessageBuffer message buffer waiting for data to
		arrive. */
		xMessageBufferSendCompletedFromISR( xUpdatedMessageBuffer, &xHigherPriorityTaskWoken );
	}

	/* Normal FreeRTOS yield from interrupt semantics, where
	xHigherPriorityTaskWoken is initialzed to pdFALSE and will then get set to
	pdTRUE if the interrupt safe API unblocks a task that has a priority above
	that of the currently executing task. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

BaseType_t xAreMessageBufferAMPTasksStillRunning( void )
{
static uint32_t ulLastCycleCounters[ mbaNUMBER_OF_CORE_B_TASKS ] = { 0 };
BaseType_t x;

	/* Called by the check task to determine the health status of the tasks
	implemented in this demo. */
	for( x = 0; x < mbaNUMBER_OF_CORE_B_TASKS; x++ )
	{
		if( ulLastCycleCounters[ x ] == ulCycleCounters[ x ] )
		{
			xDemoStatus = pdFAIL;
		}
		else
		{
			ulLastCycleCounters[ x ] = ulCycleCounters[ x ];
		}
	}

	return xDemoStatus;
}

