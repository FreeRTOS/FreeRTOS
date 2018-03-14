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

/* Standard includes. */
#include "stdio.h"
#include "string.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "stream_buffer.h"

/* Demo app includes. */
#include "StreamBufferDemo.h"

/* The number of bytes of storage in the stream buffers used in this test. */
#define sbSTREAM_BUFFER_LENGTH_BYTES	( ( size_t ) 30 )

/* Start and end ASCII characters used in data sent to the buffers. */
#define sbASCII_SPACE					32
#define sbASCII_TILDA					126

/* Defines the number of tasks to create in this test and demo. */
#define sbNUMBER_OF_ECHO_CLIENTS	( 2 )
#define sbNUMBER_OF_SENDER_TASKS	( 2 )

/* Priority of the test tasks.  The send and receive go from low to high
priority tasks, and from high to low priority tasks. */
#define sbLOWER_PRIORITY			( tskIDLE_PRIORITY )
#define sbHIGHER_PRIORITY			( tskIDLE_PRIORITY + 1 )

/* Block times used when sending and receiving from the stream buffers. */
#define sbRX_TX_BLOCK_TIME			pdMS_TO_TICKS( 125UL )

/* A block time of 0 means "don't block". */
#define sbDONT_BLOCK				( 0 )

/* The trigger level sets the number of bytes that must be present in the
stream buffer before a task that is blocked on the stream buffer is moved out of
the Blocked state so it can read the bytes. */
#define sbTRIGGER_LEVEL_1			( 1 )

/* The size of the stack allocated to the tasks that run as part of this demo/
test.  The stack size is over generous in most cases. */
#define sbSTACK_SIZE				( configMINIMAL_STACK_SIZE + ( configMINIMAL_STACK_SIZE >> 1 ) )

/*-----------------------------------------------------------*/

/*
 * Performs various tests that do not require multiple tasks to interact.
 */
static void prvSingleTaskTests( StreamBufferHandle_t xStreamBuffer );

/*
 * Tests sending and receiving various lengths of data via a stream buffer.
 * The echo client sends the data to the echo server, which then sends the
 * data back to the echo client, which checks it receives exactly what it
 * sent.
 */
static void prvEchoClient( void *pvParameters );
static void prvEchoServer( void *pvParameters );

/*
 * Tasks that send and receive to a stream buffer at a low priority and without
 * blocking, so the send and receive functions interleave in time as the tasks
 * are switched in and out.
 */
static void prvNonBlockingReceiverTask( void *pvParameters );
static void prvNonBlockingSenderTask( void *pvParameters );

/* Performs an assert() like check in a way that won't get removed when
performing a code coverage analysis. */
static void prvCheckExpectedState( BaseType_t xState );

/*
 * A task that creates a stream buffer with a specific trigger level, then
 * receives a string from an interrupt (the RTOS tick hook) byte by byte to
 * check it is only unblocked when the specified trigger level is reached.
 */
static void prvInterruptTriggerLevelTest( void *pvParameters );

#if( configSUPPORT_STATIC_ALLOCATION == 1  )
	/* This file tests both statically and dynamically allocated stream buffers.
	Allocate the structures and buffers to be used by the statically allocated
	objects, which get used in the echo tests. */
	static void prvReceiverTask( void *pvParameters );
	static void prvSenderTask( void *pvParameters );

	static StaticStreamBuffer_t xStaticStreamBuffers[ sbNUMBER_OF_ECHO_CLIENTS ];
	static uint8_t ucBufferStorage[ sbNUMBER_OF_SENDER_TASKS ][ sbSTREAM_BUFFER_LENGTH_BYTES + 1 ];
	static uint32_t ulSenderLoopCounters[ sbNUMBER_OF_SENDER_TASKS ] = { 0 };
#endif /* configSUPPORT_STATIC_ALLOCATION */

/*-----------------------------------------------------------*/

/* The buffers used by the echo client and server tasks. */
typedef struct ECHO_STREAM_BUFFERS
{
	/* Handles to the data structures that describe the stream buffers. */
	StreamBufferHandle_t xEchoClientBuffer;
	StreamBufferHandle_t xEchoServerBuffer;
} EchoStreamBuffers_t;
static volatile uint32_t ulEchoLoopCounters[ sbNUMBER_OF_ECHO_CLIENTS ] = { 0 };

/* The non-blocking tasks monitor their operation, and if no errors have been
found, increment ulNonBlockingRxCounter.  xAreStreamBufferTasksStillRunning()
then checks ulNonBlockingRxCounter and only returns pdPASS if
ulNonBlockingRxCounter is still incrementing. */
static volatile uint32_t ulNonBlockingRxCounter = 0;

/* The task that receives characters from the tick interrupt in order to test
different trigger levels monitors its own behaviour.  If it has not detected any
error then it increments ulInterruptTriggerCounter to indicate to the check task
that it is still operating correctly. */
static volatile uint32_t ulInterruptTriggerCounter = 0UL;

/* The stream buffer used from the tick interrupt.  This sends one byte at a time
to a test task to test the trigger level operation.  The variable is set to NULL
in between test runs. */
static volatile StreamBufferHandle_t xInterruptStreamBuffer = NULL;

/* The data sent from the tick interrupt to the task that tests the trigger
level functionality. */
static const char *pcDataSentFromInterrupt = "12345678";

/* Data that is longer than the buffer that is sent to the buffers as a stream
of bytes.  Parts of which are written to the stream buffer to test writing
different lengths at different offsets, to many bytes, part streams, streams
that wrap, etc..  Two messages are defined to ensure left over data is not
accidentally read out of the buffer. */
static const char *pc55ByteString = "One two three four five six seven eight nine ten eleven";
static const char *pc54ByteString = "01234567891abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQ";

/* Used to log the status of the tests contained within this file for reporting
to a monitoring task ('check' task). */
static BaseType_t xErrorStatus = pdPASS;

/*-----------------------------------------------------------*/

void vStartStreamBufferTasks( void )
{
StreamBufferHandle_t xStreamBuffer;

	/* The echo servers sets up the stream buffers before creating the echo
	client tasks.  One set of tasks has the server as the higher priority, and
	the other has the client as the higher priority. */
	xTaskCreate( prvEchoServer, "1StrEchoServer", sbSTACK_SIZE, NULL, sbHIGHER_PRIORITY, NULL );
	xTaskCreate( prvEchoServer, "2StrEchoServer", sbSTACK_SIZE, NULL, sbLOWER_PRIORITY, NULL );

	/* The non blocking tasks run continuously and will interleave with each
	other, so must be created at the lowest priority.  The stream buffer they
	use is created and passed in using the task's parameter. */
	xStreamBuffer = xStreamBufferCreate( sbSTREAM_BUFFER_LENGTH_BYTES, sbTRIGGER_LEVEL_1 );
	xTaskCreate( prvNonBlockingReceiverTask, "StrNonBlkRx", configMINIMAL_STACK_SIZE, ( void * ) xStreamBuffer, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvNonBlockingSenderTask, "StrNonBlkTx", configMINIMAL_STACK_SIZE, ( void * ) xStreamBuffer, tskIDLE_PRIORITY, NULL );

	/* The task that receives bytes from an interrupt to test that it unblocks
	at a specific trigger level must run at a high priority to minimise the risk
	of it receiving more characters before it can execute again after being
	unblocked. */
	xTaskCreate( prvInterruptTriggerLevelTest, "StrTrig", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, NULL );

	#if( configSUPPORT_STATIC_ALLOCATION == 1  )
	{
		/* The sender tasks set up the stream buffers before creating the
		receiver tasks.  Priorities must be 0 and 1 as the priority is used to
		index into the xStaticStreamBuffers and ucBufferStorage arrays. */
		xTaskCreate( prvSenderTask, "Str1Sender", sbSTACK_SIZE, NULL, sbHIGHER_PRIORITY, NULL );
		xTaskCreate( prvSenderTask, "Str2Sender", sbSTACK_SIZE, NULL, sbLOWER_PRIORITY, NULL );
	}
	#endif /* configSUPPORT_STATIC_ALLOCATION */
}
/*-----------------------------------------------------------*/

static void prvCheckExpectedState( BaseType_t xState )
{
	configASSERT( xState );
	if( xState == pdFAIL )
	{
		xErrorStatus = pdFAIL;
	}
}
/*-----------------------------------------------------------*/

static void prvSingleTaskTests( StreamBufferHandle_t xStreamBuffer )
{
size_t xReturned, xItem, xExpectedSpace;
const size_t xMax6ByteMessages = sbSTREAM_BUFFER_LENGTH_BYTES / 6;
const size_t x6ByteLength = 6, x17ByteLength = 17, xFullBufferSize = sbSTREAM_BUFFER_LENGTH_BYTES * ( size_t ) 2;
uint8_t *pucFullBuffer, *pucData, *pucReadData;
TickType_t xTimeBeforeCall, xTimeAfterCall;
const TickType_t xBlockTime = pdMS_TO_TICKS( 15 ), xAllowableMargin = pdMS_TO_TICKS( 3 ), xMinimalBlockTime = 2;
UBaseType_t uxOriginalPriority;

	/* Remove warning in case configASSERT() is not defined. */
	( void ) xAllowableMargin;

	/* To minimise stack and heap usage a full size buffer is allocated from the
	heap, then buffers which hold smaller amounts of data are overlayed with the
	larger buffer - just make sure not to use both at once! */
	pucFullBuffer = pvPortMalloc( xFullBufferSize );
	configASSERT( pucFullBuffer );

	pucData = pucFullBuffer;
	pucReadData = pucData + x17ByteLength;

	/* Nothing has been added or removed yet, so expect the free space to be
	exactly as created. */
	xExpectedSpace = xStreamBufferSpacesAvailable( xStreamBuffer );
	prvCheckExpectedState( xExpectedSpace == sbSTREAM_BUFFER_LENGTH_BYTES );
	prvCheckExpectedState( xStreamBufferIsEmpty( xStreamBuffer ) == pdTRUE );


	/* The buffer is 30 bytes long.  6 5 byte messages should fit before the
	buffer is completely full. */
	for( xItem = 0; xItem < xMax6ByteMessages; xItem++ )
	{
		prvCheckExpectedState( xStreamBufferIsFull( xStreamBuffer ) == pdFALSE );

		/* Generate recognisable data to write to the buffer.  This is just
		ascii characters that shows which loop iteration the data was written
		in. The 'FromISR' version is used to give it some exercise as a block
		time is not used, so the call must be inside a critical section so it
		runs with ports that don't support interrupt nesting (and therefore
		don't have interrupt safe critical sections). */
		memset( ( void * ) pucData, ( ( int ) '0' ) + ( int ) xItem, x6ByteLength );
		taskENTER_CRITICAL();
		{
			xReturned = xStreamBufferSendFromISR( xStreamBuffer, ( void * ) pucData, x6ByteLength, NULL );
		}
		taskEXIT_CRITICAL();
		prvCheckExpectedState( xReturned == x6ByteLength );

		/* The space in the buffer will have reduced by the amount of user data
		written into the buffer. */
		xExpectedSpace -= x6ByteLength;
		xReturned = xStreamBufferSpacesAvailable( xStreamBuffer );
		prvCheckExpectedState( xReturned == xExpectedSpace );
		xReturned = xStreamBufferBytesAvailable( xStreamBuffer );
		/* +1 as it is zero indexed. */
		prvCheckExpectedState( xReturned == ( ( xItem + 1 ) * x6ByteLength ) );
	}

	/* Now the buffer should be full, and attempting to add anything will should
	fail. */
	prvCheckExpectedState( xStreamBufferIsFull( xStreamBuffer ) == pdTRUE );
	xReturned = xStreamBufferSend( xStreamBuffer, ( void * ) pucData, sizeof( pucData[ 0 ] ), sbDONT_BLOCK );
	prvCheckExpectedState( xReturned == 0 );

	/* Adding with a timeout should also fail after the appropriate time.  The
	priority is temporarily boosted in this part of the test to keep the
	allowable margin to a minimum. */
	uxOriginalPriority = uxTaskPriorityGet( NULL );
	vTaskPrioritySet( NULL, configMAX_PRIORITIES - 1 );
	xTimeBeforeCall = xTaskGetTickCount();
	xReturned = xStreamBufferSend( xStreamBuffer, ( void * ) pucData, sizeof( pucData[ 0 ] ), xBlockTime );
	xTimeAfterCall = xTaskGetTickCount();
	vTaskPrioritySet( NULL, uxOriginalPriority );
	prvCheckExpectedState( ( xTimeAfterCall - xTimeBeforeCall ) >= xBlockTime );
	prvCheckExpectedState( ( xTimeAfterCall - xTimeBeforeCall ) < ( xBlockTime + xAllowableMargin ) );
	prvCheckExpectedState( xReturned == 0 );

	/* The buffer is now full of data in the form "000000", "111111", etc.  Make
	sure the data is read out as expected. */
	for( xItem = 0; xItem < xMax6ByteMessages; xItem++ )
	{
		/* Generate the data that is expected to be read out for this loop
		iteration. */
		memset( ( void * ) pucData, ( ( int ) '0' ) + ( int ) xItem, x6ByteLength );

		/* Read the next 6 bytes out.  The 'FromISR' version is used to give it
		some exercise as a block time is not used, so a it must be called from
		a critical section so this will work on ports that don't support
		interrupt nesting (so don't have interrupt safe critical sections). */
		taskENTER_CRITICAL();
		{
			xReturned = xStreamBufferReceiveFromISR( xStreamBuffer, ( void * ) pucReadData, x6ByteLength, NULL );
		}
		taskEXIT_CRITICAL();
		prvCheckExpectedState( xReturned == x6ByteLength );

		/* Does the data read out match that expected? */
		prvCheckExpectedState( memcmp( ( void * ) pucData, ( void * ) pucReadData, x6ByteLength ) == 0 );

		/* The space in the buffer will have increased by the amount of user
		data removed from the buffer. */
		xExpectedSpace += x6ByteLength;
		xReturned = xStreamBufferSpacesAvailable( xStreamBuffer );
		prvCheckExpectedState( xReturned == xExpectedSpace );
		xReturned = xStreamBufferBytesAvailable( xStreamBuffer );
		prvCheckExpectedState( xReturned == ( sbSTREAM_BUFFER_LENGTH_BYTES - xExpectedSpace ) );
	}

	/* The buffer should be empty again. */
	prvCheckExpectedState( xStreamBufferIsEmpty( xStreamBuffer ) == pdTRUE );
	xExpectedSpace = xStreamBufferSpacesAvailable( xStreamBuffer );
	prvCheckExpectedState( xExpectedSpace == sbSTREAM_BUFFER_LENGTH_BYTES );

	/* Reading with a timeout should also fail after the appropriate time.  The
	priority is temporarily boosted in this part of the test to keep the
	allowable margin to a minimum. */
	vTaskPrioritySet( NULL, configMAX_PRIORITIES - 1 );
	xTimeBeforeCall = xTaskGetTickCount();
	xReturned = xStreamBufferReceive( xStreamBuffer, ( void * ) pucReadData, x6ByteLength, xBlockTime );
	xTimeAfterCall = xTaskGetTickCount();
	vTaskPrioritySet( NULL, uxOriginalPriority );
	prvCheckExpectedState( ( xTimeAfterCall - xTimeBeforeCall ) >= xBlockTime );
	prvCheckExpectedState( ( xTimeAfterCall - xTimeBeforeCall ) < ( xBlockTime + xAllowableMargin ) );
	prvCheckExpectedState( xReturned == 0 );


	/* In the next loop 17 bytes are written to then read out on each
	iteration.  As 30 is not divisible by 17 the data will wrap around. */
	xExpectedSpace = sbSTREAM_BUFFER_LENGTH_BYTES - x17ByteLength;

	for( xItem = 0; xItem < 100; xItem++ )
	{
		/* Generate recognisable data to write to the queue.  This is just
		ascii characters that shows which loop iteration the data was written
		in. */
		memset( ( void * ) pucData, ( ( int ) '0' ) + ( int ) xItem, x17ByteLength );
		xReturned = xStreamBufferSend( xStreamBuffer, ( void * ) pucData, x17ByteLength, sbDONT_BLOCK );
		prvCheckExpectedState( xReturned == x17ByteLength );

		/* The space in the buffer will have reduced by the amount of user data
		written into the buffer. */
		xReturned = xStreamBufferSpacesAvailable( xStreamBuffer );
		prvCheckExpectedState( xReturned == xExpectedSpace );
		xReturned = xStreamBufferBytesAvailable( xStreamBuffer );
		prvCheckExpectedState( xReturned == x17ByteLength );
		prvCheckExpectedState( xStreamBufferIsFull( xStreamBuffer ) == pdFALSE );
		prvCheckExpectedState( xStreamBufferIsEmpty( xStreamBuffer ) == pdFALSE );

		/* Read the 17 bytes out again. */
		xReturned = xStreamBufferReceive( xStreamBuffer, ( void * ) pucReadData, x17ByteLength, sbDONT_BLOCK );
		prvCheckExpectedState( xReturned == x17ByteLength );

		/* Does the data read out match that expected? */
		prvCheckExpectedState( memcmp( ( void * ) pucData, ( void * ) pucReadData, x17ByteLength ) == 0 );

		/* Full buffer space available again. */
		xReturned = xStreamBufferSpacesAvailable( xStreamBuffer );
		prvCheckExpectedState( xReturned == sbSTREAM_BUFFER_LENGTH_BYTES );
		xReturned = xStreamBufferBytesAvailable( xStreamBuffer );
		prvCheckExpectedState( xReturned == 0 );
		prvCheckExpectedState( xStreamBufferIsFull( xStreamBuffer ) == pdFALSE );
		prvCheckExpectedState( xStreamBufferIsEmpty( xStreamBuffer ) == pdTRUE );
	}

	/* Fill the buffer with one message, check it is full, then read it back
	again and check the correct data is received. */
	xStreamBufferSend( xStreamBuffer, ( const void * ) pc55ByteString, sbSTREAM_BUFFER_LENGTH_BYTES, sbDONT_BLOCK );
	xStreamBufferReceive( xStreamBuffer, ( void * ) pucFullBuffer, sbSTREAM_BUFFER_LENGTH_BYTES, sbDONT_BLOCK );
	prvCheckExpectedState( memcmp( pc55ByteString, pucFullBuffer, sbSTREAM_BUFFER_LENGTH_BYTES ) == 0 );

	/* Fill the buffer one bytes at a time. */
	for( xItem = 0; xItem < sbSTREAM_BUFFER_LENGTH_BYTES; xItem++ )
	{
		/* Block time is only for test coverage, the task should never actually
		block here. */
		xStreamBufferSend( xStreamBuffer, ( const void * ) &( pc54ByteString[ xItem ] ), sizeof( char ), sbRX_TX_BLOCK_TIME );
	}

	/* The buffer should now be full. */
	prvCheckExpectedState( xStreamBufferIsFull( xStreamBuffer ) == pdTRUE );

	/* Read the message out in one go, even though it was written in individual
	bytes.  Try reading much more data than is actually available to ensure only
	the available bytes are returned (otherwise this read will write outside of
	the memory allocated anyway!). */
	xReturned = xStreamBufferReceive( xStreamBuffer, pucFullBuffer, sbSTREAM_BUFFER_LENGTH_BYTES * ( size_t ) 2, sbRX_TX_BLOCK_TIME );
	prvCheckExpectedState( xReturned == sbSTREAM_BUFFER_LENGTH_BYTES );
	prvCheckExpectedState( memcmp( ( const void * ) pc54ByteString, ( const void * ) pucFullBuffer, sbSTREAM_BUFFER_LENGTH_BYTES ) == 0 );

	/* Now do the opposite, write in one go and read out in single bytes. */
	xReturned = xStreamBufferSend( xStreamBuffer, ( const void * ) pc55ByteString, sbSTREAM_BUFFER_LENGTH_BYTES, sbRX_TX_BLOCK_TIME );
	prvCheckExpectedState( xReturned == sbSTREAM_BUFFER_LENGTH_BYTES );
	prvCheckExpectedState( xStreamBufferIsFull( xStreamBuffer ) == pdTRUE );
	prvCheckExpectedState( xStreamBufferIsEmpty( xStreamBuffer ) == pdFALSE );
	prvCheckExpectedState( xStreamBufferBytesAvailable( xStreamBuffer ) == sbSTREAM_BUFFER_LENGTH_BYTES );
	prvCheckExpectedState( xStreamBufferSpacesAvailable( xStreamBuffer ) == 0 );

	/* Read from the buffer one byte at a time. */
	for( xItem = 0; xItem < sbSTREAM_BUFFER_LENGTH_BYTES; xItem++ )
	{
		/* Block time is only for test coverage, the task should never actually
		block here. */
		xStreamBufferReceive( xStreamBuffer, ( void * ) pucFullBuffer, sizeof( char ), sbRX_TX_BLOCK_TIME );
		prvCheckExpectedState( pc55ByteString[ xItem ] == pucFullBuffer[ 0 ] );
	}
	prvCheckExpectedState( xStreamBufferIsEmpty( xStreamBuffer ) == pdTRUE );
	prvCheckExpectedState( xStreamBufferIsFull( xStreamBuffer ) == pdFALSE );

	/* Try writing more bytes than there is space. */
	vTaskPrioritySet( NULL, configMAX_PRIORITIES - 1 );
	xTimeBeforeCall = xTaskGetTickCount();
	xReturned = xStreamBufferSend( xStreamBuffer, ( const void * ) pc54ByteString, sbSTREAM_BUFFER_LENGTH_BYTES * ( size_t ) 2, xMinimalBlockTime );
	xTimeAfterCall = xTaskGetTickCount();
	vTaskPrioritySet( NULL, uxOriginalPriority );
	prvCheckExpectedState( ( xTimeAfterCall - xTimeBeforeCall ) >= xMinimalBlockTime );
	prvCheckExpectedState( ( xTimeAfterCall - xTimeBeforeCall ) < ( xMinimalBlockTime + xAllowableMargin ) );
	prvCheckExpectedState( xReturned == sbSTREAM_BUFFER_LENGTH_BYTES );
	prvCheckExpectedState( xStreamBufferIsFull( xStreamBuffer ) == pdTRUE );
	prvCheckExpectedState( xStreamBufferIsEmpty( xStreamBuffer ) == pdFALSE );

	/* No space now though. */
	xReturned = xStreamBufferSend( xStreamBuffer, ( const void * ) pc54ByteString, sbSTREAM_BUFFER_LENGTH_BYTES * ( size_t ) 2, xMinimalBlockTime );
	prvCheckExpectedState( xReturned == 0 );

	/* Ensure data was written as expected even when there was an attempt to
	write more than was available.  This also tries to read more bytes than are
	available. */
	xReturned = xStreamBufferReceive( xStreamBuffer, ( void * ) pucFullBuffer, xFullBufferSize, xMinimalBlockTime );
	prvCheckExpectedState( memcmp( ( const void * ) pucFullBuffer, ( const void * ) pc54ByteString, sbSTREAM_BUFFER_LENGTH_BYTES ) == 0 );
	prvCheckExpectedState( xStreamBufferIsFull( xStreamBuffer ) == pdFALSE );
	prvCheckExpectedState( xStreamBufferIsEmpty( xStreamBuffer ) == pdTRUE );

	/* Clean up with data in the buffer to ensure the tests that follow don't
	see the data (the data should be discarded). */
	( void ) xStreamBufferSend( xStreamBuffer, ( const void * ) pc55ByteString, sbSTREAM_BUFFER_LENGTH_BYTES / ( size_t ) 2, sbDONT_BLOCK );
	vPortFree( pucFullBuffer );
	xStreamBufferReset( xStreamBuffer );
}
/*-----------------------------------------------------------*/

static void prvNonBlockingSenderTask( void *pvParameters )
{
StreamBufferHandle_t xStreamBuffer;
size_t xNextChar = 0, xBytesToSend, xBytesActuallySent;
const size_t xStringLength = strlen( pc54ByteString );

	/* In this case the stream buffer has already been created and is passed
	into the task using the task's parameter. */
	xStreamBuffer = ( StreamBufferHandle_t ) pvParameters;

	/* Keep sending the string to the stream buffer as many bytes as possible in
	each go.  Doesn't block so calls can interleave with the non-blocking
	receives performed by prvNonBlockingReceiverTask(). */
	for( ;; )
	{
		/* The whole string cannot be sent at once, so xNextChar is an index to
		the position within the string that has been sent so far.  How many
		bytes are there left to send before the end of the string? */
		xBytesToSend = xStringLength - xNextChar;

		/* Attempt to send right up to the end of the string. */
		xBytesActuallySent = xStreamBufferSend( xStreamBuffer, ( const void * ) &( pc54ByteString[ xNextChar ] ), xBytesToSend, sbDONT_BLOCK );
		prvCheckExpectedState( xBytesActuallySent <= xBytesToSend );

		/* Move the index up the string to the next character to be sent,
		wrapping if the end of the string has been reached. */
		xNextChar += xBytesActuallySent;
		prvCheckExpectedState( xNextChar <= xStringLength );

		if( xNextChar == xStringLength )
		{
			xNextChar = 0;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvNonBlockingReceiverTask( void *pvParameters )
{
StreamBufferHandle_t xStreamBuffer;
size_t xNextChar = 0, xReceiveLength, xBytesToTest, xStartIndex;
const size_t xStringLength = strlen( pc54ByteString );
char cRxString[ 12 ]; /* Holds received characters. */
BaseType_t xNonBlockingReceiveError = pdFALSE;

	/* In this case the stream buffer has already been created and is passed
	into the task using the task's parameter. */
	xStreamBuffer = ( StreamBufferHandle_t ) pvParameters;

	/* Expects to receive the pc54ByteString over and over again.  Sends and
	receives are not blocking so will interleave. */
	for( ;; )
	{
		/* Attempt to receive as many bytes as possible, up to the limit of the
		Rx buffer size. */
		xReceiveLength = xStreamBufferReceive( xStreamBuffer, ( void * ) cRxString, sizeof( cRxString ), sbDONT_BLOCK );

		if( xReceiveLength > 0 )
		{
			/* xNextChar is the index into pc54ByteString that has been received
			already.  If xReceiveLength bytes are added to that, will it go off
			the end of the string?  If so, then first test up to the end of the
			string, then go back to the start of pc54ByteString to test the
			remains of the received data. */
			xBytesToTest = xReceiveLength;
			if( ( xNextChar + xBytesToTest ) > xStringLength )
			{
				/* Cap to test the received data to the end of the string. */
				xBytesToTest = xStringLength - xNextChar;

				if( memcmp( ( const void * ) &( pc54ByteString[ xNextChar ] ), ( const void * ) cRxString, xBytesToTest ) != 0 )
				{
					xNonBlockingReceiveError = pdTRUE;
				}

				/* Then move back to the start of the string to test the
				remaining received bytes. */
				xNextChar = 0;
				xStartIndex = xBytesToTest;
				xBytesToTest = xReceiveLength - xBytesToTest;
			}
			else
			{
				/* The string didn't wrap in the buffer, so start comparing from
				the start of the received data. */
				xStartIndex = 0;
			}

			/* Test the received bytes are as expected, then move the index
			along the string to the next expected char to receive. */
			if( memcmp( ( const void * ) &( pc54ByteString[ xNextChar ] ), ( const void * ) &( cRxString[ xStartIndex ] ), xBytesToTest ) != 0 )
			{
				xNonBlockingReceiveError = pdTRUE;
			}

			if( xNonBlockingReceiveError == pdFALSE )
			{
				/* No errors detected so increment the counter that lets the
				check task know this test is still functioning correctly. */
				ulNonBlockingRxCounter++;
			}

			xNextChar += xBytesToTest;
			if( xNextChar >= xStringLength )
			{
				xNextChar = 0;
			}
		}
	}
}
/*-----------------------------------------------------------*/

#if( configSUPPORT_STATIC_ALLOCATION == 1  )

	static void prvSenderTask( void *pvParameters )
	{
	StreamBufferHandle_t xStreamBuffer, xTempStreamBuffer;
	static uint8_t ucTempBuffer[ 10 ]; /* Just used to exercise stream buffer creating and deletion. */
	const TickType_t xTicksToWait = sbRX_TX_BLOCK_TIME, xShortDelay = pdMS_TO_TICKS( 50 );
	StaticStreamBuffer_t xStaticStreamBuffer;
	size_t xNextChar = 0, xBytesToSend, xBytesActuallySent;
	const size_t xStringLength = strlen( pc55ByteString );

	/* The task's priority is used as an index into the loop counters used to
	indicate this task is still running. */
	UBaseType_t uxIndex = uxTaskPriorityGet( NULL );

		/* Make sure a change in priority does not inadvertently result in an
		invalid array index. */
		prvCheckExpectedState( uxIndex < sbNUMBER_OF_ECHO_CLIENTS );

		/* Avoid compiler warnings about unused parameters. */
		( void ) pvParameters;

		xStreamBuffer = xStreamBufferCreateStatic( sizeof( ucBufferStorage ) / sbNUMBER_OF_SENDER_TASKS, /* The number of bytes in each buffer in the array. */
												   sbTRIGGER_LEVEL_1, /* The number of bytes to be in the buffer before a task blocked to wait for data is unblocked. */
												   &( ucBufferStorage[ uxIndex ][ 0 ] ), /* The address of the buffer to use within the array. */
												   &( xStaticStreamBuffers[ uxIndex ] ) ); /* The static stream buffer structure to use within the array. */

		/* Now the stream buffer has been created the receiver task can be
		created.  If this sender task has the higher priority then the receiver
		task is created at the lower priority - if this sender task has the
		lower priority then the receiver task is created at the higher
		priority. */
		if( uxTaskPriorityGet( NULL ) == sbLOWER_PRIORITY )
		{
			/* Here prvSingleTaskTests() performs various tests on a stream buffer
			that was created statically. */
			prvSingleTaskTests( xStreamBuffer );
			xTaskCreate( prvReceiverTask, "StrReceiver", sbSTACK_SIZE,  ( void * ) xStreamBuffer, sbHIGHER_PRIORITY, NULL );
		}
		else
		{
			xTaskCreate( prvReceiverTask, "StrReceiver", sbSTACK_SIZE,  ( void * ) xStreamBuffer, sbLOWER_PRIORITY, NULL );
		}

		for( ;; )
		{
			/* The whole string cannot be sent at once, so xNextChar is an index
			to the position within the string that has been sent so far.  How
			many bytes are there left to send before the end of the string? */
			xBytesToSend = xStringLength - xNextChar;

			/* Attempt to send right up to the end of the string. */
			xBytesActuallySent = xStreamBufferSend( xStreamBuffer, ( const void * ) &( pc55ByteString[ xNextChar ] ), xBytesToSend, xTicksToWait );
			prvCheckExpectedState( xBytesActuallySent <= xBytesToSend );

			/* Move the index up the string to the next character to be sent,
			wrapping if the end of the string has been reached. */
			xNextChar += xBytesActuallySent;
			prvCheckExpectedState( xNextChar <= xStringLength );

			if( xNextChar == xStringLength )
			{
				xNextChar = 0;
			}

			/* Increment a loop counter so a check task can tell this task is
			still running as expected. */
			ulSenderLoopCounters[ uxIndex ]++;

			if( uxTaskPriorityGet( NULL ) == sbHIGHER_PRIORITY )
			{
				/* Allow other tasks to run. */
				vTaskDelay( xShortDelay );
			}

			/* This stream buffer is just created and deleted to ensure no
			issues when attempting to delete a stream buffer that was
			created using statically allocated memory.  To save stack space
			the buffer is set to point to the pc55ByteString, which is a const
			string, but no data is written into the buffer so any valid address
			will do. */
			xTempStreamBuffer = xStreamBufferCreateStatic( sizeof( ucTempBuffer ), sbTRIGGER_LEVEL_1, ucTempBuffer, &xStaticStreamBuffer );
			vStreamBufferDelete( xTempStreamBuffer );
		}
	}

#endif /* configSUPPORT_STATIC_ALLOCATION */
/*-----------------------------------------------------------*/

#if( configSUPPORT_STATIC_ALLOCATION == 1  )

	static void prvReceiverTask( void *pvParameters )
	{
	StreamBufferHandle_t * const pxStreamBuffer = ( StreamBufferHandle_t * ) pvParameters;
	char cRxString[ 12 ]; /* Large enough to hold a 32-bit number in ASCII. */
	const TickType_t xTicksToWait = pdMS_TO_TICKS( 5UL );
	const size_t xStringLength = strlen( pc55ByteString );
	size_t xNextChar = 0, xReceivedLength, xBytesToReceive;

		for( ;; )
		{
			/* Attempt to receive the number of bytes to the end of the string,
			or the number of byte that can be placed into the rx buffer,
			whichever is smallest. */
			xBytesToReceive = configMIN( ( xStringLength - xNextChar ), sizeof( cRxString ) );

			do
			{
				xReceivedLength = xStreamBufferReceive( pxStreamBuffer, ( void * ) cRxString, xBytesToReceive, xTicksToWait );

			} while( xReceivedLength == 0 );

			/* Ensure the received string matches the expected string. */
			prvCheckExpectedState( memcmp( ( void * ) cRxString, ( const void * ) &( pc55ByteString[ xNextChar ] ), xReceivedLength ) == 0 );

			/* Move the index into the string up to the end of the bytes
			received so far - wrapping if the end of the string has been
			reached. */
			xNextChar += xReceivedLength;
			if( xNextChar >= xStringLength )
			{
				xNextChar = 0;
			}
		}
	}

#endif /* configSUPPORT_STATIC_ALLOCATION */
/*-----------------------------------------------------------*/

static void prvEchoClient( void *pvParameters )
{
size_t xSendLength = 0, ux;
char *pcStringToSend, *pcStringReceived, cNextChar = sbASCII_SPACE;
const TickType_t xTicksToWait = pdMS_TO_TICKS( 50 );
StreamBufferHandle_t xTempStreamBuffer;

/* The task's priority is used as an index into the loop counters used to
indicate this task is still running. */
UBaseType_t uxIndex = uxTaskPriorityGet( NULL );

/* Pointers to the client and server stream buffers are passed into this task
using the task's parameter. */
EchoStreamBuffers_t *pxStreamBuffers = ( EchoStreamBuffers_t * ) pvParameters;

	/* Prevent compiler warnings. */
	( void ) pvParameters;

	/* Create the buffer into which strings to send to the server will be
	created, and the buffer into which strings echoed back from the server will
	be copied. */
	pcStringToSend = ( char * ) pvPortMalloc( sbSTREAM_BUFFER_LENGTH_BYTES );
	pcStringReceived = ( char * ) pvPortMalloc( sbSTREAM_BUFFER_LENGTH_BYTES );

	configASSERT( pcStringToSend );
	configASSERT( pcStringReceived );

	for( ;; )
	{
		/* Generate the length of the next string to send. */
		xSendLength++;

		/* The stream buffer is being used to hold variable length data, so
		each data item requires sizeof( size_t ) bytes to hold the data's
		length, hence the sizeof() in the if() condition below. */
		if( xSendLength > ( sbSTREAM_BUFFER_LENGTH_BYTES - sizeof( size_t ) ) )
		{
			/* Back to a string length of 1. */
			xSendLength = sizeof( char );
		}

		memset( pcStringToSend, 0x00, sbSTREAM_BUFFER_LENGTH_BYTES );

		for( ux = 0; ux < xSendLength; ux++ )
		{
			pcStringToSend[ ux ] = cNextChar;

			cNextChar++;

			if( cNextChar > sbASCII_TILDA )
			{
				cNextChar = sbASCII_SPACE;
			}
		}

		/* Send the generated string to the buffer. */
		do
		{
			ux = xStreamBufferSend( pxStreamBuffers->xEchoClientBuffer, ( void * ) pcStringToSend, xSendLength, xTicksToWait );

		} while( ux == 0 );

		/* Wait for the string to be echoed back. */
		memset( pcStringReceived, 0x00, sbSTREAM_BUFFER_LENGTH_BYTES );
		xStreamBufferReceive( pxStreamBuffers->xEchoServerBuffer, ( void * ) pcStringReceived, xSendLength, portMAX_DELAY );

		prvCheckExpectedState( strcmp( pcStringToSend, pcStringReceived ) == 0 );

		/* Maintain a count of the number of times this code executes so a
		check task can determine if this task is still functioning as
		expected or not.  As there are two client tasks, and the priorities
		used are 0 and 1, the task's priority is used as an index into the
		loop count array. */
		ulEchoLoopCounters[ uxIndex ]++;

		/* This stream buffer is just created and deleted to ensure no memory
		leaks. */
		xTempStreamBuffer = xStreamBufferCreate( sbSTREAM_BUFFER_LENGTH_BYTES, sbTRIGGER_LEVEL_1 );
		prvSingleTaskTests( xTempStreamBuffer );
		vStreamBufferDelete( xTempStreamBuffer );
	}
}
/*-----------------------------------------------------------*/

static void prvEchoServer( void *pvParameters )
{
size_t xReceivedLength;
char *pcReceivedString;
EchoStreamBuffers_t xStreamBuffers;
TickType_t xTimeOnEntering;
const TickType_t xTicksToBlock = pdMS_TO_TICKS( 350UL );

	/* Prevent compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* Create the stream buffer used to send data from the client to the server,
	and the stream buffer used to echo the data from the server back to the
	client. */
	xStreamBuffers.xEchoClientBuffer = xStreamBufferCreate( sbSTREAM_BUFFER_LENGTH_BYTES, sbTRIGGER_LEVEL_1 );
	xStreamBuffers.xEchoServerBuffer = xStreamBufferCreate( sbSTREAM_BUFFER_LENGTH_BYTES, sbTRIGGER_LEVEL_1 );
	configASSERT( xStreamBuffers.xEchoClientBuffer );
	configASSERT( xStreamBuffers.xEchoServerBuffer );

	/* Create the buffer into which received strings will be copied. */
	pcReceivedString = ( char * ) pvPortMalloc( sbSTREAM_BUFFER_LENGTH_BYTES );
	configASSERT( pcReceivedString );

	/* Don't expect to receive anything yet! */
	xTimeOnEntering = xTaskGetTickCount();
	xReceivedLength = xStreamBufferReceive( xStreamBuffers.xEchoClientBuffer, ( void * ) pcReceivedString, sbSTREAM_BUFFER_LENGTH_BYTES, xTicksToBlock );
	prvCheckExpectedState( ( xTaskGetTickCount() - xTimeOnEntering ) >= xTicksToBlock );
	prvCheckExpectedState( xReceivedLength == 0 );

	/* Now the stream buffers have been created the echo client task can be
	created.  If this server task has the higher priority then the client task
	is created at the lower priority - if this server task has the lower
	priority then the client task is created at the higher priority. */
	if( uxTaskPriorityGet( NULL ) == sbLOWER_PRIORITY )
	{
		xTaskCreate( prvEchoClient, "EchoClient", sbSTACK_SIZE,  ( void * ) &xStreamBuffers, sbHIGHER_PRIORITY, NULL );
	}
	else
	{
		/* Here prvSingleTaskTests() performs various tests on a stream buffer
		that was created dynamically. */
		prvSingleTaskTests( xStreamBuffers.xEchoClientBuffer );
		xTaskCreate( prvEchoClient, "EchoClient", sbSTACK_SIZE, ( void * ) &xStreamBuffers, sbLOWER_PRIORITY, NULL );
	}

	for( ;; )
	{
		memset( pcReceivedString, 0x00, sbSTREAM_BUFFER_LENGTH_BYTES );

		/* Has any data been sent by the client? */
		xReceivedLength = xStreamBufferReceive( xStreamBuffers.xEchoClientBuffer, ( void * ) pcReceivedString, sbSTREAM_BUFFER_LENGTH_BYTES, xTicksToBlock );

		/* Should always receive data as a delay was used. */
		prvCheckExpectedState( xReceivedLength > 0 );

		/* Echo the received data back to the client. */
		xStreamBufferSend( xStreamBuffers.xEchoServerBuffer, ( void * ) pcReceivedString, xReceivedLength, portMAX_DELAY );
	}
}
/*-----------------------------------------------------------*/

void vPeriodicStreamBufferProcessing( void )
{
static size_t xNextChar = 0;
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	/* Called from the tick interrupt hook.  If the global stream buffer
	variable is not NULL then the prvInterruptTriggerTest() task expects a byte
	to be sent to the stream buffer on each tick interrupt. */
	if( xInterruptStreamBuffer != NULL )
	{
		/* One character from the pcDataSentFromInterrupt string is sent on each
		interrupt.  The task blocked on the stream buffer should not be
		unblocked until the defined trigger level is hit. */
		xStreamBufferSendFromISR( xInterruptStreamBuffer, ( const void * ) &( pcDataSentFromInterrupt[ xNextChar ] ), sizeof( char ), &xHigherPriorityTaskWoken );

		if( xNextChar < strlen( pcDataSentFromInterrupt ) )
		{
			xNextChar++;
		}
	}
	else
	{
		/* Start at the beginning of the string being sent again. */
		xNextChar = 0;
	}
}
/*-----------------------------------------------------------*/

static void prvInterruptTriggerLevelTest( void *pvParameters )
{
StreamBufferHandle_t xStreamBuffer;
size_t xTriggerLevel = 1, xBytesReceived;
const size_t xStreamBufferSizeBytes = ( size_t ) 8, xMaxTriggerLevel = ( size_t ) 6, xMinTriggerLevel = ( size_t ) 1;
const TickType_t xReadBlockTime = 4, xCycleBlockTime = pdMS_TO_TICKS( 100 );
uint8_t ucRxData[ 8 ];
BaseType_t xErrorDetected = pdFALSE;
#ifndef configSTREAM_BUFFER_TRIGGER_LEVEL_TEST_MARGIN
    const size_t xAllowableMargin = ( size_t ) 0;
#else
    const size_t xAllowableMargin = ( size_t ) configSTREAM_BUFFER_TRIGGER_LEVEL_TEST_MARGIN;
#endif

	/* Remove compiler warning about unused parameter. */
	( void ) pvParameters;

	for( ;; )
	{
		for( xTriggerLevel = xMinTriggerLevel; xTriggerLevel < xMaxTriggerLevel; xTriggerLevel++ )
		{
			/* Create the stream buffer that will be used from inside the tick
			interrupt. */
			xStreamBuffer = xStreamBufferCreate( xStreamBufferSizeBytes, xTriggerLevel );
			configASSERT( xStreamBuffer );

			/* Now the stream buffer has been created it can be assigned to the
			file scope variable, which will allow the tick interrupt to start
			using it. */
			taskENTER_CRITICAL();
			{
				xInterruptStreamBuffer = xStreamBuffer;
			}
			taskEXIT_CRITICAL();

			xBytesReceived = xStreamBufferReceive( xStreamBuffer, ( void * ) ucRxData, sizeof( ucRxData ), xReadBlockTime );

			/* Set the file scope variable back to NULL so the interrupt doesn't
			try to use it again. */
			taskENTER_CRITICAL();
			{
				xInterruptStreamBuffer = NULL;
			}
			taskEXIT_CRITICAL();

			/* Now check the number of bytes received equals the trigger level,
			except in the case that the read timed out before the trigger level
			was reached. */
			if( xBytesReceived < xTriggerLevel )
			{
				/* This should only happen if the trigger level was greater than
				the block time. */
				if( xTriggerLevel < xReadBlockTime )
				{
					xErrorDetected = pdTRUE;
				}
			}
			else if( ( xBytesReceived - xTriggerLevel ) > xAllowableMargin )
			{
				/* A margin may be required here if there are other high priority
				tasks prevent the task that reads from the message buffer running
				immediately. */
				xErrorDetected = pdTRUE;
			}

			if( xBytesReceived > sizeof( ucRxData ) )
			{
				xErrorDetected = pdTRUE;
			}
			else if( memcmp( ( void * ) ucRxData, ( const void * ) pcDataSentFromInterrupt, xBytesReceived ) != 0 )
			{
				/* Received data didn't match that expected. */
				xErrorDetected = pdTRUE;
			}

			if( xErrorDetected == pdFALSE )
			{
				/* Increment the cycle counter so the 'check' task knows this test
				is still running without error. */
				ulInterruptTriggerCounter++;
			}

			/* Tidy up ready for the next loop. */
			vStreamBufferDelete( xStreamBuffer );
			vTaskDelay( xCycleBlockTime );
		}
	}
}
/*-----------------------------------------------------------*/

BaseType_t xAreStreamBufferTasksStillRunning( void )
{
static uint32_t ulLastEchoLoopCounters[ sbNUMBER_OF_ECHO_CLIENTS ] = { 0 };
static uint32_t ulLastNonBlockingRxCounter = 0;
static uint32_t ulLastInterruptTriggerCounter = 0;
BaseType_t x;

	for( x = 0; x < sbNUMBER_OF_ECHO_CLIENTS; x++ )
	{
		if( ulLastEchoLoopCounters[ x ] == ulEchoLoopCounters[ x ] )
		{
			xErrorStatus = pdFAIL;
		}
		else
		{
			ulLastEchoLoopCounters[ x ] = ulEchoLoopCounters[ x ];
		}
	}

	if( ulNonBlockingRxCounter == ulLastNonBlockingRxCounter )
	{
		xErrorStatus = pdFAIL;
	}
	else
	{
		ulLastNonBlockingRxCounter = ulNonBlockingRxCounter;
	}

	if( ulLastInterruptTriggerCounter == ulInterruptTriggerCounter )
	{
		xErrorStatus = pdFAIL;
	}
	else
	{
		ulLastInterruptTriggerCounter = ulInterruptTriggerCounter;
	}

	#if( configSUPPORT_STATIC_ALLOCATION == 1 )
	{
		static uint32_t ulLastSenderLoopCounters[ sbNUMBER_OF_ECHO_CLIENTS ] = { 0 };

		for( x = 0; x < sbNUMBER_OF_SENDER_TASKS; x++ )
		{
			if( ulLastSenderLoopCounters[ x ] == ulSenderLoopCounters[ x ] )
			{
				xErrorStatus = pdFAIL;
			}
			else
			{
				ulLastSenderLoopCounters[ x ] = ulSenderLoopCounters[ x ];
			}
		}
	}
	#endif /* configSUPPORT_STATIC_ALLOCATION */

	return xErrorStatus;
}
/*-----------------------------------------------------------*/

