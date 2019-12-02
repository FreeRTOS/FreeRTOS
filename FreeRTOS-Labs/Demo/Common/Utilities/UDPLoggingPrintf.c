/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

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
 * Logging utility that allows FreeRTOS tasks to log to a UDP port.
 *
 * Logging print calls generate messages that are buffered in a stream buffer.
 * A background task then retrieves messages from the stream buffer and sends
 * them to a UDP port.
 */

/* Standard includes. */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <limits.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_tcp_server.h"
#include "FreeRTOS_Stream_Buffer.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"

/* Demo includes. */
#include "hr_gettime.h"
#include "UDPLoggingPrintf.h"

/* Set to 1 to end each line with \r\n, or 0 for just \n. */
#ifndef configUDP_LOGGING_NEEDS_CR_LF
	#define configUDP_LOGGING_NEEDS_CR_LF  ( 0 )
#endif

/* The maximum string length for each logged message. */
#ifndef configUDP_LOGGING_STRING_LENGTH
	#define configUDP_LOGGING_STRING_LENGTH	( 200 )
#endif

/* The maximum number of messages that can be buffered at any one time. */
#ifndef configUDP_LOGGING_MAX_MESSAGES_IN_BUFFER
	#define	configUDP_LOGGING_MAX_MESSAGES_IN_BUFFER	( 30 )
#endif

#ifndef configUDP_LOGGING_TASK_STACK_SIZE
	#define	configUDP_LOGGING_TASK_STACK_SIZE  	( 512 )
#endif

#ifndef configUDP_LOGGING_TASK_PRIORITY
	#define configUDP_LOGGING_TASK_PRIORITY   	( tskIDLE_PRIORITY + 2 )
#endif

/* configUDP_LOGGING_PORT_REMOTE is the port number to which the logging
will be sent. */
#ifndef configUDP_LOGGING_PORT_REMOTE
	#error configUDP_LOGGING_PORT_REMOTE must be defined in FreeRTOSconfig.h to use UDP logging
#endif

/* configUDP_LOGGING_PORT_LOCAL is the port number to which the
socket will be bound. It is possible to send messages to
this socket. */
#ifndef configUDP_LOGGING_PORT_LOCAL
	/* If not defined, the UDP socket will be bound to a random port number.
	If you want to use a specific port number, please define so in FreeRTOSconfig.h */
	#define configUDP_LOGGING_PORT_LOCAL 0
#endif

/* The logging task's block time.  This is used as the UDP socket's send block
time, and the maximum time the logging task will spend in the Blocked state
waiting to be notified of a new message to send before manually looking for a
message. */
#ifndef	logUDP_LOGGING_BLOCK_TIME_MS
	#define logUDP_LOGGING_BLOCK_TIME_MS	( 1000ul )
#endif

/* Log messages are cached in a stream buffer.  The stream buffer's storage
area is dimensioned to contain the maximum number of strings of the maximum
string length. */
#define logMESSAGE_BUFFER_SIZE_BYTES  ( ( configUDP_LOGGING_STRING_LENGTH ) * ( configUDP_LOGGING_MAX_MESSAGES_IN_BUFFER ) )

/* Ascii characters used in this file. */
#define logASCII_CR 			( 13 )
#define logASCII_NL				( 10 )

#ifndef iptraceUDP_LOGGING_TASK_STARTING
	/* This macro will be called once when the UDP logging task is starting up. */
	#define	iptraceUDP_LOGGING_TASK_STARTING()	do { } while( 0 )
#endif
/*-----------------------------------------------------------*/

/*
 * Called automatically to create the stream buffer.
 */
static BaseType_t prvInitialiseLogging( void );

/*
 * The task that reads messages from the stream buffer and sends them to the
 * UDP port.
 */
static void prvLoggingTask( void *pvParameters );

/*
 * Obtain a message from the stream buffer.
 */
static size_t prvGetMessageFromStreamBuffer( char *pcBuffer, size_t xBufferLength );

/*
 * Generate a formatted string and add it to the stream buffer ready for the
 * logging task to transmit.
 */
static size_t prvBufferFormattedString( const char *pcFormatString, va_list xArgs );

/*-----------------------------------------------------------*/

/* Is this structure used anywhere? */
typedef struct LogStruct
{
	size_t xLength;

	#if LOGBUF_SHOW_US
		uint64_t ullLogTime;
	#else
		uint32_t ulLogTime;
	#endif
	uint32_t ulPriority;

} LogStruct_t;

typedef struct LogUnit_t
{
	LogStruct_t xHeader;
	char cMessage[ configUDP_LOGGING_STRING_LENGTH ];

} LogUnit_t;

static LogUnit_t xLogEntry;
static StreamBuffer_t *pxStreamBuffer = NULL;
static TaskHandle_t xLoggingTask = NULL;
static xSocket_t xUDPLoggingSocket = FREERTOS_INVALID_SOCKET;

/*-----------------------------------------------------------*/

static BaseType_t prvInitialiseLogging( void )
{
size_t xSize;
static BaseType_t xLoggingInitialised = pdFALSE;

	if( xLoggingInitialised == pdFALSE )
	{
		/* Don't attempt to log unless the scheduler is running. */
		if( xTaskGetSchedulerState() == taskSCHEDULER_RUNNING )
		{
			/* Create a stream buffer large enough for the maximum number of
			bytes + 1. */ /*_RB_ Why is the size of pxStreamBuffer->ucArray
			subtracted here? */
			xSize = sizeof( StreamBuffer_t ) - sizeof( pxStreamBuffer->ucArray ) + logMESSAGE_BUFFER_SIZE_BYTES + 1;
			pxStreamBuffer = pvPortMalloc( xSize );

			if( pxStreamBuffer != NULL )
			{
				memset( pxStreamBuffer, '\0', xSize );
				pxStreamBuffer->LENGTH = logMESSAGE_BUFFER_SIZE_BYTES + 1;

				xLoggingInitialised = pdTRUE;
			}
		}
	}

	return xLoggingInitialised;
}
/*-----------------------------------------------------------*/

static size_t prvGetMessageFromStreamBuffer( char* pcBuffer, size_t xBufferLength )
{
size_t uxLength;
size_t xMessageLength = 0;

	if( pxStreamBuffer != NULL )
	{
		/* Is there data in the stream buffer? */
		uxLength = uxStreamBufferGetSize( pxStreamBuffer );
		if( uxLength > sizeof( size_t ) )
		{
			/* Avoid concurrent access to the buffer. */
			vTaskSuspendAll();
			{
				/* Every message is stored as a length followed by the string.
				Obtain the length of the data first. */
				uxStreamBufferGet( pxStreamBuffer, 0, ( uint8_t * ) &xMessageLength, sizeof( xMessageLength ), pdFALSE );

				if( xBufferLength < xMessageLength )
				{
					/* The 'pcBuffer' provided by the caller is too small.  Load
					the message first into 'xLogEntry.message', and then copy
					as much as possible to 'pcBuffer'. */
					uxStreamBufferGet( pxStreamBuffer, 0, ( uint8_t * ) xLogEntry.cMessage, xMessageLength, pdFALSE );
					memcpy( pcBuffer, xLogEntry.cMessage, xBufferLength );
					xMessageLength = xBufferLength;

					/* Terminate the string at the very end of the buffer. */
					pcBuffer[ xBufferLength - 1 ] = 0x00;
				}
				else
				{
					/* The 'pcBuffer' provided by the caller is big enough. */
					uxStreamBufferGet( pxStreamBuffer, 0, ( uint8_t * ) pcBuffer, xMessageLength, pdFALSE );

					/* Terminate the string after the string's last character. */
					pcBuffer[ xMessageLength ] = 0x00;
				}
			}
			xTaskResumeAll();
		}
	}

	return xMessageLength;
}
/*-----------------------------------------------------------*/

static size_t prvBufferFormattedString( const char *pcFormatString, va_list xArgs )
{
size_t xLength, xSpace;
uint64_t ullCurrentTime;
uint32_t ulSeconds, ulMilliSeconds, ulMicroSeconds;

	/* Sanity check. */
	configASSERT( pxStreamBuffer );

	vTaskSuspendAll();
	{
		ullCurrentTime = ullGetHighResolutionTime();
		ulSeconds = ( uint32_t ) ( ullCurrentTime / 1000000ull );
		ullCurrentTime = ullCurrentTime % 1000000ull;
		ulMilliSeconds = ( uint32_t ) ( ullCurrentTime / 1000ull );
		ulMicroSeconds = ( uint32_t ) ( ullCurrentTime % 1000ull );

		xLength = ( size_t ) snprintf( xLogEntry.cMessage, sizeof( xLogEntry.cMessage ), "%4u.%03u.%03u [%-10s] ",
			( unsigned int ) ulSeconds, ( unsigned int ) ulMilliSeconds, ( unsigned int ) ulMicroSeconds, pcTaskGetTaskName( NULL ) );
		xLength += ( size_t ) vsnprintf( xLogEntry.cMessage + xLength, sizeof( xLogEntry.cMessage ) - xLength, pcFormatString, xArgs );

		xSpace = uxStreamBufferGetSpace( pxStreamBuffer );

		if( xSpace > ( xLength + sizeof( BaseType_t ) ) )
		{
			uxStreamBufferAdd( pxStreamBuffer, 0, ( const uint8_t * ) &xLength, sizeof( xLength ) );
			uxStreamBufferAdd( pxStreamBuffer, 0, ( const uint8_t * ) ( xLogEntry.cMessage ), xLength );
		}
	}
	xTaskResumeAll();

	if( xLoggingTask != NULL )
	{
		/* Unblock the logging task so it can output the message. */
		xTaskNotifyGive( xLoggingTask );
	}

	return xLength;
}
/*-----------------------------------------------------------*/

int lUDPLoggingPrintf( const char *pcFormatString, ... )
{
size_t xLength;

	if( prvInitialiseLogging() != pdFALSE )
	{
		va_list args;
		va_start (args, pcFormatString);
		xLength = prvBufferFormattedString (pcFormatString, args);
		va_end (args);
	}
	else
	{
		xLength = 0;
	}

	return ( int ) xLength;
}
/*-----------------------------------------------------------*/

void vUDPLoggingTaskCreate( void )
{
	/* Start a task which will send out the logging lines to a UDP address. */
	xTaskCreate( prvLoggingTask, "LogTask", configUDP_LOGGING_TASK_STACK_SIZE, NULL, configUDP_LOGGING_TASK_PRIORITY, &xLoggingTask );
}
/*-----------------------------------------------------------*/

xSocket_t xLoggingGetSocket( void )
{
xSocket_t xReturn;

	if( ( xUDPLoggingSocket != NULL ) && ( xUDPLoggingSocket != FREERTOS_INVALID_SOCKET ) )
	{
		xReturn = xUDPLoggingSocket;
	}
	else
	{
		xReturn = NULL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void prvLoggingTask( void *pvParameters )
{
TickType_t xBlockingTime = pdMS_TO_TICKS( logUDP_LOGGING_BLOCK_TIME_MS );
struct freertos_sockaddr xLocalAddress, xRemoteAddress;
BaseType_t xSendTimeOut;
int32_t lLines;
size_t xCount;
static char cLoggingLine[ configUDP_LOGGING_STRING_LENGTH ];
const TickType_t xResolveDelay = pdMS_TO_TICKS( ( TickType_t ) 250 );

	/* Prevent compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* A possibility to set some additional task properties. */
	iptraceUDP_LOGGING_TASK_STARTING();

	xRemoteAddress.sin_port = FreeRTOS_htons( configUDP_LOGGING_PORT_REMOTE );
	#if defined( configUDP_LOGGING_ADDR0 )
	{
		/* Use a fixed address to where the logging will be sent. */
		xRemoteAddress.sin_addr = FreeRTOS_inet_addr_quick( configUDP_LOGGING_ADDR0,
															configUDP_LOGGING_ADDR1,
															configUDP_LOGGING_ADDR2,
															configUDP_LOGGING_ADDR3 );
	}
	#else
	{
		/* The logging will be broadcasted on the local broadcasting
		address, such as 192.168.0.255 */
		xRemoteAddress.sin_addr = FreeRTOS_GetIPAddress() | ~( FreeRTOS_GetNetmask() );
	}
	#endif

	/* Loop until a socket is created. */
	do
	{
		vTaskDelay( xBlockingTime );
		xUDPLoggingSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
	} while( xUDPLoggingSocket == FREERTOS_INVALID_SOCKET );

	xLocalAddress.sin_port = FreeRTOS_htons( configUDP_LOGGING_PORT_LOCAL );
	xLocalAddress.sin_addr = FreeRTOS_GetIPAddress();

	FreeRTOS_bind( xUDPLoggingSocket, &xLocalAddress, sizeof( xLocalAddress ) );

	xSendTimeOut = xBlockingTime;
	FreeRTOS_setsockopt( xUDPLoggingSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xSendTimeOut ) );

	/* Send a dummy message to resolve the IP address before sending the logging 
	messages. */
	snprintf( cLoggingLine, configUDP_LOGGING_STRING_LENGTH, "Logging Probe\n" );
	FreeRTOS_sendto( xUDPLoggingSocket, ( void * ) cLoggingLine, strlen( cLoggingLine ), 0, &xRemoteAddress, sizeof( xRemoteAddress ) );
	vTaskDelay( xResolveDelay );

	for( ;; )
	{
		/* Wait for another message to be placed into the stream buffer. */
		ulTaskNotifyTake( pdTRUE, xBlockingTime );

		if( xGetPhyLinkStatus() != pdFALSE )
		{
			/* Check for messages in the buffer. */
			for( lLines = 0; lLines < configUDP_LOGGING_MAX_MESSAGES_IN_BUFFER; lLines++ )
			{
				xCount = prvGetMessageFromStreamBuffer ( cLoggingLine, sizeof( cLoggingLine ) );

				if( xCount <= 0 )
				{
					break;
				}

				#if( configUDP_LOGGING_NEEDS_CR_LF != 0 )
				{
				char *pcTarget;
				const char *pcSource;

					/* Within the code, a single "\n" is used to denote	a
					newline.  If 'configUDP_LOGGING_NEEDS_CR_LF' is defined as non-zero,
					every "\n" will be translated into a "\r\n". */
					pcTarget = cLoggingLine;
					pcSource = cLoggingLine;

					while( ( *pcSource != 0x00 ) && ( pcSource < ( cLoggingLine + xCount ) ) )
					{
						*pcTarget = *pcSource;

						if( ( ( pcSource == cLoggingLine ) || ( pcSource[ -1 ] != logASCII_CR ) ) && ( pcSource[ 0 ] == logASCII_NL ) )
						{
							pcTarget[ 0 ] = logASCII_CR;
							pcTarget[ 1 ] = logASCII_NL;

							if( xCount < ( sizeof( cLoggingLine ) - 1 ) )
							{
								xCount++;
								pcTarget++;
							}
						}

						pcTarget++;
						pcSource++;
					}
				}
				#endif

				FreeRTOS_sendto( xUDPLoggingSocket, ( void * ) cLoggingLine, xCount, 0, &xRemoteAddress, sizeof( xRemoteAddress ) );
			}
		}
	}
}
/*-----------------------------------------------------------*/

void vUDPLoggingFlush( void )
{
const TickType_t xDelay = pdMS_TO_TICKS( 20UL );

	/* In some situations a lot of logging is produced deliberately in which
	case vUDPLoggingFlush() can be called to prevent the buffer overflowing. */
	if( xLoggingTask != NULL )
	{
		/* Unblock the logging task so it can output the message. */
		xTaskNotifyGive( xLoggingTask );
	}

	/* Allow the low priority logging task a chance to clear the buffer. */
	vTaskDelay( pdMS_TO_TICKS( xDelay ) );
}

