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
 * Logging utility that allows FreeRTOS tasks to log to a UDP port, stdout, and
 * disk file without making any Win32 system calls themselves.
 *
 * Messages logged to a UDP port are sent directly (using FreeRTOS+TCP), but as
 * FreeRTOS tasks cannot make Win32 system calls messages sent to stdout or a
 * disk file are sent via a stream buffer to a Win32 thread which then performs
 * the actual output.
 */

/* Standard includes. */
#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <io.h>
#include <ctype.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_Stream_Buffer.h"

/* Demo includes. */
#include "demo_logging.h"

/*-----------------------------------------------------------*/

/* The maximum size to which the log file may grow, before being renamed
to .ful. */
#define dlLOGGING_FILE_SIZE		( 40ul * 1024ul * 1024ul )

/* Dimensions the arrays into which print messages are created. */
#define dlMAX_PRINT_STRING_LENGTH	255

/* The size of the stream buffer used to pass messages from FreeRTOS tasks to
the Win32 thread that is responsible for making any Win32 system calls that are
necessary for the selected logging method. */
#define dlLOGGING_STREAM_BUFFER_SIZE  32768

/* A block time of zero simply means don't block. */
#define dlDONT_BLOCK	0

/*-----------------------------------------------------------*/

/*
 * Called from vLoggingInit() to start a new disk log file.
 */
static void prvFileLoggingInit( void );

/*
 * Attempt to write a message to the file.
 */
static void prvLogToFile( const char *pcMessage, size_t xLength );

/*
 * Simply close the logging file, if it is open.
 */
static void prvFileClose( void );

/*
 * Before the scheduler is started this function is called directly.  After the
 * scheduler has started it is called from the Windows thread dedicated to
 * outputting log messages.  Only the windows thread actually performs the
 * writing so as not to disrupt the simulation by making Windows system calls
 * from FreeRTOS tasks.
 */
static void prvLoggingFlushBuffer( void );

/*
 * The windows thread that performs the actual writing of messages that require
 * Win32 system calls.  Only the windows thread can make system calls so as not
 * to disrupt the simulation by making Windows calls from FreeRTOS tasks.
 */
static DWORD WINAPI prvWin32LoggingThread( void *pvParam );

/*
 * Creates the socket to which UDP messages are sent.  This function is not
 * called directly to prevent the print socket being created from within the IP
 * task - which could result in a deadlock.  Instead the function call is
 * deferred to run in the RTOS daemon task - hence it prototype.
 */
static void prvCreatePrintSocket( void *pvParameter1, uint32_t ulParameter2 );

/*-----------------------------------------------------------*/

/* Windows event used to wake the Win32 thread which performs any logging that
needs Win32 system calls. */
static void *pvLoggingThreadEvent = NULL;

/* Stores the selected logging targets passed in as parameters to the
vLoggingInit() function. */
BaseType_t xStdoutLoggingUsed = pdFALSE, xDiskFileLoggingUsed = pdFALSE, xUDPLoggingUsed = pdFALSE;

/* Circular buffer used to pass messages from the FreeRTOS tasks to the Win32
thread that is responsible for making Win32 calls (when stdout or a disk log is
used). */
static StreamBuffer_t *xLogStreamBuffer = NULL;

/* Handle to the file used for logging.  This is left open while there are
messages waiting to be logged, then closed again in between logs. */
static FILE *pxLoggingFileHandle = NULL;

/* When true prints are performed directly.  After start up xDirectPrint is set
to pdFALSE - at which time prints that require Win32 system calls are done by
the Win32 thread responsible for logging. */
BaseType_t xDirectPrint = pdTRUE;

/* File names for the in use and complete (full) log files. */
static const char *pcLogFileName = "RTOSDemo.log";
static const char *pcFullLogFileName = "RTOSDemo.ful";

/* Keep the current file size in a variable, as an optimisation. */
static size_t ulSizeOfLoggingFile = 0ul;

/* The UDP socket and address on/to which print messages are sent. */
Socket_t xPrintSocket = FREERTOS_INVALID_SOCKET;
struct freertos_sockaddr xPrintUDPAddress;

/*-----------------------------------------------------------*/

void vLoggingInit( BaseType_t xLogToStdout, BaseType_t xLogToFile, BaseType_t xLogToUDP, uint32_t ulRemoteIPAddress, uint16_t usRemotePort )
{
	/* Can only be called before the scheduler has started. */
	configASSERT( xTaskGetSchedulerState() == taskSCHEDULER_NOT_STARTED );

	#if( ( ipconfigHAS_DEBUG_PRINTF == 1 ) || ( ipconfigHAS_PRINTF == 1 ) )
	{
		HANDLE Win32Thread;

		/* Record which output methods are to be used. */
		xStdoutLoggingUsed = xLogToStdout;
		xDiskFileLoggingUsed = xLogToFile;
		xUDPLoggingUsed = xLogToUDP;

		/* If a disk file is used then initialise it now. */
		if( xDiskFileLoggingUsed != pdFALSE )
		{
			prvFileLoggingInit();
		}

		/* If UDP logging is used then store the address to which the log data
		will be sent - but don't create the socket yet because the network is
		not initialised. */
		if( xUDPLoggingUsed != pdFALSE )
		{
			/* Set the address to which the print messages are sent. */
			xPrintUDPAddress.sin_port = FreeRTOS_htons( usRemotePort );
			xPrintUDPAddress.sin_addr = ulRemoteIPAddress;
		}

		/* If a disk file or stdout are to be used then Win32 system calls will
		have to be made.  Such system calls cannot be made from FreeRTOS tasks
		so create a stream buffer to pass the messages to a Win32 thread, then
		create the thread itself, along with a Win32 event that can be used to
		unblock the thread. */
		if( ( xStdoutLoggingUsed != pdFALSE ) || ( xDiskFileLoggingUsed != pdFALSE ) )
		{
			/* Create the buffer. */
			xLogStreamBuffer = ( StreamBuffer_t * ) malloc( sizeof( *xLogStreamBuffer ) - sizeof( xLogStreamBuffer->ucArray ) + dlLOGGING_STREAM_BUFFER_SIZE + 1 );
			configASSERT( xLogStreamBuffer );
			memset( xLogStreamBuffer, '\0', sizeof( *xLogStreamBuffer ) - sizeof( xLogStreamBuffer->ucArray ) );
			xLogStreamBuffer->LENGTH = dlLOGGING_STREAM_BUFFER_SIZE + 1;

			/* Create the Windows event. */
			pvLoggingThreadEvent = CreateEvent( NULL, FALSE, TRUE, "StdoutLoggingEvent" );

			/* Create the thread itself. */
			Win32Thread = CreateThread(
				NULL,	/* Pointer to thread security attributes. */
				0,		/* Initial thread stack size, in bytes. */
				prvWin32LoggingThread,	/* Pointer to thread function. */
				NULL,	/* Argument for new thread. */
				0,		/* Creation flags. */
				NULL );

			/* Use the cores that are not used by the FreeRTOS tasks. */
			SetThreadAffinityMask( Win32Thread, ~0x01u );
			SetThreadPriorityBoost( Win32Thread, TRUE );
			SetThreadPriority( Win32Thread, THREAD_PRIORITY_IDLE );
		}
	}
	#else
	{
		/* FreeRTOSIPConfig is set such that no print messages will be output.
		Avoid compiler warnings about unused parameters. */
		( void ) xLogToStdout;
		( void ) xLogToFile;
		( void ) xLogToUDP;
		( void ) usRemotePort;
		( void ) ulRemoteIPAddress;
	}
	#endif /* ( ipconfigHAS_DEBUG_PRINTF == 1 ) || ( ipconfigHAS_PRINTF == 1 )  */
}
/*-----------------------------------------------------------*/

static void prvCreatePrintSocket( void *pvParameter1, uint32_t ulParameter2 )
{
static const TickType_t xSendTimeOut = pdMS_TO_TICKS( 0 );
Socket_t xSocket;

	/* The function prototype is that of a deferred function, but the parameters
	are not actually used. */
	( void ) pvParameter1;
	( void ) ulParameter2;

	xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );

	if( xSocket != FREERTOS_INVALID_SOCKET )
	{
		/* FreeRTOS+TCP decides which port to bind to. */
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xSendTimeOut ) );
		FreeRTOS_bind( xSocket, NULL, 0 );

		/* Now the socket is bound it can be assigned to the print socket. */
		xPrintSocket = xSocket;
	}
}
/*-----------------------------------------------------------*/

void vLoggingPrintf( const char *pcFormat, ... )
{
char cPrintString[ dlMAX_PRINT_STRING_LENGTH ];
char cOutputString[ dlMAX_PRINT_STRING_LENGTH ];
char *pcSource, *pcTarget, *pcBegin;
size_t xLength, xLength2, rc;
static BaseType_t xMessageNumber = 0;
va_list args;
uint32_t ulIPAddress;
const char *pcTaskName;
const char *pcNoTask = "None";
int iOriginalPriority;
HANDLE xCurrentTask;


	if( ( xStdoutLoggingUsed != pdFALSE ) || ( xDiskFileLoggingUsed != pdFALSE ) || ( xUDPLoggingUsed != pdFALSE ) )
	{
		/* There are a variable number of parameters. */
		va_start( args, pcFormat );

		/* Additional info to place at the start of the log. */
		if( xTaskGetSchedulerState() != taskSCHEDULER_NOT_STARTED )
		{
			pcTaskName = pcTaskGetName( NULL );
		}
		else
		{
			pcTaskName = pcNoTask;
		}

		if( strcmp( pcFormat, "\n" ) != 0 )
		{
			xLength = snprintf( cPrintString, dlMAX_PRINT_STRING_LENGTH, "%lu %lu [%s] ",
				xMessageNumber++,
				( unsigned long ) xTaskGetTickCount(),
				pcTaskName );
		}
		else
		{
			xLength = 0;
			memset( cPrintString, 0x00, dlMAX_PRINT_STRING_LENGTH );
		}

		xLength2 = vsnprintf( cPrintString + xLength, dlMAX_PRINT_STRING_LENGTH - xLength, pcFormat, args );

		if( xLength2 <  0 )
		{
			/* Clean up. */
			xLength2 = sizeof( cPrintString ) - 1 - xLength;
			cPrintString[ sizeof( cPrintString ) - 1 ] = '\0';
		}

		xLength += xLength2;
		va_end( args );

		/* For ease of viewing, copy the string into another buffer, converting
		IP addresses to dot notation on the way. */
		pcSource = cPrintString;
		pcTarget = cOutputString;

		while( ( *pcSource ) != '\0' )
		{
			*pcTarget = *pcSource;
			pcTarget++;
			pcSource++;

			/* Look forward for an IP address denoted by 'ip'. */
			if( ( isxdigit( pcSource[ 0 ] ) != pdFALSE ) && ( pcSource[ 1 ] == 'i' ) && ( pcSource[ 2 ] == 'p' ) )
			{
				*pcTarget = *pcSource;
				pcTarget++;
				*pcTarget = '\0';
				pcBegin = pcTarget - 8;

				while( ( pcTarget > pcBegin ) && ( isxdigit( pcTarget[ -1 ] ) != pdFALSE ) )
				{
					pcTarget--;
				}

				sscanf( pcTarget, "%8X", &ulIPAddress );
				rc = sprintf( pcTarget, "%lu.%lu.%lu.%lu",
					( unsigned long ) ( ulIPAddress >> 24UL ),
					( unsigned long ) ( (ulIPAddress >> 16UL) & 0xffUL ),
					( unsigned long ) ( (ulIPAddress >> 8UL) & 0xffUL ),
					( unsigned long ) ( ulIPAddress & 0xffUL ) );
				pcTarget += rc;
				pcSource += 3; /* skip "<n>ip" */
			}
		}

		/* How far through the buffer was written? */
		xLength = ( BaseType_t ) ( pcTarget - cOutputString );

		/* If the message is to be logged to a UDP port then it can be sent directly
		because it only uses FreeRTOS function (not Win32 functions). */
		if( xUDPLoggingUsed != pdFALSE )
		{
			if( ( xPrintSocket == FREERTOS_INVALID_SOCKET ) && ( FreeRTOS_IsNetworkUp() != pdFALSE ) )
			{
				/* Create and bind the socket to which print messages are sent.  The
				xTimerPendFunctionCall() function is used even though this is
				not an interrupt because this function is called from the IP task
				and the	IP task cannot itself wait for a socket to bind.  The
				parameters to prvCreatePrintSocket() are not required so set to
				NULL or 0. */
				xTimerPendFunctionCall( prvCreatePrintSocket, NULL, 0, dlDONT_BLOCK );
			}

			if( xPrintSocket != FREERTOS_INVALID_SOCKET )
			{
				FreeRTOS_sendto( xPrintSocket, cOutputString, xLength, 0, &xPrintUDPAddress, sizeof( xPrintUDPAddress ) );

				/* Just because the UDP data logger I'm using is dumb. */
				FreeRTOS_sendto( xPrintSocket, "\r", sizeof( char ), 0, &xPrintUDPAddress, sizeof( xPrintUDPAddress ) );
			}
		}

		/* If logging is also to go to either stdout or a disk file then it cannot
		be output here - so instead write the message to the stream buffer and wake
		the Win32 thread which will read it from the stream buffer and perform the
		actual output. */
		if( ( xStdoutLoggingUsed != pdFALSE ) || ( xDiskFileLoggingUsed != pdFALSE ) )
		{
			configASSERT( xLogStreamBuffer );

			/* How much space is in the buffer? */
			xLength2 = uxStreamBufferGetSpace( xLogStreamBuffer );

			/* There must be enough space to write both the string and the length of
			the string. */
			if( xLength2 >= ( xLength + sizeof( xLength ) ) )
			{
				/* First write in the length of the data, then write in the data
				itself.  Raising the thread priority is used as a critical section
				as there are potentially multiple writers.  The stream buffer is
				only thread safe when there is a single writer (likewise for
				reading from the buffer). */
				xCurrentTask = GetCurrentThread();
				iOriginalPriority = GetThreadPriority( xCurrentTask );
				SetThreadPriority( GetCurrentThread(), THREAD_PRIORITY_TIME_CRITICAL );
				uxStreamBufferAdd( xLogStreamBuffer, 0, ( const uint8_t * ) &( xLength ), sizeof( xLength ) );
				uxStreamBufferAdd( xLogStreamBuffer, 0, ( const uint8_t * ) cOutputString, xLength );
				SetThreadPriority( GetCurrentThread(), iOriginalPriority );
			}

			/* xDirectPrint is initialised to pdTRUE, and while it remains true the
			logging output function is called directly.  When the system is running
			the output function cannot be called directly because it would get
			called from both FreeRTOS tasks and Win32 threads - so instead wake the
			Win32 thread responsible for the actual output. */
			if( xDirectPrint != pdFALSE )
			{
				/* While starting up, the thread which calls prvWin32LoggingThread()
				is not running yet and xDirectPrint will be pdTRUE. */
				prvLoggingFlushBuffer();
			}
			else if( pvLoggingThreadEvent != NULL )
			{
				/* While running, wake up prvWin32LoggingThread() to send the
				logging data. */
				SetEvent( pvLoggingThreadEvent );
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvLoggingFlushBuffer( void )
{
size_t xLength;
char cPrintString[ dlMAX_PRINT_STRING_LENGTH ];

	/* Is there more than the length value stored in the circular buffer
	used to pass data from the FreeRTOS simulator into this Win32 thread? */
	while( uxStreamBufferGetSize( xLogStreamBuffer ) > sizeof( xLength ) )
	{
		memset( cPrintString, 0x00, dlMAX_PRINT_STRING_LENGTH );
		uxStreamBufferGet( xLogStreamBuffer, 0, ( uint8_t * ) &xLength, sizeof( xLength ), pdFALSE );
		uxStreamBufferGet( xLogStreamBuffer, 0, ( uint8_t * ) cPrintString, xLength, pdFALSE );

		/* Write the message to standard out if requested to do so when
		vLoggingInit() was called, or if the network is not yet up. */
		if( ( xStdoutLoggingUsed != pdFALSE ) || ( FreeRTOS_IsNetworkUp() == pdFALSE ) )
		{
			/* Write the message to stdout. */
			printf( "%s", cPrintString ); /*_RB_ Replace with _write(). */
		}

		/* Write the message to a file if requested to do so when
		vLoggingInit() was called. */
		if( xDiskFileLoggingUsed != pdFALSE )
		{
			prvLogToFile( cPrintString, xLength );
		}
	}

	prvFileClose();
}
/*-----------------------------------------------------------*/

static DWORD WINAPI prvWin32LoggingThread( void *pvParameter )
{
const DWORD xMaxWait = 1000;

	( void ) pvParameter;

	/* From now on, prvLoggingFlushBuffer() will only be called from this
	Windows thread */
	xDirectPrint = pdFALSE;

	for( ;; )
	{
		/* Wait to be told there are message waiting to be logged. */
		WaitForSingleObject( pvLoggingThreadEvent, xMaxWait );

		/* Write out all waiting messages. */
		prvLoggingFlushBuffer();
	}
}
/*-----------------------------------------------------------*/

static void prvFileLoggingInit( void )
{
FILE *pxHandle = fopen( pcLogFileName, "a" );

	if( pxHandle != NULL )
	{
		fseek( pxHandle, SEEK_END, 0ul );
		ulSizeOfLoggingFile = ftell( pxHandle );
		fclose( pxHandle );
	}
	else
	{
		ulSizeOfLoggingFile = 0ul;
	}
}
/*-----------------------------------------------------------*/

static void prvFileClose( void )
{
	if( pxLoggingFileHandle != NULL )
	{
		fclose( pxLoggingFileHandle );
		pxLoggingFileHandle = NULL;
	}
}
/*-----------------------------------------------------------*/

static void prvLogToFile( const char *pcMessage, size_t xLength )
{
	if( pxLoggingFileHandle == NULL )
	{
		pxLoggingFileHandle = fopen( pcLogFileName, "a" );
	}

	if( pxLoggingFileHandle != NULL )
	{
		fwrite( pcMessage, 1, xLength, pxLoggingFileHandle );
		ulSizeOfLoggingFile += xLength;

		/* If the file has grown to its maximum permissible size then close and
		rename it - then start with a new file. */
		if( ulSizeOfLoggingFile > ( size_t ) dlLOGGING_FILE_SIZE )
		{
			prvFileClose();
			if( _access( pcFullLogFileName, 00 ) == 0 )
			{
				remove( pcFullLogFileName );
			}
			rename( pcLogFileName, pcFullLogFileName );
			ulSizeOfLoggingFile = 0;
		}
	}
}
/*-----------------------------------------------------------*/

