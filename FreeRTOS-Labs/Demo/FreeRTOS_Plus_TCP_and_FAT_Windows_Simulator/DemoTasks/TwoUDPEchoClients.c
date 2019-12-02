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
 * Two tasks are created that send UDP echo requests to the standard echo port
 * (port 7).  One task uses the standard socket interface, the other the zero
 * copy socket interface.  The IP address of the echo server must be configured
 * using the configECHO_SERVER_ADDR0 to configECHO_SERVER_ADDR3 constants in
 * FreeRTOSConfig.h.  These tasks are self checking and will trigger a
 * configASSERT() if the received echo reply does not match the transmitted echo
 * request.  As these tasks use UDP, and can therefore loose packets, they will
 * cause configASSERT() to be called when they are run in a less than perfect
 * networking environment, or when connected to an echo server that
 * legitimately as UDP is used) opts not to reply to every echo request.
 *
 * See the following web page for essential demo usage and configuration
 * details:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Small delay used between attempts to obtain a zero copy buffer. */
#define echoTINY_DELAY	( ( TickType_t ) 2 )

/* The echo tasks create a socket, send out a number of echo requests
(listening for each echo reply), then close the socket again before
starting over.  This delay is used between each iteration to ensure the
network does not get too congested. */
#define echoLOOP_DELAY	( ( TickType_t ) 250 / portTICK_PERIOD_MS )

/* When the trace recorder code is not included just #define away the call
to post the user event. */
#define echoMARK_SEND_IN_TRACE_BUFFER( x )
#define xZeroCopySendEvent 0
#define xZeroCopyReceiveEvent 0

/* The echo server is assumed to be on port 7, which is the standard echo
protocol port. */
#define echoECHO_PORT	( 7 )

/*-----------------------------------------------------------*/

/*
 * Uses a socket to send data to, then receive data from, the standard echo
 * port number 7.  prvEchoClientTask() uses the standard interface.
 * prvZeroCopyEchoClientTask() uses the zero copy interface.
 */
static void prvEchoClientTask( void *pvParameters );
static void prvZeroCopyEchoClientTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* Timeouts used to ensure the sockets don't wait forever. */
static const TickType_t xReceiveTimeOut = 1500 / portTICK_PERIOD_MS;
static const TickType_t xSendTimeOut = 1500 / portTICK_PERIOD_MS;

/* Simple delay to ensure ARPs don't get in the way. */
const TickType_t ulInitialARPReplyDelay = ( 500UL / portTICK_PERIOD_MS );

/* Used for detecting errors. */
static uint32_t ulStandardCycles = 0, ulZeroCopyCycles = 0;

/*-----------------------------------------------------------*/

void vStartUDPEchoClientTasks( uint16_t usTaskStackSize, UBaseType_t uxTaskPriority )
{
	/* Create the echo client task that does not use the zero copy interface. */
	xTaskCreate( 	prvEchoClientTask,	/* The function that implements the task. */
					"UDPEcho0",			/* Just a text name for the task to aid debugging. */
					usTaskStackSize,	/* The stack size is defined in FreeRTOSIPConfig.h. */
					NULL,				/* The task parameter, not used in this case. */
					uxTaskPriority,		/* The priority assigned to the task is defined in FreeRTOSConfig.h. */
					NULL );				/* The task handle is not used. */

	/* Create the echo client task that does use the zero copy interface. */
	xTaskCreate( 	prvZeroCopyEchoClientTask,	/* The function that implements the task. */
					"UDPEcho1",					/* Just a text name for the task to aid debugging. */
					usTaskStackSize,			/* The stack size is defined in FreeRTOSIPConfig.h. */
					NULL,						/* The task parameter, not used in this case. */
					uxTaskPriority,				/* The priority assigned to the task is defined in FreeRTOSConfig.h. */
					NULL );						/* The task handle is not used. */
}
/*-----------------------------------------------------------*/

static void prvEchoClientTask( void *pvParameters )
{
Socket_t xSocket;
struct freertos_sockaddr xEchoServerAddress;
int8_t cTxString[ 50 ], cRxString[ 50 ]; /* Make sure the stack is large enough to hold these.  Turn on stack overflow checking during debug to be sure. */
int32_t lLoopCount = 0UL, lReturned;
const int32_t lMaxLoopCount = 50;
uint32_t xAddressLength = sizeof( xEchoServerAddress ), ulTxCount = 0;

	/* Remove compiler warning about unused parameters. */
	( void ) pvParameters;

	/* Echo requests are sent to the echo server.  The address of the echo
	server is configured by the constants configECHO_SERVER_ADDR0 to
	configECHO_SERVER_ADDR3 in FreeRTOSConfig.h. */
	xEchoServerAddress.sin_port = FreeRTOS_htons( echoECHO_PORT );
	xEchoServerAddress.sin_addr = FreeRTOS_inet_addr_quick( configECHO_SERVER_ADDR0,
															configECHO_SERVER_ADDR1,
															configECHO_SERVER_ADDR2,
															configECHO_SERVER_ADDR3 );

	/* Send a ping to elicit an ARP to ensure the MAC address is known before
	the first UDP packet is sent - otherwise the UDP packet lost to the ARP will
	trigger an assert.  Wait enough time for the ARP reply before continuing. */
	#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
	{
		FreeRTOS_SendPingRequest( xEchoServerAddress.sin_addr, 1, portMAX_DELAY );
	}
	#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

	/* Just ensure ARPS don't get in the way. */
	vTaskDelay( ulInitialARPReplyDelay );

	for( ;; )
	{
		/* Create a socket. */
		xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
		configASSERT( xSocket != FREERTOS_INVALID_SOCKET );

		/* Set time outs so failed sends and missing replies do not cause the
		task to block indefinitely. */
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xSendTimeOut ) );

		/* Send a number of echo requests. */
		for( lLoopCount = 0; lLoopCount < lMaxLoopCount; lLoopCount++ )
		{
			/* Create the string that is sent to the echo server. */
			sprintf( ( char * ) cTxString, "Message number %u\r\n", ulTxCount );
			ulTxCount++;

			/* Send the string to the socket.  ulFlags is set to 0, so the zero
			copy interface is not used.  That means the data from cTxString is
			copied into a network buffer inside FreeRTOS_sendto(), and cTxString
			can be reused as soon as FreeRTOS_sendto() has returned.  1 is added
			to ensure the NULL string terminator is sent as part of the message. */
			lReturned = FreeRTOS_sendto( xSocket,				/* The socket being sent to. */
										( void * ) cTxString,	/* The data being sent. */
										strlen( ( const char * ) cTxString ) + 1, /* The length of the data being sent. */
										0,						/* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
										&xEchoServerAddress,	/* The destination address. */
										sizeof( xEchoServerAddress ) );
			configASSERT( lReturned > 0 );

			/* Receive data echoed back to the socket.  ulFlags is zero, so the
			zero copy option is not being used and the received data will be
			copied into the buffer pointed to by cRxString.  xAddressLength is
			not actually used (at the time of writing this comment, anyway) by
			FreeRTOS_recvfrom(), but is set appropriately in case future
			versions do use it. */
			memset( ( void * ) cRxString, 0x00, sizeof( cRxString ) );
			lReturned = FreeRTOS_recvfrom(	xSocket,				/* The socket being received from. */
											cRxString,				/* The buffer into which the received data will be written. */
											sizeof( cRxString ),	/* The size of the buffer provided to receive the data. */
											0,						/* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
											&xEchoServerAddress,	/* The address from which the data was sent (the source address). */
											&xAddressLength );

			/* Compare the transmitted string to the received string. */
			if( lReturned > 1 )
			{
				if( strcmp( ( char * ) cRxString, ( char * ) cTxString ) == 0 )
				{
					/* The echo reply was received without error. */
					ulStandardCycles++;
				}
			}
		}

		/* Pause for a short while to ensure the network is not too
		congested. */
		vTaskDelay( echoLOOP_DELAY );

		/* Close this socket before looping back to create another. */
		FreeRTOS_closesocket( xSocket );
	}
}
/*-----------------------------------------------------------*/

static void prvZeroCopyEchoClientTask( void *pvParameters )
{
Socket_t xSocket;
struct freertos_sockaddr xEchoServerAddress;
static int8_t cTxString[ 40 ];
int32_t lLoopCount = 0UL;
uint32_t xAddressLength = sizeof( xEchoServerAddress ), ulTxCount = 0;
int32_t lReturned;
uint8_t *pucUDPPayloadBuffer;
const int32_t lMaxLoopCount = 50;
const char * const pcStringToSend = "Zero copy message number";
/* The buffer is large enough to hold the string, a number, and the string terminator. */
const size_t xBufferLength = strlen( pcStringToSend ) + 35;

	#if ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS == 1
	{
		/* When the trace recorder code is included user events are generated to
		mark the sending and receiving of the echoed data (only in the zero copy
		task). */
		xZeroCopySendEvent = xTraceOpenLabel( "ZeroCopyTx" );
		xZeroCopyReceiveEvent = xTraceOpenLabel( "ZeroCopyRx" );
	}
	#endif /* ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS */

	/* Remove compiler warning about unused parameters. */
	( void ) pvParameters;

	/* Delay for a little while to ensure the other task has sent out a ping
	in order for the ARP cache to contain the address of the echo server. */
	vTaskDelay( echoLOOP_DELAY >> 1 );

	/* Echo requests are sent to the echo server.  The address of the echo
	server is configured by the constants configECHO_SERVER_ADDR0 to
	configECHO_SERVER_ADDR3 in FreeRTOSConfig.h. */
	xEchoServerAddress.sin_port = FreeRTOS_htons( echoECHO_PORT );
	xEchoServerAddress.sin_addr = FreeRTOS_inet_addr_quick( configECHO_SERVER_ADDR0,
															configECHO_SERVER_ADDR1,
															configECHO_SERVER_ADDR2,
															configECHO_SERVER_ADDR3 );

	for( ;; )
	{
		/* Create a socket. */
		xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
		configASSERT( xSocket != FREERTOS_INVALID_SOCKET );

		/* Set a time outs so failed sends and missing replies do not cause the
		task to block indefinitely. */
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_SNDTIMEO, &xSendTimeOut, sizeof( xSendTimeOut ) );

		/* Send a number of echo requests. */
		for( lLoopCount = 0; lLoopCount < lMaxLoopCount; lLoopCount++ )
		{
			/* This task is going to send using the zero copy interface.  The
			data being sent is therefore written directly into a buffer that is
			passed by reference into the FreeRTOS_sendto() function.  First
			obtain a buffer of adequate size from the IP stack.  Although a max
			delay is used, the actual delay will be capped to
			ipconfigMAX_SEND_BLOCK_TIME_TICKS, hence the test to ensure a buffer
			was actually obtained. */
			pucUDPPayloadBuffer = ( uint8_t * ) FreeRTOS_GetUDPPayloadBuffer( xBufferLength, portMAX_DELAY );

			if( pucUDPPayloadBuffer != NULL )
			{
				/* A buffer was successfully obtained.  Create the string that is
				sent to the echo server.  Note the string is written directly
				into the buffer obtained from the IP stack. */
				sprintf( ( char * ) pucUDPPayloadBuffer, "%s %u\r\n", ( const char * ) "Zero copy message number", ulTxCount );
				ulTxCount++;

				/* Also copy the string into a local buffer so it can be compared
				with the string that is later received back from the echo server. */
				strcpy( ( char * ) cTxString, ( char * ) pucUDPPayloadBuffer );

				/* Pass the buffer into the send function.  ulFlags has the
				FREERTOS_ZERO_COPY bit set so the IP stack will take control of
				the	buffer, rather than copy data out of the buffer. */
				echoMARK_SEND_IN_TRACE_BUFFER( xZeroCopySendEvent );
				lReturned = FreeRTOS_sendto( 	xSocket,					/* The socket being sent to. */
												( void * ) pucUDPPayloadBuffer,	/* The buffer being passed into the IP stack. */
												strlen( ( const char * ) cTxString ) + 1, /* The length of the data being sent.  Plus 1 to ensure the null terminator is part of the data. */
												FREERTOS_ZERO_COPY,			/* ulFlags with the zero copy bit is set. */
												&xEchoServerAddress,		/* Where the data is being sent. */
												sizeof( xEchoServerAddress ) );

				if( lReturned == 0 )
				{
					/* The send operation failed, so this task is still
					responsible	for the buffer obtained from the IP stack.  To
					ensure the buffer is not lost it must either be used again,
					or, as in this case, returned to the IP stack using
					FreeRTOS_ReleaseUDPPayloadBuffer().  pucUDPPayloadBuffer can
					be safely re-used to receive from the socket below once the
					buffer has been returned to the stack. */
					FreeRTOS_ReleaseUDPPayloadBuffer( ( void * ) pucUDPPayloadBuffer );
				}
				else
				{
					/* The send was successful so the IP stack is now managing
					the	buffer pointed to by pucUDPPayloadBuffer, and the IP
					stack will return the buffer once it has been sent.
					pucUDPPayloadBuffer can	be safely re-used to receive from
					the socket below. */
				}

				/* Receive data on the socket.  ulFlags has the zero copy bit set
				(FREERTOS_ZERO_COPY) indicating to the stack that a reference to
				the	received data should be passed out to this task using the
				second parameter to the FreeRTOS_recvfrom() call.  When this is
				done the IP stack is no longer responsible for releasing the
				buffer, and	the task *must* return the buffer to the stack when
				it is no longer	needed.  By default the receive block time is
				portMAX_DELAY. */
				echoMARK_SEND_IN_TRACE_BUFFER( xZeroCopyReceiveEvent );
				lReturned = FreeRTOS_recvfrom(	xSocket,					/* The socket to receive from. */
												( void * ) &pucUDPPayloadBuffer,  /* pucUDPPayloadBuffer will be set to point to the buffer that already contains the received data. */
												0,							/* Ignored because the zero copy interface is being used. */
												FREERTOS_ZERO_COPY,			/* ulFlags with the FREERTOS_ZERO_COPY bit set. */
												&xEchoServerAddress,		/* The address from which the data was sent. */
												&xAddressLength );

				if( lReturned > 0 )
				{
					/* Compare the string sent to the echo server with the string
					received back from the echo server. */
					if( strcmp( ( char * ) pucUDPPayloadBuffer, ( char * ) cTxString ) == 0 )
					{
						/* The strings matched. */
						ulZeroCopyCycles++;
					}

					/* The buffer that contains the data passed out of the stack
					*must* be returned to the stack. */
					FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayloadBuffer );
				}
			}
		}

		/* Pause for a short while to ensure the network is not too
		congested. */
		vTaskDelay( echoLOOP_DELAY );

		/* Close this socket before looping back to create another. */
		FreeRTOS_closesocket( xSocket );
	}
}
/*-----------------------------------------------------------*/

BaseType_t xAreUDPEchoClientsStillRunning( void )
{
static uint32_t ulLastStandardCycles = 0, ulLastZeroCopyCycles = 0;
BaseType_t xReturn = pdPASS;

	if( ulStandardCycles == ulLastStandardCycles )
	{
		xReturn = pdFAIL;
	}
	else
	{
		ulLastStandardCycles = ulStandardCycles;
	}

	if( ulZeroCopyCycles == ulLastZeroCopyCycles )
	{
		xReturn = pdFAIL;
	}
	else
	{
		ulLastZeroCopyCycles = ulZeroCopyCycles;
	}

	return xReturn;
}
