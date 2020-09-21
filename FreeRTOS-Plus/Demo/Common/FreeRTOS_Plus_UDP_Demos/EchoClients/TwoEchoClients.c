/*
 * FreeRTOS Kernel V10.3.0
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


/******************************************************************************
 *
 * See the following web page for essential TwoEchoClient.c usage and
 * configuration details:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/Embedded_Ethernet_Examples/Common_Echo_Clients.shtml
 *
 ******************************************************************************/


/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"

/* Small delay used between attempts to obtain a zero copy buffer. */
#define echoTINY_DELAY	( ( TickType_t ) 2 )

/* The echo tasks create a socket, send out a number of echo requests
(listening for each echo reply), then close the socket again before
starting over.  This delay is used between each iteration to ensure the
network does not get too congested. */
#define echoLOOP_DELAY	( ( TickType_t ) 250 / portTICK_RATE_MS )

#if ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS == 1
	/* When the trace recorder code is included user events are generated to
	mark the sending and receiving of the echoed data (only in the zero copy
	task. */
	#define echoMARK_SEND_IN_TRACE_BUFFER( x ) vTraceUserEvent( x )
	traceLabel xZeroCopySendEvent, xZeroCopyReceiveEvent;

#else
	/* When the trace recorder code is not included just #define away the call
	to post the user event. */
	#define echoMARK_SEND_IN_TRACE_BUFFER( x )
	#define xZeroCopySendEvent 0
	#define xZeroCopyReceiveEvent 0
#endif

/* The echo server is assumed to be on port 7, which is the standard echo
protocol port. */
#define echoECHO_PORT	( 7 )

/*
 * Uses a socket to send data to, then receive data from, the standard echo
 * port number 7.  prvEchoClientTask() uses the standard interface.
 * prvZeroCopyEchoClientTask() uses the zero copy interface.
 */
static void prvEchoClientTask( void *pvParameters );
static void prvZeroCopyEchoClientTask( void *pvParameters );

/* The receive timeout is set shorter when the windows simulator is used
because simulated time is slower than real time. */
#ifdef _WINDOWS_
	const TickType_t xReceiveTimeOut = 50 / portTICK_RATE_MS;
#else
	const TickType_t xReceiveTimeOut = 500 / portTICK_RATE_MS;
#endif

/*-----------------------------------------------------------*/

void vStartEchoClientTasks( uint16_t usTaskStackSize, UBaseType_t uxTaskPriority )
{
	/* Create the echo client task that does not use the zero copy interface. */
	xTaskCreate( 	prvEchoClientTask,	/* The function that implements the task. */
					"Echo0",			/* Just a text name for the task to aid debugging. */
					usTaskStackSize,	/* The stack size is defined in FreeRTOSIPConfig.h. */
					NULL,				/* The task parameter, not used in this case. */
					uxTaskPriority,		/* The priority assigned to the task is defined in FreeRTOSConfig.h. */
					NULL );				/* The task handle is not used. */

	/* Create the echo client task that does use the zero copy interface. */
	xTaskCreate( 	prvZeroCopyEchoClientTask,	/* The function that implements the task. */
					"Echo1",					/* Just a text name for the task to aid debugging. */
					usTaskStackSize,			/* The stack size is defined in FreeRTOSIPConfig.h. */
					NULL,						/* The task parameter, not used in this case. */
					uxTaskPriority,				/* The priority assigned to the task is defined in FreeRTOSConfig.h. */
					NULL );						/* The task handle is not used. */
}
/*-----------------------------------------------------------*/

static void prvEchoClientTask( void *pvParameters )
{
xSocket_t xSocket;
struct freertos_sockaddr xEchoServerAddress;
char cTxString[ 25 ], cRxString[ 25 ]; /* Make sure the stack is large enough to hold these.  Turn on stack overflow checking during debug to be sure. */
int32_t lLoopCount = 0UL;
const int32_t lMaxLoopCount = 50;
volatile uint32_t ulRxCount = 0UL, ulTxCount = 0UL;
uint32_t xAddressLength = sizeof( xEchoServerAddress );

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

	for( ;; )
	{
		/* Create a socket. */
		xSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
		configASSERT( xSocket != FREERTOS_INVALID_SOCKET );

		/* Set a time out so a missing reply does not cause the task to block
		indefinitely. */
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );

		/* Send a number of echo requests. */
		for( lLoopCount = 0; lLoopCount < lMaxLoopCount; lLoopCount++ )
		{
			/* Create the string that is sent to the echo server. */
			sprintf( cTxString, "Message number %u\r\n", ( unsigned int ) ulTxCount );

			/* Send the string to the socket.  ulFlags is set to 0, so the zero
			copy interface is not used.  That means the data from cTxString is
			copied into a network buffer inside FreeRTOS_sendto(), and cTxString
			can be reused as soon as FreeRTOS_sendto() has returned.  1 is added
			to ensure the NULL string terminator is sent as part of the message. */
			FreeRTOS_sendto( xSocket,				/* The socket being sent to. */
							( void * ) cTxString,	/* The data being sent. */
							strlen( cTxString ) + 1,/* The length of the data being sent. */
							0,						/* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
							&xEchoServerAddress,	/* The destination address. */
							sizeof( xEchoServerAddress ) );

			/* Keep a count of how many echo requests have been transmitted so
			it can be compared to the number of echo replies received.  It would
			be expected to loose at least one to an ARP message the first time
			the	connection is created. */
			ulTxCount++;

			/* Receive data echoed back to the socket.  ulFlags is zero, so the
			zero copy option is not being used and the received data will be
			copied into the buffer pointed to by cRxString.  xAddressLength is
			not actually used (at the time of writing this comment, anyway) by
			FreeRTOS_recvfrom(), but is set appropriately in case future
			versions do use it. */
			memset( ( void * ) cRxString, 0x00, sizeof( cRxString ) );
			FreeRTOS_recvfrom(	xSocket,				/* The socket being received from. */
								cRxString,				/* The buffer into which the received data will be written. */
								sizeof( cRxString ),	/* The size of the buffer provided to receive the data. */
								0,						/* ulFlags with the FREERTOS_ZERO_COPY bit clear. */
								&xEchoServerAddress,	/* The address from where the data was sent (the source address). */
								&xAddressLength );

			/* Compare the transmitted string to the received string. */
			if( strcmp( cRxString, cTxString ) == 0 )
			{
				/* The echo reply was received without error. */
				ulRxCount++;
			}
		};

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
xSocket_t xSocket;
struct freertos_sockaddr xEchoServerAddress;
static char cTxString[ 40 ];
int32_t lLoopCount = 0UL;
volatile uint32_t ulRxCount = 0UL, ulTxCount = 0UL;
uint32_t xAddressLength = sizeof( xEchoServerAddress );
int32_t lReturned;
uint8_t *pucUDPPayloadBuffer;

const int32_t lMaxLoopCount = 50;
const char * const pcStringToSend = "Zero copy message number";
/* The buffer is large enough to hold the string, a number, and the string terminator. */
const size_t xBufferLength = strlen( pcStringToSend ) + 15;

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

	/* Delay for a little while to ensure the task is out of synch with the
	other echo task implemented above. */
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

		/* Set a time out so a missing reply does not cause the task to block
		indefinitely. */
		FreeRTOS_setsockopt( xSocket, 0, FREERTOS_SO_RCVTIMEO, &xReceiveTimeOut, sizeof( xReceiveTimeOut ) );

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
				sprintf( ( char * ) pucUDPPayloadBuffer, "%s %u\r\n", "Zero copy message number", ( unsigned int ) ulTxCount );

				/* Also copy the string into a local buffer so it can be compared
				with the string that is later received back from the echo server. */
				strcpy( cTxString, ( char * ) pucUDPPayloadBuffer );

				/* Pass the buffer into the send function.  ulFlags has the
				FREERTOS_ZERO_COPY bit set so the IP stack will take control of
				the	buffer, rather than copy data out of the buffer. */
				echoMARK_SEND_IN_TRACE_BUFFER( xZeroCopySendEvent );
				lReturned = FreeRTOS_sendto( 	xSocket,					/* The socket being sent to. */
												( void * ) pucUDPPayloadBuffer,	/* The buffer being passed into the IP stack. */
												strlen( cTxString ) + 1, 	/* The length of the data being sent.  Plus 1 to ensure the null terminator is part of the data. */
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

				/* Keep a count of how many echo requests have been transmitted
				so it can be compared to the number of echo replies received.
				It would be expected to loose at least one to an ARP message the
				first time the connection is created. */
				ulTxCount++;

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
					if( strcmp( ( char * ) pucUDPPayloadBuffer, cTxString ) == 0 )
					{
						/* The strings matched. */
						ulRxCount++;
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

