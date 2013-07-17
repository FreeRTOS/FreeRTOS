/*
    FreeRTOS V7.5.0 - Copyright (C) 2013 Real Time Engineers Ltd.

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

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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
 * Creates two transmitting tasks and two receiving tasks.  The transmitting
 * tasks send values that are received by the receiving tasks.  One set of tasks
 * uses the standard API.  The other set of tasks uses the zero copy API.
 */

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"

#define simpTINY_DELAY	( ( portTickType ) 2 )

/*
 * Uses a socket to send data without using the zero copy option.
 * prvSimpleServerTask() will receive the data.
 */
static void prvSimpleClientTask( void *pvParameters );

/*
 * Uses a socket to receive the data sent by the prvSimpleClientTask() task.
 * Does not use the zero copy option.
 */
static void prvSimpleServerTask( void *pvParameters );

/*
 * Uses a socket to send data using the zero copy option.
 * prvSimpleZeroCopyServerTask() will receive the data.
 */
static void prvSimpleZeroCopyUDPClientTask( void *pvParameters );

/*
 * Uses a socket to receive the data sent by the prvSimpleZeroCopyUDPClientTask()
 * task.  Uses the zero copy option.
 */
static void prvSimpleZeroCopyServerTask( void *pvParameters );

/*-----------------------------------------------------------*/

void vStartSimpleUDPClientServerTasks( uint16_t usStackSize, uint32_t ulPort, unsigned portBASE_TYPE uxPriority )
{
	/* Create the client and server tasks that do not use the zero copy
	interface. */
	xTaskCreate( prvSimpleClientTask, "SimpCpyClnt", usStackSize, ( void * ) ulPort, uxPriority, NULL );
	xTaskCreate( prvSimpleServerTask, "SimpCpySrv", usStackSize, ( void * ) ulPort, uxPriority + 1, NULL );

	/* Create the client and server tasks that do use the zero copy interface. */
	xTaskCreate( prvSimpleZeroCopyUDPClientTask, "SimpZCpyClnt", usStackSize, ( void * ) ( ulPort + 1 ), uxPriority, NULL );
	xTaskCreate( prvSimpleZeroCopyServerTask, "SimpZCpySrv", usStackSize, ( void * ) ( ulPort + 1 ), uxPriority + 1, NULL );
}
/*-----------------------------------------------------------*/

static void prvSimpleClientTask( void *pvParameters )
{
xSocket_t xClientSocket;
struct freertos_sockaddr xDestinationAddress;
uint8_t cString[ 50 ];
portBASE_TYPE lReturned;
uint32_t ulCount = 0UL, ulIPAddress;
const uint32_t ulLoopsPerSocket = 10UL;
const portTickType x150ms = 150UL / portTICK_RATE_MS;

	/* Remove compiler warning about unused parameters. */
	( void ) pvParameters;

	/* It is assumed that this task is not created until the network is up,
	so the IP address can be obtained immediately.  store the IP address being
	used in ulIPAddress.  This is done so the socket can send to a different
	port on the same IP address. */
	FreeRTOS_GetAddressConfiguration( &ulIPAddress, NULL, NULL, NULL );

	/* This test sends to itself, so data sent from here is received by a server
	socket on the same IP address.  Setup the freertos_sockaddr structure with
	this nodes IP address, and the port number being sent to.  The strange
	casting is to try and remove compiler warnings on 32 bit machines. */
	xDestinationAddress.sin_addr = ulIPAddress;
	xDestinationAddress.sin_port = ( uint16_t ) ( ( uint32_t ) pvParameters ) & 0xffffUL;
	xDestinationAddress.sin_port = FreeRTOS_htons( xDestinationAddress.sin_port );

	for( ;; )
	{
		/* Create the socket. */
		xClientSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
		configASSERT( xClientSocket != FREERTOS_INVALID_SOCKET );

		/* The count is used to differentiate between different messages sent to
		the server, and to break out of the do while loop below. */
		ulCount = 0UL;

		do
		{
			/* Create the string that is sent to the server. */
			sprintf( ( char * ) cString, "Server received (not zero copy): Message number %lu\r\n", ulCount );

			/* Send the string to the socket.  ulFlags is set to 0, so the zero
			copy option is not selected.  That means the data from cString[] is
			copied into a network buffer inside FreeRTOS_sendto(), and cString[]
			can be reused as soon as FreeRTOS_sendto() has returned. */
			lReturned = FreeRTOS_sendto( xClientSocket, ( void * ) cString, strlen( ( const char * ) cString ), 0, &xDestinationAddress, sizeof( xDestinationAddress ) );

			ulCount++;

		} while( ( lReturned != FREERTOS_SOCKET_ERROR ) && ( ulCount < ulLoopsPerSocket ) );

		FreeRTOS_closesocket( xClientSocket );

		/* A short delay to prevent the messages printed by the server task
		scrolling off the screen too quickly, and to prevent reduce the network
		loading. */
		vTaskDelay( x150ms );
	}
}
/*-----------------------------------------------------------*/

static void prvSimpleServerTask( void *pvParameters )
{
long lBytes;
uint8_t cReceivedString[ 60 ];
struct freertos_sockaddr xClient, xBindAddress;
uint32_t xClientLength = sizeof( xClient );
xSocket_t xListeningSocket;

	/* Just to prevent compiler warnings. */
	( void ) pvParameters;

	/* Attempt to open the socket. */
	xListeningSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
	configASSERT( xListeningSocket != FREERTOS_INVALID_SOCKET );

	/* This test receives data sent from a different port on the same IP
	address.  Configure the freertos_sockaddr structure with the address being
	bound to.  The strange casting is to try and remove	compiler warnings on 32
	bit machines.  Note that this task is only created after the network is up,
	so the IP address is valid here. */
	xBindAddress.sin_port = ( uint16_t ) ( ( uint32_t ) pvParameters ) & 0xffffUL;
	xBindAddress.sin_port = FreeRTOS_htons( xBindAddress.sin_port );

	/* Bind the socket to the port that the client task will send to. */
	FreeRTOS_bind( xListeningSocket, &xBindAddress, sizeof( xBindAddress ) );

	for( ;; )
	{
		/* Zero out the receive array so there is NULL at the end of the string
		when it is printed out. */
		memset( cReceivedString, 0x00, sizeof( cReceivedString ) );

		/* Receive data on the socket.  ulFlags is zero, so the zero copy option
		is not set and the received data is copied into the buffer pointed to by
		cReceivedString.  By default the block time is portMAX_DELAY.
		xClientLength is not actually used by FreeRTOS_recvfrom(), but is set
		appropriately in case future versions do use it. */
		lBytes = FreeRTOS_recvfrom( xListeningSocket, cReceivedString, sizeof( cReceivedString ), 0, &xClient, &xClientLength );

		/* Print the received characters. */
		if( lBytes > 0 )
		{
			vOutputString( ( char * ) cReceivedString );
		}

		/* Error check. */
		configASSERT( lBytes == ( portBASE_TYPE ) strlen( ( const char * ) cReceivedString ) );
	}
}
/*-----------------------------------------------------------*/

static void prvSimpleZeroCopyUDPClientTask( void *pvParameters )
{
xSocket_t xClientSocket;
uint8_t *pucUDPPayloadBuffer;
struct freertos_sockaddr xDestinationAddress;
portBASE_TYPE lReturned;
uint32_t ulCount = 0UL, ulIPAddress;
const uint32_t ulLoopsPerSocket = 10UL;
const uint8_t *pucStringToSend = ( const uint8_t * ) "Server received (using zero copy): Message number ";
const portTickType x150ms = 150UL / portTICK_RATE_MS;
/* 15 is added to ensure the number, \r\n and terminating zero fit. */
const size_t xStringLength = strlen( ( char * ) pucStringToSend ) + 15;

	/* Remove compiler warning about unused parameters. */
	( void ) pvParameters;

	/* It is assumed that this task is not created until the network is up,
	so the IP address can be obtained immediately.  store the IP address being
	used in ulIPAddress.  This is done so the socket can send to a different
	port on the same IP address. */
	FreeRTOS_GetAddressConfiguration( &ulIPAddress, NULL, NULL, NULL );

	/* This test sends to itself, so data sent from here is received by a server
	socket on the same IP address.  Setup the freertos_sockaddr structure with
	this nodes IP address, and the port number being sent to.  The strange
	casting is to try and remove compiler warnings on 32 bit machines. */
	xDestinationAddress.sin_addr = ulIPAddress;
	xDestinationAddress.sin_port = ( uint16_t ) ( ( uint32_t ) pvParameters ) & 0xffffUL;
	xDestinationAddress.sin_port = FreeRTOS_htons( xDestinationAddress.sin_port );

	for( ;; )
	{
		/* Create the socket. */
		xClientSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
		configASSERT( xClientSocket != FREERTOS_INVALID_SOCKET );

		/* The count is used to differentiate between different messages sent to
		the server, and to break out of the do while loop below. */
		ulCount = 0UL;

		do
		{
			/* This task is going to send using the zero copy interface.  The
			data being sent is therefore written directly into a buffer that is
			passed into, rather than copied into, the FreeRTOS_sendto()
			function.

			First obtain a buffer of adequate length from the IP stack into which
			the string will be written.  Although a max delay is used, the actual
			delay will be capped to ipconfigMAX_SEND_BLOCK_TIME_TICKS, hence
			the do while loop is used to ensure a buffer is obtained. */
			do
			{
			} while( ( pucUDPPayloadBuffer = ( uint8_t * ) FreeRTOS_GetUDPPayloadBuffer( xStringLength, portMAX_DELAY ) ) == NULL );

			/* A buffer was successfully obtained.  Create the string that is
			sent to the server.  First the string is filled with zeros as this will
			effectively be the null terminator when the string is received at the other
			end.  Note that the string is being written directly into the buffer
			obtained from the IP stack above. */
			memset( ( void * ) pucUDPPayloadBuffer, 0x00, xStringLength );
			sprintf( ( char * ) pucUDPPayloadBuffer, "%s%lu\r\n", ( char * ) pucStringToSend, ulCount );

			/* Pass the buffer into the send function.  ulFlags has the
			FREERTOS_ZERO_COPY bit set so the IP stack will take control of the
			buffer rather than copy data out of the buffer. */
			lReturned = FreeRTOS_sendto( xClientSocket,  				/* The socket being sent to. */
										( void * ) pucUDPPayloadBuffer, /* A pointer to the the data being sent. */
										strlen( ( const char * ) pucUDPPayloadBuffer ) + 1, /* The length of the data being sent - including the string's null terminator. */
										FREERTOS_ZERO_COPY, 			/* ulFlags with the FREERTOS_ZERO_COPY bit set. */
										&xDestinationAddress, 			/* Where the data is being sent. */
										sizeof( xDestinationAddress ) );

			if( lReturned == 0 )
			{
				/* The send operation failed, so this task is still responsible
				for the buffer obtained from the IP stack.  To ensure the buffer
				is not lost it must either be used again, or, as in this case,
				returned to the IP stack using FreeRTOS_ReleaseUDPPayloadBuffer().
				pucUDPPayloadBuffer can be safely re-used after this call. */
				FreeRTOS_ReleaseUDPPayloadBuffer( ( void * ) pucUDPPayloadBuffer );
			}
			else
			{
				/* The send was successful so the IP stack is now managing the
				buffer pointed to by pucUDPPayloadBuffer, and the IP stack will
				return the buffer once it has been sent.  pucUDPPayloadBuffer can
				be safely re-used. */
			}

			ulCount++;

		} while( ( lReturned != FREERTOS_SOCKET_ERROR ) && ( ulCount < ulLoopsPerSocket ) );

		FreeRTOS_closesocket( xClientSocket );

		/* A short delay to prevent the messages scrolling off the screen too
		quickly. */
		vTaskDelay( x150ms );
	}
}
/*-----------------------------------------------------------*/

static void prvSimpleZeroCopyServerTask( void *pvParameters )
{
int32_t lBytes;
uint8_t *pucUDPPayloadBuffer;
struct freertos_sockaddr xClient, xBindAddress;
uint32_t xClientLength = sizeof( xClient ), ulIPAddress;
xSocket_t xListeningSocket;

	/* Just to prevent compiler warnings. */
	( void ) pvParameters;

	/* Attempt to open the socket. */
	xListeningSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_DGRAM, FREERTOS_IPPROTO_UDP );
	configASSERT( xListeningSocket != FREERTOS_INVALID_SOCKET );

	/* This test receives data sent from a different port on the same IP address.
	Obtain the nodes IP address.  Configure the freertos_sockaddr structure with
	the address being bound to.  The strange casting is to try and remove
	compiler warnings on 32 bit machines.  Note that this task is only created
	after the network is up, so the IP address is valid here. */
	FreeRTOS_GetAddressConfiguration( &ulIPAddress, NULL, NULL, NULL );
	xBindAddress.sin_addr = ulIPAddress;
	xBindAddress.sin_port = ( uint16_t ) ( ( uint32_t ) pvParameters ) & 0xffffUL;
	xBindAddress.sin_port = FreeRTOS_htons( xBindAddress.sin_port );

	/* Bind the socket to the port that the client task will send to. */
	FreeRTOS_bind( xListeningSocket, &xBindAddress, sizeof( xBindAddress ) );

	for( ;; )
	{
		/* Receive data on the socket.  ulFlags has the zero copy bit set
		(FREERTOS_ZERO_COPY) indicating to the stack that a reference to the
		received data should be passed out to this task using the second
		parameter to the FreeRTOS_recvfrom() call.  When this is done the
		IP stack is no longer responsible for releasing the buffer, and
		the task *must* return the buffer to the stack when it is no longer
		needed.  By default the block time is portMAX_DELAY. */
		lBytes = FreeRTOS_recvfrom( xListeningSocket, ( void * ) &pucUDPPayloadBuffer, 0, FREERTOS_ZERO_COPY, &xClient, &xClientLength );

		/* It is expected to receive one more byte than the string length as
		the NULL terminator is also transmitted. */
		configASSERT( lBytes == ( ( portBASE_TYPE ) strlen( ( const char * ) pucUDPPayloadBuffer ) + 1 ) );

		/* Print the received characters. */
		if( lBytes > 0 )
		{
			vOutputString( ( char * ) pucUDPPayloadBuffer );
		}

		if( lBytes >= 0 )
		{
			/* The buffer *must* be freed once it is no longer needed. */
			FreeRTOS_ReleaseUDPPayloadBuffer( pucUDPPayloadBuffer );
		}
	}
}

