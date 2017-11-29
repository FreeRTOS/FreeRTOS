/*
 * FreeRTOS+UDP V1.0.4
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
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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

#ifndef FREERTOS_UDP_H
#define FREERTOS_UDP_H

/* Standard includes. */
#include <string.h>

/* Application level configuration options. */
#include "FreeRTOSIPConfig.h"

#ifndef INC_FREERTOS_H
	#error FreeRTOS.h must be included before FreeRTOS_Sockets.h.
#endif

#ifndef INC_TASK_H
	#ifndef TASK_H /* For compatibility with older FreeRTOS versions. */
		#error The FreeRTOS header file task.h must be included before FreeRTOS_Sockets.h.
	#endif
#endif

/* Assigned to an xSocket_t variable when the socket is not valid, probably
because it could not be created. */
#define FREERTOS_INVALID_SOCKET	( ( void * ) ~0U )

/* API function error values.  As errno is supported, the FreeRTOS sockets
functions return error codes rather than just a pass or fail indication. */
#define FREERTOS_SOCKET_ERROR	( -1 )
#define FREERTOS_EWOULDBLOCK	( -2 )
#define FREERTOS_EINVAL			( -4 )
#define FREERTOS_EADDRNOTAVAIL	( -5 )
#define FREERTOS_EADDRINUSE		( -6 )
#define FREERTOS_ENOBUFS		( -7 )
#define FREERTOS_ENOPROTOOPT	( -8 )

/* Values for the parameters to FreeRTOS_socket(), inline with the Berkeley
standard.  See the documentation of FreeRTOS_socket() for more information. */
#define FREERTOS_AF_INET		( 2 )
#define FREERTOS_SOCK_DGRAM		( 2 )
#define FREERTOS_IPPROTO_UDP	( 17 )

/* A bit value that can be passed into the FreeRTOS_sendto() function as part of
the flags parameter.  Setting the FREERTOS_ZERO_COPY in the flags parameter
indicates that the zero copy interface is being used.  See the documentation for
FreeRTOS_sockets() for more information. */
#define FREERTOS_ZERO_COPY		( 0x01UL )

/* Values that can be passed in the option name parameter of calls to
FreeRTOS_setsockopt(). */
#define FREERTOS_SO_RCVTIMEO		( 0 )		/* Used to set the receive time out. */
#define FREERTOS_SO_SNDTIMEO		( 1 )		/* Used to set the send time out. */
#define FREERTOS_SO_UDPCKSUM_OUT	( 0x02 ) 	/* Used to turn the use of the UDP checksum by a socket on or off.  This also doubles as part of an 8-bit bitwise socket option. */
#define FREERTOS_NOT_LAST_IN_FRAGMENTED_PACKET 	( 0x80 )  /* For internal use only, but also part of an 8-bit bitwise value. */
#define FREERTOS_FRAGMENTED_PACKET				( 0x40 )  /* For internal use only, but also part of an 8-bit bitwise value. */

/* For compatibility with the expected Berkeley sockets naming. */
#define socklen_t uint32_t

/* For this limited implementation, only two members are required in the
Berkeley style sockaddr structure. */
struct freertos_sockaddr
{
	uint16_t sin_port;
	uint32_t sin_addr;
};

#if ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN

	#define FreeRTOS_inet_addr_quick( ucOctet0, ucOctet1, ucOctet2, ucOctet3 )				\
										( ( ( ( uint32_t ) ( ucOctet3 ) ) << 24UL ) |		\
										  ( ( ( uint32_t ) ( ucOctet2 ) ) << 16UL ) |		\
										  ( ( ( uint32_t ) ( ucOctet1 ) ) <<  8UL ) |		\
										  ( ( uint32_t ) ( ucOctet0 ) ) )

	#define FreeRTOS_inet_ntoa( ulIPAddress, pucBuffer )									\
										sprintf( ( char * ) ( pucBuffer ), "%d.%d.%d.%d",	\
											( int ) ( ( ulIPAddress ) & 0xffUL ),			\
											( int ) ( ( ( ulIPAddress ) >> 8UL ) & 0xffUL ),\
											( int ) ( ( ( ulIPAddress ) >> 16UL ) & 0xffUL ),\
											( int ) ( ( ( ulIPAddress ) >> 24UL ) & 0xffUL ) )

#else /* ipconfigBYTE_ORDER */

	#define FreeRTOS_inet_addr_quick( ucOctet0, ucOctet1, ucOctet2, ucOctet3 )				\
										( ( ( ( uint32_t ) ( ucOctet0 ) ) << 24UL ) |		\
										  ( ( ( uint32_t ) ( ucOctet1 ) ) << 16UL ) |		\
										  ( ( ( uint32_t ) ( ucOctet2 ) ) <<  8UL ) |		\
										  ( ( uint32_t ) ( ucOctet3 ) ) )

	#define FreeRTOS_inet_ntoa( ulIPAddress, pucBuffer )									\
										sprintf( ( char * ) ( pucBuffer ), "%d.%d.%d.%d",	\
											( ( ( ulIPAddress ) >> 24UL ) & 0xffUL ),		\
											( ( ( ulIPAddress ) >> 16UL ) & 0xffUL ),		\
											( ( ( ulIPAddress ) >> 8UL ) & 0xffUL ),		\
											( ( ulIPAddress ) & 0xffUL ) )

#endif /* ipconfigBYTE_ORDER */

/* The socket type itself. */
typedef void *xSocket_t;

/* The xSocketSet_t type is the equivalent to the fd_set type used by the
Berkeley API. */
typedef void *xSocketSet_t;

/**
 * FULL, UP-TO-DATE AND MAINTAINED REFERENCE DOCUMENTATION FOR ALL THESE
 * FUNCTIONS IS AVAILABLE ON THE FOLLOWING URL:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/FreeRTOS_UDP_API_Functions.shtml
 */
xSocket_t FreeRTOS_socket( BaseType_t xDomain, BaseType_t xType, BaseType_t xProtocol );
int32_t FreeRTOS_recvfrom( xSocket_t xSocket, void *pvBuffer, size_t xBufferLength, uint32_t ulFlags, struct freertos_sockaddr *pxSourceAddress, socklen_t *pxSourceAddressLength );
int32_t FreeRTOS_sendto( xSocket_t xSocket, const void *pvBuffer, size_t xTotalDataLength, uint32_t ulFlags, const struct freertos_sockaddr *pxDestinationAddress, socklen_t xDestinationAddressLength );
BaseType_t FreeRTOS_bind( xSocket_t xSocket, struct freertos_sockaddr *pxAddress, socklen_t xAddressLength );
BaseType_t FreeRTOS_setsockopt( xSocket_t xSocket, int32_t lLevel, int32_t lOptionName, const void *pvOptionValue, size_t xOptionLength );
BaseType_t FreeRTOS_closesocket( xSocket_t xSocket );
uint32_t FreeRTOS_gethostbyname( const char *pcHostName );
uint32_t FreeRTOS_inet_addr( const char *pcIPAddress );

#if ipconfigSUPPORT_SELECT_FUNCTION == 1
	xSocketSet_t FreeRTOS_CreateSocketSet( UBaseType_t uxEventQueueLength );
	BaseType_t FreeRTOS_FD_SET( xSocket_t xSocket, xSocketSet_t xSocketSet );
	BaseType_t FreeRTOS_FD_CLR( xSocket_t xSocket, xSocketSet_t xSocketSet );
	xSocket_t FreeRTOS_select( xSocketSet_t xSocketSet, TickType_t xBlockTimeTicks );
#endif /* ipconfigSUPPORT_SELECT_FUNCTION */

#endif /* FREERTOS_UDP_H */













