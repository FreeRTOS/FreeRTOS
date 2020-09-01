/*
 * FreeRTOS+TCP V2.2.1
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#ifndef FREERTOS_IP_H
#define FREERTOS_IP_H

#ifdef __cplusplus
extern "C" {
#endif

/* Application level configuration options. */
#include "FreeRTOSIPConfig.h"
#include "FreeRTOSIPConfigDefaults.h"
#include "IPTraceMacroDefaults.h"

/* Some constants defining the sizes of several parts of a packet.
These defines come before inlucding the configuration header files. */
#define ipSIZE_OF_ETH_HEADER			14U
#define ipSIZE_OF_IPv4_HEADER			20U
#define ipSIZE_OF_IPv6_HEADER			40U
#define ipSIZE_OF_IGMP_HEADER			8U
#define ipSIZE_OF_ICMPv4_HEADER			8U
#define ipSIZE_OF_ICMPv6_HEADER			24U
#define ipSIZE_OF_UDP_HEADER			8U
#define ipSIZE_OF_TCP_HEADER			20U

/* Application level configuration options. */
#include "FreeRTOSIPConfig.h"
#include "FreeRTOSIPConfigDefaults.h"
#include "IPTraceMacroDefaults.h"

#define ipSIZE_OF_IPv4_ADDRESS	4U
#define ipSIZE_OF_IPv6_ADDRESS	16U

#if( ipconfigUSE_IPv6 != 0 )

	struct xIPv6_Address
	{
		uint8_t ucBytes[ 16 ];
	};

	typedef struct xIPv6_Address IPv6_Address_t;

	#ifndef _MSC_VER
		extern const struct xIPv6_Address in6addr_any;
		extern const struct xIPv6_Address in6addr_loopback;
	#else
		/* Microsoft visual C already has these objects defined.
		Name them slightly different. */
		extern const struct xIPv6_Address FreeRTOS_in6addr_any;
		extern const struct xIPv6_Address FreeRTOS_in6addr_loopback;
		#define in6addr_any			FreeRTOS_in6addr_any
		#define in6addr_loopback	FreeRTOS_in6addr_loopback
	#endif

	/* Note that 'xCompareIPv6_Address' will also check if 'pxRight' is
	the special unicast address: ff02::1:ffnn:nnnn, where nn:nnnn are
	the last 3 bytes of the IPv6 address. */
	BaseType_t xCompareIPv6_Address( const IPv6_Address_t *pxLeft, const IPv6_Address_t *pxRight, size_t uxPrefixLength );

#endif /* ipconfigUSE_IPv6 */

/*
 * Generate a randomized TCP Initial Sequence Number per RFC.
 * This function must be provided my the application builder.
 */
extern uint32_t ulApplicationGetNextSequenceNumber( uint32_t ulSourceAddress,
													uint16_t usSourcePort,
													uint32_t ulDestinationAddress,
													uint16_t usDestinationPort );

/* The number of octets in the MAC and IP addresses respectively. */
#define ipMAC_ADDRESS_LENGTH_BYTES ( 6 )
#define ipIP_ADDRESS_LENGTH_BYTES ( 4 )

/* IP protocol definitions. */
#define ipPROTOCOL_EXT_HEADER	( 0U )	/* Extension header, IPv6 only. */
#define ipPROTOCOL_ICMP			( 1U )
#define ipPROTOCOL_IGMP         ( 2U )
#define ipPROTOCOL_TCP			( 6U )
#define ipPROTOCOL_UDP			( 17U )

#define ipPROTOCOL_ICMP_IPv6	( 58U )

#define ipTYPE_IPv4				( 0x40U )
#define ipTYPE_IPv6				( 0x60U )

/* Some IPv6 ICMP requests. */
#define ipICMP_DEST_UNREACHABLE_IPv6		( ( uint8_t )   1U )
#define ipICMP_PACKET_TOO_BIG_IPv6			( ( uint8_t )   2U )
#define ipICMP_TIME_EXEEDED_IPv6			( ( uint8_t )   3U )
#define ipICMP_PARAMETER_PROBLEM_IPv6		( ( uint8_t )   4U )
#define ipICMP_PING_REQUEST_IPv6			( ( uint8_t ) 128U )
#define ipICMP_PING_REPLY_IPv6				( ( uint8_t ) 129U )
#define ipICMP_ROUTER_SOLICITATION_IPv6		( ( uint8_t ) 133U )
#define ipICMP_ROUTER_ADVERTISEMENT_IPv6	( ( uint8_t ) 134U )
#define ipICMP_NEIGHBOR_SOLICITATION_IPv6	( ( uint8_t ) 135U )
#define ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6	( ( uint8_t ) 136U )

/* The character used to fill ICMP echo requests, and therefore also the
character expected to fill ICMP echo replies. */
#define ipECHO_DATA_FILL_BYTE						'x'

/* Dimensions the buffers that are filled by received Ethernet frames. */
#define ipSIZE_OF_ETH_CRC_BYTES					( 4UL )
#define ipSIZE_OF_ETH_OPTIONAL_802_1Q_TAG_BYTES	( 4UL )
#define ipTOTAL_ETHERNET_FRAME_SIZE				( ( ( uint32_t ) ipconfigNETWORK_MTU ) + ( ( uint32_t ) ipSIZE_OF_ETH_HEADER ) + ipSIZE_OF_ETH_CRC_BYTES + ipSIZE_OF_ETH_OPTIONAL_802_1Q_TAG_BYTES )


/* Space left at the beginning of a network buffer storage area to store a
pointer back to the network buffer.  Should be a multiple of 8 to ensure 8 byte
alignment is maintained on architectures that require it.

In order to get a 32-bit alignment of network packets, an offset of 2 bytes
would be desirable, as defined by ipconfigPACKET_FILLER_SIZE.  So the malloc'd
buffer will have the following contents:
	uint32_t pointer;	// word-aligned
	uchar_8 filler[6];
	<< ETH-header >>	// half-word-aligned
	uchar_8 dest[6];    // start of pucEthernetBuffer
	uchar_8 dest[6];
	uchar16_t type;
	<< IP-header >>		// word-aligned
	uint8_t ucVersionHeaderLength;
	etc
 */

#if( ipconfigBUFFER_PADDING != 0 )
    #define ipBUFFER_PADDING    ipconfigBUFFER_PADDING
#else
    #define ipBUFFER_PADDING    ( 8U + ipconfigPACKET_FILLER_SIZE )
#endif

/* A forward declaration of 'struct xNetworkEndPoint' and 'xNetworkInterface'.
The actual declaration can be found in FreeRTOS_Routing.h which is included
as the last +TCP header file. */
struct xNetworkEndPoint;
struct xNetworkInterface;

/* The structure used to store buffers and pass them around the network stack.
Buffers can be in use by the stack, in use by the network interface hardware
driver, or free (not in use). */
typedef struct xNETWORK_BUFFER
{
	ListItem_t xBufferListItem; 	/* Used to reference the buffer form the free buffer list or a socket. */
	uint32_t ulIPAddress;			/* Source or destination IP address, depending on usage scenario. */
	uint8_t *pucEthernetBuffer; 	/* Pointer to the start of the Ethernet frame. */
	size_t xDataLength; 			/* Starts by holding the total Ethernet frame length, then the UDP/TCP payload length. */
	struct xNetworkInterface *pxInterface;	/* The interface on which the packet was received. */
	struct xNetworkEndPoint *pxEndPoint;	/* The end-point through which this packet shall be sent. */
	uint16_t usPort;				/* Source or destination port, depending on usage scenario. */
	uint16_t usBoundPort;			/* The port to which a transmitting socket is bound. */
	#if( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
		struct xNETWORK_BUFFER *pxNextBuffer; /* Possible optimisation for expert users - requires network driver support. */
	#endif
	#if( ipconfigUSE_IPv6 != 0 )
		IPv6_Address_t xIPv6_Address;
	#endif
} NetworkBufferDescriptor_t;

#include "pack_struct_start.h"
struct xMAC_ADDRESS
{
	uint8_t ucBytes[ ipMAC_ADDRESS_LENGTH_BYTES ];
}
#include "pack_struct_end.h"

typedef struct xMAC_ADDRESS MACAddress_t;

typedef enum eNETWORK_EVENTS
{
	eNetworkUp,		/* The network is configured. */
	eNetworkDown	/* The network connection has been lost. */
} eIPCallbackEvent_t;

typedef enum ePING_REPLY_STATUS
{
	eSuccess = 0,		/* A correct reply has been received for an outgoing ping. */
	eInvalidChecksum,	/* A reply was received for an outgoing ping but the checksum of the reply was incorrect. */
	eInvalidData		/* A reply was received to an outgoing ping but the payload of the reply was not correct. */
} ePingReplyStatus_t;

typedef struct xIP_TIMER
{
	uint32_t
		bActive : 1,	/* This timer is running and must be processed. */
		bExpired : 1;	/* Timer has expired and a task must be processed. */
	TimeOut_t xTimeOut;
	TickType_t ulRemainingTime;
	TickType_t ulReloadTime;
} IPTimer_t;

/* Endian related definitions. */
#if( ipconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN )

	/* FreeRTOS_htons / FreeRTOS_htonl: some platforms might have built-in versions
	using a single instruction so allow these versions to be overridden. */
	#ifndef FreeRTOS_htons
		#define FreeRTOS_htons( usIn ) ( (uint16_t) ( ( ( usIn ) << 8U ) | ( ( usIn ) >> 8U ) ) )
	#endif

	#ifndef	FreeRTOS_htonl
		#define FreeRTOS_htonl( ulIn ) 											\
			(																	\
				( uint32_t ) 													\
				( 																\
					( ( ( ( uint32_t ) ( ulIn ) )                ) << 24  ) | 	\
					( ( ( ( uint32_t ) ( ulIn ) ) & 0x0000ff00UL ) <<  8  ) | 	\
					( ( ( ( uint32_t ) ( ulIn ) ) & 0x00ff0000UL ) >>  8  ) | 	\
					( ( ( ( uint32_t ) ( ulIn ) )                ) >> 24  )  	\
				) 																\
			)
	#endif

#else /* ipconfigBYTE_ORDER */

	#define FreeRTOS_htons( x ) ( ( uint16_t ) ( x ) )
	#define FreeRTOS_htonl( x ) ( ( uint32_t ) ( x ) )

#endif /* ipconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN */

#define FreeRTOS_ntohs( x ) FreeRTOS_htons( x )
#define FreeRTOS_ntohl( x ) FreeRTOS_htonl( x )

#if( ipconfigHAS_INLINE_FUNCTIONS == 1 )

	static portINLINE int32_t  FreeRTOS_max_int32  (int32_t  a, int32_t  b);
	static portINLINE uint32_t FreeRTOS_max_uint32 (uint32_t a, uint32_t b);
	static portINLINE int32_t  FreeRTOS_min_int32  (int32_t  a, int32_t  b);
	static portINLINE uint32_t FreeRTOS_min_uint32 (uint32_t a, uint32_t b);
	static portINLINE uint32_t FreeRTOS_round_up   (uint32_t a, uint32_t d);
	static portINLINE uint32_t FreeRTOS_round_down (uint32_t a, uint32_t d);
	static portINLINE BaseType_t  FreeRTOS_min_BaseType  (BaseType_t  a, BaseType_t  b);

	static portINLINE int32_t  FreeRTOS_max_int32  (int32_t  a, int32_t  b) { return ( a >= b ) ? a : b; }
	static portINLINE uint32_t FreeRTOS_max_uint32 (uint32_t a, uint32_t b) { return ( a >= b ) ? a : b; }
	static portINLINE int32_t  FreeRTOS_min_int32  (int32_t  a, int32_t  b) { return ( a <= b ) ? a : b; }
	static portINLINE uint32_t FreeRTOS_min_uint32 (uint32_t a, uint32_t b) { return ( a <= b ) ? a : b; }
	static portINLINE uint32_t FreeRTOS_round_up   (uint32_t a, uint32_t d) { return d * ( ( a + d - 1U ) / d ); }
	static portINLINE uint32_t FreeRTOS_round_down (uint32_t a, uint32_t d) { return d * ( a / d ); }

	static portINLINE BaseType_t  FreeRTOS_min_BaseType  (BaseType_t  a, BaseType_t  b) { return ( a <= b ) ? a : b; }

#else

	#define FreeRTOS_max_int32(a,b)  ( ( ( ( int32_t  ) ( a ) ) >= ( ( int32_t  ) ( b ) ) ) ? ( ( int32_t  ) ( a ) ) : ( ( int32_t  ) ( b ) ) )
	#define FreeRTOS_max_uint32(a,b) ( ( ( ( uint32_t ) ( a ) ) >= ( ( uint32_t ) ( b ) ) ) ? ( ( uint32_t ) ( a ) ) : ( ( uint32_t ) ( b ) ) )

	#define FreeRTOS_min_int32(a,b)  ( ( ( ( int32_t  ) a ) <= ( ( int32_t  ) b ) ) ? ( ( int32_t  ) a ) : ( ( int32_t  ) b ) )
	#define FreeRTOS_min_uint32(a,b) ( ( ( ( uint32_t ) a ) <= ( ( uint32_t ) b ) ) ? ( ( uint32_t ) a ) : ( ( uint32_t ) b ) )

	/*  Round-up: a = d * ( ( a + d - 1 ) / d ) */
	#define FreeRTOS_round_up(a,d)   ( ( ( uint32_t ) ( d ) ) * ( ( ( ( uint32_t ) ( a ) ) + ( ( uint32_t ) ( d ) ) - 1UL ) / ( ( uint32_t ) ( d ) ) ) )
	#define FreeRTOS_round_down(a,d) ( ( ( uint32_t ) ( d ) ) * ( ( ( uint32_t ) ( a ) ) / ( ( uint32_t ) ( d ) ) ) )

	#define FreeRTOS_min_BaseType(a, b)  ( ( ( BaseType_t  ) ( a ) ) <= ( ( BaseType_t  ) ( b ) ) ? ( ( BaseType_t  ) ( a ) ) : ( ( BaseType_t  ) ( b ) ) )

#endif /* ipconfigHAS_INLINE_FUNCTIONS */

#define ipMS_TO_MIN_TICKS( xTimeInMs ) ( ( pdMS_TO_TICKS( ( xTimeInMs ) ) < ( ( TickType_t ) 1U ) ) ? ( ( TickType_t ) 1U ) : pdMS_TO_TICKS( ( xTimeInMs ) ) )

/* For backward compatibility. */
#define pdMS_TO_MIN_TICKS( xTimeInMs )	ipMS_TO_MIN_TICKS( xTimeInMs )

#ifndef pdTRUE_SIGNED
	/* Temporary solution: eventually the defines below will appear in 'Source\include\projdefs.h' */
	#define pdTRUE_SIGNED		pdTRUE
	#define pdFALSE_SIGNED		pdFALSE
	#define pdTRUE_UNSIGNED		( 1U )
	#define pdFALSE_UNSIGNED	( 0U )
	#define ipTRUE_BOOL			( 1 == 1 )
	#define ipFALSE_BOOL		( 1 == 2 )
#endif

/*
 * FULL, UP-TO-DATE AND MAINTAINED REFERENCE DOCUMENTATION FOR ALL THESE
 * FUNCTIONS IS AVAILABLE ON THE FOLLOWING URL:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/FreeRTOS_TCP_API_Functions.html
 */

/* FreeRTOS_IPStart() replaces the earlier FreeRTOS_IPInit().  It assumes
that network interfaces and IP-addresses have been added using the functions
from FreeRTOS_Routing.h. */
BaseType_t FreeRTOS_IPStart( void );

#if( ipconfigUSE_IPv6 != 0 )
	/* The last parameter is either ipTYPE_IPv4 or ipTYPE_IPv6. */
	void * FreeRTOS_GetUDPPayloadBuffer( size_t uxRequestedSizeBytes, TickType_t uxBlockTimeTicks, uint8_t ucIPType );
#else
void * FreeRTOS_GetUDPPayloadBuffer( size_t uxRequestedSizeBytes, TickType_t uxBlockTimeTicks );
#endif
/*
 * Calculates the starting offset of the UDP payload.
 * If IPv6 enabled, checks for ( usFrameType == ipIPv6_FRAME_TYPE )
 */
uint8_t *pcNetworkBuffer_to_UDPPayloadBuffer( NetworkBufferDescriptor_t *pxNetworkBuffer );

/*
 * Returns the addresses stored in an end-point structure.
 * This function already existed in the release with the single-interface.
 * Only the first parameters is new: an end-point
 */
void FreeRTOS_GetAddressConfiguration( uint32_t *pulIPAddress,
									   uint32_t *pulNetMask,
									   uint32_t *pulGatewayAddress,
									   uint32_t *pulDNSServerAddress,
									   struct xNetworkEndPoint *pxEndPoint );

void FreeRTOS_SetAddressConfiguration( const uint32_t *pulIPAddress,
									   const uint32_t *pulNetMask,
									   const uint32_t *pulGatewayAddress,
									   const uint32_t *pulDNSServerAddress,
									   struct xNetworkEndPoint *pxEndPoint );

BaseType_t FreeRTOS_SendPingRequest( uint32_t ulIPAddress, size_t uxNumberOfBytesToSend, TickType_t uxBlockTimeTicks );
void FreeRTOS_ReleaseUDPPayloadBuffer( void *pvBuffer );
/* _HT_ FreeRTOS_GetMACAddress() can not continue to exist with multiple interfaces.*/
//const uint8_t * FreeRTOS_GetMACAddress( void );
void vApplicationIPNetworkEventHook( eIPCallbackEvent_t eNetworkEvent, struct xNetworkEndPoint *pxEndPoint );
	void vApplicationPingReplyHook( ePingReplyStatus_t eStatus, uint16_t usIdentifier );
uint32_t FreeRTOS_GetIPAddress( void );
/*
	_HT_ : these functions come from the IPv4-only library.
	They should get an extra parameter, the end-point
void FreeRTOS_SetIPAddress( uint32_t ulIPAddress );
void FreeRTOS_SetNetmask( uint32_t ulNetmask );
void FreeRTOS_SetGatewayAddress( uint32_t ulGatewayAddress );
uint32_t FreeRTOS_GetGatewayAddress( void );
uint32_t FreeRTOS_GetDNSServerAddress( void );
uint32_t FreeRTOS_GetNetmask( void );
*/

void FreeRTOS_OutputARPRequest( uint32_t ulIPAddress );

/* Return true if a given end-point is up and running.
When FreeRTOS_IsNetworkUp() is called with NULL as a parameter,
it will return pdTRUE when all end-points are up. */
BaseType_t FreeRTOS_IsEndPointUp( const struct xNetworkEndPoint *pxEndPoint );

/* Return pdTRUE if all end-points are up.
When pxInterface is null, all end-points will be checked. */
BaseType_t FreeRTOS_AllEndPointsUp( const struct xNetworkInterface *pxInterface );

/* For backward compatibility: FreeRTOS_IsNetworkUp() returns true
as soon as all end-points are up. */
BaseType_t FreeRTOS_IsNetworkUp( void );

#if( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
	UBaseType_t uxGetMinimumIPQueueSpace( void );
#endif

#if ( ipconfigHAS_PRINTF != 0 )
	extern void vPrintResourceStats( void );
#else
	#define vPrintResourceStats()	do {} while( ipFALSE_BOOL )
#endif

/*
 * Defined in FreeRTOS_Sockets.c
 * //_RB_ Don't think this comment is correct.  If this is for internal use only it should appear after all the public API functions and not start with FreeRTOS_.
 * Socket has had activity, reset the timer so it will not be closed
 * because of inactivity
 */
const char *FreeRTOS_GetTCPStateName( UBaseType_t ulState);

/* _HT_ Temporary: show all valid ARP entries
 */
void FreeRTOS_PrintARPCache( void );
#if( ipconfigUSE_IPv6 != 0 )
	void FreeRTOS_ClearND( void );
#endif/* ( ipconfigUSE_IPv6 != 0 ) */

/* Return pdTRUE if the IPv4 address is a multicast address. */
BaseType_t xIsIPv4Multicast( uint32_t ulIPAddress );

#if( ipconfigUSE_IPv6 != 0 )
	BaseType_t xIsIPv6Multicast( const IPv6_Address_t *pxIPAddress );
#endif/* ( ipconfigUSE_IPv6 != 0 ) */

#if( ipconfigDHCP_REGISTER_HOSTNAME == 1 )

	/* DHCP has an option for clients to register their hostname.  It doesn't
	have much use, except that a device can be found in a router along with its
	name. If this option is used the callback below must be provided by the
	application	writer to return a const string, denoting the device's name. */
	const char *pcApplicationHostnameHook( void );

#endif /* ipconfigDHCP_REGISTER_HOSTNAME */


/* This xApplicationGetRandomNumber() will set *pulNumber to a random number,
and return pdTRUE. When the random number generator is broken, it shall return
pdFALSE.
The function is defined in 'iot_secure_sockets.c'.
If that module is not included in the project, the application must provide an
implementation of it.
The macro's ipconfigRAND32() and configRAND32() are not in use anymore. */
BaseType_t xApplicationGetRandomNumber( uint32_t *pulNumber );

/* For backward compatibility define old structure names to the newer equivalent
structure name. */
#ifndef ipconfigENABLE_BACKWARD_COMPATIBILITY
	#define ipconfigENABLE_BACKWARD_COMPATIBILITY	1
#endif

#if( ipconfigENABLE_BACKWARD_COMPATIBILITY == 1 )
	#define xIPStackEvent_t 			IPStackEvent_t
	#define xNetworkBufferDescriptor_t 	NetworkBufferDescriptor_t
	#define xMACAddress_t 				MACAddress_t
	#define xWinProperties_t 			WinProperties_t
	#define xSocket_t 					Socket_t
	#define xSocketSet_t 				SocketSet_t
	#define ipSIZE_OF_IP_HEADER			ipSIZE_OF_IPv4_HEADER

	/* Since August 2016, the public types and fields below have changed name:
	abbreviations TCP/UDP are now written in capitals, and type names now end with "_t". */
	#define FOnConnected				FOnConnected_t
	#define FOnTcpReceive				FOnTCPReceive_t
	#define FOnTcpSent					FOnTCPSent_t
	#define FOnUdpReceive				FOnUDPReceive_t
	#define FOnUdpSent					FOnUDPSent_t

	#define pOnTcpConnected				pxOnTCPConnected
	#define pOnTcpReceive				pxOnTCPReceive
	#define pOnTcpSent					pxOnTCPSent
	#define pOnUdpReceive				pxOnUDPReceive
	#define pOnUdpSent					pxOnUDPSent

	#define FOnUdpSent					FOnUDPSent_t
	#define FOnTcpSent					FOnTCPSent_t
#endif /* ipconfigENABLE_BACKWARD_COMPATIBILITY */

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* FREERTOS_IP_H */













