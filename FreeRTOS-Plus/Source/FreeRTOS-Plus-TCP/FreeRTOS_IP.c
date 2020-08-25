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

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_ND.h"

#if !defined( ipconfigMULTI_INTERFACE ) || ( ipconfigMULTI_INTERFACE == 0 )
	#ifndef _lint
		#error Please define ipconfigMULTI_INTERFACE as 1 to use the multi version
	#endif
#endif

/* Used to ensure the structure packing is having the desired effect.  The
'volatile' is used to prevent compiler warnings about comparing a constant with
a constant. */
#ifndef _lint
	#define ipEXPECTED_EthernetHeader_t_SIZE	( ( size_t ) 14 )
	#define ipEXPECTED_ARPHeader_t_SIZE			( ( size_t ) 28 )
	#define ipEXPECTED_IPHeader_t_SIZE			( ( size_t ) 20 )
	#define ipEXPECTED_IGMPHeader_t_SIZE		( ( size_t ) 8 )
	#define ipEXPECTED_ICMPHeader_t_SIZE		( ( size_t ) 8 )
	#define ipEXPECTED_UDPHeader_t_SIZE			( ( size_t ) 8 )
	#define ipEXPECTED_TCPHeader_t_SIZE			( ( size_t ) 20 )
#endif

/* ICMP protocol definitions. */
#define ipICMP_ECHO_REQUEST				( ( uint8_t ) 8 )
#define ipICMP_ECHO_REPLY				( ( uint8_t ) 0 )

#if( ipconfigUSE_IPv6 != 0 )
	/* IPv6 multicast MAC address starts with 33-33-. */
	#define ipMULTICAST_MAC_ADDRESS_IPv6_0	0x33U
	#define ipMULTICAST_MAC_ADDRESS_IPv6_1	0x33U
#endif

/* IPv4 multi-cast addresses range from 224.0.0.0.0 to 240.0.0.0. */
#define	ipFIRST_MULTI_CAST_IPv4		0xE0000000UL
#define	ipLAST_MULTI_CAST_IPv4		0xF0000000UL

/* The first byte in the IPv4 header combines the IP version (4) with
with the length of the IP header. */
#define	ipIPV4_VERSION_HEADER_LENGTH_MIN	0x45U
#define	ipIPV4_VERSION_HEADER_LENGTH_MAX	0x4FU
	
/* Time delay between repeated attempts to initialise the network hardware. */
#ifndef ipINITIALISATION_RETRY_DELAY
	#define ipINITIALISATION_RETRY_DELAY	( pdMS_TO_TICKS( 3000U ) )
#endif

/* Defines how often the ARP timer callback function is executed.  The time is
shorted in the Windows simulator as simulated time is not real time. */
#ifndef	ipARP_TIMER_PERIOD_MS
	#ifdef _WINDOWS_
		#define ipARP_TIMER_PERIOD_MS	( 500U ) /* For windows simulator builds. */
	#else
		#define ipARP_TIMER_PERIOD_MS	( 10000U )
	#endif
#endif

#ifndef iptraceIP_TASK_STARTING
	#define	iptraceIP_TASK_STARTING()	do {} while( ipFALSE_BOOL )
#endif

#if( ( ipconfigUSE_TCP == 1 ) && !defined( ipTCP_TIMER_PERIOD_MS ) )
	/* When initialising the TCP timer,
	give it an initial time-out of 1 second. */
	#define ipTCP_TIMER_PERIOD_MS	( 1000U )
#endif

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
driver will filter incoming packets and only pass the stack those packets it
considers need processing.  In this case ipCONSIDER_FRAME_FOR_PROCESSING() can
be #defined away.  If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 0
then the Ethernet driver will pass all received packets to the stack, and the
stack must do the filtering itself.  In this case ipCONSIDER_FRAME_FOR_PROCESSING
needs to call eConsiderFrameForProcessing. */
#if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#else
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eProcessBuffer
#endif

#if( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 )
	#if( ipconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN )
		/* The bits in the two byte IP header field that make up the fragment offset value. */
		#define ipFRAGMENT_OFFSET_BIT_MASK				( ( uint16_t ) 0xff0f )
	#else
		/* The bits in the two byte IP header field that make up the fragment offset value. */
		#define ipFRAGMENT_OFFSET_BIT_MASK				( ( uint16_t ) 0x0fff )
	#endif /* ipconfigBYTE_ORDER */
#endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */

/* The maximum time the IP task is allowed to remain in the Blocked state if no
events are posted to the network event queue. */
#ifndef	ipconfigMAX_IP_TASK_SLEEP_TIME
	#define ipconfigMAX_IP_TASK_SLEEP_TIME ( pdMS_TO_TICKS( 10000UL ) )
#endif

/* Returned as the (invalid) checksum when the protocol being checked is not
handled.  The value is chosen simply to be easy to spot when debugging. */
#define ipUNHANDLED_PROTOCOL		0x4321U

/* Returned to indicate a valid checksum. */
#define ipCORRECT_CRC				0xffffU

/* Returned to indicate incorrect checksum. */
#define ipWRONG_CRC					0x0000U

/* Returned as the (invalid) checksum when the length of the data being checked
had an invalid length. */
#define ipINVALID_LENGTH			0x1234U

/*-----------------------------------------------------------*/

#if( ipconfigUSE_IPv6 != 0 )
	const struct xIPv6_Address in6addr_any = { 0 };
	const struct xIPv6_Address in6addr_loopback = { { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 } };
#endif

/*-----------------------------------------------------------*/

/* Used in checksum calculation. */
typedef union _xUnion32
{
	uint32_t u32;
	uint16_t u16[ 2 ];
	uint8_t u8[ 4 ];
} xUnion32;

/* Used in checksum calculation. */
typedef union _xUnionPtr
{
	uint32_t *u32ptr;
	uint16_t *u16ptr;
	uint8_t *u8ptr;
} xUnionPtr;

/*-----------------------------------------------------------*/

/*
 * The main TCP/IP stack processing task.  This task receives commands/events
 * from the network hardware drivers and tasks that are using sockets.  It also
 * maintains a set of protocol timers.
 */
static void prvIPTask( void *pvParameters );

/*
 * Called when new data is available from the network interface.
 */
static void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

/*
 * Process incoming IP packets.
 */
static eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket, NetworkBufferDescriptor_t * const pxNetworkBuffer );

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
	/*
	 * Process incoming ICMP packets.
	 */
	static eFrameProcessingResult_t prvProcessICMPPacket( ICMPPacket_t * const pxICMPPacket );
#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */

/*
 * Turns around an incoming ping request to convert it into a ping reply.
 */
#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )
	static eFrameProcessingResult_t prvProcessICMPEchoRequest( ICMPPacket_t * const pxICMPPacket );
#endif /* ipconfigREPLY_TO_INCOMING_PINGS */

/*
 * Processes incoming ping replies.  The application callback function
 * vApplicationPingReplyHook() is called with the results.
 */
#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
	static void prvProcessICMPEchoReply( ICMPPacket_t * const pxICMPPacket );
#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

/*
 * Called to create a network connection when the stack is first started, or
 * when the network connection is lost.
 */
static void prvProcessNetworkDownEvent( NetworkInterface_t *pxInterface );

/*
 * Checks the ARP, DHCP and TCP timers to see if any periodic or timeout
 * processing is required.
 */
static void prvCheckNetworkTimers( void );

/*
 * Determine how long the IP task can sleep for, which depends on when the next
 * periodic or timeout processing must be performed.
 */
static TickType_t prvCalculateSleepTime( void );

/*
 * The network card driver has received a packet.  In the case that it is part
 * of a linked packet chain, walk through it to handle every message.
 */
static void prvHandleEthernetPacket( NetworkBufferDescriptor_t *pxBuffer );

/* Handle the 'eNetworkTxEvent': forward a packet from an application to the NIC. */
static void prvForwardTxPacket( NetworkBufferDescriptor_t * pxNetworkBuffer, BaseType_t xReleaseAfterSend );

/*
 * Utility functions for the light weight IP timers.
 */
static void prvIPTimerStart( IPTimer_t *pxTimer, TickType_t xTime );
static BaseType_t prvIPTimerCheck( IPTimer_t *pxTimer );
static void prvIPTimerReload( IPTimer_t *pxTimer, TickType_t xTime );

/* The function 'prvAllowIPPacket()' checks if a packets should be processed. */
static eFrameProcessingResult_t prvAllowIPPacketIPv4( const IPPacket_t * const pxIPPacket,
													  const NetworkBufferDescriptor_t * const pxNetworkBuffer,
													  UBaseType_t uxHeaderLength );

#if( ipconfigUSE_IPv6 != 0 )
	static eFrameProcessingResult_t prvAllowIPPacketIPv6( const IPHeader_IPv6_t * const pxIPv6Header,
														  const NetworkBufferDescriptor_t * const pxNetworkBuffer,
														  UBaseType_t uxHeaderLength );
#endif

/*-----------------------------------------------------------*/

/* The queue used to pass events into the IP-task for processing. */
QueueHandle_t xNetworkEventQueue = NULL;

/*_RB_ Requires comment. */
uint16_t usPacketIdentifier = 0U;

/* For convenience, a MAC address of all 0xffs is defined const for quick
reference. */
const MACAddress_t xBroadcastMACAddress = { { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff } };

/* Used to ensure network down events cannot be missed when they cannot be
posted to the network event queue because the network event queue is already
full. */
static volatile BaseType_t xNetworkDownEventPending = pdFALSE;

/* Stores the handle of the task that handles the stack.  The handle is used
(indirectly) by some utility function to determine if the utility function is
being called by a task (in which case it is ok to block) or by the IP task
itself (in which case it is not ok to block). */
static TaskHandle_t xIPTaskHandle = NULL;

#if( ipconfigUSE_TCP != 0 )
	/* Set to a non-zero value if one or more TCP message have been processed
	within the last round. */
	static BaseType_t xProcessedTCPMessage;
#endif

/* 'xAllNetworksUp' becomes pdTRUE as soon as all network interfaces have
been initialised. */
static BaseType_t xAllNetworksUp = pdFALSE;

/* As long as not all networks are up, repeat initialisation by calling the
xNetworkInterfaceInitialise() function of the interfaces that are not ready. */
static IPTimer_t xNetworkTimer;

/*
A timer for each of the following processes, all of which need attention on a
regular basis:
	1. ARP, to check its table entries
	2. DPHC, to send requests and to renew a reservation
	3. TCP, to check for timeouts, resends
	4. DNS, to check for timeouts when looking-up a domain.
 */
static IPTimer_t xARPTimer;
#if( ipconfigUSE_TCP != 0 )
	static IPTimer_t xTCPTimer;
#endif
#if( ipconfigDNS_USE_CALLBACKS != 0 )
	static IPTimer_t xDNSTimer;
#endif

/* Set to pdTRUE when the IP task is ready to start processing packets. */
/* coverity[misra_c_2012_rule_8_9_violation] */
/* "xIPTaskInitialised" should be defined at block scope. */
static BaseType_t xIPTaskInitialised = pdFALSE;

#if( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
	/* Keep track of the lowest amount of space in 'xNetworkEventQueue'. */
	static UBaseType_t uxQueueMinimumSpace = ipconfigEVENT_QUEUE_LENGTH;
#endif

/*-----------------------------------------------------------*/

/* Coverity want to make pvParameters const, which would make it incompatible. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static void prvIPTask( void *pvParameters )
{
IPStackEvent_t xReceivedEvent;
TickType_t xNextIPSleep;
FreeRTOS_Socket_t *pxSocket;
#if( ipconfigUSE_IPv6 != 0 )
	struct freertos_sockaddr6 xAddress;
#else
	struct freertos_sockaddr xAddress;
#endif
NetworkInterface_t *pxInterface;

	/* Just to prevent compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* A possibility to set some additional task properties. */
	iptraceIP_TASK_STARTING();

	/* Generate a dummy message to say that the network connection has gone
	down.  This will cause this task to initialise the network interface.  After
	this it is the responsibility of the network interface hardware driver to
	send this message if a previously connected network is disconnected. */

	prvIPTimerReload( &( xNetworkTimer ), pdMS_TO_TICKS( ipINITIALISATION_RETRY_DELAY ) );
	for( pxInterface = pxNetworkInterfaces; pxInterface != NULL; pxInterface = pxInterface->pxNext )
	{
		/* Post a 'eNetworkDownEvent' for every interface. */
		FreeRTOS_NetworkDown( pxInterface );
	}

	#if( ipconfigUSE_TCP == 1 )
	{
		/* Initialise the TCP timer. */
		prvIPTimerReload( &xTCPTimer, pdMS_TO_TICKS( ipTCP_TIMER_PERIOD_MS ) );
	}
	#endif

	#if( ipconfigDNS_USE_CALLBACKS != 0 )
	{
		/* The following function is declared in FreeRTOS_DNS.c	and 'private' to
		this library */
		vDNSInitialise();
	}
	#endif /* ipconfigDNS_USE_CALLBACKS != 0 */

	/* Initialisation is complete and events can now be processed. */
	xIPTaskInitialised = pdTRUE;

	FreeRTOS_debug_printf( ( "prvIPTask started\n" ) );

	/* Loop, processing IP events. */
	for( ;; )
	{
		ipconfigWATCHDOG_TIMER();

		/* Check the ARP, DHCP and TCP timers to see if there is any periodic
		or timeout processing to perform. */
		prvCheckNetworkTimers();

		/* Calculate the acceptable maximum sleep time. */
		xNextIPSleep = prvCalculateSleepTime();

		/* Wait until there is something to do. If the following call exits
		 * due to a time out rather than a message being received, set a
		 * 'NoEvent' value. */
		if( xQueueReceive( xNetworkEventQueue, ipPOINTER_CAST( void *, &xReceivedEvent ), xNextIPSleep ) == pdFALSE )
		{
			xReceivedEvent.eEventType = eNoEvent;
		}

		#if( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
		{
			if( xReceivedEvent.eEventType != eNoEvent )
			{
			UBaseType_t uxCount;

				uxCount = uxQueueSpacesAvailable( xNetworkEventQueue );
				if( uxQueueMinimumSpace > uxCount )
				{
					uxQueueMinimumSpace = uxCount;
				}
			}
		}
		#endif /* ipconfigCHECK_IP_QUEUE_SPACE */

		iptraceNETWORK_EVENT_RECEIVED( xReceivedEvent.eEventType );

		switch( xReceivedEvent.eEventType )
		{
			case eNetworkDownEvent :
				/* Attempt to establish a connection. */
				prvProcessNetworkDownEvent( ipPOINTER_CAST( NetworkInterface_t *, xReceivedEvent.pvData ) );
				break;

			case eNetworkRxEvent:
				/* The network hardware driver has received a new packet.  A
				pointer to the received buffer is located in the pvData member
				of the received event structure. */
				prvHandleEthernetPacket( ipPOINTER_CAST( NetworkBufferDescriptor_t *, xReceivedEvent.pvData ) );
				break;

			case eNetworkTxEvent:
				/* Send a network packet. The ownership will  be transferred to
				the driver, which will release it after delivery. */
				prvForwardTxPacket( ipPOINTER_CAST( NetworkBufferDescriptor_t *, xReceivedEvent.pvData ), pdTRUE );
				break;

			case eARPTimerEvent :
				/* The ARP timer has expired, process the ARP cache. */
				vARPAgeCache();
				break;

			case eSocketBindEvent:
				/* FreeRTOS_bind (a user API) wants the IP-task to bind a socket
				to a port. The port number is communicated in the socket field
				usLocalPort. vSocketBind() will actually bind the socket and the
				API will unblock as soon as the eSOCKET_BOUND event is
				triggered. */
				pxSocket = ipPOINTER_CAST( FreeRTOS_Socket_t *, xReceivedEvent.pvData );
				xAddress.sin_len = ( uint8_t ) sizeof( xAddress );
			#if( ipconfigUSE_IPv6 != 0 )
				if( pxSocket->bits.bIsIPv6 != pdFALSE_UNSIGNED )
				{
					xAddress.sin_family = FREERTOS_AF_INET6;
					( void ) memcpy( xAddress.sin_addrv6.ucBytes, pxSocket->xLocalAddress_IPv6.ucBytes, sizeof( xAddress.sin_addrv6.ucBytes ) );
				}
				else
			#endif
				{
				struct freertos_sockaddr *pxAddress = ipPOINTER_CAST( struct freertos_sockaddr *, &( xAddress ) );

					pxAddress->sin_family = FREERTOS_AF_INET;
					pxAddress->sin_addr = FreeRTOS_htonl( pxSocket->ulLocalAddress );
				}
				xAddress.sin_port = FreeRTOS_htons( pxSocket->usLocalPort );
				/* 'ulLocalAddress' and 'usLocalPort' will be set again by vSocketBind(). */
				pxSocket->ulLocalAddress = 0;
				pxSocket->usLocalPort = 0;
				( void ) vSocketBind( pxSocket, ipPOINTER_CAST( struct freertos_sockaddr *, &( xAddress ) ), sizeof( xAddress ), pdFALSE );

				/* Before 'eSocketBindEvent' was sent it was tested that
				( xEventGroup != NULL ) so it can be used now to wake up the
				user. */
				pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_BOUND;
				vSocketWakeUpUser( pxSocket );
				break;

			case eSocketCloseEvent :
				/* The user API FreeRTOS_closesocket() has sent a message to the
				IP-task to actually close a socket. This is handled in
				vSocketClose().  As the socket gets closed, there is no way to
				report back to the API, so the API won't wait for the result */
				( void ) vSocketClose( ipPOINTER_CAST( FreeRTOS_Socket_t *, xReceivedEvent.pvData ) );
				break;

			case eStackTxEvent :
				/* The network stack has generated a packet to send.  A
				pointer to the generated buffer is located in the pvData
				member of the received event structure. */
				vProcessGeneratedUDPPacket( ipPOINTER_CAST( NetworkBufferDescriptor_t *, xReceivedEvent.pvData ) );
				break;

			case eDHCP_RA_Event:
				/* The DHCP state machine needs processing. */
				#if( ipconfigUSE_DHCP == 1 )
				{
					/* Process DHCP messages for a given end-point. */
					vDHCPProcess( pdFALSE, ipPOINTER_CAST( NetworkEndPoint_t *, xReceivedEvent.pvData ) );
				}
				#endif /* ipconfigUSE_DHCP */
				#if( ipconfigUSE_RA == 1 )
				{
					/* Process RA messages for a given end-point. */
					vRAProcess( pdFALSE, ipPOINTER_CAST( NetworkEndPoint_t *, xReceivedEvent.pvData ) );
				}
				#endif /* ipconfigUSE_RA */
				break;

			case eSocketSelectEvent :
				/* FreeRTOS_select() has got unblocked by a socket event,
				vSocketSelect() will check which sockets actually have an event
				and update the socket field xSocketBits. */
				#if( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
				{
					#if( ipconfigSELECT_USES_NOTIFY != 0 )
					{
						SocketSelectMessage_t *pxMessage = ipPOINTER_CAST( SocketSelectMessage_t *, xReceivedEvent.pvData );
						vSocketSelect( pxMessage->pxSocketSet );
						( void ) xTaskNotifyGive( pxMessage->xTaskhandle );
					}
					#else
					{
						vSocketSelect( ipPOINTER_CAST( SocketSelect_t *, xReceivedEvent.pvData ) );
					}
					#endif	/* ( ipconfigSELECT_USES_NOTIFY != 0 ) */
				}
				#endif /* ipconfigSUPPORT_SELECT_FUNCTION == 1 */
				break;

			case eSocketSignalEvent :
				#if( ipconfigSUPPORT_SIGNALS != 0 )
				{
					/* Some task wants to signal the user of this socket in
					order to interrupt a call to recv() or a call to select(). */
					( void ) FreeRTOS_SignalSocket( ipPOINTER_CAST( Socket_t, xReceivedEvent.pvData ) );
				}
				#endif /* ipconfigSUPPORT_SIGNALS */
				break;

			case eTCPTimerEvent :
				#if( ipconfigUSE_TCP == 1 )
				{
					/* Simply mark the TCP timer as expired so it gets processed
					the next time prvCheckNetworkTimers() is called. */
					xTCPTimer.bExpired = pdTRUE_UNSIGNED;
				}
				#endif /* ipconfigUSE_TCP */
				break;

			case eTCPAcceptEvent:
				/* The API FreeRTOS_accept() was called, the IP-task will now
				check if the listening socket (communicated in pvData) actually
				received a new connection. */
				#if( ipconfigUSE_TCP == 1 )
				{
					pxSocket = ipPOINTER_CAST( FreeRTOS_Socket_t *, xReceivedEvent.pvData );

					if( xTCPCheckNewClient( pxSocket ) != pdFALSE )
					{
						pxSocket->xEventBits |= ( EventBits_t ) eSOCKET_ACCEPT;
						vSocketWakeUpUser( pxSocket );
					}
				}
				#endif /* ipconfigUSE_TCP */
				break;

			case eTCPNetStat:
				/* FreeRTOS_netstat() was called to have the IP-task print an
				overview of all sockets and their connections */
				#if( ( ipconfigUSE_TCP == 1 ) && ( ipconfigHAS_PRINTF == 1 ) )
				{
					vTCPNetStat();
				}
				#endif /* ipconfigUSE_TCP */
				break;

			case eNoEvent:
				/* xQueueReceive() returned because of a normal time-out. */
				break;

			default :
				/* Should not get here. */
				break;
		}

		if( xNetworkDownEventPending != pdFALSE )
		{
			/* A network down event could not be posted to the network event
			queue because the queue was full.
			As this code runs in the IP-task, it can be done directly by
			calling prvProcessNetworkDownEvent(). */
			xNetworkDownEventPending = pdFALSE;
			for( pxInterface = FreeRTOS_FirstNetworkInterface();
				 pxInterface != NULL;
				 pxInterface = FreeRTOS_NextNetworkInterface( pxInterface ) )
			{
				if( pxInterface->bits.bCallDownEvent != pdFALSE_UNSIGNED )
				{
					prvProcessNetworkDownEvent( pxInterface );
					pxInterface->bits.bCallDownEvent = pdFALSE_UNSIGNED;
				}
			}
		}
	}
}
/*-----------------------------------------------------------*/

BaseType_t xIsCallingFromIPTask( void )
{
BaseType_t xReturn;

	if( xTaskGetCurrentTaskHandle() == xIPTaskHandle )
	{
		xReturn = pdTRUE;
	}
	else
	{
		xReturn = pdFALSE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvHandleEthernetPacket( NetworkBufferDescriptor_t *pxBuffer )
{
	#if( ipconfigUSE_LINKED_RX_MESSAGES == 0 )
	{
		/* When ipconfigUSE_LINKED_RX_MESSAGES is not set to 0 then only one
		buffer will be sent at a time.  This is the default way for +TCP to pass
		messages from the MAC to the TCP/IP stack. */
		prvProcessEthernetPacket( pxBuffer );
	}
	#else /* ipconfigUSE_LINKED_RX_MESSAGES */
	{
	NetworkBufferDescriptor_t *pxNextBuffer;

		/* An optimisation that is useful when there is high network traffic.
		Instead of passing received packets into the IP task one at a time the
		network interface can chain received packets together and pass them into
		the IP task in one go.  The packets are chained using the pxNextBuffer
		member.  The loop below walks through the chain processing each packet
		in the chain in turn. */
		do
		{
			/* Store a pointer to the buffer after pxBuffer for use later on. */
			pxNextBuffer = pxBuffer->pxNextBuffer;

			/* Make it NULL to avoid using it later on. */
			pxBuffer->pxNextBuffer = NULL;

			prvProcessEthernetPacket( pxBuffer );
			pxBuffer = pxNextBuffer;

		/* While there is another packet in the chain. */
		} while( pxBuffer != NULL );
	}
	#endif /* ipconfigUSE_LINKED_RX_MESSAGES */
}
/*-----------------------------------------------------------*/

static void prvForwardTxPacket( NetworkBufferDescriptor_t * pxNetworkBuffer, BaseType_t xReleaseAfterSend )
{
	if( pxNetworkBuffer->pxInterface != NULL )
	{
		( void ) pxNetworkBuffer->pxInterface->pfOutput( pxNetworkBuffer->pxInterface, pxNetworkBuffer, xReleaseAfterSend );
	}
}
/*-----------------------------------------------------------*/

static TickType_t prvCalculateSleepTime( void )
{
TickType_t xMaximumSleepTime;

	/* Start with the maximum sleep time, then check this against the remaining
	time in any other timers that are active. */
	xMaximumSleepTime = ipconfigMAX_IP_TASK_SLEEP_TIME;

	if( xARPTimer.bActive != pdFALSE_UNSIGNED )
	{
		if( xARPTimer.ulRemainingTime < xMaximumSleepTime )
		{
			xMaximumSleepTime = xARPTimer.ulReloadTime;
		}
	}

	#if( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 )
	{
	NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;

		while( pxEndPoint != NULL )
		{
			if( pxEndPoint->xDHCP_RATimer.bActive != pdFALSE_UNSIGNED )
			{
				if( pxEndPoint->xDHCP_RATimer.ulRemainingTime < xMaximumSleepTime )
				{
					xMaximumSleepTime = pxEndPoint->xDHCP_RATimer.ulRemainingTime;
				}
			}
			pxEndPoint = pxEndPoint->pxNext;
		}
	}
	#endif /* ipconfigUSE_DHCP */

	#if( ipconfigUSE_TCP == 1 )
	{
		if( xTCPTimer.ulRemainingTime < xMaximumSleepTime )
		{
			xMaximumSleepTime = xTCPTimer.ulRemainingTime;
		}
	}
	#endif

	#if( ipconfigDNS_USE_CALLBACKS != 0 )
	{
		if( xDNSTimer.bActive != pdFALSE_UNSIGNED )
		{
			if( xDNSTimer.ulRemainingTime < xMaximumSleepTime )
			{
				xMaximumSleepTime = xDNSTimer.ulRemainingTime;
			}
		}
	}
	#endif

	return xMaximumSleepTime;
}
/*-----------------------------------------------------------*/

static void prvCheckNetworkTimers( void )
{
NetworkInterface_t *pxInterface;

	/* Is it time for ARP processing? */
	if( prvIPTimerCheck( &xARPTimer ) != pdFALSE )
	{
		( void ) xSendEventToIPTask( eARPTimerEvent );
	}

	#if( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 )
	{
	/* Is it time for DHCP processing? */
	NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;

		while( pxEndPoint != NULL )
		{
			if( prvIPTimerCheck( &( pxEndPoint->xDHCP_RATimer ) ) != pdFALSE )
			{
				#if( ipconfigUSE_DHCP == 1 )
				if( END_POINT_USES_DHCP( pxEndPoint ) )
				{
					( void ) vDHCPProcess( pdFALSE, pxEndPoint );
				}
				#endif /* ( ipconfigUSE_DHCP == 1 ) */

				#if( ipconfigUSE_RA != 0 )
				if( END_POINT_USES_RA( pxEndPoint ) )
				{
					vRAProcess( pdFALSE, pxEndPoint );
				}
				#endif	/* ( ipconfigUSE_RA != 0 ) */
			}

			pxEndPoint = pxEndPoint->pxNext;
		}
	}
	#endif /* ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA != 0 ) */

	#if( ipconfigDNS_USE_CALLBACKS != 0 )
	{
		/* Is it time for DNS processing? */
		if( prvIPTimerCheck( &xDNSTimer ) != pdFALSE )
		{
			vDNSCheckCallBack( NULL );
		}
	}
	#endif /* ipconfigDNS_USE_CALLBACKS */

	#if( ipconfigUSE_TCP == 1 )
	{
	BaseType_t xWillSleep;
	TickType_t xNextTime;
	BaseType_t xCheckTCPSockets;

		/* If the IP task has messages waiting to be processed then
		it will not sleep in any case. */
		if( uxQueueMessagesWaiting( xNetworkEventQueue ) == 0U )
		{
			xWillSleep = pdTRUE;
		}
		else
		{
			xWillSleep = pdFALSE;
		}

		/* Sockets need to be checked if the TCP timer has expired. */
		xCheckTCPSockets = prvIPTimerCheck( &xTCPTimer );

		/* Sockets will also be checked if there are TCP messages but the
		message queue is empty (indicated by xWillSleep being true). */
		if( ( xProcessedTCPMessage != pdFALSE ) && ( xWillSleep != pdFALSE ) )
		{
			xCheckTCPSockets = pdTRUE;
		}

		if( xCheckTCPSockets != pdFALSE )
		{
			/* Attend to the sockets, returning the period after which the
			check must be repeated. */
			xNextTime = xTCPTimerCheck( xWillSleep );
			prvIPTimerStart( &xTCPTimer, xNextTime );
			xProcessedTCPMessage = 0;
		}
	}
	#endif /* ipconfigUSE_TCP == 1 */

	/* Is it time to trigger the repeated NetworkDown events? */
	if( xAllNetworksUp == pdFALSE )
	{
		if( prvIPTimerCheck( &( xNetworkTimer ) ) != pdFALSE )
		{
		BaseType_t xUp = pdTRUE;

			for( pxInterface = pxNetworkInterfaces; pxInterface != NULL; pxInterface = pxInterface->pxNext )
			{
				if( pxInterface->bits.bInterfaceUp == pdFALSE_UNSIGNED )
				{
					xUp = pdFALSE;
					FreeRTOS_NetworkDown( pxInterface );
				}
			}
			xAllNetworksUp = xUp;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvIPTimerStart( IPTimer_t *pxTimer, TickType_t xTime )
{
	vTaskSetTimeOutState( &pxTimer->xTimeOut );
	pxTimer->ulRemainingTime = xTime;

	if( xTime == ( TickType_t ) 0 )
	{
		pxTimer->bExpired = pdTRUE_UNSIGNED;
	}
	else
	{
		pxTimer->bExpired = pdFALSE_UNSIGNED;
	}

	pxTimer->bActive = pdTRUE_UNSIGNED;
}
/*-----------------------------------------------------------*/

static void prvIPTimerReload( IPTimer_t *pxTimer, TickType_t xTime )
{
	pxTimer->ulReloadTime = xTime;
	prvIPTimerStart( pxTimer, xTime );
}
/*-----------------------------------------------------------*/

static BaseType_t prvIPTimerCheck( IPTimer_t *pxTimer )
{
BaseType_t xReturn;

	if( pxTimer->bActive == pdFALSE_UNSIGNED )
	{
		/* The timer is not enabled. */
		xReturn = pdFALSE;
	}
	else
	{
		/* The timer might have set the bExpired flag already, if not, check the
		value of xTimeOut against ulRemainingTime. */
		if( pxTimer->bExpired == pdFALSE_UNSIGNED )
		{
			if( xTaskCheckForTimeOut( &( pxTimer->xTimeOut ), &( pxTimer->ulRemainingTime ) ) != pdFALSE )
			{
				pxTimer->bExpired = pdTRUE_UNSIGNED;
			}
		}
		if( pxTimer->bExpired != pdFALSE_UNSIGNED )
		{
			prvIPTimerStart( pxTimer, pxTimer->ulReloadTime );
			xReturn = pdTRUE;
		}
		else
		{
			xReturn = pdFALSE;
		}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void FreeRTOS_NetworkDown( struct xNetworkInterface *pxNetworkInterface )
{
IPStackEvent_t xNetworkDownEvent;
const TickType_t xDontBlock = 0;

	pxNetworkInterface->bits.bInterfaceUp = pdFALSE_UNSIGNED;
	xNetworkDownEvent.eEventType = eNetworkDownEvent;
	xNetworkDownEvent.pvData = pxNetworkInterface;

	/* Simply send the network task the appropriate event. */
	if( xSendEventStructToIPTask( &xNetworkDownEvent, xDontBlock ) != pdPASS )
	{
		/* Could not send the message, so it is still pending. */
		pxNetworkInterface->bits.bCallDownEvent = pdTRUE;
		xNetworkDownEventPending = pdTRUE;
	}
	else
	{
		/* Message was sent so it is not pending. */
		pxNetworkInterface->bits.bCallDownEvent = pdFALSE;
	}

	iptraceNETWORK_DOWN();
}
/*-----------------------------------------------------------*/

BaseType_t FreeRTOS_NetworkDownFromISR( struct xNetworkInterface *pxNetworkInterface )
{
static IPStackEvent_t xNetworkDownEvent;
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	xNetworkDownEvent.eEventType = eNetworkDownEvent;
	xNetworkDownEvent.pvData = pxNetworkInterface;

	/* Simply send the network task the appropriate event. */
	if( xQueueSendToBackFromISR( xNetworkEventQueue, &xNetworkDownEvent, &xHigherPriorityTaskWoken ) != pdPASS )
	{
		/* Could not send the message, so it is still pending. */
		pxNetworkInterface->bits.bCallDownEvent = pdTRUE;
		xNetworkDownEventPending = pdTRUE;
	}
	else
	{
		/* Message was sent so it is not pending. */
		pxNetworkInterface->bits.bCallDownEvent = pdFALSE;
	}

	iptraceNETWORK_DOWN();

	return xHigherPriorityTaskWoken;
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_IPv6 != 0 )
/* The last parameter is either ipTYPE_IPv4 (0x40) or ipTYPE_IPv6 (0x60) */
void * FreeRTOS_GetUDPPayloadBuffer( size_t uxRequestedSizeBytes, TickType_t uxBlockTimeTicks, uint8_t ucIPType )
#else
void * FreeRTOS_GetUDPPayloadBuffer( size_t uxRequestedSizeBytes, TickType_t uxBlockTimeTicks )
#endif
{
NetworkBufferDescriptor_t *pxNetworkBuffer;
void *pvReturn;
TickType_t uxBlockTime = uxBlockTimeTicks;

	/* Cap the block time.  The reason for this is explained where
	ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS is defined (assuming an official
	FreeRTOSIPConfig.h header file is being used). */
	if( uxBlockTime > ( ( TickType_t ) ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS ) )
	{
		uxBlockTime = ( ( TickType_t ) ipconfigUDP_MAX_SEND_BLOCK_TIME_TICKS );
	}

	/* Obtain a network buffer with the required amount of storage. */
	pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( sizeof( UDPPacket_t ) + uxRequestedSizeBytes, uxBlockTime );

	if( pxNetworkBuffer != NULL )
	{
		#if( ipconfigUSE_IPv6 != 0 )
		{
		uint8_t *pucIPType;
		size_t uxIPHeaderLength;

			if( ucIPType == ipTYPE_IPv6)
			{
				uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;
			}
			else
			{
				uxIPHeaderLength = ipSIZE_OF_IPv4_HEADER;
			}

			/* Skip 3 headers. */
			pvReturn = ipPOINTER_CAST( void *,
									   &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPHeaderLength + ipSIZE_OF_UDP_HEADER ] ) );
			/* Later a pointer to a UDP payload is used to retrieve a NetworkBuffer.
			Store the packet type at 48 bytes before the start of the UDP payload. */
			pucIPType = ipPOINTER_CAST( uint8_t *, pvReturn );
			pucIPType = &( pucIPType[ 0 - ( BaseType_t ) ipUDP_PAYLOAD_IP_TYPE_OFFSET ] );
			/* For a IPv4 packet, pucIPType points to 6 bytes before the pucEthernetBuffer,
			for a IPv6 packet, pucIPType will point to the first byte of the IP-header: 'ucVersionTrafficClass'. */
			*pucIPType = ucIPType;
		}
		#else
		{
			/* Set the actual packet size in case a bigger buffer was returned. */
			pxNetworkBuffer->xDataLength = sizeof( UDPPacket_t ) + uxRequestedSizeBytes;
			/* Skip 3 headers. */
			pvReturn = &( pxNetworkBuffer->pucEthernetBuffer [ sizeof( UDPPacket_t ) ] );
		}
		#endif
	}
	else
	{
		pvReturn = NULL;
	}

	return ( void * ) pvReturn;
}
/*-----------------------------------------------------------*/

NetworkBufferDescriptor_t *pxDuplicateNetworkBufferWithDescriptor( const NetworkBufferDescriptor_t * const pxNetworkBuffer,
	size_t uxNewLength )
{
NetworkBufferDescriptor_t * pxNewBuffer;

	/* This function is only used when 'ipconfigZERO_COPY_TX_DRIVER' is set to 1.
	The transmit routine wants to have ownership of the network buffer
	descriptor, because it will pass the buffer straight to DMA. */
	pxNewBuffer = pxGetNetworkBufferWithDescriptor( uxNewLength, ( TickType_t ) 0 );

	if( pxNewBuffer != NULL )
	{
		/* Set the actual packet size in case a bigger buffer than requested
		was returned. */
		pxNewBuffer->xDataLength = uxNewLength;

		/* Copy the original packet information. */
		pxNewBuffer->ulIPAddress = pxNetworkBuffer->ulIPAddress;
		pxNewBuffer->usPort = pxNetworkBuffer->usPort;
		pxNewBuffer->usBoundPort = pxNetworkBuffer->usBoundPort;
		pxNewBuffer->pxInterface = pxNetworkBuffer->pxInterface;
		pxNewBuffer->pxEndPoint = pxNetworkBuffer->pxEndPoint;
		( void ) memcpy( pxNewBuffer->pucEthernetBuffer, pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength );
		#if( ipconfigUSE_IPv6 != 0 )
		{
			( void ) memcpy( pxNewBuffer->xIPv6_Address.ucBytes, pxNetworkBuffer->xIPv6_Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
		}
		#endif	/* ipconfigUSE_IPv6 != 0 */
	}

	return pxNewBuffer;
}
/*-----------------------------------------------------------*/

#if( ipconfigZERO_COPY_TX_DRIVER != 0 ) || ( ipconfigZERO_COPY_RX_DRIVER != 0 )

	NetworkBufferDescriptor_t *pxPacketBuffer_to_NetworkBuffer( const void *pvBuffer )
	{
	const uint8_t *pucBuffer;
	NetworkBufferDescriptor_t *pxResult;

		if( pvBuffer == NULL )
		{
			pxResult = NULL;
		}
		else
		{
			/* Obtain the network buffer from the zero copy pointer. */
			pucBuffer = ipPOINTER_CAST( const uint8_t *, pvBuffer );

			/* The input here is a pointer to a payload buffer.  Subtract the
			size of the header in the network buffer, usually 8 + 2 bytes. */
			pucBuffer -= ipBUFFER_PADDING;

			/* Here a pointer was placed to the network descriptor.  As a
			pointer is dereferenced, make sure it is well aligned. */
			if( ( ( ( size_t ) pucBuffer ) & ( sizeof( pucBuffer ) - 1U ) ) == ( size_t ) 0U )
			{
				pxResult = * ( ipPOINTER_CAST( NetworkBufferDescriptor_t **, pucBuffer ) );
			}
			else
			{
				pxResult = NULL;
			}
		}

		return pxResult;
	}

#endif /* ipconfigZERO_COPY_TX_DRIVER != 0 */
/*-----------------------------------------------------------*/

NetworkBufferDescriptor_t *pxUDPPayloadBuffer_to_NetworkBuffer( const void *pvBuffer )
{
const uint8_t *pucBuffer;
NetworkBufferDescriptor_t *pxResult;

	if( pvBuffer == NULL )
	{
		pxResult = NULL;
	}
	else
	{
		/* The input here is a pointer to a payload buffer.  Subtract
		the total size of a UDP/IP header plus the size of the header in
		the network buffer, usually 8 + 2 bytes. */
		#if( ipconfigUSE_IPv6 != 0 )
		{
		uint8_t *pucIPType;
		uint8_t ucIPType;
			/* When IPv6 is supported, find out the type of the packet.
			It is stored 48 bytes before the payload buffer as 0x40 or 0x60. */
			pucIPType = ipPOINTER_CAST( uint8_t *, pvBuffer );
			pucIPType = &( pucIPType[ 0 - ( BaseType_t ) ipUDP_PAYLOAD_IP_TYPE_OFFSET ] );
			/* For a IPv4 packet, pucIPType points to 6 bytes before the pucEthernetBuffer,
			for a IPv6 packet, pucIPType will point to the first byte of the IP-header: 'ucVersionTrafficClass'. */
			ucIPType = *pucIPType & 0xf0U;

			/* To help the translation from a UDP payload pointer to a networkBuffer,
			a byte was stored at a certain negative offset (-48 bytes).
			It must have a value of either 0x4x or 0x6x. */
			configASSERT( ( ucIPType == ipTYPE_IPv4 ) || ( ucIPType == ipTYPE_IPv6 ) );

			pucBuffer = ipPOINTER_CAST( uint8_t *, pvBuffer );
			if( ucIPType == ipTYPE_IPv6 )
			{
				pucBuffer = &( pucBuffer[ 0 - ( ( BaseType_t ) sizeof( UDPPacket_IPv6_t ) + ( BaseType_t ) ipBUFFER_PADDING ) ] );
			}
			else /* ucIPType == ipTYPE_IPv4 */
			{
				pucBuffer = &( pucBuffer[ 0 - ( ( BaseType_t ) sizeof( UDPPacket_t ) + ( BaseType_t ) ipBUFFER_PADDING ) ] );
			}
		}
		#else
		{
			/* Obtain the network buffer from the zero copy pointer. */
			pucBuffer = ipPOINTER_CAST( const uint8_t *, pvBuffer );

			/* The input here is a pointer to a payload buffer.  Subtract
			the total size of a UDP/IP header plus the size of the header in
			the network buffer, usually 8 + 2 bytes. */
			pucBuffer -= ( sizeof( UDPPacket_t ) + ( ( size_t ) ipBUFFER_PADDING ) );
		}
		#endif /* ipconfigUSE_IPv6 */

		/* Here a pointer was placed to the network descriptor,
		As a pointer is dereferenced, make sure it is well aligned */
		if( ( ( ( size_t ) pucBuffer ) & ( sizeof( pucBuffer ) - 1U ) ) == 0U )
		{
			/* The following statement may trigger a:
			warning: cast increases required alignment of target type [-Wcast-align].
			It has been confirmed though that the alignment is suitable. */
			pxResult = * ( ipPOINTER_CAST( NetworkBufferDescriptor_t **, pucBuffer ) );
		#if( ipconfigTCP_IP_SANITY != 0 )
			configASSERT( bIsValidNetworkDescriptor( pxResult ) != pdFALSE_UNSIGNED );
		#endif
			{
			BaseType_t xIndex = ( BaseType_t ) ipBUFFER_PADDING;
			/* Check if the buffer has been released already. */
			configASSERT( pxResult->pucEthernetBuffer != NULL );
			const uint8_t *pucEthBuffer1 = &( pxResult->pucEthernetBuffer[ 0 - xIndex ] );
			const uint8_t *pucEthBuffer2 = pucBuffer;

				configASSERT( pucEthBuffer1 == pucEthBuffer2 );
				( void ) pucEthBuffer1;
				( void ) pucEthBuffer2;
			}
		}
		else
		{
			pxResult = NULL;
		}
	}

	return pxResult;
}
/*-----------------------------------------------------------*/

uint8_t *pcNetworkBuffer_to_UDPPayloadBuffer( NetworkBufferDescriptor_t *pxNetworkBuffer )
{
uint8_t *pcResult;
size_t uxOffset;
	#if( ipconfigUSE_IPv6 != 0 )
	{
	EthernetHeader_t *pxHeader = ipPOINTER_CAST( EthernetHeader_t *, pxNetworkBuffer->pucEthernetBuffer );

		if( pxHeader->usFrameType == ( uint16_t ) ipIPv6_FRAME_TYPE )
		{
			uxOffset = ipUDP_PAYLOAD_OFFSET_IPv6;
		}
	}
#endif	/* ( ipconfigUSE_IPv6 != 0 ) */
	pcResult = &( pxNetworkBuffer->pucEthernetBuffer[ uxOffset ] );

	return pcResult;
}
/*-----------------------------------------------------------*/

void FreeRTOS_ReleaseUDPPayloadBuffer( void *pvBuffer )
{
NetworkBufferDescriptor_t *pxBuffer;

	pxBuffer = pxUDPPayloadBuffer_to_NetworkBuffer( pvBuffer );
	configASSERT( pxBuffer != NULL );
	vReleaseNetworkBufferAndDescriptor( pxBuffer );
}
/*-----------------------------------------------------------*/

BaseType_t FreeRTOS_IPStart( void )
{
BaseType_t xReturn = pdFALSE;
NetworkEndPoint_t *pxFirstEndPoint;

	/* There must be at least one interface and one end-point. */
	configASSERT( FreeRTOS_FirstNetworkInterface() != NULL );

	for( pxFirstEndPoint = FreeRTOS_FirstEndPoint( NULL );
		pxFirstEndPoint != NULL;
		pxFirstEndPoint = FreeRTOS_NextEndPoint( NULL, pxFirstEndPoint ) )
	{
		if( ENDPOINT_IS_IPv4( pxFirstEndPoint ) )
		{
			break;
		}
	}
	/* At least one IPv4 end-point must be defined. */
	configASSERT( pxFirstEndPoint != NULL );

	/* This function should only be called once. */
	configASSERT( xIPIsNetworkTaskReady() == pdFALSE );
	configASSERT( xNetworkEventQueue == NULL );
	configASSERT( xIPTaskHandle == NULL );

	#ifndef _lint
	{
		/* Check if MTU is big enough. */
		configASSERT( ( ( size_t ) ipconfigNETWORK_MTU ) >= ( ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_TCP_HEADER + ipconfigTCP_MSS ) );
		/* Check structure packing is correct. */
		configASSERT( sizeof( EthernetHeader_t ) == ipEXPECTED_EthernetHeader_t_SIZE );
		configASSERT( sizeof( ARPHeader_t ) == ipEXPECTED_ARPHeader_t_SIZE );
		configASSERT( sizeof( IPHeader_t ) == ipEXPECTED_IPHeader_t_SIZE );
		configASSERT( sizeof( ICMPHeader_t ) == ipEXPECTED_ICMPHeader_t_SIZE );
		configASSERT( sizeof( UDPHeader_t ) == ipEXPECTED_UDPHeader_t_SIZE );
		#if ipconfigUSE_TCP == 1
		{
			configASSERT( sizeof( TCPHeader_t ) == ( ipEXPECTED_TCPHeader_t_SIZE + ipSIZE_TCP_OPTIONS ) );
		}
		#endif
		configASSERT( sizeof( ICMPHeader_t ) == ipEXPECTED_ICMPHeader_t_SIZE );
		configASSERT( sizeof( IGMPHeader_t ) == ipEXPECTED_IGMPHeader_t_SIZE );
	}
	#endif
	/* Attempt to create the queue used to communicate with the IP task. */
	xNetworkEventQueue = xQueueCreate( ( UBaseType_t ) ipconfigEVENT_QUEUE_LENGTH, ( UBaseType_t )sizeof( IPStackEvent_t ) );
	configASSERT( xNetworkEventQueue != NULL );

	if( xNetworkEventQueue != NULL )
	{
		#if ( configQUEUE_REGISTRY_SIZE > 0 )
		{
			/* A queue registry is normally used to assist a kernel aware
			debugger.  If one is in use then it will be helpful for the debugger
			to show information about the network event queue. */
			vQueueAddToRegistry( xNetworkEventQueue, "NetEvnt" );
		}
		#endif /* configQUEUE_REGISTRY_SIZE */

		if( xNetworkBuffersInitialise() == pdPASS )
		{
			/* Prepare the sockets interface. */
			vNetworkSocketsInit();

			/* Create the task that processes Ethernet and stack events. */
			xReturn = xTaskCreate( prvIPTask,
								   "IP-task",
								   ( uint16_t ) ipconfigIP_TASK_STACK_SIZE_WORDS,
								   NULL,
								   ( UBaseType_t ) ipconfigIP_TASK_PRIORITY,
								   &( xIPTaskHandle ) );
		}
		else
		{
			FreeRTOS_debug_printf( ( "FreeRTOS_IPStart: xNetworkBuffersInitialise() failed\n") );

			/* Clean up. */
			vQueueDelete( xNetworkEventQueue );
			xNetworkEventQueue = NULL;
		}
	}
	else
	{
		FreeRTOS_debug_printf( ( "FreeRTOS_IPStart: Network event queue could not be created\n") );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

/*_RB_ Is it best, from the end user's perspective, to pass in an end point here, or for data hiding purposes, is it best to pass in a interface number (0, 1, etc.)? */
void FreeRTOS_GetAddressConfiguration( uint32_t *pulIPAddress,
									   uint32_t *pulNetMask,
									   uint32_t *pulGatewayAddress,
									   uint32_t *pulDNSServerAddress,
									   struct xNetworkEndPoint *pxEndPoint )
{
	if( ENDPOINT_IS_IPv4( pxEndPoint ) )
	{
	/* Return the address configuration to the caller. */

		if( pulIPAddress != NULL )
		{
			*pulIPAddress = pxEndPoint->ipv4_settings.ulIPAddress;
		}

		if( pulNetMask != NULL )
		{
			*pulNetMask = pxEndPoint->ipv4_settings.ulNetMask;
		}

		if( pulGatewayAddress != NULL )
		{
			*pulGatewayAddress = pxEndPoint->ipv4_settings.ulGatewayAddress;
		}

		if( pulDNSServerAddress != NULL )
		{
			*pulDNSServerAddress = pxEndPoint->ipv4_settings.ulDNSServerAddresses[ 0 ]; /*_RB_ Only returning the address of the first DNS server. */
		}
	}
}
/*-----------------------------------------------------------*/

void FreeRTOS_SetAddressConfiguration( const uint32_t *pulIPAddress,
									   const uint32_t *pulNetMask,
									   const uint32_t *pulGatewayAddress,
									   const uint32_t *pulDNSServerAddress,
									   struct xNetworkEndPoint *pxEndPoint )
{
	/* Update the address configuration. */

	if( ENDPOINT_IS_IPv4( pxEndPoint ) )
	{
		if( pulIPAddress != NULL )
		{
			pxEndPoint->ipv4_settings.ulIPAddress = *pulIPAddress;
		}

		if( pulNetMask != NULL )
		{
			pxEndPoint->ipv4_settings.ulNetMask = *pulNetMask;
		}

		if( pulGatewayAddress != NULL )
		{
			pxEndPoint->ipv4_settings.ulGatewayAddress = *pulGatewayAddress;
		}

		if( pulDNSServerAddress != NULL )
		{
			pxEndPoint->ipv4_settings.ulDNSServerAddresses[ 0 ] = *pulDNSServerAddress;
		}
	}
}
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

	BaseType_t FreeRTOS_SendPingRequest( uint32_t ulIPAddress, size_t uxNumberOfBytesToSend, TickType_t uxBlockTimeTicks )
	{
	NetworkBufferDescriptor_t *pxNetworkBuffer;
	ICMPHeader_t *pxICMPHeader;
	EthernetHeader_t *pxEthernetHeader;
	BaseType_t xReturn = pdFAIL;
	static uint16_t usSequenceNumber = 0;
	uint8_t *pucChar;
	size_t uxTotalLength;
	IPStackEvent_t xStackTxEvent = { eStackTxEvent, NULL };

		uxTotalLength = uxNumberOfBytesToSend + sizeof( ICMPPacket_t );
		pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxTotalLength, uxBlockTimeTicks );

		if( pxNetworkBuffer != NULL )
		{
		BaseType_t xEnoughSpace;

			if( uxNumberOfBytesToSend < ( ipconfigNETWORK_MTU - ( sizeof( IPHeader_t ) + sizeof( ICMPHeader_t ) ) ) )
			{
				xEnoughSpace = pdTRUE;
			}
			else
			{
				xEnoughSpace = pdFALSE;
			}
			if( ( uxGetNumberOfFreeNetworkBuffers() >= 3U ) && ( uxNumberOfBytesToSend >= 1U ) && ( xEnoughSpace != pdFALSE ) )
			{
				pxEthernetHeader = ipPOINTER_CAST( EthernetHeader_t *, pxNetworkBuffer->pucEthernetBuffer );
				pxEthernetHeader->usFrameType = ipIPv4_FRAME_TYPE;
				

				pxICMPHeader = ipPOINTER_CAST( ICMPHeader_t *, &( pxNetworkBuffer->pucEthernetBuffer[ ipIP_PAYLOAD_OFFSET ] ) );
				usSequenceNumber++;

				/* Fill in the basic header information. */
				pxICMPHeader->ucTypeOfMessage = ipICMP_ECHO_REQUEST;
				pxICMPHeader->ucTypeOfService = 0;
				pxICMPHeader->usIdentifier = usSequenceNumber;
				pxICMPHeader->usSequenceNumber = usSequenceNumber;

				/* Find the start of the data. */
				pucChar = ( uint8_t * ) pxICMPHeader;
				pucChar = &(pucChar[ sizeof( ICMPHeader_t ) ] );

				/* Just memset the data to a fixed value. */
				( void ) memset( pucChar, ( int ) ipECHO_DATA_FILL_BYTE, uxNumberOfBytesToSend );

				/* The message is complete, IP and checksum's are handled by
				vProcessGeneratedUDPPacket */
				pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] = FREERTOS_SO_UDPCKSUM_OUT;
				pxNetworkBuffer->ulIPAddress = ulIPAddress;
				pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;
				/* xDataLength is the size of the total packet, including the Ethernet header. */
				pxNetworkBuffer->xDataLength = uxTotalLength;

				/* Send to the stack. */
				xStackTxEvent.pvData = pxNetworkBuffer;

				if( xSendEventStructToIPTask( &( xStackTxEvent ), uxBlockTimeTicks ) != pdPASS )
				{
					vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
					iptraceSTACK_TX_EVENT_LOST( ipSTACK_TX_EVENT );
				}
				else
				{
					xReturn = ( BaseType_t ) usSequenceNumber;
				}
			}
		}
		else
		{
			/* The requested number of bytes will not fit in the available space
			in the network buffer. */
		}

		return xReturn;
	}

#endif /* ipconfigSUPPORT_OUTGOING_PINGS == 1 */
/*-----------------------------------------------------------*/

BaseType_t xSendEventToIPTask( eIPEvent_t eEvent )
{
IPStackEvent_t xEventMessage;
const TickType_t xDontBlock = ( TickType_t ) 0;

	xEventMessage.eEventType = eEvent;
	xEventMessage.pvData = ( void* )NULL;

	return xSendEventStructToIPTask( &xEventMessage, xDontBlock );
}
/*-----------------------------------------------------------*/

BaseType_t xSendEventStructToIPTask( const IPStackEvent_t *pxEvent, TickType_t uxTimeout )
{
BaseType_t xReturn, xSendMessage;
TickType_t uxUseTimeout = uxTimeout;

	if( ( xIPIsNetworkTaskReady() == pdFALSE ) && ( pxEvent->eEventType != eNetworkDownEvent ) )
	{
		/* Only allow eNetworkDownEvent events if the IP task is not ready
		yet.  Not going to attempt to send the message so the send failed. */
		xReturn = pdFAIL;
	}
	else
	{
		xSendMessage = pdTRUE;

		#if( ipconfigUSE_TCP == 1 )
		{
			if( pxEvent->eEventType == eTCPTimerEvent )
			{
				/* TCP timer events are sent to wake the timer task when
				xTCPTimer has expired, but there is no point sending them if the
				IP task is already awake processing other message. */
				xTCPTimer.bExpired = pdTRUE_UNSIGNED;

				if( uxQueueMessagesWaiting( xNetworkEventQueue ) != 0U )
				{
					/* Not actually going to send the message but this is not a
					failure as the message didn't need to be sent. */
					xSendMessage = pdFALSE;
				}
			}
		}
		#endif /* ipconfigUSE_TCP */

		if( xSendMessage != pdFALSE )
		{
			/* The IP task cannot block itself while waiting for itself to
			respond. */
			if( ( xIsCallingFromIPTask() == pdTRUE ) && ( uxUseTimeout > ( TickType_t ) 0U ) )
			{
				uxUseTimeout = ( TickType_t ) 0;
			}

			xReturn = xQueueSendToBack( xNetworkEventQueue, pxEvent, uxUseTimeout );

			if( xReturn == pdFAIL )
			{
				/* A message should have been sent to the IP task, but wasn't. */
				FreeRTOS_debug_printf( ( "xSendEventStructToIPTask: CAN NOT ADD %d\n", pxEvent->eEventType ) );
				iptraceSTACK_TX_EVENT_LOST( pxEvent->eEventType );
			}
		}
		else
		{
			/* It was not necessary to send the message to process the event so
			even though the message was not sent the call was successful. */
			xReturn = pdPASS;
		}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

eFrameProcessingResult_t eConsiderFrameForProcessing( const uint8_t * const pucEthernetBuffer )
{
eFrameProcessingResult_t eReturn;
const EthernetHeader_t *pxEthernetHeader;
NetworkEndPoint_t *pxEndPoint;

	/* Map the buffer onto Ethernet Header struct for easy access to fields. */
	pxEthernetHeader = ipPOINTER_CAST( const EthernetHeader_t *, pucEthernetBuffer );

	/* Examine the destination MAC from the Ethernet header to see if it matches
	that of an end point managed by FreeRTOS+TCP. */
	pxEndPoint = FreeRTOS_FindEndPointOnMAC( &( pxEthernetHeader->xDestinationAddress ), NULL );

	if( pxEndPoint != NULL )
	{
		/* The packet was directed to this node - process it. */
		eReturn = eProcessBuffer;
	}
	else if( memcmp( xBroadcastMACAddress.ucBytes, pxEthernetHeader->xDestinationAddress.ucBytes, sizeof( MACAddress_t ) ) == 0 )
	{
		/* The packet was a broadcast - process it. */
		eReturn = eProcessBuffer;
	}
	else
	#if( ipconfigUSE_LLMNR == 1 )
	if( memcmp( xLLMNR_MacAdress.ucBytes, pxEthernetHeader->xDestinationAddress.ucBytes, sizeof( MACAddress_t ) ) == 0 )
	{
		/* The packet is a request for LLMNR - process it. */
		eReturn = eProcessBuffer;
	}
	else
	#endif /* ipconfigUSE_LLMNR */

	#if( ipconfigUSE_IPv6 != 0 )
	if( ( pxEthernetHeader->xDestinationAddress.ucBytes[ 0 ] == ipMULTICAST_MAC_ADDRESS_IPv6_0 ) &&
		( pxEthernetHeader->xDestinationAddress.ucBytes[ 1 ] == ipMULTICAST_MAC_ADDRESS_IPv6_1 ) )
	{
		/* The packet is a request for LLMNR - process it. */
		eReturn = eProcessBuffer;
	}
	else
	#endif /* ipconfigUSE_IPv6 */
	{
		/* The packet was not a broadcast, or for this node, just release
		the buffer without taking any other action. */
		eReturn = eReleaseBuffer;
	}

	#if( ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES == 1 )
	{
	uint16_t usFrameType;

		if( eReturn == eProcessBuffer )
		{
			usFrameType = pxEthernetHeader->usFrameType;
			usFrameType = FreeRTOS_ntohs( usFrameType );

			if( usFrameType <= 0x600U )
			{
				/* Not an Ethernet II frame. */
				eReturn = eReleaseBuffer;
			}
		}
	}
	#endif /* ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES == 1  */

	#if( ipconfigHAS_DEBUG_PRINTF != 0 )
	{
		if( eReturn != eProcessBuffer )
		{
			FreeRTOS_debug_printf( ( "eConsiderFrameForProcessing: Drop MAC %02x:%02x:%02x:%02x:%02x:%02x\n",
				pxEthernetHeader->xDestinationAddress.ucBytes[ 0 ],
				pxEthernetHeader->xDestinationAddress.ucBytes[ 1 ],
				pxEthernetHeader->xDestinationAddress.ucBytes[ 2 ],
				pxEthernetHeader->xDestinationAddress.ucBytes[ 3 ],
				pxEthernetHeader->xDestinationAddress.ucBytes[ 4 ],
				pxEthernetHeader->xDestinationAddress.ucBytes[ 5 ] ) );
		}
	}
	#endif /* ipconfigHAS_DEBUG_PRINTF */

	return eReturn;
}
/*-----------------------------------------------------------*/

static void prvProcessNetworkDownEvent( NetworkInterface_t *pxInterface )
{
NetworkEndPoint_t *pxEndPoint;

	configASSERT( pxInterface != NULL );
	configASSERT( pxInterface->pfInitialise != NULL );


	/* The first network down event is generated by the IP stack itself to
	initialise the network hardware, so do not call the network down event
	the first time through. */
	/*_RB_ Similarly it is not clear to me why there is not a one to one
	mapping between the interface and the end point, which would negate
	the need for this loop.  Likewise the loop further down the same function. */
	/*_HT_ Because a single interface can have multiple end-points. */
	for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
		 pxEndPoint != NULL;
		 pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
	{
		/* The bit 'bEndPointUp' stays low until vIPNetworkUpCalls() is called. */
		pxEndPoint->bits.bEndPointUp = pdFALSE_UNSIGNED;
		#if ipconfigUSE_NETWORK_EVENT_HOOK == 1
		{
			if( pxEndPoint->bits.bCallDownHook != pdFALSE_UNSIGNED )
			{
				vApplicationIPNetworkEventHook( eNetworkDown, pxEndPoint );
			}
			else
			{
				/* The next time NetworkEventHook will be called for this end-point. */
				pxEndPoint->bits.bCallDownHook = pdTRUE_UNSIGNED;
			}
		}
		#endif /* ipconfigUSE_NETWORK_EVENT_HOOK */
	}
	/* Per the ARP Cache Validation section of https://tools.ietf.org/html/rfc1122, 
	treat network down as a "delivery problem" and flush the ARP cache for this
	interface. */
	FreeRTOS_ClearARP( ipPOINTER_CAST( struct xNetworkEndPoint *, pxInterface ) );

	/* The network has been disconnected (or is being initialised for the first
	time).  Perform whatever hardware processing is necessary to bring it up
	again, or wait for it to be available again.  This is hardware dependent. */

	if( pxInterface->pfInitialise( pxInterface ) == pdPASS )
	{
		pxInterface->bits.bInterfaceUp = pdTRUE_UNSIGNED;
		/* Set remaining time to 0 so it will become active immediately. */
		/* The network is not up until DHCP has completed.
		Start it now for all associated end-points. */

		for( pxEndPoint = FreeRTOS_FirstEndPoint( pxInterface );
			 pxEndPoint != NULL;
			 pxEndPoint = FreeRTOS_NextEndPoint( pxInterface, pxEndPoint ) )
		{
			#if( ipconfigUSE_DHCP == 1 )
			if( END_POINT_USES_DHCP( pxEndPoint ) )
			{
				/* Reset the DHCP process for this end-point. */
				vDHCPProcess( pdTRUE, pxEndPoint );
				/* And do the first run. */
				vDHCPProcess( pdFALSE, pxEndPoint );
 			}
			else
			#endif /* ( ipconfigUSE_DHCP == 1 ) */

			#if( ipconfigUSE_RA != 0 )
			if( END_POINT_USES_RA( pxEndPoint ) )
			{
				/* Reset the RA/SLAAC process for this end-point. */
				vRAProcess( pdTRUE, pxEndPoint );
			}
			else
			#endif/* ( #if( ipconfigUSE_IPv6 != 0 ) */

			{
				#if( ipconfigUSE_IPv6 != 0 )
				if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
				{
					( void ) memcpy( &( pxEndPoint->ipv6_settings ), &( pxEndPoint->ipv6_defaults ), sizeof( pxEndPoint->ipv6_settings ) );
				}
				else
				#endif
				{
					( void ) memcpy( &( pxEndPoint->ipv4_settings ), &( pxEndPoint->ipv4_defaults ), sizeof( pxEndPoint->ipv4_settings ) );
				}
				/* DHCP or Router Advertisement are not enabled for this end-point.
				Perform any necessary 'network up' processing. */
				vIPNetworkUpCalls( pxEndPoint );
			}
		}
	}
	else
	{
		/* Nothing to do. When the 'xNetworkTimer' expires, all interfaces
		with bits.bInterfaceUp cleared will get a new 'eNetworkDownEvent' */
	}
}
/*-----------------------------------------------------------*/

void vIPNetworkUpCalls( struct xNetworkEndPoint *pxEndPoint )
{
	pxEndPoint->bits.bEndPointUp = pdTRUE_UNSIGNED;

	#if( ipconfigUSE_NETWORK_EVENT_HOOK == 1 )
	{
		vApplicationIPNetworkEventHook( eNetworkUp, pxEndPoint );
	}
	#endif /* ipconfigUSE_NETWORK_EVENT_HOOK */

	/* The call to vDNSInitialise() has been moved to an earlier stage. */

	/* Set remaining time to 0 so it will become active immediately. */
	prvIPTimerReload( &xARPTimer, pdMS_TO_TICKS( ipARP_TIMER_PERIOD_MS ) );
}
/*-----------------------------------------------------------*/

static void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
const EthernetHeader_t *pxEthernetHeader;
eFrameProcessingResult_t eReturned = eReleaseBuffer;

	configASSERT( pxNetworkBuffer != NULL );

	/* Interpret the Ethernet frame. */
	if( pxNetworkBuffer->xDataLength >= sizeof( EthernetHeader_t ) )
	{
		eReturned = ipCONSIDER_FRAME_FOR_PROCESSING( pxNetworkBuffer->pucEthernetBuffer );

		/* Map the buffer onto the Ethernet Header struct for easy access to the fields. */
		pxEthernetHeader = ipPOINTER_CAST( const EthernetHeader_t *, pxNetworkBuffer->pucEthernetBuffer );

		/* The condition "eReturned == eProcessBuffer" must be true. */
		#if( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
		if( eReturned == eProcessBuffer )
		#endif
		{
			/* Interpret the received Ethernet packet. */
			switch( pxEthernetHeader->usFrameType )
			{
			case ipARP_FRAME_TYPE:
				/* The Ethernet frame contains an ARP packet. */
				if( pxNetworkBuffer->xDataLength >= sizeof( ARPPacket_t ) )
				{
					eReturned = eARPProcessPacket( pxNetworkBuffer );
				}
				else
				{
					eReturned = eReleaseBuffer;
				}
				break;

			case ipIPv4_FRAME_TYPE:
		#if( ipconfigUSE_IPv6 != 0 )
			case ipIPv6_FRAME_TYPE :
		#endif
				/* The Ethernet frame contains an IP packet. */
				if( pxNetworkBuffer->xDataLength >= sizeof( IPPacket_t ) )
				{
					eReturned = prvProcessIPPacket( ipPOINTER_CAST( IPPacket_t *, pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer );
				}
				else
				{
					eReturned = eReleaseBuffer;
				}
				break;

			default:
				/* No other packet types are handled.  Nothing to do. */
				eReturned = eReleaseBuffer;
				break;
			}
		}
	}
	#if( ipconfigHAS_DEBUG_PRINTF != 0 )
	else
	{
		FreeRTOS_debug_printf( ( "prvProcessEthernetPacket: Drop MAC %02x:%02x:%02x:%02x:%02x:%02x\n",
			pxEthernetHeader->xDestinationAddress.ucBytes[ 0 ],
			pxEthernetHeader->xDestinationAddress.ucBytes[ 1 ],
			pxEthernetHeader->xDestinationAddress.ucBytes[ 2 ],
			pxEthernetHeader->xDestinationAddress.ucBytes[ 3 ],
			pxEthernetHeader->xDestinationAddress.ucBytes[ 4 ],
			pxEthernetHeader->xDestinationAddress.ucBytes[ 5 ] ) );
	}
	#endif /* ipconfigHAS_DEBUG_PRINTF */

	/* Perform any actions that resulted from processing the Ethernet frame. */
	switch( eReturned )
	{
		case eReturnEthernetFrame :
			/* The Ethernet frame will have been updated (maybe it was
			an ARP request or a PING request?) and should be sent back to
			its source. */
			vReturnEthernetFrame( pxNetworkBuffer, pdTRUE );
			/* parameter pdTRUE: the buffer must be released once
			the frame has been transmitted */
			break;

		case eFrameConsumed :
			/* The frame is in use somewhere, don't release the buffer
			yet. */
			break;

		case eReleaseBuffer :
		case eProcessBuffer :
		default :
			/* The frame is not being used anywhere, and the
			NetworkBufferDescriptor_t structure containing the frame should
			just be	released back to the list of free buffers. */
			vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
			break;
	}
}
/*-----------------------------------------------------------*/

BaseType_t xIsIPv4Multicast( uint32_t ulIPAddress )
{
BaseType_t xReturn;
uint32_t ulIP = FreeRTOS_ntohl( ulIPAddress );

	if( ( ulIP >= ipFIRST_MULTI_CAST_IPv4 ) && ( ulIP < ipLAST_MULTI_CAST_IPv4 ) )
	{
		xReturn = pdTRUE;
	}
	else
	{
		xReturn = pdFALSE;
	}
	return xReturn;
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_IPv6 != 0 )
	BaseType_t xIsIPv6Multicast( const IPv6_Address_t *pxIPAddress )
	{
	BaseType_t xReturn;

		if( pxIPAddress->ucBytes[ 0 ] == 0xffU )
		{
			xReturn = pdTRUE;
		}
		else
		{
			xReturn = pdFALSE;
		}
		return xReturn;
	}
#endif /* ipconfigUSE_IPv6 */
/*-----------------------------------------------------------*/

#if( ipconfigUSE_IPv6 != 0 )
	BaseType_t xCompareIPv6_Address( const IPv6_Address_t *pxLeft, const IPv6_Address_t *pxRight, size_t uxPrefixLength )
	{
	BaseType_t xResult;

		// 0    2    4    6    8    10   12   14
		// ff02:0000:0000:0000:0000:0001:ff66:4a81
		if( ( pxRight->ucBytes[  0 ] == 0xffU ) &&
			( pxRight->ucBytes[  1 ] == 0x02U ) &&
			( pxRight->ucBytes[ 12 ] == 0xffU ) )
		{
			/* This is an LLMNR address. */
			xResult = memcmp( &( pxLeft->ucBytes[ 13 ] ), &( pxRight->ucBytes[ 13 ] ), 3 );
		}
		else
		if( ( pxRight->ucBytes[  0 ] == 0xffU ) &&
			( pxRight->ucBytes[  1 ] == 0x02U ) )
		{
			/* FF02::1 is all node address to reach out all nodes in the same link. */
			xResult = 0;
		}
		else
		if( ( pxRight->ucBytes[ 0 ] == 0xfeU ) &&
			( pxRight->ucBytes[ 1 ] == 0x80U ) &&
			( pxLeft ->ucBytes[ 0 ] == 0xfeU ) &&
			( pxLeft ->ucBytes[ 1 ] == 0x80U ) )
		{
			/* Both are local addresses. */
			xResult = 0;
		}
		else
		{
			if( uxPrefixLength == 0U )
			{
				xResult = 0;
			}
			else if( uxPrefixLength == ( 8U * ipSIZE_OF_IPv6_ADDRESS ) )
			{
				xResult = memcmp( pxLeft->ucBytes, pxRight->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
			}
			else
			{
			size_t uxLength = uxPrefixLength / 8U;

				xResult = 0;
				if( uxLength > 0U )
				{
					xResult = memcmp( pxLeft->ucBytes, pxRight->ucBytes, uxLength );
				}
				if( ( xResult == 0 ) && ( ( uxPrefixLength % 8U ) != 0U ) )
				{
				/* One byte has both a network- and a host-address. */
				size_t uxBits = uxPrefixLength % 8U;
				size_t uxHostLen = 8U - uxBits;
				uint32_t uxHostMask = ( ( ( size_t ) 1U ) << uxHostLen ) - 1U;
				uint8_t ucNetMask = ( uint8_t ) ~( uxHostMask );

					if( ( pxLeft->ucBytes[ uxLength ] & ucNetMask ) != ( pxRight->ucBytes[ uxLength ] & ucNetMask ) )
					{
						xResult = 1;
					}
				}
			}
		}

		return xResult;
	}
#endif /* ipconfigUSE_IPv6 */

#if( ipconfigUSE_IPv6 != 0 )
	static eFrameProcessingResult_t prvAllowIPPacketIPv6( const IPHeader_IPv6_t * const pxIPv6Header,
														  const NetworkBufferDescriptor_t * const pxNetworkBuffer,
														  UBaseType_t uxHeaderLength )
	{
	eFrameProcessingResult_t eReturn;

		#if( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 )
		{
			/* In systems with a very small amount of RAM, it might be advantageous
			to have incoming messages checked earlier, by the network card driver.
			This method may decrease the usage of sparse network buffers. */
			const IPv6_Address_t *pxDestinationIPAddress = &( pxIPv6Header->xDestinationAddress );

				/* Is the packet for this IP address? */
				if( ( FreeRTOS_FindEndPointOnIP_IPv6( pxDestinationIPAddress ) != NULL ) ||
					/* Is it the multicast address FF00::/8 ? */
					( xIsIPv6Multicast ( pxDestinationIPAddress ) != pdFALSE ) ||
					/* Or (during DHCP negotiation) we have no IP-address yet? */
					( FreeRTOS_IsNetworkUp() == 0 ) )
				{
					/* Packet is not for this node, or the network is still not up,
					release it */
					eReturn = eProcessBuffer;
				}
				else
				{
					eReturn = eReleaseBuffer;
					FreeRTOS_printf( ( "prvAllowIPPacketIPv6: drop %pip (from %pip)\n", pxDestinationIPAddress->ucBytes, pxIPv6Header->xSourceAddress.ucBytes ) );
				}
		}
		#else
		{
			( void ) pxIPv6Header;
			/* The packet has been checked by the network interface. */
			eReturn = eProcessBuffer;
		}
		#endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */

		#if( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 )
		{
			/* Some drivers of NIC's with checksum-offloading will enable the above
			define, so that the checksum won't be checked again here */
			if( eReturn == eProcessBuffer )/*lint !e774 Boolean within 'if' always evaluates to True [FreeRTOS_IP.c] [MISRA 2012 Rule 14.3, required]. */
			{
			const IPPacket_t * pxIPPacket = ipPOINTER_CAST( const IPPacket_t *, pxNetworkBuffer->pucEthernetBuffer );
			NetworkEndPoint_t *pxEndPoint = FreeRTOS_FindEndPointOnMAC( &( pxIPPacket->xEthernetHeader.xSourceAddress ), NULL );
				/* IPv6 does not have a separate checksum in the IP-header */
				/* Is the upper-layer checksum (TCP/UDP/ICMP) correct? */
				/* Do not check the checksum of loop-back messages. */
				if( pxEndPoint == NULL )
				{
					if( usGenerateProtocolChecksum( ( uint8_t * )( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE ) != ipCORRECT_CRC )
					{
						/* Protocol checksum not accepted. */
						eReturn = eReleaseBuffer;
					}
				}
			}
		}
		#else
		{
			/* to avoid warning unused parameters */
			( void ) pxNetworkBuffer;
		}
		#endif /* ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 */
		( void ) uxHeaderLength;

		return eReturn;
	}
#endif /* ipconfigUSE_IPv6 */
/*-----------------------------------------------------------*/

static eFrameProcessingResult_t prvAllowIPPacketIPv4( const IPPacket_t * const pxIPPacket,
	const NetworkBufferDescriptor_t * const pxNetworkBuffer, UBaseType_t uxHeaderLength )
{
eFrameProcessingResult_t eReturn = eProcessBuffer;

#if( ( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 ) || ( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 ) )
	const IPHeader_t * pxIPHeader = &( pxIPPacket->xIPHeader );
#else
	/* or else, the parameter won't be used and the function will be optimised
	away */
	( void ) pxIPPacket;
#endif

	#if( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 0 )
	{
	/* In systems with a very small amount of RAM, it might be advantageous
	to have incoming messages checked earlier, by the network card driver.
	This method may decrease the usage of sparse network buffers. */
	uint32_t ulDestinationIPAddress = pxIPHeader->ulDestinationIPAddress;

		/* Ensure that the incoming packet is not fragmented (fragmentation
		was only supported for outgoing packets, and is not currently
		not supported at all). */
		if( ( pxIPHeader->usFragmentOffset & ipFRAGMENT_OFFSET_BIT_MASK ) != 0U )
		{
			/* Can not handle, fragmented packet. */
			eReturn = eReleaseBuffer;
		}
		/* Test if the length of the IP-header is between 20 and 60 bytes,
		and if the IP-version is 4. */
		else if( ( pxIPHeader->ucVersionHeaderLength < ipIPV4_VERSION_HEADER_LENGTH_MIN ) ||
				 ( pxIPHeader->ucVersionHeaderLength > ipIPV4_VERSION_HEADER_LENGTH_MAX ) )
		{
			/* Can not handle, unknown or invalid header version. */
			eReturn = eReleaseBuffer;
		}
	else if(
			( pxNetworkBuffer->pxEndPoint == NULL ) &&
			( FreeRTOS_FindEndPointOnIP_IPv4( ulDestinationIPAddress, 4 ) == NULL ) &&
			/* Is it an IPv4 broadcast address x.x.x.255 ? */
			( ( FreeRTOS_ntohl( ulDestinationIPAddress ) & 0xff ) != 0xff ) &&
			( xIsIPv4Multicast( ulDestinationIPAddress ) == pdFALSE ) &&
			/* Or (during DHCP negotiation) we have no IP-address yet? */
			( FreeRTOS_IsNetworkUp() != pdFALSE ) )
		{
			/* Packet is not for this node, release it */
			eReturn = eReleaseBuffer;
		}
		else
		{
			/* Packet is not fragemented, destination is this device. */
		}
	}
	#endif /* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */

	#if( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 )
	{
		/* Some drivers of NIC's with checksum-offloading will enable the above
		define, so that the checksum won't be checked again here */
		if (eReturn == eProcessBuffer )
		{
			NetworkEndPoint_t *pxEndPoint = FreeRTOS_FindEndPointOnMAC( &( pxIPPacket->xEthernetHeader.xSourceAddress ), NULL );
			/* Do not check the checksum of loop-back messages. */
			if( pxEndPoint == NULL )
			{
				/* Is the IP header checksum correct? */
				if( ( pxIPHeader->ucProtocol != ( uint8_t ) ipPROTOCOL_ICMP ) &&
					( usGenerateChecksum( 0U, ipPOINTER_CAST( uint8_t *, &( pxIPHeader->ucVersionHeaderLength ) ), ( size_t ) uxHeaderLength ) != ipCORRECT_CRC ) )	/*lint !e9007 side effects on right hand of logical operator, ''&&'' [MISRA 2012 Rule 13.5, required]. */
				{
					/* Check sum in IP-header not correct. */
					eReturn = eReleaseBuffer;
				}
				/* Is the upper-layer checksum (TCP/UDP/ICMP) correct? */
				else if( usGenerateProtocolChecksum( ( uint8_t * )( pxNetworkBuffer->pucEthernetBuffer ), pxNetworkBuffer->xDataLength, pdFALSE ) != ipCORRECT_CRC )
				{
					/* Protocol checksum not accepted. */
					eReturn = eReleaseBuffer;
				}
				else
				{
					/* The checksum of the received packet is OK. */
				}
			}
		}
	}
	#else
	{

		if (eReturn == eProcessBuffer )
		{
			if( usGenerateProtocolChecksum( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdFALSE ) != ipCORRECT_CRC )
			{
				/* Some of the size or length checks were not successful. */
				eReturn = eReleaseBuffer;
			}
		}

		#if( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 )
		{
			/* Check if this is a UDP packet without a checksum. */
			if (eReturn == eProcessBuffer )
			{
			uint8_t ucProtocol;
			ProtocolHeaders_t *pxProtocolHeaders;
			#if( ipconfigUSE_IPv6 != 0 )
			const IPHeader_IPv6_t * pxIPPacket_IPv6;

				pxIPPacket_IPv6 = ipPOINTER_CAST( const IPHeader_IPv6_t *, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
				if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
				{
					ucProtocol = pxIPPacket_IPv6->ucNextHeader;
					pxProtocolHeaders = ipPOINTER_CAST( ProtocolHeaders_t *, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
				}
				else
			#endif	/* ( ipconfigUSE_IPv6 != 0 ) */
				{
					ucProtocol = pxIPPacket->xIPHeader.ucProtocol;
					pxProtocolHeaders = ipPOINTER_CAST( ProtocolHeaders_t *, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ( size_t ) ipSIZE_OF_IPv4_HEADER ] ) );
				}
				if( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
				{
					if( pxProtocolHeaders->xUDPHeader.usChecksum == ( uint16_t ) 0U )
					{
						#if( ipconfigHAS_PRINTF != 0 )
						{
						static BaseType_t xCount = 0;

							if( xCount < 5 )
							{
								FreeRTOS_printf( ( "prvAllowIPPacket: UDP packet from %xip without CRC dropped\n",
									FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulSourceIPAddress ) ) );
								xCount++;
							}
						}
						#endif	/* ( ipconfigHAS_PRINTF != 0 ) */

						/* Protocol checksum not accepted. */
						eReturn = eReleaseBuffer;
					}
				}
			}
		}
		#endif	/* ( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 ) */

		/* to avoid warning unused parameters */
		( void ) pxNetworkBuffer;
		( void ) uxHeaderLength;
	}
	#endif /* ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 */

	return eReturn;
}
/*-----------------------------------------------------------*/

static eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket, NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
eFrameProcessingResult_t eReturn;
IPHeader_t * pxIPHeader = &( pxIPPacket->xIPHeader );
ProtocolHeaders_t *pxProtocolHeaders;
#if( ipconfigUSE_IPv6 != 0 )
	const IPHeader_IPv6_t * pxIPHeader_IPv6;
#endif
UBaseType_t uxHeaderLength;
uint8_t ucProtocol;

	#if( ipconfigUSE_IPv6 != 0 )
	pxIPHeader_IPv6 = ipPOINTER_CAST( const IPHeader_IPv6_t *, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
	if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
	{
		uxHeaderLength = ipSIZE_OF_IPv6_HEADER;
		ucProtocol = pxIPHeader_IPv6->ucNextHeader;
		pxProtocolHeaders = ipPOINTER_CAST( ProtocolHeaders_t *, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
		eReturn = prvAllowIPPacketIPv6( ipPOINTER_CAST( IPHeader_IPv6_t *, &( pxIPPacket->xIPHeader ) ), pxNetworkBuffer, uxHeaderLength );
		/* The IP-header type is copied to a location 6 bytes before the messages
		starts.  It might be needed later on when a UDP-payload buffer is being
		used. */
		pxNetworkBuffer->pucEthernetBuffer[ 0 - ( BaseType_t ) ipIP_TYPE_OFFSET ] = pxIPHeader_IPv6->ucVersionTrafficClass;
	}
	else
	#endif
	{
	size_t uxLength = ( size_t ) pxIPHeader->ucVersionHeaderLength;

		/* Check if the IP headers are acceptable and if it has our destination.
		The lowest four bits of 'ucVersionHeaderLength' indicate the IP-header
		length in multiples of 4. */
		uxHeaderLength = ( size_t ) ( ( uxLength & 0x0FU ) << 2 );
		ucProtocol = pxIPPacket->xIPHeader.ucProtocol;
		pxProtocolHeaders = ipPOINTER_CAST( ProtocolHeaders_t *, &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxHeaderLength ] ) );
		eReturn = prvAllowIPPacketIPv4( pxIPPacket, pxNetworkBuffer, uxHeaderLength );
		#if( ipconfigUSE_IPv6 != 0 )
		{
			/* The IP-header type is copied to a location 6 bytes before the
			messages starts.  It might be needed later on when a UDP-payload
			buffer is being used. */
			pxNetworkBuffer->pucEthernetBuffer[ 0 - ( BaseType_t ) ipIP_TYPE_OFFSET ] = pxIPHeader->ucVersionHeaderLength;
		}
		#endif /* ipconfigUSE_IPv6 */
	}

	if( eReturn == eProcessBuffer )
	{
		if(
			#if( ipconfigUSE_IPv6 != 0 )
				( pxIPPacket->xEthernetHeader.usFrameType != ipIPv6_FRAME_TYPE ) &&
			#endif /* ipconfigUSE_IPv6 */
			( uxHeaderLength > ipSIZE_OF_IPv4_HEADER ) )
		{
			#if( ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS != 0 )
			{
				/* All structs of headers expect a IP header size of 20 bytes
				 * IP header options were included, we'll ignore them and cut them out. */
				const size_t optlen = ( ( size_t ) uxHeaderLength ) - ipSIZE_OF_IPv4_HEADER;
				/* From: the previous start of UDP/ICMP/TCP data. */
				const uint8_t *pucSource = ( const uint8_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( EthernetHeader_t ) + uxHeaderLength ] );
				/* To: the usual start of UDP/ICMP/TCP data at offset 20 (decimal ) from IP header. */
				uint8_t *pucTarget = ( uint8_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ sizeof( EthernetHeader_t ) + ipSIZE_OF_IPv4_HEADER ] );
				/* How many: total length minus the options and the lower headers. */
				const size_t  xMoveLen = pxNetworkBuffer->xDataLength - ( optlen + ipSIZE_OF_IPv4_HEADER + ipSIZE_OF_ETH_HEADER );

				( void ) memmove( pucTarget, pucSource, xMoveLen );
				pxNetworkBuffer->xDataLength -= optlen;

				/* Rewrite the Version/IHL byte to indicate that this packet has no IP options. */
				pxIPHeader->ucVersionHeaderLength = ( pxIPHeader->ucVersionHeaderLength & 0xF0U ) | /* High nibble is the version. */
													( ( ipSIZE_OF_IPv4_HEADER >> 2 ) & 0x0FU );
			}
			#else
			{
					/* 'ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS' is not set, so packets carrying
				IP-options will be dropped. */
				eReturn = eReleaseBuffer;
			}
			#endif
		}

		if( eReturn != eReleaseBuffer )
		{
			/* Add the IP and MAC addresses to the ARP table if they are not
			 already there - otherwise refresh the age of the existing
			 entry. */
			if( ucProtocol != ( uint8_t ) ipPROTOCOL_UDP )
			{
				/* Refresh the ARP cache with the IP/MAC-address of the received
				packet.  For UDP packets, this will be done later in
				xProcessReceivedUDPPacket(), as soon as it's know that the message
				will be handled.  This will prevent the ARP cache getting
				overwritten with the IP address of useless broadcast packets. */
#if( ipconfigUSE_IPv6 != 0 )
				if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
				{
					vNDRefreshCacheEntry( &( pxIPPacket->xEthernetHeader.xSourceAddress ), &( pxIPHeader_IPv6->xSourceAddress ), pxNetworkBuffer->pxEndPoint );
				}
				else
#endif /* ipconfigUSE_IPv6 */
				{
					vARPRefreshCacheEntry( &( pxIPPacket->xEthernetHeader.xSourceAddress ), pxIPHeader->ulSourceIPAddress, pxNetworkBuffer->pxEndPoint );
				}
			}

			switch( ucProtocol )
			{
				case ipPROTOCOL_ICMP :
					/* The IP packet contained an ICMP frame.  Don't bother checking
					the ICMP checksum, as if it is wrong then the wrong data will
					also be returned, and the source of the ping will know something
					went wrong because it will not be able to validate what it
					receives. */
					#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
					{
						if( pxNetworkBuffer->xDataLength >= sizeof( ICMPPacket_t ) )
						{
							/* Map the buffer onto a ICMP-Packet struct to easily access the
							 * fields of ICMP packet. */
							ICMPPacket_t *pxICMPPacket = ipPOINTER_CAST( ICMPPacket_t *, pxNetworkBuffer->pucEthernetBuffer );
							eReturn = prvProcessICMPPacket( pxICMPPacket );
						}
						else
						{
							eReturn = eReleaseBuffer;
						}
					}
					#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */
					break;

#if( ipconfigUSE_IPv6 != 0 )
				case ipPROTOCOL_ICMP_IPv6:
					eReturn = prvProcessICMPMessage_IPv6( pxNetworkBuffer );
					break;
#endif

				case ipPROTOCOL_UDP :
					{
					/* The IP packet contained a UDP frame. */
					UDPPacket_t *pxUDPPacket = ipPOINTER_CAST( UDPPacket_t *, pxNetworkBuffer->pucEthernetBuffer );

					size_t uxMinSize = ipSIZE_OF_ETH_HEADER + ( size_t ) uxIPHeaderSizePacket( pxNetworkBuffer ) + ipSIZE_OF_UDP_HEADER;
					size_t uxLength;
					uint16_t usLength;

						usLength = FreeRTOS_ntohs( pxProtocolHeaders->xUDPHeader.usLength );
						uxLength = ( size_t ) usLength;

						/* Note the header values required prior to the checksum
						generation as the checksum pseudo header may clobber some of
						these values. */
						if ( ( pxNetworkBuffer->xDataLength >= uxMinSize ) &&
						 	 ( uxLength >= sizeof( UDPHeader_t ) ) )
						{
						size_t uxPayloadSize_1, uxPayloadSize_2;
							/* Ensure that downstream UDP packet handling has the lesser
							of: the actual network buffer Ethernet frame length, or
							the sender's UDP packet header payload length, minus the
							size of the UDP header.

							The size of the UDP packet structure in this implementation
							includes the size of the Ethernet header, the size of
							the IP header, and the size of the UDP header. */
							uxPayloadSize_1 = pxNetworkBuffer->xDataLength - uxMinSize;
							uxPayloadSize_2 = uxLength - ipSIZE_OF_UDP_HEADER;
							if( uxPayloadSize_1 > uxPayloadSize_2 )
							{
								pxNetworkBuffer->xDataLength = uxPayloadSize_2 + uxMinSize;
							}

							pxNetworkBuffer->usPort = pxProtocolHeaders->xUDPHeader.usSourcePort;
						pxNetworkBuffer->ulIPAddress = pxUDPPacket->xIPHeader.ulSourceIPAddress;

						/* ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM:
						In some cases, the upper-layer checksum has been calculated
						by the NIC driver. */

						/* Pass the packet payload to the UDP sockets
						implementation. */
						if( xProcessReceivedUDPPacket( pxNetworkBuffer,
													   pxProtocolHeaders->xUDPHeader.usDestinationPort ) == pdPASS )
						{
							eReturn = eFrameConsumed;
						}
					}
				}
				break;

#if ipconfigUSE_TCP == 1
				case ipPROTOCOL_TCP :
					{

						if( xProcessReceivedTCPPacket( pxNetworkBuffer ) == pdPASS )
						{
							eReturn = eFrameConsumed;
						}

						/* Setting this variable will cause xTCPTimerCheck()
						to be called just before the IP-task blocks. */
						xProcessedTCPMessage++;
					}
					break;
	#endif
				default	:
					/* Not a supported frame type. */
					break;
			}
		}
	}

	return eReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

	static void prvProcessICMPEchoReply( ICMPPacket_t * const pxICMPPacket )
	{
	ePingReplyStatus_t eStatus = eSuccess;
	uint16_t usDataLength, usCount;
	uint8_t *pucByte;

		/* Find the total length of the IP packet. */
		usDataLength = pxICMPPacket->xIPHeader.usLength;
		usDataLength = FreeRTOS_ntohs( usDataLength );

		/* Remove the length of the IP headers to obtain the length of the ICMP
		message itself. */
		usDataLength = ( uint16_t ) ( ( ( uint32_t ) usDataLength ) - ipSIZE_OF_IPv4_HEADER );

		/* Remove the length of the ICMP header, to obtain the length of
		data contained in the ping. */
		usDataLength = ( uint16_t ) ( ( ( uint32_t ) usDataLength ) - ipSIZE_OF_ICMPv4_HEADER );

		/* Checksum has already been checked before in prvProcessIPPacket */

		/* Find the first byte of the data within the ICMP packet. */
		pucByte = ( uint8_t * ) pxICMPPacket;
		pucByte = &( pucByte[ sizeof( ICMPPacket_t ) ] );

		/* Check each byte. */
		for( usCount = 0; usCount < usDataLength; usCount++ )
		{
			if( *pucByte != ( uint8_t ) ipECHO_DATA_FILL_BYTE )
			{
				eStatus = eInvalidData;
				break;
			}

			pucByte++;
		}

		/* Call back into the application to pass it the result. */
		vApplicationPingReplyHook( eStatus, pxICMPPacket->xICMPHeader.usIdentifier );
	}

#endif
/*-----------------------------------------------------------*/

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )

	static eFrameProcessingResult_t prvProcessICMPEchoRequest( ICMPPacket_t * const pxICMPPacket )
	{
	ICMPHeader_t *pxICMPHeader;
	IPHeader_t *pxIPHeader;
	uint16_t usRequest;
	uint32_t ulIPAddress;

		pxICMPHeader = &( pxICMPPacket->xICMPHeader );
		pxIPHeader = &( pxICMPPacket->xIPHeader );

		/* HT:endian: changed back */
		iptraceSENDING_PING_REPLY( pxIPHeader->ulSourceIPAddress );

		/* The checksum can be checked here - but a ping reply should be
		returned even if the checksum is incorrect so the other end can
		tell that the ping was received - even if the ping reply contains
		invalid data. */
		pxICMPHeader->ucTypeOfMessage = ( uint8_t ) ipICMP_ECHO_REPLY;
		ulIPAddress = pxIPHeader->ulDestinationIPAddress;
		pxIPHeader->ulDestinationIPAddress = pxIPHeader->ulSourceIPAddress;
		pxIPHeader->ulSourceIPAddress = ulIPAddress;

		/* Update the checksum because the ucTypeOfMessage member in the header
		has been changed to ipICMP_ECHO_REPLY.  This is faster than calling
		usGenerateChecksum(). */

		/* due to compiler warning "integer operation result is out of range" */

		usRequest = ( uint16_t ) ( ( uint16_t )ipICMP_ECHO_REQUEST << 8 );

		if( pxICMPHeader->usChecksum >= FreeRTOS_htons( 0xFFFFU - usRequest ) )
		{
			pxICMPHeader->usChecksum = pxICMPHeader->usChecksum + FreeRTOS_htons( usRequest + 1U );
		}
		else
		{
			pxICMPHeader->usChecksum = pxICMPHeader->usChecksum + FreeRTOS_htons( usRequest );
		}
		return eReturnEthernetFrame;
	}

#endif /* ipconfigREPLY_TO_INCOMING_PINGS == 1 */
/*-----------------------------------------------------------*/

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

	static eFrameProcessingResult_t prvProcessICMPPacket( ICMPPacket_t * const pxICMPPacket )
	{
	eFrameProcessingResult_t eReturn = eReleaseBuffer;

		iptraceICMP_PACKET_RECEIVED();
		switch( pxICMPPacket->xICMPHeader.ucTypeOfMessage )
		{
			case ipICMP_ECHO_REQUEST	:
				#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )
				{
					eReturn = prvProcessICMPEchoRequest( pxICMPPacket );
				}
				#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) */
				break;

			case ipICMP_ECHO_REPLY		:
				#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
				{
					prvProcessICMPEchoReply( pxICMPPacket );
				}
				#endif /* ipconfigSUPPORT_OUTGOING_PINGS */
				break;

			default	:
				/* Only ICMP echo packets are handled. */
				break;
		}

		return eReturn;
	}

#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */
/*-----------------------------------------------------------*/

uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer, size_t uxBufferLength, BaseType_t xOutgoingPacket )
{
uint32_t ulLength;
uint16_t usChecksum, *pusChecksum, usPayloadLength, usProtolBytes;
const IPPacket_t * pxIPPacket;
size_t uxIPHeaderLength;
ProtocolHeaders_t *pxProtocolHeaders;
uint8_t ucProtocol = 0U;
BaseType_t xLocation = 0;
#if( ipconfigUSE_IPv6 != 0 )
	BaseType_t xIsIPv6;
	const IPHeader_IPv6_t * pxIPPacket_IPv6;
	uint32_t pulHeader[ 2 ];
#endif

#if( ipconfigHAS_DEBUG_PRINTF != 0 )
	const char *pcType;
#endif

	/* Introduce a do-while loop to allow use of break statements.
	 * Note: MISRA prohibits use of 'goto', thus replaced with breaks. */
	do
	{
		/* Parse the packet length. */
		pxIPPacket = ipPOINTER_CAST( const IPPacket_t *, pucEthernetBuffer );

	#if( ipconfigUSE_IPv6 != 0 )
		pxIPPacket_IPv6 = ipPOINTER_CAST( const IPHeader_IPv6_t *, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER ] ) );
		if( pxIPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
		{
			xIsIPv6 = pdTRUE;
		}
		else
		{
			xIsIPv6 = pdFALSE;
		}

		if( xIsIPv6 != pdFALSE )
		{
			uxIPHeaderLength = ipSIZE_OF_IPv6_HEADER;

			/* Check for minimum packet size: ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER (54 bytes) */
			if( uxBufferLength < sizeof( IPPacket_IPv6_t ) )
			{
				usChecksum = ipINVALID_LENGTH;
				xLocation = 1;
				break;
			}

			ucProtocol = pxIPPacket_IPv6->ucNextHeader;
			pxProtocolHeaders = ipPOINTER_CAST( ProtocolHeaders_t *, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ] ) );
			usPayloadLength = FreeRTOS_ntohs( pxIPPacket_IPv6->usPayloadLength );
			/* For IPv6, the number of bytes in the protocol is indicated. */
			usProtolBytes = usPayloadLength;
			if( uxBufferLength < ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + usPayloadLength ) )
			{
				usChecksum = ipINVALID_LENGTH;
				xLocation = 2;
				break;
			}
		}
		else
	#endif	/* ( ipconfigUSE_IPv6 != 0 ) */
		{
			/* Check for minimum packet size ( 14 + 20 bytes ). */
			if( uxBufferLength < sizeof( IPPacket_t ) )
			{
				usChecksum = ipINVALID_LENGTH;
				xLocation = 3;
				break;
			}
			uxIPHeaderLength = 4U * ( ( ( uint8_t ) 0x0FU ) & pxIPPacket->xIPHeader.ucVersionHeaderLength );/*lint !e9031 !e9033 Impermissible cast of composite expression (wider essential type for the destination) [MISRA 2012 Rule 10.8, required]. */

			/* Check for minimum packet size. */
			if( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + uxIPHeaderLength ) )
			{
				usChecksum = ipINVALID_LENGTH;
				xLocation = 4;
				break;
			}
			/* xIPHeader.usLength is the total length, minus the Ethernet header. */
			usPayloadLength = FreeRTOS_ntohs( pxIPPacket->xIPHeader.usLength );
			if( uxBufferLength < ipNUMERIC_CAST( size_t, ipSIZE_OF_ETH_HEADER + usPayloadLength ) )
			{
				usChecksum = ipINVALID_LENGTH;
				xLocation = 5;
				break;
			}

			/* Identify the next protocol. */
			ucProtocol = pxIPPacket->xIPHeader.ucProtocol;
			pxProtocolHeaders = ipPOINTER_CAST( ProtocolHeaders_t *, &( pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + ( size_t ) uxIPHeaderLength ] ) );
			/* For IPv4, the number of bytes in IP-header + the protocol is indicated. */
			usProtolBytes = usPayloadLength - ( ( uint16_t ) uxIPHeaderLength );
		}
		/* Compare 'uxBufferLength' with the total expected length of the packet. */
		if( uxBufferLength < ipNUMERIC_CAST( size_t, ipSIZE_OF_ETH_HEADER + usPayloadLength ) )
		{
			usChecksum = ipINVALID_LENGTH;
			xLocation = 6;
			break;
		}

		/* Switch on the Layer 3/4 protocol. */
		if( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
		{
			if( ( usProtolBytes < ipSIZE_OF_UDP_HEADER ) ||
				( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + uxIPHeaderLength + ipSIZE_OF_UDP_HEADER ) ) )
			{
				usChecksum = ipINVALID_LENGTH;
				xLocation = 7;
				break;
			}

			pusChecksum = ( uint16_t * ) ( &( pxProtocolHeaders->xUDPHeader.usChecksum ) );
			#if( ipconfigHAS_DEBUG_PRINTF != 0 )
			{
				pcType = "UDP";
			}
			#endif	/* ipconfigHAS_DEBUG_PRINTF != 0 */
		}
		else if( ucProtocol == ( uint8_t ) ipPROTOCOL_TCP )
		{
			if( ( usProtolBytes < ipSIZE_OF_TCP_HEADER ) ||
				( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + uxIPHeaderLength + ipSIZE_OF_TCP_HEADER ) ) )
			{
				usChecksum = ipINVALID_LENGTH;
				xLocation = 8;
				break;
			}

			pusChecksum = ( uint16_t * ) ( &( pxProtocolHeaders->xTCPHeader.usChecksum ) );
			#if( ipconfigHAS_DEBUG_PRINTF != 0 )
			{
				pcType = "TCP";
			}
			#endif	/* ipconfigHAS_DEBUG_PRINTF != 0 */
		}
		else if( ( ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP ) ||
				( ucProtocol == ( uint8_t ) ipPROTOCOL_IGMP ) )
		{
			if( ( usProtolBytes < ipSIZE_OF_ICMPv4_HEADER ) ||
				( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + uxIPHeaderLength + ipSIZE_OF_ICMPv4_HEADER ) ) )
			{
				usChecksum = ipINVALID_LENGTH;
				xLocation = 9;
				break;
			}

			pusChecksum = ( uint16_t * ) ( &( pxProtocolHeaders->xICMPHeader.usChecksum ) );

			#if( ipconfigHAS_DEBUG_PRINTF != 0 )
			{
				if( ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP )
				{
					pcType = "ICMP";
				}
				else
				{
					pcType = "IGMP";
				}
			}
			#endif	/* ipconfigHAS_DEBUG_PRINTF != 0 */
		}
		#if( ipconfigUSE_IPv6 != 0 )
		else if( ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP_IPv6 )
		{
		size_t xICMPLength;
			switch( pxProtocolHeaders->xICMPHeader_IPv6.ucTypeOfMessage )
			{
				case ipICMP_PING_REQUEST_IPv6:
				case ipICMP_PING_REPLY_IPv6:
					xICMPLength = sizeof( ICMPEcho_IPv6_t );
					break;
				case ipICMP_ROUTER_SOLICITATION_IPv6:
					xICMPLength = sizeof( ICMPRouterSolicitation_IPv6_t );
					break;
				default:
					xICMPLength = ipSIZE_OF_ICMPv6_HEADER;
					break;
			}
			if( uxBufferLength < ( ipSIZE_OF_ETH_HEADER + uxIPHeaderLength + xICMPLength ) )
			{
				usChecksum = ipINVALID_LENGTH;
				xLocation = 10;
				break;
			}
			pusChecksum = ( uint16_t * ) ( &( pxProtocolHeaders->xICMPHeader.usChecksum ) );
			#if( ipconfigHAS_DEBUG_PRINTF != 0 )
			{
				pcType = "ICMP_IPv6";
			}
			#endif	/* ipconfigHAS_DEBUG_PRINTF != 0 */
		}
		#endif
		else
		{
			/* Unhandled protocol, other than ICMP, IGMP, UDP, or TCP. */
			usChecksum = ipUNHANDLED_PROTOCOL;
			xLocation = 11;
			break;
		}

		if( xOutgoingPacket != pdFALSE )
		{
			/* This is an outgoing packet. Before calculating the checksum, set it
			to zero. */
			*( pusChecksum ) = 0U;
		}
		else if( ( *pusChecksum == 0U ) && ( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP ) )
		{
			#if( ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS == 0 )
			{
				/* Sender hasn't set the checksum, drop the packet because
				ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS is not set. */
				usChecksum = ipWRONG_CRC;
				#if( ipconfigHAS_PRINTF != 0 )
				{
				static BaseType_t xCount = 0;

					if( xCount < 5 )
					{
						FreeRTOS_printf( ( "usGenerateProtocolChecksum: UDP packet from %xip without CRC dropped\n",
							FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulSourceIPAddress ) ) );
						xCount++;
					}
				}
				#endif	/* ( ipconfigHAS_PRINTF != 0 ) */
			}
			#else
			{
				/* Sender hasn't set the checksum, no use to calculate it. */
				usChecksum = ipCORRECT_CRC;
			}
			#endif
			xLocation = 12;
			break;
		}
		else
		{
			/* This is an incoming packet, not being an UDP packet without a checksum. */
		}

		#if( ipconfigUSE_IPv6 != 0 )
		if( xIsIPv6 != pdFALSE )
		{
			ulLength = ( uint32_t ) usPayloadLength;
			/* IPv6 has a 40-byte pseudo header:
			 0..15 Source IPv6 address
			16..31 Target IPv6 address
			32..35 Length of payload
			36..38 three zero's
			39 Next Header, i.e. the protocol type. */

			pulHeader[ 0 ] = FreeRTOS_htonl( ulLength );
			pulHeader[ 1 ] = ( uint32_t ) pxIPPacket_IPv6->ucNextHeader;
			pulHeader[ 1 ] = FreeRTOS_htonl( pulHeader[ 1 ] );

			usChecksum = usGenerateChecksum( 0U,
											 ( const uint8_t * )&( pxIPPacket_IPv6->xSourceAddress ),
											 ( size_t )( 2U * sizeof( pxIPPacket_IPv6->xSourceAddress ) ) );

			usChecksum = usGenerateChecksum( usChecksum,
											 ( const uint8_t * ) pulHeader,
											 ( size_t )( sizeof( pulHeader ) ) );
		}
		else
		#endif
		{
			ulLength = ( uint32_t ) usPayloadLength;
			ulLength -= uxIPHeaderLength; /* normally minus 20 */
			usChecksum = 0;
		}

		if( ( ulLength < sizeof( pxProtocolHeaders->xUDPHeader ) ) ||
			( ulLength > ( uint32_t )( ipconfigNETWORK_MTU - uxIPHeaderLength ) ) )
		{
			#if( ipconfigHAS_DEBUG_PRINTF != 0 )
			{
				FreeRTOS_debug_printf( ( "usGenerateProtocolChecksum[%s]: len invalid: %lu\n", pcType, ulLength ) );
			}
			#endif	/* ipconfigHAS_DEBUG_PRINTF != 0 */

			/* Again, in a 16-bit return value there is no space to indicate an
			error.  For incoming packets, 0x1234 will cause dropping of the packet.
			For outgoing packets, there is a serious problem with the
			format/length */
			usChecksum = ipINVALID_LENGTH;
			xLocation = 13;
			break;
		}
		if( ( ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP ) || ( ucProtocol == ( uint8_t ) ipPROTOCOL_IGMP ) )
		{
			/* ICMP/IGMP do not have a pseudo header for CRC-calculation. */
			usChecksum = ( uint16_t )
				( ~usGenerateChecksum( 0U, ( uint8_t * ) &( pxProtocolHeaders->xICMPHeader ), ( size_t ) ulLength ) );
		}
		#if( ipconfigUSE_IPv6 != 0 )
		else if( ucProtocol == ( uint8_t ) ipPROTOCOL_ICMP_IPv6 )
		{
			usChecksum = ( uint16_t )
				( ~usGenerateChecksum( usChecksum,
									   ( uint8_t * ) &( pxProtocolHeaders->xTCPHeader ),
									   ( size_t ) ulLength ) );
		}
		#endif /* ipconfigUSE_IPv6 */
		else
		{
			#if( ipconfigUSE_IPv6 != 0 )
			if( xIsIPv6 != pdFALSE )
			{
				/* The CRC of the IPv6 pseudo-header has already been calculated. */
				usChecksum = ( uint16_t )
					( ~usGenerateChecksum( usChecksum,
										   ( uint8_t * )&( pxProtocolHeaders->xUDPHeader.usSourcePort ),
										   ( size_t )( ulLength ) ) );
			}
			else
			#endif /* ipconfigUSE_IPv6 */
			{
				/* For UDP and TCP, sum the pseudo header, i.e. IP protocol + length
				fields */
				usChecksum = ( uint16_t ) ( ulLength + ( ( uint16_t ) ucProtocol ) );

				/* And then continue at the IPv4 source and destination addresses. */
				usChecksum = ( uint16_t )
					( ~usGenerateChecksum( usChecksum,
										   ipPOINTER_CAST( const uint8_t *, &( pxIPPacket->xIPHeader.ulSourceIPAddress ) ),
										   ( size_t )( ( 2U * ipSIZE_OF_IPv4_ADDRESS ) + ulLength ) ) );
			}
			/* Sum TCP header and data. */
		}

		if( xOutgoingPacket == pdFALSE )
		{
			/* This is in incoming packet. If the CRC is correct, it should be zero. */
			if( usChecksum == 0U )
			{
				usChecksum = ( uint16_t )ipCORRECT_CRC;
			}
		}
		else
		{
			if( ( usChecksum == 0U ) && ( ucProtocol == ( uint8_t ) ipPROTOCOL_UDP ) )
			{
				/* In case of UDP, a calculated checksum of 0x0000 is transmitted
				as 0xffff. A value of zero would mean that the checksum is not used. */
				#if( ipconfigHAS_DEBUG_PRINTF != 0 )
				{
					if( xOutgoingPacket != pdFALSE )
					{
						FreeRTOS_debug_printf( ( "usGenerateProtocolChecksum[%s]: crc swap: %04X\n", pcType, usChecksum ) );
					}
				}
				#endif	/* ipconfigHAS_DEBUG_PRINTF != 0 */

				usChecksum = ( uint16_t )0xffffu;
			}
		}
		usChecksum = FreeRTOS_htons( usChecksum );

		if( xOutgoingPacket != pdFALSE )
		{
			*( pusChecksum ) = usChecksum;
		}
		#if( ipconfigHAS_DEBUG_PRINTF != 0 )
		else if( ( xOutgoingPacket == pdFALSE ) && ( usChecksum != ipCORRECT_CRC ) )/*lint !e774 Boolean within 'left side of && within if' always evaluates to True [MISRA 2012 Rule 14.3, required]. */
		{
		uint16_t usGot, usCalculated;
			usGot = *pusChecksum;
			usCalculated = ~usGenerateProtocolChecksum( pucEthernetBuffer, uxBufferLength, pdTRUE );
			FreeRTOS_debug_printf( ( "usGenerateProtocolChecksum[%s]: len %ld ID %04X: from %lxip to %lxip cal %04X got %04X\n",
				pcType,
				ulLength,
				FreeRTOS_ntohs( pxIPPacket->xIPHeader.usIdentification ),
				FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulSourceIPAddress ),
				FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulDestinationIPAddress ),
				FreeRTOS_ntohs( usCalculated ),
				FreeRTOS_ntohs( usGot ) ) );
		}
		else
		{
			/* This is incoming packete and doesn't need denug logging. */
		}
		#endif	/* ipconfigHAS_DEBUG_PRINTF != 0 */
	} while( ipFALSE_BOOL );

	if( ( usChecksum == ipUNHANDLED_PROTOCOL ) || 
		( usChecksum == ipINVALID_LENGTH ) )
	{
		FreeRTOS_printf( ( "CRC error: %04x location %ld\n", usChecksum, xLocation ) );
	}

	return usChecksum;
}
/*-----------------------------------------------------------*/

int do_swap = 1;
uint16_t usGenerateChecksum( uint16_t usSum, const uint8_t * pucNextData, size_t uxDataLengthBytes )
{
xUnion32 xSum2, xSum, xTerm;
xUnionPtr xSource;
xUnionPtr xLastSource;
uintptr_t uxAlignBits;
uint32_t ulCarry = 0UL;
uint16_t usTemp;

	/* Small MCUs often spend up to 30% of the time doing checksum calculations
	This function is optimised for 32-bit CPUs; Each time it will try to fetch
	32-bits, sums it with an accumulator and counts the number of carries. */

	/* Swap the input (little endian platform only). */
	usTemp = FreeRTOS_ntohs( usSum );
	xSum.u32 = ( uint32_t ) usTemp;
	xTerm.u32 = 0UL;

	xSource.u8ptr = ipPOINTER_CAST( uint8_t *, pucNextData );
	uxAlignBits = ( ( ( uintptr_t ) pucNextData ) & 0x03U ); /*lint !e9078 !e923*/	/* gives 0, 1, 2, or 3 */
if( uxAlignBits )
{
	FreeRTOS_printf( ( "uxAlignBits = %u\n", uxAlignBits ) );
}
	/*
	 * If pucNextData is non-aligned then the checksum is starting at an
	 * odd position and we need to make sure the usSum value now in xSum is
	 * as if it had been "aligned" in the same way.
	 */
	if( ( uxAlignBits & 1UL) != 0U )
	{
		if(do_swap)
		xSum.u32 = ( ( xSum.u32 & 0xffU ) << 8 ) | ( ( xSum.u32 & 0xff00U ) >> 8 );
	}

	/* If byte (8-bit) aligned... */
	if( ( ( uxAlignBits & 1UL ) != 0UL ) && ( uxDataLengthBytes >= ( size_t ) 1 ) )
	{
		xTerm.u8[ 1 ] = *( xSource.u8ptr );
		xSource.u8ptr++;
		uxDataLengthBytes--;
		/* Now xSource is word (16-bit) aligned. */
	}

	/* If half-word (16-bit) aligned... */
	if( ( ( uxAlignBits == 1U ) || ( uxAlignBits == 2U ) ) && ( uxDataLengthBytes >= 2U ) )
	{
		xSum.u32 += *(xSource.u16ptr);
		xSource.u16ptr++;
		uxDataLengthBytes -= 2U;
		/* Now xSource is word (32-bit) aligned. */
	}

	/* Word (32-bit) aligned, do the most part. */
	xLastSource.u32ptr = ( xSource.u32ptr + ( uxDataLengthBytes / 4U ) ) - 3U;

	/* In this loop, four 32-bit additions will be done, in total 16 bytes.
	Indexing with constants (0,1,2,3) gives faster code than using
	post-increments. */
	while( xSource.u32ptr < xLastSource.u32ptr )
	{
		/* Use a secondary Sum2, just to see if the addition produced an
		overflow. */
		xSum2.u32 = xSum.u32 + xSource.u32ptr[ 0 ];
		if( xSum2.u32 < xSum.u32 )
		{
			ulCarry++;
		}

		/* Now add the secondary sum to the major sum, and remember if there was
		a carry. */
		xSum.u32 = xSum2.u32 + xSource.u32ptr[ 1 ];
		if( xSum2.u32 > xSum.u32 )
		{
			ulCarry++;
		}

		/* And do the same trick once again for indexes 2 and 3 */
		xSum2.u32 = xSum.u32 + xSource.u32ptr[ 2 ];
		if( xSum2.u32 < xSum.u32 )
		{
			ulCarry++;
		}

		xSum.u32 = xSum2.u32 + xSource.u32ptr[ 3 ];

		if( xSum2.u32 > xSum.u32 )
		{
			ulCarry++;
		}

		/* And finally advance the pointer 4 * 4 = 16 bytes. */
		xSource.u32ptr = &( xSource.u32ptr[ 4 ] );
	}

	/* Now add all carries. */
	xSum.u32 = ( uint32_t )xSum.u16[ 0 ] + xSum.u16[ 1 ] + ulCarry;

	uxDataLengthBytes %= 16U;
	xLastSource.u8ptr = ( uint8_t * ) ( xSource.u8ptr + ( uxDataLengthBytes & ~( ( size_t ) 1 ) ) );

	/* Half-word aligned. */
	/* Coverity does not like Unions. Warning issued here: "The operator "<"
	 * is being applied to the pointers "xSource.u16ptr" and "xLastSource.u16ptr",
	 * which do not point into the same object." */
	while( xSource.u16ptr < xLastSource.u16ptr )
	{
		/* At least one more short. */
		xSum.u32 += xSource.u16ptr[ 0 ];
		xSource.u16ptr++;
	}

	if( ( uxDataLengthBytes & ( size_t ) 1 ) != 0U )	/* Maybe one more ? */
	{
		xTerm.u8[ 0 ] = xSource.u8ptr[ 0 ];
	}
	xSum.u32 += xTerm.u32;

	/* Now add all carries again. */
	/* Assigning value from "xTerm.u32" to "xSum.u32" here, but that stored value is overwritten before it can be used.
	Coverity doesn't understand about union variables. */
	xSum.u32 = ( uint32_t ) xSum.u16[ 0 ] + xSum.u16[ 1 ];

	/* coverity[value_overwrite] */
	xSum.u32 = ( uint32_t ) xSum.u16[ 0 ] + xSum.u16[ 1 ];

	if( ( uxAlignBits & 1U ) != 0U )
	{
		/* Quite unlikely, but pucNextData might be non-aligned, which would
		 mean that a checksum is calculated starting at an odd position. */
		xSum.u32 = ( ( xSum.u32 & 0xffU ) << 8 ) | ( ( xSum.u32 & 0xff00U ) >> 8 );
	}

	/* swap the output (little endian platform only). */
	return FreeRTOS_htons( ( (uint16_t) xSum.u32 ) );
}
/*-----------------------------------------------------------*/

/* This function is used in other files, has external linkage e.g. in
 * FreeRTOS_DNS.c. Not to be made static. */
void vReturnEthernetFrame( NetworkBufferDescriptor_t * pxNetworkBuffer, BaseType_t xReleaseAfterSend )
{
IPPacket_t *pxIPPacket;

#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
	NetworkBufferDescriptor_t *pxNewBuffer;
#endif

	#if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES )
	{
		if( pxNetworkBuffer->xDataLength < ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES )
		{
		BaseType_t xIndex;

			FreeRTOS_printf( ( "vReturnEthernetFrame: length %u\n", ( unsigned ) pxNetworkBuffer->xDataLength ) );
			for( xIndex = ( BaseType_t ) pxNetworkBuffer->xDataLength; xIndex < ( BaseType_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES; xIndex++ )
			{
				pxNetworkBuffer->pucEthernetBuffer[ xIndex ] = 0U;
			}
			pxNetworkBuffer->xDataLength = ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES;
		}
	}
	#endif

#if( ipconfigZERO_COPY_TX_DRIVER != 0 )

	if( xReleaseAfterSend == pdFALSE )
	{
		pxNewBuffer = pxDuplicateNetworkBufferWithDescriptor( pxNetworkBuffer, pxNetworkBuffer->xDataLength );
		xReleaseAfterSend = pdTRUE;
		/* Want no rounding up. */
		pxNewBuffer->xDataLength = pxNetworkBuffer->xDataLength;
		pxNetworkBuffer = pxNewBuffer;
	}

	if( pxNetworkBuffer != NULL )
#endif
	{
		pxIPPacket = ipPOINTER_CAST( IPPacket_t *, pxNetworkBuffer->pucEthernetBuffer );

		/* Send! */
		if( pxNetworkBuffer->pxEndPoint == NULL )
		{
			/* _HT_ I wonder if this ad-hoc search of an end-point it necessary. */
			FreeRTOS_printf( ( "vReturnEthernetFrame: No pxEndPoint yet for %lxip?\n", FreeRTOS_ntohl( pxIPPacket->xIPHeader.ulDestinationIPAddress ) ) );
			#if( ipconfigUSE_IPv6 != 0 )
			if( ( ipPOINTER_CAST( EthernetHeader_t *, pxNetworkBuffer->pucEthernetBuffer ) )->usFrameType == ipIPv6_FRAME_TYPE )
			{
				// To do
			}
			else
			#endif /* ipconfigUSE_IPv6 */
			{
				pxNetworkBuffer->pxEndPoint = FreeRTOS_FindEndPointOnNetMask( pxIPPacket->xIPHeader.ulDestinationIPAddress, 7 );
			}
		}

		if( pxNetworkBuffer->pxEndPoint != NULL )
		{
		NetworkInterface_t *pxInterface = pxNetworkBuffer->pxEndPoint->pxNetworkInterface; /*_RB_ Why not use the pxNetworkBuffer->pxNetworkInterface directly? */

			/* Swap source and destination MAC addresses. */
			( void ) memcpy( &( pxIPPacket->xEthernetHeader.xDestinationAddress ), &( pxIPPacket->xEthernetHeader.xSourceAddress ), sizeof( pxIPPacket->xEthernetHeader.xDestinationAddress ) );
			( void ) memcpy( &( pxIPPacket->xEthernetHeader.xSourceAddress), pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
			( void ) pxInterface->pfOutput( pxInterface, pxNetworkBuffer, xReleaseAfterSend );
		}
	}
}
/*-----------------------------------------------------------*/

#if ( ipconfigHAS_PRINTF != 0 )
	
	#ifndef ipMONITOR_MAX_HEAP
		/* As long as the heap has more space than e.g. 1 MB, there
		will be no messages. */
		#define	ipMONITOR_MAX_HEAP			( 1024U * 1024U )
	#endif	/* ipMONITOR_MAX_HEAP */

	#ifndef ipMONITOR_PERCENTAGE_90
		/* Make this number lower to get less logging messages. */
		#define ipMONITOR_PERCENTAGE_90		( 90U )
	#endif

	#define ipMONITOR_PERCENTAGE_100		( 100U )

	void vPrintResourceStats( void )
	{
	static UBaseType_t uxLastMinBufferCount = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
	static size_t uxMinLastSize = 0u;
	UBaseType_t uxCurrentBufferCount;
	size_t uxMinSize;

		/* When setting up and testing a project with FreeRTOS+TCP, it is
		can be helpful to monitor a few resources: the number of network
		buffers and the amount of available heap.
		This function will issue some logging when a minimum value has
		changed. */
		uxCurrentBufferCount = uxGetMinimumFreeNetworkBuffers();

		if( uxLastMinBufferCount > uxCurrentBufferCount )
		{
			/* The logging produced below may be helpful
			 * while tuning +TCP: see how many buffers are in use. */
			uxLastMinBufferCount = uxCurrentBufferCount;
			FreeRTOS_printf( ( "Network buffers: %lu lowest %lu\n",
							   uxGetNumberOfFreeNetworkBuffers(),
							   uxCurrentBufferCount ) );
		}

		uxMinSize = xPortGetMinimumEverFreeHeapSize();
		if( uxMinLastSize == 0U )
		{
			/* Probably the first time this function is called. */
			uxMinLastSize = uxMinSize;
		}
		else if( uxMinSize >= ipMONITOR_MAX_HEAP )
		{
			/* There is more than enough heap space. No need for logging. */
		}
		/* Write logging if there is a 10% decrease since the last time logging was written. */
		else if( ( uxMinLastSize * ipMONITOR_PERCENTAGE_90 ) > ( uxMinSize * ipMONITOR_PERCENTAGE_100 ) )
		{
			uxMinLastSize = uxMinSize;
			FreeRTOS_printf( ( "Heap: current %lu lowest %lu\n", xPortGetFreeHeapSize(), uxMinSize ) );
		}
		else
		{
			/* Nothing to log. */
		}

		#if ( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
		{
			static UBaseType_t uxLastMinQueueSpace = 0;
			UBaseType_t uxCurrentCount = 0u;

			uxCurrentCount = uxGetMinimumIPQueueSpace();

			if( uxLastMinQueueSpace != uxCurrentCount )
			{
				/* The logging produced below may be helpful
				 * while tuning +TCP: see how many buffers are in use. */
				uxLastMinQueueSpace = uxCurrentCount;
				FreeRTOS_printf( ( "Queue space: lowest %lu\n", uxCurrentCount ) );
			}
		}
		#endif /* ipconfigCHECK_IP_QUEUE_SPACE */
	}
#endif /* ( ipconfigHAS_PRINTF != 0 ) */
/*-----------------------------------------------------------*/

uint32_t FreeRTOS_GetIPAddress( void )
{
NetworkEndPoint_t * pxEndPoint;
uint32_t ulIPAddress;

	for( pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
		 pxEndPoint != NULL;
		 pxEndPoint = FreeRTOS_NextEndPoint( NULL, pxEndPoint ) )
	{
		if( ENDPOINT_IS_IPv4( pxEndPoint ) )
		{
			break;
		}
	}
	/* Returns the IP address of the NIC. */
	if( pxEndPoint == NULL )
	{
		ulIPAddress = 0UL;
	}
	else if( pxEndPoint->ipv4_settings.ulIPAddress != 0UL )	/* access to 'ipv4_settings' is checked. */
	{
		ulIPAddress = pxEndPoint->ipv4_settings.ulIPAddress;
	}
	else
	{
		ulIPAddress = pxEndPoint->ipv4_defaults.ulIPAddress;
	}

	return ulIPAddress;
}
/*-----------------------------------------------------------*/

/*
 * The helper functions here below can not exist in a multi-interface environment.
 */
/*
void FreeRTOS_SetIPAddress( uint32_t ulIPAddress )
{
	/* Sets the IP address of the NIC. */
	*ipLOCAL_IP_ADDRESS_POINTER = ulIPAddress;
}
/*-----------------------------------------------------------*/

uint32_t FreeRTOS_GetGatewayAddress( void )
{
	return xNetworkAddressing.ulGatewayAddress;
}
/*-----------------------------------------------------------*/

uint32_t FreeRTOS_GetDNSServerAddress( void )
{
	return xNetworkAddressing.ulDNSServerAddress;
}
/*-----------------------------------------------------------*/

uint32_t FreeRTOS_GetNetmask( void )
{
	return xNetworkAddressing.ulNetMask;
}

const uint8_t * FreeRTOS_GetMACAddress( void )
{
	return ipLOCAL_MAC_ADDRESS;
}
/*-----------------------------------------------------------*/

void FreeRTOS_SetNetmask ( uint32_t ulNetmask )
{
	xNetworkAddressing.ulNetMask = ulNetmask;
}
/*-----------------------------------------------------------*/

void FreeRTOS_SetGatewayAddress ( uint32_t ulGatewayAddress )
{
	xNetworkAddressing.ulGatewayAddress = ulGatewayAddress;
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 )
	void vIPSetDHCP_RATimerEnableState( struct xNetworkEndPoint *pxEndPoint, BaseType_t xEnableState )
	{
		/* 'xDHCP_RATimer' is shared between DHCP (IPv4) and RA/SLAAC (IPv6). */
		if( xEnableState != 0 )
		{
			pxEndPoint->xDHCP_RATimer.bActive = pdTRUE_UNSIGNED;
		}
		else
		{
			pxEndPoint->xDHCP_RATimer.bActive = pdFALSE_UNSIGNED;
		}
	}
#endif /* ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 ) */
/*-----------------------------------------------------------*/

#if( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 )
	void vIPReloadDHCP_RATimer( struct xNetworkEndPoint *pxEndPoint, TickType_t uxClockTicks )
	{
		prvIPTimerReload( &( pxEndPoint->xDHCP_RATimer ), uxClockTicks );
	}
#endif /* ( ipconfigUSE_DHCP == 1 ) || ( ipconfigUSE_RA == 1 ) */
/*-----------------------------------------------------------*/

#if( ipconfigDNS_USE_CALLBACKS == 1 )
	void vIPSetDnsTimerEnableState( BaseType_t xEnableState )
	{
		if( xEnableState != 0 )
		{
			xDNSTimer.bActive = pdTRUE;
		}
		else
		{
			xDNSTimer.bActive = pdFALSE;
		}
	}
#endif /* ipconfigUSE_DHCP */
/*-----------------------------------------------------------*/

#if( ipconfigDNS_USE_CALLBACKS != 0 )
	void vIPReloadDNSTimer( uint32_t ulCheckTime )
	{
		prvIPTimerReload( &xDNSTimer, ulCheckTime );
	}
#endif /* ipconfigDNS_USE_CALLBACKS != 0 */
/*-----------------------------------------------------------*/

BaseType_t xIPIsNetworkTaskReady( void )
{
	return xIPTaskInitialised;
}
/*-----------------------------------------------------------*/

BaseType_t FreeRTOS_IsNetworkUp()
{
	/* IsNetworkUp() is kept for backward compatibility. */
	return FreeRTOS_IsEndPointUp( NULL );
}
/*-----------------------------------------------------------*/

BaseType_t FreeRTOS_IsEndPointUp( const struct xNetworkEndPoint *pxEndPoint )
{
BaseType_t xReturn;

	if( pxEndPoint != NULL )
	{
		/* Is this particular end-point up? */
		xReturn	= ( BaseType_t ) pxEndPoint->bits.bEndPointUp;
	}
	else
	{
		/* Are all end-points up? */
		xReturn = FreeRTOS_AllEndPointsUp( NULL );
	}
	return xReturn;
}
/*-----------------------------------------------------------*/

/* Return pdTRUE if all end-points belonging to a given interface are up.
When pxInterface is null, all end-points will be checked. */
BaseType_t FreeRTOS_AllEndPointsUp( const struct xNetworkInterface *pxInterface )
{
BaseType_t xResult = pdTRUE;
NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;

	while( pxEndPoint != NULL )
	{
		if( ( pxInterface == NULL ) ||
			( pxEndPoint->pxNetworkInterface == pxInterface ) )

		{
			if( pxEndPoint->bits.bEndPointUp == pdFALSE_UNSIGNED )
			{
				xResult = pdFALSE;
				break;
			}
		}
		pxEndPoint = pxEndPoint->pxNext;
	}

	return xResult;
}
/*-----------------------------------------------------------*/

#if( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
	UBaseType_t uxGetMinimumIPQueueSpace( void )
	{
		return uxQueueMinimumSpace;
	}
#endif
/*-----------------------------------------------------------*/
/* Utility function: Convert error number to a human readable
 * string. Decalartion in FreeRTOS_errno_TCP.h. */
const char *FreeRTOS_strerror_r( BaseType_t xErrnum, char *pcBuffer, size_t uxLength )
{
const char *pcName;

	switch( xErrnum )
	{
		case pdFREERTOS_ERRNO_EADDRINUSE:     pcName = "EADDRINUSE"; break;
		case pdFREERTOS_ERRNO_ENOMEM:         pcName = "ENOMEM"; break;
		case pdFREERTOS_ERRNO_EADDRNOTAVAIL:  pcName = "EADDRNOTAVAIL"; break;
		case pdFREERTOS_ERRNO_ENOPROTOOPT:    pcName = "ENOPROTOOPT"; break;
		case pdFREERTOS_ERRNO_EBADF:          pcName = "EBADF"; break;
		case pdFREERTOS_ERRNO_ENOSPC:         pcName = "ENOSPC"; break;
		case pdFREERTOS_ERRNO_ECANCELED:      pcName = "ECANCELED"; break;
		case pdFREERTOS_ERRNO_ENOTCONN:       pcName = "ENOTCONN"; break;
		case pdFREERTOS_ERRNO_EINPROGRESS:    pcName = "EINPROGRESS"; break;
		case pdFREERTOS_ERRNO_EOPNOTSUPP:     pcName = "EOPNOTSUPP"; break;
		case pdFREERTOS_ERRNO_EINTR:          pcName = "EINTR"; break;
		case pdFREERTOS_ERRNO_ETIMEDOUT:      pcName = "ETIMEDOUT"; break;
		case pdFREERTOS_ERRNO_EINVAL:         pcName = "EINVAL"; break;
		case pdFREERTOS_ERRNO_EWOULDBLOCK:    pcName = "EWOULDBLOCK"; break; /* same as EAGAIN */
		case pdFREERTOS_ERRNO_EISCONN:        pcName = "EISCONN"; break;
		default:
			/* Using function "snprintf". */
			( void ) snprintf( pcBuffer, uxLength, "Errno %d", ( int32_t ) xErrnum );
			pcName = NULL;
			break;
	}
	if( pcName != NULL )
	{
		/* Using function "snprintf". */
		( void ) snprintf( pcBuffer, uxLength, "%s", pcName );
	}
	if( uxLength > 0U )
	{
		pcBuffer[ uxLength - 1U ] = '\0';
	}

	return pcBuffer;
}
/*-----------------------------------------------------------*/

/* Provide access to private members for verification. */
#ifdef FREERTOS_TCP_ENABLE_VERIFICATION
	#include "aws_freertos_ip_verification_access_ip_define.h"
#endif

