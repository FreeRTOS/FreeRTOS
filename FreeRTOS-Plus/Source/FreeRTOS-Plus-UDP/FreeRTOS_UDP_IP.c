/*
 * FreeRTOS+UDP V1.0.0 (C) 2013 Real Time Engineers ltd.
 *
 * FreeRTOS+UDP is an add-on component to FreeRTOS.  It is not, in itself, part
 * of the FreeRTOS kernel.  FreeRTOS+UDP is licensed separately from FreeRTOS,
 * and uses a different license to FreeRTOS.  FreeRTOS+UDP uses a dual license
 * model, information on which is provided below:
 *
 * - Open source licensing -
 * FreeRTOS+UDP is a free download and may be used, modified and distributed
 * without charge provided the user adheres to version two of the GNU General
 * Public license (GPL) and does not remove the copyright notice or this text.
 * The GPL V2 text is available on the gnu.org web site, and on the following
 * URL: http://www.FreeRTOS.org/gpl-2.0.txt
 *
 * - Commercial licensing -
 * Businesses and individuals who wish to incorporate FreeRTOS+UDP into
 * proprietary software for redistribution in any form must first obtain a
 * (very) low cost commercial license - and in-so-doing support the maintenance,
 * support and further development of the FreeRTOS+UDP product.  Commercial
 * licenses can be obtained from http://shop.freertos.org and do not require any
 * source files to be changed.
 *
 * FreeRTOS+UDP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+UDP unless you agree that you use the software 'as is'.
 * FreeRTOS+UDP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/udp
 *
 */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"
#include "timers.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

/* Sanity check the configuration. */
#if configUSE_TIMERS != 1
	#error configUSE_TIMERS must be set to 1 in FreeRTOSConfig.h to use this file
#endif

#if configTICK_RATE_HZ > 1000
	#error configTICK_RATE_HZ must be less than 1000 to use FreeRTOS+UDP
#endif

#if ( ipconfigEVENT_QUEUE_LENGTH < ( ipconfigNUM_NETWORK_BUFFERS + 5 ) )
	#error The ipconfigEVENT_QUEUE_LENGTH parameter must be at least ipconfigNUM_NETWORK_BUFFERS + 5
#endif

#if ipconfigCAN_FRAGMENT_OUTGOING_PACKETS == 1 && ipconfigSUPPORT_OUTGOING_PINGS == 1
	#error ipconfigSUPPORT_OUTGOING_PINGS can only be set to 1 if ipconfigCAN_FRAGMENT_OUTGOING_PACKETS is set to 0 as IP fragmentation is not supported for ICMP (ping) packets
#endif

#if ( ipconfigNETWORK_MTU < 46 )
	#error ipconfigNETWORK_MTU must be at least 46.
#endif
/*-----------------------------------------------------------*/

/* The IP header length in bytes. */
#define ipIP_HEADER_LENGTH		( 20 )

/* IP protocol definitions. */
#define ipPROTOCOL_ICMP			( 1 )
#define ipPROTOCOL_UDP			( 17 )

/* ICMP protocol definitions. */
#define ipICMP_ECHO_REQUEST		( ( uint16_t ) 8 )
#define ipICMP_ECHO_REPLY		( ( uint16_t ) 0 )

/* The expected IP version and header length coded into the IP header itself. */
#define ipIP_VERSION_AND_HEADER_LENGTH_BYTE ( ( uint8_t ) 0x45 )

/* Time delay between repeated attempts to initialise the network hardware. */
#define ipINITIALISATION_RETRY_DELAY	( ( ( portTickType ) 3000 ) / portTICK_RATE_MS )

/* The local MAC address is accessed from within xDefaultPartUDPPacketHeader,
rather than duplicated in its own variable. */
#define ipLOCAL_MAC_ADDRESS ( xDefaultPartUDPPacketHeader )

/* The local IP address is accessed from within xDefaultPartUDPPacketHeader,
rather than duplicated in its own variable. */
#define ipLOCAL_IP_ADDRESS_POINTER ( ( uint32_t * ) &( xDefaultPartUDPPacketHeader[ 20 ] ) )

/* Defines how often the ARP timer callback function is executed.  The time is
shorted in the Windows simulator as simulated time is not real time. */
#ifdef _WINDOWS_
	#define ipARP_TIMER_PERIOD_MS	( 500 ) /* For windows simulator builds. */
#else
	#define ipARP_TIMER_PERIOD_MS	( 10000 )
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

/* When the age of an entry in the ARP table reaches this value (it counts down
to zero, so this is an old entry) an ARP request will be sent to see if the
entry is still valid and can therefore be refreshed. */
#define ipMAX_ARP_AGE_BEFORE_NEW_ARP_REQUEST		( 3 )

/* Number of bits to shift to divide by 8.  Used to remove the need for a
divide. */
#define ipSHIFT_TO_DIVIDE_BY_8 						( 3U )

/* The bit set in the IP header flags to indicate that the IP packet contains
a fragment of the eventual total payload, and that more fragments will follow. */
#define ipMORE_FRAGMENTS_FLAG_BIT 					( 0x2000U )

/* ICMP packets are sent using the same function as UDP packets.  The port
number is used to distinguish between the two, as 0 is an invalid UDP port. */
#define ipPACKET_CONTAINS_ICMP_DATA					( 0 )

/* The character used to fill ICMP echo requests, and therefore also the
character expected to fill ICMP echo replies. */
#define ipECHO_DATA_FILL_BYTE						'x'

#if( ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN )
	#define ipFRAGMENT_OFFSET_BIT_MASK				( ( uint16_t ) 0xff0f ) /* The bits in the two byte IP header field that make up the fragment offset value. */
#else
	#define ipFRAGMENT_OFFSET_BIT_MASK				( ( uint16_t ) 0x0fff ) /* The bits in the two byte IP header field that make up the fragment offset value. */
	#if ipconfigCAN_FRAGMENT_OUTGOING_PACKETS == 1
		#warning Fragment offsets have not been tested on big endian machines.
	#endif /* ipconfigCAN_FRAGMENT_OUTGOING_PACKETS */
#endif /* ipconfigBYTE_ORDER */

/*-----------------------------------------------------------*/
/* Miscellaneous structure and definitions. */
/*-----------------------------------------------------------*/

typedef struct xARP_CACHE_TABLE_ROW
{
	uint32_t ulIPAddress;		/* The IP address of an ARP cache entry. */
	xMACAddress_t xMACAddress;  /* The MAC address of an ARP cache entry. */
	uint8_t ucAge;				/* A value that is periodically decremented but can also be refreshed by active communication.  The ARP cache entry is removed if the value reaches zero. */
} xARPCacheRow_t;

typedef enum
{
	eARPCacheMiss = 0,			/* An ARP table lookup did not find a valid entry. */
	eARPCacheHit,				/* An ARP table lookup found a valid entry. */
	eCantSendPacket				/* There is no IP address, or an ARP is still in progress, so the packet cannot be sent. */
} eARPLookupResult_t;

typedef enum
{
	eNotFragment = 0,			/* The IP packet being sent is not part of a fragment. */
	eFirstFragment,				/* The IP packet being sent is the first in a set of fragmented packets. */
	eFollowingFragment			/* The IP packet being sent is part of a set of fragmented packets. */
} eIPFragmentStatus_t;


/*-----------------------------------------------------------*/

/*
 * Called when new data is available from the network interface.
 */
static void prvProcessEthernetPacket( xNetworkBufferDescriptor_t * const pxNetworkBuffer );

/*
 * Called when the application has generated a UDP packet to send.
 */
static void prvProcessGeneratedPacket( xNetworkBufferDescriptor_t * const pxNetworkBuffer );

/*
 * Processes incoming ARP packets.
 */
static eFrameProcessingResult_t prvProcessARPPacket( xARPPacket_t * const pxARPFrame );

/*
 * Process incoming IP packets.
 */
static eFrameProcessingResult_t prvProcessIPPacket( const xIPPacket_t * const pxIPPacket, xNetworkBufferDescriptor_t * const pxNetworkBuffer );

/*
 * Process incoming ICMP packets.
 */
#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
	static eFrameProcessingResult_t prvProcessICMPPacket( xICMPPacket_t * const pxICMPPacket );
#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */

/*
 * Swap the source and destination addresses in an already constructed Ethernet
 * frame, and send the frame to the network.
 */
static void prvReturnEthernetFrame( xNetworkBufferDescriptor_t * const pxNetworkBuffer );

/*
 * Return the checksum generated over usDataLengthBytes from pucNextData.
 */
static uint16_t prvGenerateChecksum( const uint8_t * const pucNextData, const uint16_t usDataLengthBytes );

/*
 * The callback function that is assigned to all periodic processing timers -
 * namely the DHCP timer and the ARP timer.
 */
void vIPFunctionsTimerCallback( xTimerHandle xTimer );

/*
 * Reduce the age count in each entry within the ARP cache.  An entry is no
 * longer considered valid and is deleted if its age reaches zero.
 */
static void prvAgeARPCache( void );

/*
 * If ulIPAddress is already in the ARP cache table then reset the age of the
 * entry back to its maximum value.  If ulIPAddress is not already in the ARP
 * cache table then add it - replacing the oldest current entry if there is not
 * a free space available.
 */
static void prvRefreshARPCacheEntry( const xMACAddress_t * const pxMACAddress, const uint32_t ulIPAddress );

/*
 * Creates the pseudo header necessary then generate the checksum over the UDP
 * packet.  Returns the calculated checksum.
 */
static uint16_t prvGenerateUDPChecksum( const xUDPPacket_t * const pxUDPPacket );

/*
 * Look for ulIPAddress in the ARP cache.  If the IP address exists, copy the
 * associated MAC address into pxMACAddress, refresh the ARP cache entry's
 * age, and return eARPCacheHit.  If the IP address does not exist in the ARP
 * cache return eARPCacheMiss.  If the packet cannot be sent for any reason
 * (maybe DHCP is still in process, or the addressing needs a gateway but there
 * isn't a gateway defined) then return eCantSendPacket.
 */
static eARPLookupResult_t prvGetARPCacheEntry( uint32_t *pulIPAddress, xMACAddress_t * const pxMACAddress );

/*
 * The main UDP/IP stack processing task.  This task receives commands/events
 * from the network hardware drivers, tasks that are using sockets, and software
 * timers (such as the ARP timer).
 */
static void prvIPTask( void *pvParameters );

/*
 * Send out an ARP request for the IP address contained in pxNetworkBuffer, and
 * add an entry into the ARP table that indicates that an ARP reply is
 * outstanding so re-transmissions can be generated.
 */
static void prvGenerateARPRequestPacket( xNetworkBufferDescriptor_t * const pxNetworkBuffer );

/*
 * Called when outgoing packets are fragmented and require a fragment offset in
 * their IP headers.  Set the fragment offset (which includes the IP flags) and
 * length from the data passed in the pxFragmentParameters structure.
 */
 #if ipconfigCAN_FRAGMENT_OUTGOING_PACKETS == 1
	static void prvCalculateFragmentOffsetAndLength( xIPFragmentParameters_t *pxFragmentParameters, uint16_t *pusFragmentOffset, uint16_t *pusFragmentLength );
#endif /* ipconfigCAN_FRAGMENT_OUTGOING_PACKETS */

/*
 * Complete the pxUDPPacket header with the information passed in
 * pxNetworkBuffer.  ucSocketOptions are passed in case the options include
 * disabling the checksum.
 */
static void prvCompleteUDPHeader( xNetworkBufferDescriptor_t *pxNetworkBuffer, xUDPPacket_t *pxUDPPacket, uint8_t ucSocketOptions );

/*
 * Send the event eEvent to the IP task event queue, using a block time of
 * zero.  Return pdPASS if the message was sent successfully, otherwise return
 * pdFALSE.
*/
static portBASE_TYPE prvSendEventToIPTask( eIPEvent_t eEvent );

/*
 * Generate and send an ARP request for the IP address passed in ulIPAddress.
 */
static void prvOutputARPRequest( uint32_t ulIPAddress );

/*
 * Turns around an incoming ping request to convert it into a ping reply.
 */
#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )
	static eFrameProcessingResult_t prvProcessICMPEchoRequest( xICMPPacket_t * const pxICMPPacket );
#endif /* ipconfigREPLY_TO_INCOMING_PINGS */

/*
 * Processes incoming ping replies.  The application callback function
 * vApplicationPingReplyHook() is called with the results.
 */
#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
	static void prvProcessICMPEchoReply( xICMPPacket_t * const pxICMPPacket );
#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

/*
 * Called to create a network connection when the stack is first started, or
 * when the network connection is lost.
 */
static void prvProcessNetworkDownEvent( void );

#if( ipconfigFREERTOS_PLUS_NABTO == 1 )
	static void prvStartNabtoTask( void );
	extern void FreeRTOS_NabtoInit();
#endif /* ipconfigFRERTOS_PLUS_NABTO */
/*-----------------------------------------------------------*/

/* The queue used to pass events into the UDP task for processing. */
xQueueHandle xNetworkEventQueue = NULL;

/* The ARP cache. */
static xARPCacheRow_t xARPCache[ ipconfigARP_CACHE_ENTRIES ];

/* The timer that triggers ARP events. */
static xTimerHandle xARPTimer = NULL;

/* Used to ensure network down events cannot be missed when they cannot be
posted to the network event queue because the network event queue is already
full. */
static portBASE_TYPE xNetworkDownEventPending = pdFALSE;

/* For convenience, a MAC address of all zeros and another of all 0xffs are
defined const for quick reference. */
static const xMACAddress_t xNullMACAddress = { { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } };
static const xMACAddress_t xBroadcastMACAddress = { { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff } };

/* Part of the Ethernet and IP headers are always constant when sending an IPv4
UDP packet.  This array defines the constant parts, allowing this part of the
packet to be filled in using a simple memcpy() instead of individual writes. */
uint8_t xDefaultPartUDPPacketHeader[] =
{
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 	/* Ethernet source MAC address. */
	0x08, 0x00, 							/* Ethernet frame type. */
	ipIP_VERSION_AND_HEADER_LENGTH_BYTE, 	/* ucVersionHeaderLength. */
	0x00, 									/* ucDifferentiatedServicesCode. */
	0x00, 0x00, 							/* usLength. */
	0x00, 0x00, 							/* usIdentification. */
	0x00, 0x00, 							/* usFragmentOffset. */
	updconfigIP_TIME_TO_LIVE, 				/* ucTimeToLive */
	ipPROTOCOL_UDP, 						/* ucProtocol. */
	0x00, 0x00, 							/* usHeaderChecksum. */
	0x00, 0x00, 0x00, 0x00 					/* Source IP address. */
};

/* Part of the Ethernet and ARP headers are always constant when sending an IPv4
ARP packet.  This array defines the constant parts, allowing this part of the
packet to be filled in using a simple memcpy() instead of individual writes. */
static const uint8_t xDefaultPartARPPacketHeader[] =
{
	0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 	/* Ethernet destination address. */
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 	/* Ethernet source address. */
	0x08, 0x06, 							/* Ethernet frame type (ipARP_TYPE). */
	0x00, 0x01, 							/* usHardwareType (ipARP_HARDWARE_TYPE_ETHERNET). */
	0x08, 0x00,								/* usProtocolType. */
	ipMAC_ADDRESS_LENGTH_BYTES, 			/* ucHardwareAddressLength. */
	ipIP_ADDRESS_LENGTH_BYTES, 				/* ucProtocolAddressLength. */
	0x00, 0x01, 							/* usOperation (ipARP_REQUEST). */
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 	/* xSenderHardwareAddress. */
	0x00, 0x00, 0x00, 0x00, 				/* ulSenderProtocolAddress. */
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00 	/* xTargetHardwareAddress. */
};

/* Structure that stores the netmask, gateway address and DNS server addresses. */
static xNetworkAddressingParameters_t xNetworkAddressing = { 0, 0, 0, 0 };

/*-----------------------------------------------------------*/

static void prvIPTask( void *pvParameters )
{
xIPStackEvent_t xReceivedEvent;

	/* Just to prevent compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* Create the ARP timer, but don't start it until the network has
	connected. */
	xARPTimer = xTimerCreate( 	( const signed char * const ) "ARPTimer", ( ipARP_TIMER_PERIOD_MS / portTICK_RATE_MS ), pdTRUE, ( void * ) eARPTimerEvent, vIPFunctionsTimerCallback );
	configASSERT( xARPTimer );

	/* Generate a dummy message to say that the network connection has gone
	down.  This will cause this task to initialise the network interface.  After
	this it is the responsibility of the network interface hardware driver to
	send this message if a previously connected network is disconnected. */
	FreeRTOS_NetworkDown();

	/* Loop, processing IP events. */
	for( ;; )
	{
		/* Wait until there is something to do. */
		if( xQueueReceive( xNetworkEventQueue, ( void * ) &xReceivedEvent, portMAX_DELAY ) == pdPASS )
		{
			iptraceNETWORK_EVENT_RECEIVED( xReceivedEvent.eEventType );

			switch( xReceivedEvent.eEventType )
			{
				case eNetworkDownEvent :
					/* Attempt to establish a connection. */
					prvProcessNetworkDownEvent();
					break;

				case eEthernetRxEvent :
					/* The network hardware driver has received a new packet.
					A pointer to the received buffer is located in the pvData
					member of the received event structure. */
					prvProcessEthernetPacket( ( xNetworkBufferDescriptor_t * ) ( xReceivedEvent.pvData ) );
					break;

				case eARPTimerEvent :
					/* The ARP timer has expired, process the ARP cache. */
					prvAgeARPCache();
					break;

				case eStackTxEvent :
					/* The network stack has generated a packet to send.  A
					pointer to the generated buffer is located in the pvData
					member of the received event structure. */
					prvProcessGeneratedPacket( ( xNetworkBufferDescriptor_t * ) ( xReceivedEvent.pvData ) );
					break;

				case eDHCPEvent:
					/* The DHCP state machine needs processing. */
					#if ipconfigUSE_DHCP == 1
					{
						vDHCPProcess( pdFALSE, ( xMACAddress_t * ) ipLOCAL_MAC_ADDRESS, ipLOCAL_IP_ADDRESS_POINTER, &xNetworkAddressing );
					}
					#endif
					break;

				default :
					/* Should not get here. */
					break;
			}

			if( xNetworkDownEventPending != pdFALSE )
			{
				/* A network down event could not be posted to the network
				event queue because the queue was full.  Try posting again. */
				FreeRTOS_NetworkDown();
			}
		}
	}
}
/*-----------------------------------------------------------*/

void FreeRTOS_NetworkDown( void )
{
static const xIPStackEvent_t xNetworkDownEvent = { eNetworkDownEvent, NULL };
const portTickType xDontBlock = 0;

	/* Simply send the network task the appropriate event. */
	if( xQueueSendToBack( xNetworkEventQueue, &xNetworkDownEvent, xDontBlock ) != pdPASS )
	{
		xNetworkDownEventPending = pdTRUE;
	}
	else
	{
		xNetworkDownEventPending = pdFALSE;
	}

	iptraceNETWORK_DOWN();
}
/*-----------------------------------------------------------*/

portBASE_TYPE FreeRTOS_NetworkDownFromISR( void )
{
static const xIPStackEvent_t xNetworkDownEvent = { eNetworkDownEvent, NULL };
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Simply send the network task the appropriate event. */
	if( xQueueSendToBackFromISR( xNetworkEventQueue, &xNetworkDownEvent, &xHigherPriorityTaskWoken ) != pdPASS )
	{
		xNetworkDownEventPending = pdTRUE;
	}
	else
	{
		xNetworkDownEventPending = pdFALSE;
	}
	iptraceNETWORK_DOWN();

	return xHigherPriorityTaskWoken;
}
/*-----------------------------------------------------------*/

void *FreeRTOS_GetUDPPayloadBuffer( size_t xRequestedSizeBytes, portTickType xBlockTimeTicks )
{
xNetworkBufferDescriptor_t *pxNetworkBuffer;
void *pvReturn;

	/* Cap the block time.  The reason for this is explained where
	ipconfigMAX_SEND_BLOCK_TIME_TICKS is defined (assuming an official
	FreeRTOSIPConfig.h header file is being used). */
	if( xBlockTimeTicks > ipconfigMAX_SEND_BLOCK_TIME_TICKS )
	{
		xBlockTimeTicks = ipconfigMAX_SEND_BLOCK_TIME_TICKS;
	}

	/* Obtain a network buffer with the required amount of storage. */
	pxNetworkBuffer = pxNetworkBufferGet( sizeof( xUDPPacket_t ) + xRequestedSizeBytes, xBlockTimeTicks );

	if( pxNetworkBuffer != NULL )
	{
		/* Leave space for the UPD header. */
		pvReturn = ( void * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET ] );
	}
	else
	{
		pvReturn = NULL;
	}

	return ( void * ) pvReturn;
}
/*-----------------------------------------------------------*/

void FreeRTOS_ReleaseUDPPayloadBuffer( void *pvBuffer )
{
uint8_t *pucBuffer;

	/* Obtain the network buffer from the zero copy pointer. */
	pucBuffer = ( uint8_t * ) pvBuffer;
	pucBuffer -= ( ipBUFFER_PADDING + sizeof( xUDPPacket_t ) );

	vNetworkBufferRelease( * ( ( xNetworkBufferDescriptor_t ** ) pucBuffer ) );
}
/*-----------------------------------------------------------*/

uint8_t * FreeRTOS_GetMACAddress( void )
{
	return ipLOCAL_MAC_ADDRESS;
}
/*-----------------------------------------------------------*/

portBASE_TYPE FreeRTOS_IPInit( const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ], const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ], const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ], const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ], const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] )
{
static portBASE_TYPE xReturn = pdFALSE;

	/* Only create the IP event queue if it has not already been created, in
	case this function is called more than once. */
	if( xNetworkEventQueue == NULL )
	{
		xNetworkEventQueue = xQueueCreate( ipconfigEVENT_QUEUE_LENGTH, sizeof( xIPStackEvent_t ) );
		configASSERT( xNetworkEventQueue );
		vQueueAddToRegistry( xNetworkEventQueue, ( signed char * ) "NetEvnt" );
	}

	if( xNetworkBuffersInitialise() == pdPASS )
	{
		if( xNetworkEventQueue != NULL )
		{
			/* xReturn is static to ensure the network interface is not
			initialised	twice. */
			if( xReturn == pdFALSE )
			{
				/* Store the local IP and MAC address. */
				xNetworkAddressing.ulDefaultIPAddress = FreeRTOS_inet_addr_quick( ucIPAddress[ 0 ], ucIPAddress[ 1 ], ucIPAddress[ 2 ], ucIPAddress[ 3 ] );
				xNetworkAddressing.ulNetMask = FreeRTOS_inet_addr_quick( ucNetMask[ 0 ], ucNetMask[ 1 ], ucNetMask[ 2 ], ucNetMask[ 3 ] );
				xNetworkAddressing.ulGatewayAddress = FreeRTOS_inet_addr_quick( ucGatewayAddress[ 0 ], ucGatewayAddress[ 1 ], ucGatewayAddress[ 2 ], ucGatewayAddress[ 3 ] );
				xNetworkAddressing.ulDNSServerAddress = FreeRTOS_inet_addr_quick( ucDNSServerAddress[ 0 ], ucDNSServerAddress[ 1 ], ucDNSServerAddress[ 2 ], ucDNSServerAddress[ 3 ] );

				#if ipconfigUSE_DHCP == 1
				{
					/* The IP address is not set until DHCP completes. */
					*ipLOCAL_IP_ADDRESS_POINTER = 0x00UL;
				}
				#else
				{
					*ipLOCAL_IP_ADDRESS_POINTER = xNetworkAddressing.ulDefaultIPAddress;
				}
				#endif /* ipconfigUSE_DHCP == 1 */

				/* The MAC address is stored in the start of the default packet
				header fragment, which is used when sending UDP packets. */
				memcpy( ( void * ) ipLOCAL_MAC_ADDRESS, ( void * ) ucMACAddress, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

				/* Prepare the sockets interface. */
				FreeRTOS_SocketsInit();

				/* Create the task that processes Ethernet and stack events. */
				xReturn = xTaskCreate( prvIPTask, ( const signed char * const ) "UDP/IP", ipconfigUDP_TASK_STACK_SIZE_WORDS, NULL, ipconfigUDP_TASK_PRIORITY, NULL );
			}
		}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void FreeRTOS_GetAddressConfiguration( uint32_t *pulIPAddress, uint32_t *pulNetMask, uint32_t *pulGatewayAddress, uint32_t *pulDNSServerAddress )
{
	if( pulIPAddress != NULL )
	{
		*pulIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;
	}

	if( pulNetMask != NULL )
	{
		*pulNetMask = xNetworkAddressing.ulNetMask;
	}

	if( pulGatewayAddress != NULL )
	{
		*pulGatewayAddress = xNetworkAddressing.ulGatewayAddress;
	}

	if( pulDNSServerAddress != NULL )
	{
		*pulDNSServerAddress = xNetworkAddressing.ulDNSServerAddress;
	}
}
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

	portBASE_TYPE FreeRTOS_SendPingRequest( uint32_t ulIPAddress, size_t xNumberOfBytesToSend, portTickType xBlockTimeTicks )
	{
	xNetworkBufferDescriptor_t *pxNetworkBuffer;
	xICMPHeader_t *pxICMPHeader;
	portBASE_TYPE xReturn = pdFAIL;
	static uint16_t usSequenceNumber = 0;
	uint8_t *pucChar;
	xIPStackEvent_t xStackTxEvent = { eStackTxEvent, NULL };

		if( xNumberOfBytesToSend < ( ( ipconfigNETWORK_MTU - sizeof( xIPHeader_t ) ) - sizeof( xICMPHeader_t ) ) )
		{
			pxNetworkBuffer = pxNetworkBufferGet( xNumberOfBytesToSend + sizeof( xICMPPacket_t ), xBlockTimeTicks );

			if( pxNetworkBuffer != NULL )
			{
				pxICMPHeader = ( xICMPHeader_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipIP_PAYLOAD_OFFSET ] );
				usSequenceNumber++;

				/* Fill in the basic header information. */
				pxICMPHeader->ucTypeOfMessage = ipICMP_ECHO_REQUEST;
				pxICMPHeader->ucTypeOfService = 0;
				pxICMPHeader->usIdentifier = usSequenceNumber;
				pxICMPHeader->usSequenceNumber = usSequenceNumber;
				pxICMPHeader->usChecksum = 0;

				/* Find the start of the data. */
				pucChar = ( uint8_t * ) pxICMPHeader;
				pucChar += sizeof( xICMPHeader_t );

				/* Just memset the data to a fixed value. */
				memset( ( void * ) pucChar, ( int ) ipECHO_DATA_FILL_BYTE, xNumberOfBytesToSend );

				/* The message is complete, calculate the checksum. */
				pxICMPHeader->usChecksum = prvGenerateChecksum( ( uint8_t * ) pxICMPHeader, ( uint16_t ) ( xNumberOfBytesToSend + sizeof( xICMPHeader_t ) ) );

				/* Complete the network buffer information. */
				pxNetworkBuffer->ulIPAddress = ulIPAddress;
				pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;
				pxNetworkBuffer->xDataLength = xNumberOfBytesToSend + sizeof( xICMPHeader_t );

				/* Send to the stack. */
				xStackTxEvent.pvData = pxNetworkBuffer;
				if( xQueueSendToBack( xNetworkEventQueue, &xStackTxEvent, xBlockTimeTicks ) != pdPASS )
				{
					vNetworkBufferRelease( pxNetworkBuffer );
					iptraceSTACK_TX_EVENT_LOST( ipSTACK_TX_EVENT );
				}
				else
				{
					xReturn = usSequenceNumber;
				}
			}
		}
		else
		{
			/* The requested number of bytes will not fit in the available space
			in the network buffer.  Outgoing fragmentation is only supported for
			UDP packets. */
		}

		return xReturn;
	}

#endif /* ipconfigSUPPORT_OUTGOING_PINGS == 1 */

/*-----------------------------------------------------------*/

static portBASE_TYPE prvSendEventToIPTask( eIPEvent_t eEvent )
{
xIPStackEvent_t xEventMessage;
const portTickType xDontBlock = 0;
portBASE_TYPE xReturn;

	xEventMessage.eEventType = eEvent;
	xReturn = xQueueSendToBack( xNetworkEventQueue, &xEventMessage, xDontBlock );

	if( xReturn != pdPASS )
	{
		iptraceSTACK_TX_EVENT_LOST( ipARP_TIMER_EVENT );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void vIPFunctionsTimerCallback( xTimerHandle xTimer )
{
eIPEvent_t eMessage;

	/* This time can be used to send more than one type of message to the IP
	task.  The message ID is stored in the ID of the timer.  The strange
	casting is to avoid compiler warnings. */
	eMessage = ( eIPEvent_t ) ( ( int ) pvTimerGetTimerID( xTimer ) );

	prvSendEventToIPTask( eMessage );
}
/*-----------------------------------------------------------*/

static void prvOutputARPRequest( uint32_t ulIPAddress )
{
xNetworkBufferDescriptor_t *pxNetworkBuffer;

	/* This is called from the context of the IP event task, so a block time
	must not be used. */
	pxNetworkBuffer = pxNetworkBufferGet( sizeof( xARPPacket_t ), 0 );
	if( pxNetworkBuffer != NULL )
	{
		pxNetworkBuffer->ulIPAddress = ulIPAddress;
		prvGenerateARPRequestPacket( pxNetworkBuffer );
		xNetworkInterfaceOutput( pxNetworkBuffer );
	}
}
/*-----------------------------------------------------------*/

static void prvAgeARPCache( void )
{
portBASE_TYPE x;

	/* Loop through each entry in the ARP cache. */
	for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
	{
		/* If the entry is valid (its age is greater than zero). */
		if( xARPCache[ x ].ucAge > 0U )
		{
			/* Decrement the age value of the entry in this ARP cache table row.
			When the age reaches zero it is no longer considered valid. */
			( xARPCache[ x ].ucAge )--;

			/* If the entry has a MAC address of 0, then it is waiting an ARP
			reply, and the ARP request should be retransmitted. */
			if( memcmp( ( void * ) &xNullMACAddress, ( void * ) &( xARPCache[ x ].xMACAddress ), sizeof( xMACAddress_t ) ) == 0 )
			{
				prvOutputARPRequest( xARPCache[ x ].ulIPAddress );
			}
			else if( xARPCache[ x ].ucAge <= ipMAX_ARP_AGE_BEFORE_NEW_ARP_REQUEST )
			{
				/* This entry will get removed soon.  See if the MAC address is
				still valid to prevent this happening. */
				iptraceARP_TABLE_ENTRY_WILL_EXPIRE( xARPCache[ x ].ulIPAddress );
				prvOutputARPRequest( xARPCache[ x ].ulIPAddress );
			}
			else
			{
				/* The age has just ticked down, with nothing to do. */
			}

			if( xARPCache[ x ].ucAge == 0 )
			{
				/* The entry is no longer valid.  Wipe it out. */
				iptraceARP_TABLE_ENTRY_EXPIRED( xARPCache[ x ].ulIPAddress );
				xARPCache[ x ].ulIPAddress = 0UL;
			}
		}
	}
}
/*-----------------------------------------------------------*/

static eARPLookupResult_t prvGetARPCacheEntry( uint32_t *pulIPAddress, xMACAddress_t * const pxMACAddress )
{
portBASE_TYPE x;
eARPLookupResult_t eReturn;
uint32_t ulAddressToLookup;

	if( *pulIPAddress == ipBROADCAST_IP_ADDRESS )
	{
		/* This is a broadcast so uses the broadcast MAC address. */
		memcpy( ( void * ) pxMACAddress, &xBroadcastMACAddress, sizeof( xMACAddress_t ) );
		eReturn = eARPCacheHit;
	}
	else if( *ipLOCAL_IP_ADDRESS_POINTER == 0UL )
	{
		/* The IP address has not yet been assigned, so there is nothing that
		can be done. */
		eReturn = eCantSendPacket;
	}
	else
	{
		if( ( *pulIPAddress & xNetworkAddressing.ulNetMask ) != ( ( *ipLOCAL_IP_ADDRESS_POINTER ) & xNetworkAddressing.ulNetMask ) )
		{
			/* The IP address is off the local network, so look up the hardware
			address of the router, if any. */
			ulAddressToLookup = xNetworkAddressing.ulGatewayAddress;
		}
		else
		{
			/* The IP address is on the local network, so lookup the requested
			IP address directly. */
			ulAddressToLookup = *pulIPAddress;
		}

		if( ulAddressToLookup == 0UL )
		{
			/* The address is not on the local network, and there is not a
			router. */
			eReturn = eCantSendPacket;
		}
		else
		{
			eReturn = eARPCacheMiss;

			/* Loop through each entry in the ARP cache. */
			for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
			{
				/* Does this row in the ARP cache table hold an entry for the IP
				address being queried? */
				if( xARPCache[ x ].ulIPAddress == ulAddressToLookup )
				{
					/* The IP address matched.  Is there a valid MAC address? */
					if( memcmp( ( void * ) &xNullMACAddress, ( void * ) &( xARPCache[ x ].xMACAddress ), sizeof( xMACAddress_t ) ) == 0 )
					{
						/* This entry is waiting an ARP reply, so is not valid. */
						eReturn = eCantSendPacket;
					}
					else
					{
						/* A valid entry was found. */
						memcpy( pxMACAddress, &( xARPCache[ x ].xMACAddress ), sizeof( xMACAddress_t ) );
						eReturn = eARPCacheHit;
					}
				}

				if( eReturn != eARPCacheMiss )
				{
					break;
				}
			}

			if( eReturn == eARPCacheMiss )
			{
				/* It might be that the ARP has to go to the gateway. */
				*pulIPAddress = ulAddressToLookup;
			}
		}
	}

	return eReturn;
}
/*-----------------------------------------------------------*/

static void prvRefreshARPCacheEntry( const xMACAddress_t * const pxMACAddress, const uint32_t ulIPAddress )
{
portBASE_TYPE x, xEntryFound = pdFALSE, xOldestEntry = 0;
uint8_t ucMinAgeFound = 0U;

	/* Only process the IP address if it is on the local network. */
	if( ( ulIPAddress & xNetworkAddressing.ulNetMask ) == ( ( *ipLOCAL_IP_ADDRESS_POINTER ) & xNetworkAddressing.ulNetMask ) )
	{
		/* Start with the maximum possible number. */
		ucMinAgeFound--;

		/* For each entry in the ARP cache table. */
		for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
		{
			/* Does this line in the cache table hold an entry for the IP
			address	being queried? */
			if( xARPCache[ x ].ulIPAddress == ulIPAddress )
			{
				/* If the MAC address is all zeros then the refresh is due to
				an ARP reply, so in effect this is a new entry in the ARP
				cache. */
				if( memcmp( &( xARPCache[ x ].xMACAddress ), &xNullMACAddress, sizeof( xMACAddress_t ) ) == 0 )
				{
					iptraceARP_TABLE_ENTRY_CREATED( xARPCache[ x ].ulIPAddress, *pxMACAddress );
				}

				/* Refresh the cache entry so the entry's age is back to its
				maximum	value. */
				xARPCache[ x ].ucAge = ipconfigMAX_ARP_AGE;
				memcpy( &( xARPCache[ x ].xMACAddress ), pxMACAddress, sizeof( xMACAddress_t ) );
				xEntryFound = pdTRUE;
				break;
			}
			else
			{
				/* As the table is traversed, remember the table row that
				contains the oldest entry (the lowest age count, as ages are
				decremented to zero) so the row can be re-used if this function
				needs to add an entry that does not already exist. */
				if( xARPCache[ x ].ucAge < ucMinAgeFound )
				{
					ucMinAgeFound = xARPCache[ x ].ucAge;
					xOldestEntry = x;
				}
			}
		}

		if( xEntryFound == pdFALSE )
		{
			/* The wanted entry does not already exist.  Add the entry into the
			cache, replacing the oldest entry (which might be an empty entry). */
			xARPCache[ xOldestEntry ].ulIPAddress = ulIPAddress;
			memcpy( &( xARPCache[ xOldestEntry ].xMACAddress ), pxMACAddress, sizeof( xMACAddress_t ) );

			/* If the MAC address is all zeros, then this entry is not yet
			complete but still waiting the reply from an ARP request.  When this
			is the case	the age is set to a much lower value as an ARP
			retransmission will be generated each time the ARP timer is called
			while the reply is still outstanding. */
			if( pxMACAddress == &xNullMACAddress )
			{
				xARPCache[ xOldestEntry ].ucAge = ipconfigMAX_ARP_RETRANSMISSIONS;
			}
			else
			{
				iptraceARP_TABLE_ENTRY_CREATED( xARPCache[ xOldestEntry ].ulIPAddress, xARPCache[ xOldestEntry ].xMACAddress );
				xARPCache[ xOldestEntry ].ucAge = ipconfigMAX_ARP_AGE;
			}
		}
	}
}
/*-----------------------------------------------------------*/

#if ipconfigCAN_FRAGMENT_OUTGOING_PACKETS == 1

	static void prvCalculateFragmentOffsetAndLength( xIPFragmentParameters_t *pxFragmentParameters, uint16_t *pusFragmentOffset, uint16_t *pusFragmentLength )
	{
		*pusFragmentOffset = pxFragmentParameters->usFragmentedPacketOffset;

		if( *pusFragmentOffset != 0 )
		{
			/* Take into account that the payload has had a UDP header added in the
			first fragment of the set. */
			*pusFragmentOffset += sizeof( xUDPHeader_t );
		}

		/* The offset is defined in multiples of 8 bytes. */
		*pusFragmentOffset >>= ipSHIFT_TO_DIVIDE_BY_8;
		*pusFragmentLength = pxFragmentParameters->usFragmentLength;

		if( ( pxFragmentParameters->ucSocketOptions & FREERTOS_NOT_LAST_IN_FRAGMENTED_PACKET ) != 0 )
		{
			/* Set the more fragments flag. */
			*pusFragmentOffset |= ipMORE_FRAGMENTS_FLAG_BIT;
		}
	}

#endif
/*-----------------------------------------------------------*/

static void prvCompleteUDPHeader( xNetworkBufferDescriptor_t *pxNetworkBuffer, xUDPPacket_t *pxUDPPacket, uint8_t ucSocketOptions )
{
xUDPHeader_t *pxUDPHeader;

	pxUDPHeader = &( pxUDPPacket->xUDPHeader );

	pxUDPHeader->usDestinationPort = pxNetworkBuffer->usPort;
	pxUDPHeader->usSourcePort = pxNetworkBuffer->usBoundPort;
	pxUDPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength + sizeof( xUDPHeader_t ) );
	pxUDPHeader->usLength = FreeRTOS_htons( pxUDPPacket->xUDPHeader.usLength );
	pxUDPHeader->usChecksum = 0;

	if( ( ucSocketOptions & FREERTOS_SO_UDPCKSUM_OUT ) != 0U )
	{
		pxUDPHeader->usChecksum = prvGenerateUDPChecksum( pxUDPPacket );
		if( pxUDPHeader->usChecksum == 0x00 )
		{
			/* A calculated checksum of 0 must be inverted as 0 means the
			checksum is disabled. */
			pxUDPHeader->usChecksum = 0xffffU;
		}
	}
}
/*-----------------------------------------------------------*/

#if ipconfigCAN_FRAGMENT_OUTGOING_PACKETS == 1

	static void prvProcessGeneratedPacket( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
	{
	xUDPPacket_t *pxUDPPacket;
	xUDPHeader_t *pxUDPHeader;
	xIPHeader_t *pxIPHeader;
	eARPLookupResult_t eReturned;
	eIPFragmentStatus_t eFragmentStatus;
	uint16_t usFragmentOffset = 0, usFragmentLength;
	xIPFragmentParameters_t *pxFragmentParameters;
	static uint16_t usPacketIdentifier = 0U;

		/* Map the UDP packet onto the start of the frame. */
		pxUDPPacket = ( xUDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

		/* Determine the ARP cache status for the requested IP address. */
		eReturned = prvGetARPCacheEntry( &( pxNetworkBuffer->ulIPAddress ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ) );

		if( eReturned != eCantSendPacket )
		{
			if( eReturned == eARPCacheHit )
			{
				iptraceSENDING_UDP_PACKET( pxNetworkBuffer->ulIPAddress );

				/* Create short cuts to the data within the packet. */
				pxUDPHeader = &( pxUDPPacket->xUDPHeader );
				pxIPHeader = &( pxUDPPacket->xIPHeader );
				pxFragmentParameters = ( xIPFragmentParameters_t * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipFRAGMENTATION_PARAMETERS_OFFSET ] );

				/* IP header source and destination addresses must be set
				before the UDP checksum is calculated. */
				pxIPHeader->ulDestinationIPAddress = pxNetworkBuffer->ulIPAddress;
				pxIPHeader->ulSourceIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

				/* If the packet is not fragmented, or if the packet is the
				first in a fragmented packet, then a UDP header is required. */
				if( ( pxFragmentParameters->ucSocketOptions & FREERTOS_FRAGMENTED_PACKET ) == 0 )
				{
					eFragmentStatus = eNotFragment;

					#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
					{
						/* Is it possible that the packet is not actually a UDP
						packet after all, but an ICMP packet. */
						if( pxNetworkBuffer->usPort != ipPACKET_CONTAINS_ICMP_DATA )
						{
							prvCompleteUDPHeader( pxNetworkBuffer, pxUDPPacket, pxFragmentParameters->ucSocketOptions );
						}
					}
					#else /* ipconfigSUPPORT_OUTGOING_PINGS */
					{
						prvCompleteUDPHeader( pxNetworkBuffer, pxUDPPacket, pxFragmentParameters->ucSocketOptions );
					}
					#endif /* ipconfigSUPPORT_OUTGOING_PINGS */


					usFragmentLength = 0U;

					/* The identifier is incremented as this is a new and
					unfragmented IP packet. */
					usPacketIdentifier++;
				}
				else if( pxFragmentParameters->usFragmentedPacketOffset == 0 )
				{
					eFragmentStatus = eFirstFragment;
					prvCalculateFragmentOffsetAndLength( pxFragmentParameters, &usFragmentOffset, &usFragmentLength );
					/* Note FREERTOS_SO_UDPCKSUM_OUT is used because checksums
					cannot currently be used on fragmented packets. */
					pxFragmentParameters->ucSocketOptions &= ~FREERTOS_SO_UDPCKSUM_OUT;
					prvCompleteUDPHeader( pxNetworkBuffer, pxUDPPacket, pxFragmentParameters->ucSocketOptions );

					/* The identifier is incremented because, although this is a
					fragmented packet, it is the first in the fragmentation
					set. */
					usPacketIdentifier++;
				}
				else
				{
					eFragmentStatus = eFollowingFragment;
					prvCalculateFragmentOffsetAndLength( pxFragmentParameters, &usFragmentOffset, &usFragmentLength );
				}

				/* memcpy() the constant parts of the header information into the
				correct location within the packet.  This fills in:
					xEthernetHeader.xSourceAddress
					xEthernetHeader.usFrameType
					xIPHeader.ucVersionHeaderLength
					xIPHeader.ucDifferentiatedServicesCode
					xIPHeader.usLength
					xIPHeader.usIdentification
					xIPHeader.usFragmentOffset
					xIPHeader.ucTimeToLive
					xIPHeader.ucProtocol
				and
					xIPHeader.usHeaderChecksum
				*/
				memcpy( ( void *) &( pxUDPPacket->xEthernetHeader.xSourceAddress ), ( void * ) xDefaultPartUDPPacketHeader, sizeof( xDefaultPartUDPPacketHeader ) );

				/* The fragment status is used to complete the length and
				fragment offset fields. */
				if( eFragmentStatus == eNotFragment )
				{
					pxIPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength + sizeof( xIPHeader_t ) + sizeof( xUDPHeader_t ) );
				}
				else if( eFragmentStatus == eFirstFragment )
				{
					pxIPHeader->usFragmentOffset = FreeRTOS_htons( usFragmentOffset );
					pxIPHeader->usLength = ( uint16_t ) ( usFragmentLength + sizeof( xIPHeader_t ) + sizeof( xUDPHeader_t ) );
				}
				else
				{
					pxIPHeader->usFragmentOffset = FreeRTOS_htons( usFragmentOffset );
					pxIPHeader->usLength = ( uint16_t ) ( usFragmentLength + sizeof( xIPHeader_t ) );
				}

				/* The total transmit size adds on the Ethernet header. */
				pxNetworkBuffer->xDataLength = pxIPHeader->usLength + sizeof( xEthernetHeader_t );
				pxIPHeader->usLength = FreeRTOS_htons( pxIPHeader->usLength );
				pxIPHeader->ulDestinationIPAddress = pxNetworkBuffer->ulIPAddress;
				pxIPHeader->usIdentification = usPacketIdentifier;
				pxIPHeader->usHeaderChecksum = prvGenerateChecksum( ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipIP_HEADER_LENGTH );
			}
			else if ( eReturned == eARPCacheMiss )
			{
				/* Send an ARP for the required IP address. */
				iptracePACKET_DROPPED_TO_GENERATE_ARP( pxNetworkBuffer->ulIPAddress );
				prvGenerateARPRequestPacket( pxNetworkBuffer );

				/* Add an entry to the ARP table with a null hardware address.
				This allows the ARP timer to know that an ARP reply is
				outstanding, and perform retransmissions if necessary. */
				prvRefreshARPCacheEntry( &xNullMACAddress, pxNetworkBuffer->ulIPAddress );
			}
			else
			{
				/* The lookup indicated that an ARP request has already been
				sent out for the queried IP address. */
				eReturned = eCantSendPacket;
			}
		}

		if( eReturned != eCantSendPacket )
		{
			/* The network driver is responsible for freeing the network buffer
			after the packet has been sent. */
			xNetworkInterfaceOutput( pxNetworkBuffer );
		}
		else
		{
			/* The packet can't be sent (DHCP not completed?).  Just drop the
			packet. */
			vNetworkBufferRelease( pxNetworkBuffer );
		}
	}

#else /* ipconfigCAN_FRAGMENT_OUTGOING_PACKETS == 1 */

	static void prvProcessGeneratedPacket( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
	{
	xUDPPacket_t *pxUDPPacket;
	xIPHeader_t *pxIPHeader;
	eARPLookupResult_t eReturned;

		/* Map the UDP packet onto the start of the frame. */
		pxUDPPacket = ( xUDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

		/* Determine the ARP cache status for the requested IP address. */
		eReturned = prvGetARPCacheEntry( &( pxNetworkBuffer->ulIPAddress ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ) );
		if( eReturned != eCantSendPacket )
		{
			if( eReturned == eARPCacheHit )
			{
				iptraceSENDING_UDP_PACKET( pxNetworkBuffer->ulIPAddress );

				/* Create short cuts to the data within the packet. */
				pxIPHeader = &( pxUDPPacket->xIPHeader );

				/* IP header source and destination addresses must be set before
				the	UDP checksum is calculated.  The socket options, which
				specify whether a checksum should be calculated or not, are
				passed in the as yet unused part of the packet data. */
				pxIPHeader->ulDestinationIPAddress = pxNetworkBuffer->ulIPAddress;
				pxIPHeader->ulSourceIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

				#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
				{
					/* Is it possible that the packet is not actually a UDP packet
					after all, but an ICMP packet. */
					if( pxNetworkBuffer->usPort != ipPACKET_CONTAINS_ICMP_DATA )
					{
						prvCompleteUDPHeader( pxNetworkBuffer, pxUDPPacket, pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] );
					}
				}
				#else /* ipconfigSUPPORT_OUTGOING_PINGS */
				{
					prvCompleteUDPHeader( pxNetworkBuffer, pxUDPPacket, pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] );
				}
				#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

				/* memcpy() the constant parts of the header information into
				the	correct location within the packet.  This fills in:
					xEthernetHeader.xSourceAddress
					xEthernetHeader.usFrameType
					xIPHeader.ucVersionHeaderLength
					xIPHeader.ucDifferentiatedServicesCode
					xIPHeader.usLength
					xIPHeader.usIdentification
					xIPHeader.usFragmentOffset
					xIPHeader.ucTimeToLive
					xIPHeader.ucProtocol
				and
					xIPHeader.usHeaderChecksum
				*/
				memcpy( ( void *) &( pxUDPPacket->xEthernetHeader.xSourceAddress ), ( void * ) xDefaultPartUDPPacketHeader, sizeof( xDefaultPartUDPPacketHeader ) );

				#if ipconfigSUPPORT_OUTGOING_PINGS == 1
				{
					if( pxNetworkBuffer->usPort == ipPACKET_CONTAINS_ICMP_DATA )
					{
						pxIPHeader->ucProtocol = ipPROTOCOL_ICMP;
						pxIPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength + sizeof( xIPHeader_t ) );
					}
					else
					{
						pxIPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength + sizeof( xIPHeader_t ) + sizeof( xUDPHeader_t ) );
					}
				}
				#else /* ipconfigSUPPORT_OUTGOING_PINGS */
				{
					pxIPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength + sizeof( xIPHeader_t ) + sizeof( xUDPHeader_t ) );
				}
				#endif /* ipconfigSUPPORT_OUTGOING_PINGS */

				/* The total transmit size adds on the Ethernet header. */
				pxNetworkBuffer->xDataLength = pxIPHeader->usLength + sizeof( xEthernetHeader_t );
				pxIPHeader->usLength = FreeRTOS_htons( pxIPHeader->usLength );
				pxIPHeader->ulDestinationIPAddress = pxNetworkBuffer->ulIPAddress;
				pxIPHeader->usHeaderChecksum = prvGenerateChecksum( ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipIP_HEADER_LENGTH );
			}
			else if ( eReturned == eARPCacheMiss )
			{
				/* Generate an ARP for the required IP address. */
				iptracePACKET_DROPPED_TO_GENERATE_ARP( pxNetworkBuffer->ulIPAddress );
				prvGenerateARPRequestPacket( pxNetworkBuffer );

				/* Add an entry to the ARP table with a null hardware address.
				This allows the ARP timer to know that an ARP reply is
				outstanding, and perform retransmissions if necessary. */
				prvRefreshARPCacheEntry( &xNullMACAddress, pxNetworkBuffer->ulIPAddress );
			}
			else
			{
				/* The lookup indicated that an ARP request has already been
				sent out for the queried IP address. */
				eReturned = eCantSendPacket;
			}
		}

		if( eReturned != eCantSendPacket )
		{
			/* The network driver is responsible for freeing the network buffer
			after the packet has been sent. */
			xNetworkInterfaceOutput( pxNetworkBuffer );
		}
		else
		{
			/* The packet can't be sent (DHCP not completed?).  Just drop the
			packet. */
			vNetworkBufferRelease( pxNetworkBuffer );
		}
	}


#endif /* ipconfigCAN_FRAGMENT_OUTGOING_PACKETS == 1 */
/*-----------------------------------------------------------*/

static void prvGenerateARPRequestPacket( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
{
xARPPacket_t *pxARPPacket;

	pxARPPacket = ( xARPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

	/* memcpy the const part of the header information into the correct
	location in the packet.  This copies:
		xEthernetHeader.ulDestinationAddress
		xEthernetHeader.usFrameType;
		xARPHeader.usHardwareType;
		xARPHeader.usProtocolType;
		xARPHeader.ucHardwareAddressLength;
		xARPHeader.ucProtocolAddressLength;
		xARPHeader.usOperation;
		xARPHeader.xTargetHardwareAddress;
	*/
	memcpy( ( void * ) &( pxARPPacket->xEthernetHeader ), ( void * ) xDefaultPartARPPacketHeader, sizeof( xDefaultPartARPPacketHeader ) );
	memcpy( ( void * ) &( pxARPPacket->xEthernetHeader.xSourceAddress ) , ( void * ) ipLOCAL_MAC_ADDRESS, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
	memcpy( ( void * ) &( pxARPPacket->xARPHeader.xSenderHardwareAddress ), ( void * ) ipLOCAL_MAC_ADDRESS, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
	pxARPPacket->xARPHeader.ulSenderProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER;
	pxARPPacket->xARPHeader.ulTargetProtocolAddress = pxNetworkBuffer->ulIPAddress;

	pxNetworkBuffer->xDataLength = sizeof( xARPPacket_t );

	iptraceCREATING_ARP_REQUEST( ulIPAddress );
}
/*-----------------------------------------------------------*/

eFrameProcessingResult_t eConsiderFrameForProcessing( const uint8_t * const pucEthernetBuffer )
{
eFrameProcessingResult_t eReturn;
const xEthernetHeader_t *pxEthernetHeader;

	pxEthernetHeader = ( const xEthernetHeader_t * ) pucEthernetBuffer;

	if( memcmp( ( void * ) &xBroadcastMACAddress, ( void * ) &( pxEthernetHeader->xDestinationAddress ), sizeof( xMACAddress_t ) ) == 0 )
	{
		/* The packet was a broadcast - process it. */
		eReturn = eProcessBuffer;
	}
	else if( memcmp( ( void * ) ipLOCAL_MAC_ADDRESS, ( void * ) &( pxEthernetHeader->xDestinationAddress ), sizeof( xMACAddress_t ) ) == 0 )
	{
		/* The packet was to this node directly - process it. */
		eReturn = eProcessBuffer;
	}
	else
	{
		/* The packet was not a broadcast, or for this node, just release
		the buffer without taking any other action. */
		eReturn = eReleaseBuffer;
	}

	#if ipconfigFILTER_OUT_NON_ETHERNET_II_FRAMES == 1
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

	return eReturn;
}
/*-----------------------------------------------------------*/

static void prvProcessNetworkDownEvent( void )
{
	/* Stop the ARP timer while there is no network. */
	xTimerStop( xARPTimer, portMAX_DELAY );

	#if ipconfigUSE_NETWORK_EVENT_HOOK == 1
	{
		static portBASE_TYPE xCallEventHook = pdFALSE;

		/* The first network down event is generated by the IP stack
		itself to initialise the network hardware, so do not call the
		network down event the first time through. */
		if( xCallEventHook == pdFALSE )
		{
			vApplicationIPNetworkEventHook( eNetworkDown );
		}
		xCallEventHook = pdTRUE;
	}
	#endif

	/* The network has been disconnected (or is being
	initialised for the first time).  Perform whatever hardware
	processing is necessary to bring it up again, or wait for it
	to be available again.  This is hardware dependent. */
	if( xNetworkInterfaceInitialise() != pdPASS )
	{
		/* Ideally the network interface initialisation function
		will only return when the network is available.  In case
		this is not the case, wait a while before retrying the
		initialisation. */
		vTaskDelay( ipINITIALISATION_RETRY_DELAY );
		FreeRTOS_NetworkDown();
	}
	else
	{
		/* Start the ARP timer. */
		xTimerStart( xARPTimer, portMAX_DELAY );

		#if ipconfigUSE_DHCP == 1
		{
			/* The network is not up until DHCP has completed. */
			vDHCPProcess( pdTRUE, ( xMACAddress_t * ) ipLOCAL_MAC_ADDRESS, ipLOCAL_IP_ADDRESS_POINTER, &xNetworkAddressing );
			prvSendEventToIPTask( eDHCPEvent );
		}
		#else
		{
			/* Static configuration is being used, so the network is now up. */
			#if ipconfigFREERTOS_PLUS_NABTO == 1
			{
				prvStartNabtoTask();
			}
			#endif /* ipconfigFREERTOS_PLUS_NABTO */

			#if ipconfigUSE_NETWORK_EVENT_HOOK == 1
			{
				vApplicationIPNetworkEventHook( eNetworkUp );
			}
			#endif /* ipconfigUSE_NETWORK_EVENT_HOOK */
		}
		#endif
	}
}
/*-----------------------------------------------------------*/

static void prvProcessEthernetPacket( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
{
xEthernetHeader_t *pxEthernetHeader;
volatile eFrameProcessingResult_t eReturned; /* Volatile to prevent complier warnings when ipCONSIDER_FRAME_FOR_PROCESSING just sets it to eProcessBuffer. */

	configASSERT( pxNetworkBuffer );

	/* Interpret the Ethernet frame. */
	eReturned = ipCONSIDER_FRAME_FOR_PROCESSING( pxNetworkBuffer->pucEthernetBuffer );
	pxEthernetHeader = ( xEthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

	if( eReturned == eProcessBuffer )
	{
		/* Interpret the received Ethernet packet. */
		switch ( pxEthernetHeader->usFrameType )
		{
			case ipARP_TYPE	:
				/* The Ethernet frame contains an ARP packet. */
				eReturned = prvProcessARPPacket( ( xARPPacket_t * ) pxEthernetHeader );
				break;

			case ipIP_TYPE	:
				/* The Ethernet frame contains an IP packet. */
				eReturned = prvProcessIPPacket( ( xIPPacket_t * ) pxEthernetHeader, pxNetworkBuffer );
				break;

			default :
				/* No other packet types are handled.  Nothing to do. */
				eReturned = eReleaseBuffer;
				break;
		}
	}

	/* Perform any actions that resulted from processing the Ethernet
	frame. */
	switch( eReturned )
	{
		case eReturnEthernetFrame :
			/* The Ethernet frame will have been updated (maybe it was
			an ARP request or a PING request?) and should be sent back to
			its source. */
			prvReturnEthernetFrame( pxNetworkBuffer );
			/* The buffer must be released once
			the frame has been transmitted. */
			break;

		case eFrameConsumed :
			/* The frame is in use somewhere, don't release the buffer
			yet. */
			break;

		default :
			/* The frame is not being used anywhere, and the
			xNetworkBufferDescriptor_t structure containing the frame should just be
			released back to the list of free buffers. */
			vNetworkBufferRelease( pxNetworkBuffer );
			break;
	}
}
/*-----------------------------------------------------------*/

static eFrameProcessingResult_t prvProcessIPPacket( const xIPPacket_t * const pxIPPacket, xNetworkBufferDescriptor_t * const pxNetworkBuffer )
{
eFrameProcessingResult_t eReturn = eReleaseBuffer;
const xIPHeader_t * pxIPHeader;
xUDPPacket_t *pxUDPPacket;
portBASE_TYPE xChecksumIsCorrect;

	pxIPHeader = &( pxIPPacket->xIPHeader );

	/* Is the packet for this node? */
	if( ( pxIPHeader->ulDestinationIPAddress == *ipLOCAL_IP_ADDRESS_POINTER ) || ( pxIPHeader->ulDestinationIPAddress == ipBROADCAST_IP_ADDRESS ) || ( *ipLOCAL_IP_ADDRESS_POINTER == 0 ) )
	{
		/* Ensure the frame is IPv4 with no options bytes, and that the incoming
		packet is not fragmented (only outgoing packets can be fragmented) as
		these are the only handled IP frames currently. */
		if( ( pxIPHeader->ucVersionHeaderLength == ipIP_VERSION_AND_HEADER_LENGTH_BYTE ) && ( ( pxIPHeader->usFragmentOffset & ipFRAGMENT_OFFSET_BIT_MASK ) == 0U ) )
		{
			/* Is the IP header checksum correct? */
			if( prvGenerateChecksum( ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipIP_HEADER_LENGTH ) == 0 )
			{
				/* Add the IP and MAC addresses to the ARP table if they are not
				already there - otherwise refresh the age of the existing
				entry. */
				prvRefreshARPCacheEntry( &( pxIPPacket->xEthernetHeader.xSourceAddress ), pxIPHeader->ulSourceIPAddress );
				switch( pxIPHeader->ucProtocol )
				{
					case ipPROTOCOL_ICMP :

						/* The IP packet contained an ICMP frame.  Don't bother
						checking the ICMP checksum, as if it is wrong then the
						wrong data will also be returned, and the source of the
						ping will know something went wrong because it will not
						be able to validate what it receives. */
						#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
						{
							if( pxIPHeader->ulDestinationIPAddress == *ipLOCAL_IP_ADDRESS_POINTER )
							{
								eReturn = prvProcessICMPPacket( ( xICMPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer ) );
							}
						}
						#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */
						break;

					case ipPROTOCOL_UDP :

						/* The IP packet contained a UDP frame. */
						pxUDPPacket = ( xUDPPacket_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

						/* Note the header values required prior to the
						checksum generation as the checksum pseudo header
						may clobber some of these values. */
						pxNetworkBuffer->xDataLength = FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usLength ) - sizeof( xUDPHeader_t );
						pxNetworkBuffer->usPort = pxUDPPacket->xUDPHeader.usSourcePort;
						pxNetworkBuffer->ulIPAddress = pxUDPPacket->xIPHeader.ulSourceIPAddress;

						/* Is the checksum required? */
						if( pxUDPPacket->xUDPHeader.usChecksum == 0 )
						{
							xChecksumIsCorrect = pdTRUE;
						}
						else if( prvGenerateUDPChecksum( pxUDPPacket ) == 0 )
						{
							xChecksumIsCorrect = pdTRUE;
						}
						else
						{
							xChecksumIsCorrect = pdFALSE;
						}

						/* Is the checksum correct? */
						if( xChecksumIsCorrect == pdTRUE )
						{
							/* Pass the packet payload to the UDP sockets
							implementation. */
							if( xProcessReceivedUDPPacket( pxNetworkBuffer, pxUDPPacket->xUDPHeader.usDestinationPort ) == pdPASS )
							{
								eReturn = eFrameConsumed;
							}
						}
						break;

					default	:

						/* Not a supported frame type. */
						break;
				}
			}
		}
	}

	return eReturn;
}
/*-----------------------------------------------------------*/

static uint16_t prvGenerateUDPChecksum( const xUDPPacket_t * const pxUDPPacket )
{
xPseudoHeader_t *pxPseudoHeader;
uint16_t usLength, usReturn;

	/* Map the pseudo header into the correct place within the real IP
	header. */
	pxPseudoHeader = ( xPseudoHeader_t * ) &( pxUDPPacket->xIPHeader.ucTimeToLive );

	/* Ordering here is important so as not to overwrite data that is required
	but has not yet been used as the pseudo header overlaps the information
	that is being copied into it. */
	pxPseudoHeader->ulSourceAddress = pxUDPPacket->xIPHeader.ulSourceIPAddress;
	pxPseudoHeader->ulDestinationAddress = pxUDPPacket->xIPHeader.ulDestinationIPAddress;
	pxPseudoHeader->ucZeros = 0x00;
	pxPseudoHeader->ucProtocol = ipPROTOCOL_UDP;
	pxPseudoHeader->usUDPLength = pxUDPPacket->xUDPHeader.usLength;

	usLength = FreeRTOS_ntohs( pxPseudoHeader->usUDPLength );
	usReturn = prvGenerateChecksum( ( uint8_t * ) pxPseudoHeader, usLength + sizeof( xPseudoHeader_t ) );

	return usReturn;
}
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

	static void prvProcessICMPEchoReply( xICMPPacket_t * const pxICMPPacket )
	{
	ePingReplyStatus_t eStatus = eSuccess;
	uint16_t usDataLength, usCount;
	uint8_t *pucByte;

		/* Find the total length of the IP packet. */
		usDataLength = pxICMPPacket->xIPHeader.usLength;
		usDataLength = FreeRTOS_ntohs( usDataLength );

		/* Remove the length of the IP headers to obtain the length of the ICMP
		message itself. */
		usDataLength -= sizeof( xIPHeader_t );

		if( prvGenerateChecksum( ( uint8_t * ) &( pxICMPPacket->xICMPHeader ), usDataLength ) != 0 )
		{
			eStatus = eInvalidChecksum;
		}
		else
		{
			/* Remove the length of the ICMP header, to obtain the length of
			data contained in the ping. */
			usDataLength -= sizeof( xICMPHeader_t );

			/* Find the first byte of the data within the ICMP packet. */
			pucByte = ( uint8_t * ) pxICMPPacket;
			pucByte += sizeof( xICMPPacket_t );

			/* Check each byte. */
			for( usCount = 0; usCount < usDataLength; usCount++ )
			{
				if( *pucByte != ipECHO_DATA_FILL_BYTE )
				{
					eStatus = eInvalidData;
					break;
				}

				pucByte++;
			}
		}

		vApplicationPingReplyHook( eStatus, pxICMPPacket->xICMPHeader.usIdentifier );
	}

#endif
/*-----------------------------------------------------------*/

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 )

	static eFrameProcessingResult_t prvProcessICMPEchoRequest( xICMPPacket_t * const pxICMPPacket )
	{
	xICMPHeader_t *pxICMPHeader;
	xIPHeader_t *pxIPHeader;

		iptraceSENDING_PING_REPLY( pxIPHeader->ulSourceIPAddress );

		pxICMPHeader = &( pxICMPPacket->xICMPHeader );
		pxIPHeader = &( pxICMPPacket->xIPHeader );

		/* The checksum can be checked here - but a ping reply should be
		returned even if the checksum is incorrect so the other end can
		tell that the ping was received - even if the ping reply contains
		invalid data. */
		pxICMPHeader->ucTypeOfMessage = ipICMP_ECHO_REPLY;
		pxIPHeader->ulDestinationIPAddress = pxIPHeader->ulSourceIPAddress;
		pxIPHeader->ulSourceIPAddress = *ipLOCAL_IP_ADDRESS_POINTER;

		/* Update the checksum because the ucTypeOfMessage member in the
		header has been changed to ipICMP_ECHO_REPLY. */
		if( pxICMPHeader->usChecksum >= FreeRTOS_htons( ( ( uint16_t ) 0xffffU ) - ( ipICMP_ECHO_REQUEST << ( ( uint16_t ) 8U ) ) ) )
		{
			pxICMPHeader->usChecksum += FreeRTOS_htons( ipICMP_ECHO_REQUEST << ( ( uint16_t ) 8U ) ) + ( uint16_t ) 1U;
		}
		else
		{
			pxICMPHeader->usChecksum += FreeRTOS_htons( ipICMP_ECHO_REQUEST << ( ( uint16_t ) 8U ) );
		}

		return eReturnEthernetFrame;
	}

#endif /* ipconfigREPLY_TO_INCOMING_PINGS == 1 */

/*-----------------------------------------------------------*/

#if ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

	static eFrameProcessingResult_t prvProcessICMPPacket( xICMPPacket_t * const pxICMPPacket )
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
				break;
		}

		return eReturn;
	}

#endif /* ( ipconfigREPLY_TO_INCOMING_PINGS == 1 ) || ( ipconfigSUPPORT_OUTGOING_PINGS == 1 ) */
/*-----------------------------------------------------------*/

static uint16_t prvGenerateChecksum( const uint8_t * const pucNextData, const uint16_t usDataLengthBytes )
{
uint32_t ulChecksum = 0;
uint16_t us, usDataLength16BitWords, *pusNextData;

	/* There are half as many 16 bit words than bytes. */
	usDataLength16BitWords = ( usDataLengthBytes >> 1U );

	pusNextData = ( uint16_t * ) pucNextData;

	for( us = 0U; us < usDataLength16BitWords; us++ )
	{
		ulChecksum += ( uint32_t ) pusNextData[ us ];
	}

	if( ( usDataLengthBytes & 0x01U ) != 0x00 )
	{
		/* There is one byte left over. */
		#if ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN
		{
			ulChecksum += ( uint32_t ) pucNextData[ usDataLengthBytes - 1 ];
		}
		#else
		{
			us = ( uint16_t ) pucNextData[ usDataLengthBytes - 1 ];
			ulChecksum += ( uint32_t ) ( us << 8 );
		}
		#endif
	}

	while( ( ulChecksum >> 16UL ) != 0x00UL )
	{
		ulChecksum = ( ulChecksum & 0xffffUL ) + ( ulChecksum >> 16UL );
	}

	return ~( ( uint16_t ) ulChecksum );
}
/*-----------------------------------------------------------*/

static void prvReturnEthernetFrame( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
{
xEthernetHeader_t *pxEthernetHeader;

	pxEthernetHeader = ( xEthernetHeader_t * ) ( pxNetworkBuffer->pucEthernetBuffer );

	/* Swap source and destination MAC addresses. */
	memcpy( ( void * ) &( pxEthernetHeader->xDestinationAddress ), ( void * ) &( pxEthernetHeader->xSourceAddress ), sizeof( pxEthernetHeader->xDestinationAddress ) );
	memcpy( ( void * ) &( pxEthernetHeader->xSourceAddress) , ( void * ) ipLOCAL_MAC_ADDRESS, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );

	/* Send! */
	xNetworkInterfaceOutput( pxNetworkBuffer );
}
/*-----------------------------------------------------------*/

static eFrameProcessingResult_t prvProcessARPPacket( xARPPacket_t * const pxARPFrame )
{
eFrameProcessingResult_t eReturn = eReleaseBuffer;
xARPHeader_t *pxARPHeader;

	pxARPHeader = &( pxARPFrame->xARPHeader );

	traceARP_PACKET_RECEIVED();

	/* Sanity check the protocol type.  Don't do anything if the local IP
	address is zero because that means a DHCP request has not completed. */
	if( ( pxARPHeader->usProtocolType == ipARP_PROTOCOL_TYPE ) && ( *ipLOCAL_IP_ADDRESS_POINTER != 0UL ) )
	{
		switch( pxARPHeader->usOperation )
		{
			case ipARP_REQUEST	:
				/* The packet contained an ARP request.  Was it for the IP
				address of the node running this code? */
				if( pxARPHeader->ulTargetProtocolAddress == *ipLOCAL_IP_ADDRESS_POINTER )
				{
					iptraceSENDING_ARP_REPLY( pxARPHeader->ulSenderProtocolAddress );

					/* The request is for the address of this node.  Add the
					entry into the ARP cache, or refresh the entry if it
					already exists. */
					prvRefreshARPCacheEntry( &( pxARPHeader->xSenderHardwareAddress ), pxARPHeader->ulSenderProtocolAddress );

					/* Generate a reply payload in the same buffer. */
					pxARPHeader->usOperation = ipARP_REPLY;
					memcpy( ( void * )  &( pxARPHeader->xTargetHardwareAddress ), ( void * ) &( pxARPHeader->xSenderHardwareAddress ), sizeof( xMACAddress_t ) );
					pxARPHeader->ulTargetProtocolAddress = pxARPHeader->ulSenderProtocolAddress;
					memcpy( ( void * ) &( pxARPHeader->xSenderHardwareAddress ), ( void * ) ipLOCAL_MAC_ADDRESS, sizeof( xMACAddress_t ) );
					pxARPHeader->ulSenderProtocolAddress = *ipLOCAL_IP_ADDRESS_POINTER;

					eReturn = eReturnEthernetFrame;
				}
				break;

			case ipARP_REPLY :
				iptracePROCESSING_RECEIVED_ARP_REPLY( pxARPHeader->ulTargetProtocolAddress );
				prvRefreshARPCacheEntry( &( pxARPHeader->xSenderHardwareAddress ), pxARPHeader->ulSenderProtocolAddress );
				break;

			default :
				/* Invalid. */
				break;
		}
	}

	return eReturn;
}
/*-----------------------------------------------------------*/

#if( ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN )
	uint16_t FreeRTOS_htons( uint16_t usIn )
	{
		return	( ( usIn & ( uint16_t ) 0x00ff ) << ( uint16_t ) 8U ) |
				( ( usIn & ( uint16_t ) 0xff00 ) >> ( uint16_t ) 8U );
	}
#endif /* ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN */
/*-----------------------------------------------------------*/

#if( ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN )
	uint32_t FreeRTOS_htonl( uint32_t ulIn )
	{
		return	( ( ulIn & 0x000000ffUL ) << 24UL ) |
				( ( ulIn & 0x0000ff00UL ) << 8UL  ) |
				( ( ulIn & 0x00ff0000UL ) >> 8UL  ) |
				( ( ulIn & 0xff000000UL ) >> 24UL );
	}
#endif /* ipconfigBYTE_ORDER == FREERTOS_LITTLE_ENDIAN */

/*-----------------------------------------------------------*/

#if( ipconfigFREERTOS_PLUS_NABTO == 1 )
	static void prvStartNabtoTask( void )
	{
	static portBASE_TYPE xNabtoTaskStarted = pdFALSE;

		if( xNabtoTaskStarted == pdFALSE )
		{
			FreeRTOS_NabtoInit();
			xNabtoTaskStarted = pdTRUE;
		}
	}
#endif /* ipconfigFREERTOS_PLUS_NABTO */


