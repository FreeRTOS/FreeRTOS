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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_DHCP.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_ND.h"

#if( ipconfigUSE_DNS == 1 ) || ( ipconfigUSE_NBNS == 1 )
	#include "FreeRTOS_DNS.h"
#endif

/* The expected IP version and header length coded into the IP header itself. */
#define ipIP_VERSION_AND_HEADER_LENGTH_BYTE ( ( uint8_t ) 0x45 )

/*-----------------------------------------------------------*/

void vProcessGeneratedUDPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
UDPPacket_t *pxUDPPacket;
IPHeader_t *pxIPHeader;
#if( ipconfigUSE_IPv6 != 0 )
	UDPPacket_IPv6_t *pxUDPPacket_IPv6;
	IPHeader_IPv6_t *pxIPHeader_IPv6 = NULL;
#endif
eARPLookupResult_t eReturned;
uint32_t ulIPAddress = pxNetworkBuffer->ulIPAddress;
NetworkEndPoint_t *pxEndPoint = pxNetworkBuffer->pxEndPoint;
#if( ipconfigUSE_IPv6 != 0 )
	BaseType_t xIsIPV6 = pdFALSE;
#endif

	/* Map the UDP packet onto the start of the frame. */
	pxUDPPacket = ipPOINTER_CAST( UDPPacket_t *, pxNetworkBuffer->pucEthernetBuffer );

	/* Create short cuts to the data within the packet. */
	pxIPHeader = &( pxUDPPacket->xIPHeader );

	#if( ipconfigUSE_IPv6 != 0 )
	pxUDPPacket_IPv6 = ipPOINTER_CAST( UDPPacket_IPv6_t *, pxNetworkBuffer->pucEthernetBuffer );
	if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
	{
		xIsIPV6 = pdTRUE;
		pxIPHeader_IPv6 = &( pxUDPPacket_IPv6->xIPHeader );
	}
	else
	#endif
	{
		pxUDPPacket->xEthernetHeader.usFrameType = ipIPv4_FRAME_TYPE;

		( void ) memset( pxIPHeader, 0, sizeof *pxIPHeader );
		pxIPHeader->ucVersionHeaderLength = ipIP_VERSION_AND_HEADER_LENGTH_BYTE;
		pxIPHeader->ucTimeToLive = ipconfigUDP_TIME_TO_LIVE;
	}

	/* Determine the ARP cache status for the requested IP address.  This may
	change the ulIPAddress to the router address.
	Beside the MAC-address, a reference to the network Interface will
    be return. */
	#if( ipconfigUSE_IPv6 != 0 )
	if( xIsIPV6 != 0 )
	{
		// #pragma warning Take away
		( void ) memset( pxUDPPacket->xEthernetHeader.xDestinationAddress.ucBytes, 0, 6 );
		eReturned = eNDGetCacheEntry( &( pxNetworkBuffer->xIPv6_Address ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), &( pxEndPoint ) );
		if( pxNetworkBuffer->pxEndPoint == NULL )
		{
			pxNetworkBuffer->pxEndPoint = pxEndPoint;
		}
	}
	else
	#endif
	{
		if( ( ( FreeRTOS_ntohl( ulIPAddress ) & 0xffU ) == 0xffU ) && ( pxEndPoint != NULL ) )
    	{
			/* This is a IPv4 broadcast address, use FF:FF:FF:FF:FF:FF. */
        	( void ) memset( pxUDPPacket->xEthernetHeader.xDestinationAddress.ucBytes, 0xff, ipMAC_ADDRESS_LENGTH_BYTES );
        	eReturned = eARPCacheHit;
    	}
    	else
    	{
	    	eReturned = eARPGetCacheEntry( &( ulIPAddress ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ), &( pxEndPoint ) );
			if( pxNetworkBuffer->pxEndPoint == NULL )
			{
				pxNetworkBuffer->pxEndPoint = pxEndPoint;
			}
		}
    }

	if( eReturned != eCantSendPacket )
	{
		if( eReturned == eARPCacheHit )
		{
			#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
				uint8_t ucSocketOptions;
			#endif
			iptraceSENDING_UDP_PACKET( pxNetworkBuffer->ulIPAddress );

			/* Is it possible that the packet is not actually a UDP packet
			after all, but an ICMP packet. */
			if( pxNetworkBuffer->usPort != ( uint16_t ) ipPACKET_CONTAINS_ICMP_DATA )
			{
			UDPHeader_t *pxUDPHeader;

				#if( ipconfigUSE_IPv6 != 0 )
				if( xIsIPV6 != 0 )
				{
					pxUDPHeader = &( pxUDPPacket_IPv6->xUDPHeader );

					pxUDPPacket_IPv6->xIPHeader.ucVersionTrafficClass = 0x60;
					pxUDPPacket_IPv6->xIPHeader.ucTrafficClassFlow = 0;
					pxUDPPacket_IPv6->xIPHeader.usFlowLabel = 0;
					pxUDPPacket_IPv6->xIPHeader.ucHopLimit = 255;
					pxUDPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER ) );
				}
				else
				#endif
				{
					pxUDPHeader = &( pxUDPPacket->xUDPHeader );
					pxUDPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv4_HEADER ) );
				}

				pxUDPHeader->usDestinationPort = pxNetworkBuffer->usPort;
				pxUDPHeader->usSourcePort = pxNetworkBuffer->usBoundPort;
				pxUDPHeader->usLength = FreeRTOS_htons( pxUDPHeader->usLength );
				pxUDPHeader->usChecksum = 0U;
			}

			/* Save options now, as they will be overwritten by memcpy */
			#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
			{
				ucSocketOptions = pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ];
			}
			#endif

			if( pxNetworkBuffer->usPort == ( uint16_t ) ipPACKET_CONTAINS_ICMP_DATA )
			{
				#if( ipconfigUSE_IPv6 != 0 )
				if( xIsIPV6 != pdFALSE )
				{
					/* When xIsIPV6 is true, pxIPHeader_IPv6 has been assigned a proper value. */
					configASSERT( pxIPHeader_IPv6 != NULL );
					pxIPHeader_IPv6->ucNextHeader = ipPROTOCOL_ICMP_IPv6;
				}
				else
				#endif	/* ( ipconfigUSE_IPv6 != 0 ) */
				{
					pxIPHeader->ucProtocol = ipPROTOCOL_ICMP;
					pxIPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );
					pxIPHeader->usLength = FreeRTOS_htons( pxIPHeader->usLength );
					pxIPHeader->ulDestinationIPAddress = pxNetworkBuffer->ulIPAddress;
				}
			}
			else
			{
				#if( ipconfigUSE_IPv6 != 0 )
				if( xIsIPV6 != pdFALSE )
				{
					pxUDPPacket_IPv6->xIPHeader.ucNextHeader = ipPROTOCOL_UDP;
					pxUDPPacket_IPv6->xIPHeader.usPayloadLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - sizeof( IPPacket_IPv6_t ) );
					/* The total transmit size adds on the Ethernet header. */
					pxUDPPacket_IPv6->xIPHeader.usPayloadLength = FreeRTOS_htons( pxUDPPacket_IPv6->xIPHeader.usPayloadLength );
					( void ) memcpy( pxUDPPacket_IPv6->xIPHeader.xDestinationAddress.ucBytes, pxNetworkBuffer->xIPv6_Address.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
				}
				else
				#endif
				{
					pxIPHeader->ucProtocol = ipPROTOCOL_UDP;
					pxIPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength - ipSIZE_OF_ETH_HEADER );
					pxIPHeader->usLength = FreeRTOS_htons( pxIPHeader->usLength );
					pxIPHeader->ulDestinationIPAddress = pxNetworkBuffer->ulIPAddress;
				}
			}

			if( pxNetworkBuffer->pxEndPoint != NULL )
			{
				/* The packet already has a destination. */
			}
			else if( pxEndPoint != NULL )
			{
				/* Using the end-point found in the ARP table. */
				pxNetworkBuffer->pxEndPoint = pxEndPoint;
			}
			else
			{
				/* Look it up. */
			}

			/* Which end point should the ping go out on? */
			if( pxNetworkBuffer->pxEndPoint == NULL )
			{
				pxNetworkBuffer->pxEndPoint = FreeRTOS_FindEndPointOnNetMask( pxNetworkBuffer->ulIPAddress, 10 );
				if( pxNetworkBuffer->pxEndPoint == NULL )
				{
					pxNetworkBuffer->pxEndPoint = FreeRTOS_FirstEndPoint( NULL );
					if( pxNetworkBuffer->pxEndPoint == NULL )
					{
						FreeRTOS_printf( ( "vProcessGeneratedUDPPacket: No pxEndPoint found? Using %lxip\n",
										   ( pxNetworkBuffer->pxEndPoint != NULL ) ? FreeRTOS_ntohl( pxNetworkBuffer->pxEndPoint->ipv4_settings.ulIPAddress ) : 0UL ) );
					}
				}
			}

			#if( ipconfigUSE_LLMNR == 1 )
			{
				/* LLMNR messages are typically used on a LAN and they're
				 * not supposed to cross routers */
				if( pxNetworkBuffer->ulIPAddress == ipLLMNR_IP_ADDR )
				{
					pxIPHeader->ucTimeToLive = 0x01;
				}
			}
			#endif
			if( pxNetworkBuffer->pxEndPoint != NULL )
			{
				#if( ipconfigUSE_IPv6 != 0 )
				if( xIsIPV6 != pdFALSE )
				{
					/* When xIsIPV6 is true, pxIPHeader_IPv6 has been assigned a proper value. */
					configASSERT( pxIPHeader_IPv6 != NULL );
					( void ) memcpy( pxIPHeader_IPv6->xSourceAddress.ucBytes, pxNetworkBuffer->pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
				}
				else
				#endif
				{
					pxIPHeader->ulSourceIPAddress = pxNetworkBuffer->pxEndPoint->ipv4_settings.ulIPAddress;
				}
			}
			#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
			{
				#if( ipconfigUSE_IPv6 != 0 )
				if( xIsIPV6 == pdFALSE )
				#endif
				{
					pxIPHeader->usHeaderChecksum = 0U;
					pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
					pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );
				}

				if( ( ucSocketOptions & ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT ) != 0U )
				{
					( void ) usGenerateProtocolChecksum( ( uint8_t * ) pxUDPPacket, pxNetworkBuffer->xDataLength, pdTRUE );
				}
				else
				{
					pxUDPPacket->xUDPHeader.usChecksum = 0U;
				}
			}
			#endif
		}
		else if( eReturned == eARPCacheMiss )
		{
			#if( ipconfigUSE_IPv6 != 0 )
			if( xIsIPV6 != 0 )
			{
				FreeRTOS_printf( ( "Looking up %pip with%s end-point\n", pxNetworkBuffer->xIPv6_Address.ucBytes, ( pxNetworkBuffer->pxEndPoint != NULL ) ? "" : "out" ) );

				if( pxNetworkBuffer->pxEndPoint != NULL )
				{
					vNDSendNeighbourSolicitation( pxNetworkBuffer, &( pxNetworkBuffer->xIPv6_Address ) );
					/* pxNetworkBuffer has been sent and released. Return from function. */
					return;
				}
			}
			else
			#endif
			{
				FreeRTOS_printf( ( "Looking up %lxip%s with%s end-point\n",
					FreeRTOS_ntohl( ulIPAddress ),
					( pxNetworkBuffer->ulIPAddress != ulIPAddress ) ? " (gateway)" : "",
					( pxNetworkBuffer->pxEndPoint != NULL ) ? "" : "out" ) );

				/* Add an entry to the ARP table with a null hardware address.
				This allows the ARP timer to know that an ARP reply is
				outstanding, and perform retransmissions if necessary. */
				vARPRefreshCacheEntry( NULL, ulIPAddress, NULL );

				/* Generate an ARP for the required IP address. */
				iptracePACKET_DROPPED_TO_GENERATE_ARP( pxNetworkBuffer->ulIPAddress );
				pxNetworkBuffer->ulIPAddress = ulIPAddress;

				/* 'ulIPAddress' might have become the address of the Gateway.
				Find the route again. */
				pxNetworkBuffer->pxEndPoint = FreeRTOS_FindEndPointOnNetMask( ulIPAddress, 11 );	/* ARP request */
				if( pxNetworkBuffer->pxEndPoint == NULL )
				{
					eReturned = eCantSendPacket;
				}
				else
				{
					vARPGenerateRequestPacket( pxNetworkBuffer );
				}
			}
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
		if( pxNetworkBuffer->pxEndPoint != NULL )
		{
		NetworkInterface_t *pxInterface = pxNetworkBuffer->pxEndPoint->pxNetworkInterface;

			( void ) memcpy( &( pxUDPPacket->xEthernetHeader.xSourceAddress), pxNetworkBuffer->pxEndPoint->xMACAddress.ucBytes, ( size_t ) ipMAC_ADDRESS_LENGTH_BYTES );
			#if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES )
			{
				if( pxNetworkBuffer->xDataLength < ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES )
				{
				BaseType_t xIndex;
	
					for( xIndex = ( BaseType_t ) pxNetworkBuffer->xDataLength; xIndex < ( BaseType_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES; xIndex++ )
					{
						pxNetworkBuffer->pucEthernetBuffer[ xIndex ] = 0U;
					}
					pxNetworkBuffer->xDataLength = ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES;
				}
			}
			#endif

			#if( ipconfigUSE_IPv6 != 0 )
			if( xIsIPV6 != pdFALSE )
			{
				/* When xIsIPV6 is true, pxIPHeader_IPv6 has been assigned a proper value. */
				configASSERT( pxIPHeader_IPv6 != NULL );
			}
			#endif

			( void ) pxInterface->pfOutput( pxInterface, pxNetworkBuffer, pdTRUE );
		}
		else
		{
			/* The packet can't be sent (no route found).  Drop the packet. */
			vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
		}
	}
	else
	{
		/* The packet can't be sent (DHCP not completed?).  Just drop the
		packet. */
		vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
	}
}
/*-----------------------------------------------------------*/

BaseType_t xProcessReceivedUDPPacket( NetworkBufferDescriptor_t *pxNetworkBuffer, uint16_t usPort )
{
BaseType_t xReturn = pdPASS;
FreeRTOS_Socket_t *pxSocket;
ProtocolHeaders_t *pxProtocolHeaders;
UDPPacket_t *pxUDPPacket = ipPOINTER_CAST( UDPPacket_t *, pxNetworkBuffer->pucEthernetBuffer );
size_t uxIPLength;
#if( ipconfigUSE_IPv6 != 0 )
	UDPPacket_IPv6_t *pxUDPPacket_IPv6;
	BaseType_t xIsIPV6 = pdFALSE;
#endif

	/* Caller must check for minimum packet size. */
	pxSocket = pxUDPSocketLookup( usPort );

	configASSERT( pxNetworkBuffer->pucEthernetBuffer != NULL );

	uxIPLength = uxIPHeaderSizePacket( pxNetworkBuffer );

	pxProtocolHeaders = ipPOINTER_CAST( ProtocolHeaders_t *, &( pxNetworkBuffer->pucEthernetBuffer[ ( size_t ) ipSIZE_OF_ETH_HEADER + uxIPLength ] ) );
	#if( ipconfigUSE_IPv6 != 0 )
	pxUDPPacket_IPv6 = ipPOINTER_CAST( UDPPacket_IPv6_t *, pxNetworkBuffer->pucEthernetBuffer );
	if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
	{
		xIsIPV6 = pdTRUE;
	}
	#endif


	if( pxSocket != NULL )
	{

		#if( ipconfigUSE_IPv6 != 0 )
		if( xIsIPV6 != 0 )
		{
			vNDRefreshCacheEntry( &( pxUDPPacket_IPv6->xEthernetHeader.xSourceAddress ), &( pxUDPPacket_IPv6->xIPHeader.xSourceAddress ), pxNetworkBuffer->pxEndPoint );
		}
		else
		#endif
		{
			/* When refreshing the ARP cache with received UDP packets we must be
			careful;  hundreds of broadcast messages may pass and if we're not
			handling them, no use to fill the ARP cache with those IP addresses. */
			vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress, pxNetworkBuffer->pxEndPoint );
		}

		#if( ipconfigUSE_CALLBACKS == 1 )
		{
			/* Did the owner of this socket register a reception handler ? */
			if( ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xUDP.pxHandleReceive ) )
			{
			void *pcData = &( pxNetworkBuffer->pucEthernetBuffer[ ipSIZE_OF_ETH_HEADER + uxIPLength + ipSIZE_OF_UDP_HEADER ] );
			FOnUDPReceive_t xHandler = ( FOnUDPReceive_t ) pxSocket->u.xUDP.pxHandleReceive;
			size_t uxPayloadSize;
			#if( ipconfigUSE_IPv6 != 0 )
				struct freertos_sockaddr6 xSourceAddress, destinationAddress;
			#else
				struct freertos_sockaddr xSourceAddress, destinationAddress;
			#endif

				xSourceAddress.sin_port = pxNetworkBuffer->usPort;
				destinationAddress.sin_port = usPort;

				#if( ipconfigUSE_IPv6 != 0 )
				if( xIsIPV6 != 0 )
				{

					( void ) memcpy( xSourceAddress.sin_addrv6.ucBytes,     pxUDPPacket_IPv6->xIPHeader.xSourceAddress.ucBytes,      ipSIZE_OF_IPv6_ADDRESS );
					( void ) memcpy( destinationAddress.sin_addrv6.ucBytes, pxUDPPacket_IPv6->xIPHeader.xDestinationAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
					xSourceAddress.sin_family     = ( uint8_t ) FREERTOS_AF_INET6;
					destinationAddress.sin_family = ( uint8_t ) FREERTOS_AF_INET6;
					xSourceAddress.sin_len        = ( uint8_t ) sizeof( xSourceAddress );
					destinationAddress.sin_len    = ( uint8_t ) sizeof( destinationAddress );
				}
				else
				{
				struct freertos_sockaddr *xSourceAddress4     = ipPOINTER_CAST( struct freertos_sockaddr *, &( xSourceAddress ) );
				struct freertos_sockaddr *destinationAddress4 = ipPOINTER_CAST( struct freertos_sockaddr *, &( destinationAddress ) );
					xSourceAddress4->sin_addr       = pxNetworkBuffer->ulIPAddress;
					destinationAddress4->sin_addr   = pxUDPPacket->xIPHeader.ulDestinationIPAddress;
					xSourceAddress4->sin_family     = FREERTOS_AF_INET;
					destinationAddress4->sin_family = FREERTOS_AF_INET;
					xSourceAddress4->sin_len        = ( uint8_t ) sizeof( xSourceAddress );
					destinationAddress4->sin_len    = ( uint8_t ) sizeof( destinationAddress );
				}
				#else
				{
					xSourceAddress.sin_addr = pxNetworkBuffer->ulIPAddress;
					destinationAddress.sin_addr = pxUDPPacket->xIPHeader.ulDestinationIPAddress;
					xSourceAddress.sin_family = FREERTOS_AF_INET4;
					destinationAddress.sin_family = FREERTOS_AF_INET4;
					xSourceAddress.sin_len        = sizeof( xSourceAddress );
					destinationAddress.sin_len    = sizeof( destinationAddress );
				}
				#endif	/* ( ipconfigUSE_IPv6 != 0 ) */

				uxPayloadSize = pxNetworkBuffer->xDataLength - ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_UDP_HEADER + ( size_t ) uxIPHeaderSizePacket( pxNetworkBuffer ) );
				if( xHandler( pxSocket,
							  pcData, ( size_t ) uxPayloadSize,
							  ipPOINTER_CAST( struct freertos_sockaddr *, &( xSourceAddress ) ),
							  ipPOINTER_CAST( struct freertos_sockaddr *, &( destinationAddress ) ) ) != pdFALSE )
				{
					xReturn = pdFAIL; /* xHandler has consumed the data, do not add it to .xWaitingPacketsList'. */
				}
			}
		}
		#endif /* ipconfigUSE_CALLBACKS */

		#if( ipconfigUDP_MAX_RX_PACKETS > 0U )
		{
			if( xReturn == pdPASS )
			{
				if ( listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) ) >= pxSocket->u.xUDP.uxMaxPackets )
				{
					FreeRTOS_debug_printf( ( "xProcessReceivedUDPPacket: buffer full %ld >= %ld port %u\n",
						listCURRENT_LIST_LENGTH( &( pxSocket->u.xUDP.xWaitingPacketsList ) ),
						pxSocket->u.xUDP.uxMaxPackets, pxSocket->usLocalPort ) );
					xReturn = pdFAIL; /* we did not consume or release the buffer */
				}
			}
		}
		#endif

		if( xReturn == pdPASS )	/*lint !e774: Boolean within 'if' always evaluates to True, depending on configuration. [MISRA 2012 Rule 14.3, required. */
		{
			vTaskSuspendAll();
			{
				taskENTER_CRITICAL();
				{
					/* Add the network packet to the list of packets to be
					processed by the socket. */
					vListInsertEnd( &( pxSocket->u.xUDP.xWaitingPacketsList ), &( pxNetworkBuffer->xBufferListItem ) );
				}
				taskEXIT_CRITICAL();
			}
			( void ) xTaskResumeAll();

			/* Set the socket's receive event */
			if( pxSocket->xEventGroup != NULL )
			{
				( void ) xEventGroupSetBits( pxSocket->xEventGroup, ( EventBits_t ) eSOCKET_RECEIVE );
			}

			#if( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
			{
				if( ( pxSocket->pxSocketSet != NULL ) && ( ( pxSocket->xSelectBits & ( ( EventBits_t ) eSELECT_READ ) ) != 0U ) )
				{
					( void ) xEventGroupSetBits( pxSocket->pxSocketSet->xSelectGroup, ( EventBits_t ) eSELECT_READ );
				}
			}
			#endif

			#if( ipconfigSOCKET_HAS_USER_SEMAPHORE == 1 )
			{
				if( pxSocket->pxUserSemaphore != NULL )
				{
					( void ) xSemaphoreGive( pxSocket->pxUserSemaphore );
				}
			}
			#endif

			#if( ipconfigUSE_DHCP == 1 )
			{
				if( xIsDHCPSocket( pxSocket ) != 0 )
				{
					/* This is the DHCP clients socket, bound to port 68. */
					/* Can call this function directly, because this code is running from the IP-task. */
					vDHCPProcess( pdFALSE, NULL );
				}
			}
			#endif
		}
	}
	else
	{
		/* There is no socket listening to the target port, but still it might
		be for this node. */

		#if( ipconfigUSE_DNS == 1 ) && ( ipconfigDNS_USE_CALLBACKS == 1 )
			/* A DNS reply, check for the source port.  Although the DNS client
			does open a UDP socket to send a messages, this socket will be
			closed after a short timeout.  Messages that come late (after the
			socket is closed) will be treated here. */
			if( FreeRTOS_ntohs( pxProtocolHeaders->xUDPHeader.usSourcePort ) == ( uint16_t ) ipDNS_PORT )
			{
				#if( ipconfigUSE_IPv6 != 0 )
				if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
				{
				}
				else
				#endif
				{
					vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress,
						pxNetworkBuffer->pxEndPoint );
				}
				xReturn = ( BaseType_t )ulDNSHandlePacket( pxNetworkBuffer );
			}
			else
		#endif

		#if( ipconfigUSE_LLMNR == 1 )
			/* A LLMNR request, check for the destination port. */
			if( ( usPort == FreeRTOS_ntohs( ipLLMNR_PORT ) ) ||
				( pxProtocolHeaders->xUDPHeader.usSourcePort == FreeRTOS_ntohs( ipLLMNR_PORT ) ) )
			{
				#if( ipconfigUSE_IPv6 != 0 )
				if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
				{
				}
				else
				#endif
				{
					vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress,
						pxNetworkBuffer->pxEndPoint );
				}

				xReturn = ( BaseType_t ) ulDNSHandlePacket( pxNetworkBuffer );
			}
			else
		#endif /* ipconfigUSE_LLMNR */

		#if( ipconfigUSE_NBNS == 1 )
			/* a NetBIOS request, check for the destination port */
			if( ( usPort == FreeRTOS_ntohs( ipNBNS_PORT ) ) ||
				( pxProtocolHeaders->xUDPHeader.usSourcePort == FreeRTOS_ntohs( ipNBNS_PORT ) ) )/*lint !e9007 !e845 */
			{
				#if( ipconfigUSE_IPv6 != 0 )
				if( pxUDPPacket->xEthernetHeader.usFrameType == ipIPv6_FRAME_TYPE )
				{
				}
				else
				#endif
				{
					vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress,
						pxNetworkBuffer->pxEndPoint );
				}
				xReturn = ( BaseType_t )ulNBNSHandlePacket( pxNetworkBuffer );
			}
			else
		#endif /* ipconfigUSE_NBNS */
			{
				xReturn = pdFAIL;
			}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/
