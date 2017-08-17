/*
 * FreeRTOS+TCP Labs Build 160919 (C) 2016 Real Time Engineers ltd.
 * Authors include Hein Tibosch and Richard Barry
 *
 *******************************************************************************
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 ***                                                                         ***
 ***                                                                         ***
 ***   FREERTOS+TCP IS STILL IN THE LAB (mainly because the FTP and HTTP     ***
 ***   demos have a dependency on FreeRTOS+FAT, which is only in the Labs    ***
 ***   download):                                                            ***
 ***                                                                         ***
 ***   FreeRTOS+TCP is functional and has been used in commercial products   ***
 ***   for some time.  Be aware however that we are still refining its       ***
 ***   design, the source code does not yet quite conform to the strict      ***
 ***   coding and style standards mandated by Real Time Engineers ltd., and  ***
 ***   the documentation and testing is not necessarily complete.            ***
 ***                                                                         ***
 ***   PLEASE REPORT EXPERIENCES USING THE SUPPORT RESOURCES FOUND ON THE    ***
 ***   URL: http://www.FreeRTOS.org/contact  Active early adopters may, at   ***
 ***   the sole discretion of Real Time Engineers Ltd., be offered versions  ***
 ***   under a license other than that described below.                      ***
 ***                                                                         ***
 ***                                                                         ***
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 *******************************************************************************
 *
 * FreeRTOS+TCP can be used under two different free open source licenses.  The
 * license that applies is dependent on the processor on which FreeRTOS+TCP is
 * executed, as follows:
 *
 * If FreeRTOS+TCP is executed on one of the processors listed under the Special
 * License Arrangements heading of the FreeRTOS+TCP license information web
 * page, then it can be used under the terms of the FreeRTOS Open Source
 * License.  If FreeRTOS+TCP is used on any other processor, then it can be used
 * under the terms of the GNU General Public License V2.  Links to the relevant
 * licenses follow:
 *
 * The FreeRTOS+TCP License Information Page: http://www.FreeRTOS.org/tcp_license
 * The FreeRTOS Open Source License: http://www.FreeRTOS.org/license
 * The GNU General Public License Version 2: http://www.FreeRTOS.org/gpl-2.0.txt
 *
 * FreeRTOS+TCP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+TCP unless you agree that you use the software 'as is'.
 * FreeRTOS+TCP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/plus
 * http://www.FreeRTOS.org/labs
 *
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
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

#if( ipconfigUSE_DNS == 1 )
	#include "FreeRTOS_DNS.h"
#endif

/* The expected IP version and header length coded into the IP header itself. */
#define ipIP_VERSION_AND_HEADER_LENGTH_BYTE ( ( uint8_t ) 0x45 )

/* Part of the Ethernet and IP headers are always constant when sending an IPv4
UDP packet.  This array defines the constant parts, allowing this part of the
packet to be filled in using a simple memcpy() instead of individual writes. */
UDPPacketHeader_t xDefaultPartUDPPacketHeader =
{
	/* .ucBytes : */
	{
		0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 	/* Ethernet source MAC address. */
		0x08, 0x00, 							/* Ethernet frame type. */
		ipIP_VERSION_AND_HEADER_LENGTH_BYTE, 	/* ucVersionHeaderLength. */
		0x00, 									/* ucDifferentiatedServicesCode. */
		0x00, 0x00, 							/* usLength. */
		0x00, 0x00, 							/* usIdentification. */
		0x00, 0x00, 							/* usFragmentOffset. */
		ipconfigUDP_TIME_TO_LIVE, 				/* ucTimeToLive */
		ipPROTOCOL_UDP, 						/* ucProtocol. */
		0x00, 0x00, 							/* usHeaderChecksum. */
		0x00, 0x00, 0x00, 0x00 					/* Source IP address. */
	}
};
/*-----------------------------------------------------------*/

void vProcessGeneratedUDPPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
UDPPacket_t *pxUDPPacket;
IPHeader_t *pxIPHeader;
eARPLookupResult_t eReturned;
uint32_t ulIPAddress = pxNetworkBuffer->ulIPAddress;

	/* Map the UDP packet onto the start of the frame. */
	pxUDPPacket = ( UDPPacket_t * ) pxNetworkBuffer->pucEthernetBuffer;

	/* Determine the ARP cache status for the requested IP address. */
	eReturned = eARPGetCacheEntry( &( ulIPAddress ), &( pxUDPPacket->xEthernetHeader.xDestinationAddress ) );

	if( eReturned != eCantSendPacket )
	{
		if( eReturned == eARPCacheHit )
		{
			#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
				uint8_t ucSocketOptions;
			#endif
			iptraceSENDING_UDP_PACKET( pxNetworkBuffer->ulIPAddress );

			/* Create short cuts to the data within the packet. */
			pxIPHeader = &( pxUDPPacket->xIPHeader );

		#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )
			/* Is it possible that the packet is not actually a UDP packet
			after all, but an ICMP packet. */
			if( pxNetworkBuffer->usPort != ipPACKET_CONTAINS_ICMP_DATA )
		#endif /* ipconfigSUPPORT_OUTGOING_PINGS */
			{
			UDPHeader_t *pxUDPHeader;

				pxUDPHeader = &( pxUDPPacket->xUDPHeader );

				pxUDPHeader->usDestinationPort = pxNetworkBuffer->usPort;
				pxUDPHeader->usSourcePort = pxNetworkBuffer->usBoundPort;
				pxUDPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength + sizeof( UDPHeader_t ) );
				pxUDPHeader->usLength = FreeRTOS_htons( pxUDPHeader->usLength );
				pxUDPHeader->usChecksum = 0u;
			}

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

			/* Save options now, as they will be overwritten by memcpy */
			#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
			{
				ucSocketOptions = pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ];
			}
			#endif

			memcpy( ( void *) &( pxUDPPacket->xEthernetHeader.xSourceAddress ), ( void * ) xDefaultPartUDPPacketHeader.ucBytes, sizeof( xDefaultPartUDPPacketHeader ) );

		#if ipconfigSUPPORT_OUTGOING_PINGS == 1
			if( pxNetworkBuffer->usPort == ipPACKET_CONTAINS_ICMP_DATA )
			{
				pxIPHeader->ucProtocol = ipPROTOCOL_ICMP;
				pxIPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength + sizeof( IPHeader_t ) );
			}
			else
		#endif /* ipconfigSUPPORT_OUTGOING_PINGS */
			{
				pxIPHeader->usLength = ( uint16_t ) ( pxNetworkBuffer->xDataLength + sizeof( IPHeader_t ) + sizeof( UDPHeader_t ) );
			}

			/* The total transmit size adds on the Ethernet header. */
			pxNetworkBuffer->xDataLength = pxIPHeader->usLength + sizeof( EthernetHeader_t );
			pxIPHeader->usLength = FreeRTOS_htons( pxIPHeader->usLength );
			pxIPHeader->ulDestinationIPAddress = pxNetworkBuffer->ulIPAddress;

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

			#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
			{
				pxIPHeader->usHeaderChecksum = 0u;
				pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0UL, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
				pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );

				if( ( ucSocketOptions & ( uint8_t ) FREERTOS_SO_UDPCKSUM_OUT ) != 0u )
				{
					usGenerateProtocolChecksum( (uint8_t*)pxUDPPacket, pdTRUE );
				}
				else
				{
					pxUDPPacket->xUDPHeader.usChecksum = 0u;
				}
			}
			#endif
		}
		else if( eReturned == eARPCacheMiss )
		{
			/* Add an entry to the ARP table with a null hardware address.
			This allows the ARP timer to know that an ARP reply is
			outstanding, and perform retransmissions if necessary. */
			vARPRefreshCacheEntry( NULL, ulIPAddress );

			/* Generate an ARP for the required IP address. */
			iptracePACKET_DROPPED_TO_GENERATE_ARP( pxNetworkBuffer->ulIPAddress );
			pxNetworkBuffer->ulIPAddress = ulIPAddress;
			vARPGenerateRequestPacket( pxNetworkBuffer );
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

		#if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES )
		{
			if( pxNetworkBuffer->xDataLength < ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES )
			{
			BaseType_t xIndex;

				for( xIndex = ( BaseType_t ) pxNetworkBuffer->xDataLength; xIndex < ( BaseType_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES; xIndex++ )
				{
					pxNetworkBuffer->pucEthernetBuffer[ xIndex ] = 0u;
				}
				pxNetworkBuffer->xDataLength = ( size_t ) ipconfigETHERNET_MINIMUM_PACKET_BYTES;
			}
		}
		#endif

		xNetworkInterfaceOutput( pxNetworkBuffer, pdTRUE );
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

UDPPacket_t *pxUDPPacket = (UDPPacket_t *) pxNetworkBuffer->pucEthernetBuffer;

	pxSocket = pxUDPSocketLookup( usPort );

	if( pxSocket )
	{

		/* When refreshing the ARP cache with received UDP packets we must be
		careful;  hundreds of broadcast messages may pass and if we're not
		handling them, no use to fill the ARP cache with those IP addresses. */
		vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );

		#if( ipconfigUSE_CALLBACKS == 1 )
		{
			/* Did the owner of this socket register a reception handler ? */
			if( ipconfigIS_VALID_PROG_ADDRESS( pxSocket->u.xUDP.pxHandleReceive ) )
			{
				struct freertos_sockaddr xSourceAddress, destinationAddress;
				void *pcData = ( void * ) &( pxNetworkBuffer->pucEthernetBuffer[ ipUDP_PAYLOAD_OFFSET_IPv4 ] );
				FOnUDPReceive_t xHandler = ( FOnUDPReceive_t ) pxSocket->u.xUDP.pxHandleReceive;
				xSourceAddress.sin_port = pxNetworkBuffer->usPort;
				xSourceAddress.sin_addr = pxNetworkBuffer->ulIPAddress;
				destinationAddress.sin_port = usPort;
				destinationAddress.sin_addr = pxUDPPacket->xIPHeader.ulDestinationIPAddress;

				if( xHandler( ( Socket_t * ) pxSocket, ( void* ) pcData, ( size_t ) pxNetworkBuffer->xDataLength,
					&xSourceAddress, &destinationAddress ) != pdFALSE )
				{
					xReturn = pdFAIL; /* xHandler has consumed the data, do not add it to .xWaitingPacketsList'. */
				}
			}
		}
		#endif /* ipconfigUSE_CALLBACKS */

		#if( ipconfigUDP_MAX_RX_PACKETS > 0 )
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

		if( xReturn == pdPASS )
		{
			vTaskSuspendAll();
			{
				if( xReturn == pdPASS )
				{
					taskENTER_CRITICAL();
					{
						/* Add the network packet to the list of packets to be
						processed by the socket. */
						vListInsertEnd( &( pxSocket->u.xUDP.xWaitingPacketsList ), &( pxNetworkBuffer->xBufferListItem ) );
					}
					taskEXIT_CRITICAL();
				}
			}
			xTaskResumeAll();

			/* Set the socket's receive event */
			if( pxSocket->xEventGroup != NULL )
			{
				xEventGroupSetBits( pxSocket->xEventGroup, eSOCKET_RECEIVE );
			}

			#if( ipconfigSUPPORT_SELECT_FUNCTION == 1 )
			{
				if( ( pxSocket->pxSocketSet != NULL ) && ( ( pxSocket->xSelectBits & eSELECT_READ ) != 0 ) )
				{
					xEventGroupSetBits( pxSocket->pxSocketSet->xSelectGroup, eSELECT_READ );
				}
			}
			#endif

			#if( ipconfigSOCKET_HAS_USER_SEMAPHORE == 1 )
			{
				if( pxSocket->pxUserSemaphore != NULL )
				{
					xSemaphoreGive( pxSocket->pxUserSemaphore );
				}
			}
			#endif

			#if( ipconfigUSE_DHCP == 1 )
			{
				if( xIsDHCPSocket( pxSocket ) )
				{
					xSendEventToIPTask( eDHCPEvent );
				}
			}
			#endif
		}
	}
	else
	{
		/* There is no socket listening to the target port, but still it might
		be for this node. */

		#if( ipconfigUSE_DNS == 1 )
			/* A DNS reply, check for the source port.  Although the DNS client
			does open a UDP socket to send a messages, this socket will be
			closed after a short timeout.  Messages that come late (after the
			socket is closed) will be treated here. */
			if( FreeRTOS_ntohs( pxUDPPacket->xUDPHeader.usSourcePort ) == ipDNS_PORT )
			{
				vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
				xReturn = ( BaseType_t )ulDNSHandlePacket( pxNetworkBuffer );
			}
			else
		#endif

		#if( ipconfigUSE_LLMNR == 1 )
			/* A LLMNR request, check for the destination port. */
			if( ( usPort == FreeRTOS_ntohs( ipLLMNR_PORT ) ) ||
				( pxUDPPacket->xUDPHeader.usSourcePort == FreeRTOS_ntohs( ipLLMNR_PORT ) ) )
			{
				vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
				xReturn = ( BaseType_t )ulDNSHandlePacket( pxNetworkBuffer );
			}
			else
		#endif /* ipconfigUSE_LLMNR */

		#if( ipconfigUSE_NBNS == 1 )
			/* a NetBIOS request, check for the destination port */
			if( ( usPort == FreeRTOS_ntohs( ipNBNS_PORT ) ) ||
				( pxUDPPacket->xUDPHeader.usSourcePort == FreeRTOS_ntohs( ipNBNS_PORT ) ) )
			{
				vARPRefreshCacheEntry( &( pxUDPPacket->xEthernetHeader.xSourceAddress ), pxUDPPacket->xIPHeader.ulSourceIPAddress );
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
