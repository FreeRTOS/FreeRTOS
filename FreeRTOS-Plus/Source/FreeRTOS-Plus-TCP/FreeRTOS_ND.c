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

/* The eniire module FreeRTOS_ND.c is skipped when IPv6 is not used. */
#if( ipconfigUSE_IPv6 != 0 )

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>


/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Routing.h"
#include "FreeRTOS_ND.h"
#if( ipconfigUSE_LLMNR == 1 )
	#include "FreeRTOS_DNS.h"
#endif /* ipconfigUSE_LLMNR */
#include "NetworkBufferManagement.h"

#define ndICMPv6_FLAG_SOLICITED					0x40000000UL
#define ndICMPv6_FLAG_UPDATE					0x20000000UL

/* Options that can be send after the ICMPv6 header. */
#define	ndICMP_SOURCE_LINK_LAYER_ADDRESS		1
#define	ndICMP_TARGET_LINK_LAYER_ADDRESS		2
#define	ndICMP_PREFIX_INFORMATION				3
#define	ndICMP_REDIRECTED_HEADER				4
#define	ndICMP_MTU_OPTION						5

/* Possible values of ucFlags in a neighbour advertisement. */
#ifndef _lint
	#define ndFlags_IsRouter		0x8000U
	#define ndFlags_Solicited		0x4000U
	#define ndFlags_Override		0x2000U
#endif

/* A block time of 0 simply means "don't block". */
#define ndDONT_BLOCK				( ( TickType_t ) 0 )

/* The character used to fill ICMP echo requests, and therefore also the
character expected to fill ICMP echo replies. */
#define ndECHO_DATA_FILL_BYTE						'x'

/*lint -e754 local struct member not referenced. */
/*lint -e766 Header file pack_struct_end.h' not used in module. */


/* All nodes on the local network segment. */
static const uint8_t pcLOCAL_NETWORK_MULTICAST_IP[ 16 ] = { 0xff, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01 };
static const uint8_t pcLOCAL_NETWORK_MULTICAST_MAC[ ipMAC_ADDRESS_LENGTH_BYTES ] = { 0x33, 0x33, 0x00, 0x00, 0x00, 0x01 };

/*
 * Lookup an MAC address in the ND cache from the IP address.
 */
static eARPLookupResult_t prvCacheLookup( IPv6_Address_t *pxAddressToLookup, MACAddress_t * const pxMACAddress, NetworkEndPoint_t **ppxEndPoint );

/* The ND cache. */
static NDCacheRow_t xNDCache[ ipconfigND_CACHE_ENTRIES ];
/*-----------------------------------------------------------*/

eARPLookupResult_t eNDGetCacheEntry( IPv6_Address_t *pxIPAddress, MACAddress_t * const pxMACAddress, struct xNetworkEndPoint **ppxEndPoint )
{
eARPLookupResult_t eReturn;
NetworkEndPoint_t *pxEndPoint;
/* For testing now, fill in Hein's laptop: 9c 5c 8e 38 06 6c */
//static const unsigned char testMAC[] = { 0x9C, 0x5C, 0x8E, 0x38, 0x06, 0x6C };
//
//	( void ) memcpy( pxMACAddress->ucBytes, testMAC, sizeof testMAC );

	eReturn = prvCacheLookup( pxIPAddress, pxMACAddress, ppxEndPoint );
	if( eReturn == eARPCacheMiss )
	{
		pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( pxIPAddress );
		if( pxEndPoint != NULL )
		{
			*( ppxEndPoint ) = pxEndPoint;
		}
		else
		{
			pxEndPoint = FreeRTOS_FindGateWay( (BaseType_t ) ipTYPE_IPv6 );
			if( pxEndPoint != NULL )
			{
			NetworkEndPoint_t *pxKeep;
				pxKeep = pxEndPoint;
				( void ) memcpy( pxIPAddress->ucBytes, pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
				FreeRTOS_printf( ( "eNDGetCacheEntry: Using gw %pip", pxIPAddress->ucBytes ) );	/* access to 'ipv6_settings' is checked. */
				eReturn = prvCacheLookup( pxIPAddress, pxMACAddress, ppxEndPoint );
				if( *( ppxEndPoint ) == NULL )
				{
					*( ppxEndPoint ) = pxKeep;
				}
			}
		}
	}

	return eReturn;
}
/*-----------------------------------------------------------*/

void vNDRefreshCacheEntry( const MACAddress_t * pxMACAddress, const IPv6_Address_t *pxIPAddress, NetworkEndPoint_t *pxEndPoint )
{
BaseType_t x;
BaseType_t xFreeEntry = -1, xEntryFound = -1;
	/* For each entry in the ARP cache table. */
	for( x = 0; x < ipconfigND_CACHE_ENTRIES; x++ )
	{
		if( xNDCache[ x ].ucValid == ( uint8_t )pdFALSE )
		{
			if( xFreeEntry == -1 )
			{
				xFreeEntry = x;
			}
		}
		else if( memcmp( xNDCache[ x ].xIPAddress.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS ) == 0 )
		{
			xEntryFound = x;
			break;
		}
		else
		{
			/* Entry is valid but the IP-address doesn't match. */
		}
	}
	if( xEntryFound < 0 )
	{
		xEntryFound = xFreeEntry;
	}
	if( xEntryFound >= 0 )
	{
		/* Copy the IP-address. */
		( void ) memcpy( xNDCache[ xEntryFound ].xIPAddress.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
		/* Copy the MAC-address. */
		( void ) memcpy( xNDCache[ xEntryFound ].xMACAddress.ucBytes, pxMACAddress->ucBytes, sizeof( MACAddress_t ) );
		xNDCache[ xEntryFound ].pxEndPoint = pxEndPoint;
		xNDCache[ xEntryFound ].ucAge = ( uint8_t ) ipconfigMAX_ARP_AGE;
		xNDCache[ xEntryFound ].ucValid = ( uint8_t ) pdTRUE;
		/* The format %pip will print a IPv6 address ( if printf-stdarg.c is included ). */
//		FreeRTOS_printf( ( "vNDRefreshCacheEntry[ %d ] %pip with %02x:%02x:%02x\n",
//			( int ) xEntryFound,
//			pxIPAddress->ucBytes,
//			pxMACAddress->ucBytes[ 3 ],
//			pxMACAddress->ucBytes[ 4 ],
//			pxMACAddress->ucBytes[ 5 ] ) );
	}
	else
	{
		FreeRTOS_printf( ( "vNDRefreshCacheEntry: %pip not found\n", pxIPAddress->ucBytes ) );
	}
}
/*-----------------------------------------------------------*/

void FreeRTOS_ClearND( void )
{
	( void ) memset( xNDCache, 0, sizeof( xNDCache ) );
}
/*-----------------------------------------------------------*/

static eARPLookupResult_t prvCacheLookup( IPv6_Address_t *pxAddressToLookup, MACAddress_t * const pxMACAddress, NetworkEndPoint_t **ppxEndPoint )
{
BaseType_t x;
eARPLookupResult_t eReturn = eARPCacheMiss;
	/* For each entry in the ARP cache table. */
	for( x = 0; x < ipconfigND_CACHE_ENTRIES; x++ )
	{
		if( xNDCache[ x ].ucValid == ( uint8_t )pdFALSE )
		{
		}
		else if( memcmp( xNDCache[ x ].xIPAddress.ucBytes, pxAddressToLookup->ucBytes, ipSIZE_OF_IPv6_ADDRESS ) == 0 )
		{
			( void ) memcpy( pxMACAddress->ucBytes, xNDCache[ x ].xMACAddress.ucBytes, sizeof( MACAddress_t ) );
			eReturn = eARPCacheHit;
			*ppxEndPoint = xNDCache[ x ].pxEndPoint;
			FreeRTOS_printf( ( "prvCacheLookup6[ %d ] %pip with %02x:%02x:%02x:%02x:%02x:%02x\n",
				( int ) x,
				pxAddressToLookup->ucBytes,
				pxMACAddress->ucBytes[ 0 ],
				pxMACAddress->ucBytes[ 1 ],
				pxMACAddress->ucBytes[ 2 ],
				pxMACAddress->ucBytes[ 3 ],
				pxMACAddress->ucBytes[ 4 ],
				pxMACAddress->ucBytes[ 5 ] ) );
			break;
		}
		else
		{
			/* Entry is valid but the MAC-address doesn't match. */
		}
	}
	if( eReturn == eARPCacheMiss )
	{
		FreeRTOS_printf( ( "prvCacheLookup %pip Miss\n", pxAddressToLookup->ucBytes ) );
		*ppxEndPoint = NULL;
	}
	return eReturn;
}
/*-----------------------------------------------------------*/

#if( ( ipconfigHAS_PRINTF != 0 ) || ( ipconfigHAS_DEBUG_PRINTF != 0 ) )

	void FreeRTOS_PrintNDCache( void )
	{
	BaseType_t x, xCount = 0;

		/* Loop through each entry in the ARP cache. */
		for( x = 0; x < ipconfigARP_CACHE_ENTRIES; x++ )
		{
			if( xNDCache[ x ].ucValid != ( uint8_t ) 0U )
			{
				/* See if the MAC-address also matches, and we're all happy */
				FreeRTOS_printf( ( "ND %2ld: %3u - %pip : %02x:%02x:%02x : %02x:%02x:%02x\n",
					x,
					xNDCache[ x ].ucAge,
					xNDCache[ x ].xIPAddress.ucBytes,
					xNDCache[ x ].xMACAddress.ucBytes[0],
					xNDCache[ x ].xMACAddress.ucBytes[1],
					xNDCache[ x ].xMACAddress.ucBytes[2],
					xNDCache[ x ].xMACAddress.ucBytes[3],
					xNDCache[ x ].xMACAddress.ucBytes[4],
					xNDCache[ x ].xMACAddress.ucBytes[5] ) );
				xCount++;
			}
		}

		FreeRTOS_printf( ( "Arp has %ld entries\n", xCount ) );
	}

#endif /* ( ipconfigHAS_PRINTF != 0 ) || ( ipconfigHAS_DEBUG_PRINTF != 0 ) */
/*-----------------------------------------------------------*/

static void prvReturnICMP_IPv6( NetworkBufferDescriptor_t * const pxNetworkBuffer, size_t uxICMPSize )
{
NetworkEndPoint_t *pxEndPoint = pxNetworkBuffer->pxEndPoint;
ICMPPacket_IPv6_t *pxICMPPacket = ipPOINTER_CAST( ICMPPacket_IPv6_t *, pxNetworkBuffer->pucEthernetBuffer );
ICMPHeader_IPv6_t *pxICMPHeader_IPv6 = ( ICMPHeader_IPv6_t * )&( pxICMPPacket->xICMPHeader_IPv6 );

	configASSERT( pxEndPoint != NULL );
	configASSERT( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED );
	
	( void ) memcpy( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes, pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
	( void ) memcpy( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
	pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( uxICMPSize );

	/* Important: tell NIC driver how many bytes must be sent */
	pxNetworkBuffer->xDataLength = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );

	pxICMPHeader_IPv6->usChecksum = 0;
	/* calculate the UDP checksum for outgoing package */
	( void ) usGenerateProtocolChecksum( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE );

	/* This function will fill in the eth addresses and send the packet */
	vReturnEthernetFrame( pxNetworkBuffer, pdFALSE );
}
/*-----------------------------------------------------------*/

/*
 * Send out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 * add an entry into the ND table that indicates that an ND reply is
 * outstanding so re-transmissions can be generated.
 */
void vNDSendNeighbourSolicitation( NetworkBufferDescriptor_t * const pxNetworkBuffer, IPv6_Address_t *pxIPAddress )
{
ICMPPacket_IPv6_t *pxICMPPacket;
ICMPHeader_IPv6_t *xICMPHeader_IPv6;
NetworkEndPoint_t *pxEndPoint = pxNetworkBuffer->pxEndPoint;
size_t uxNeededSize;
IPv6_Address_t xTargetIPAddress;
MACAddress_t xMultiCastMacAddress;
NetworkBufferDescriptor_t *pxDescriptor = pxNetworkBuffer;

	configASSERT( pxEndPoint != NULL );
	configASSERT( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED );

	uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t ) );
	if( pxDescriptor->xDataLength < uxNeededSize )
	{
		pxDescriptor = pxDuplicateNetworkBufferWithDescriptor( pxDescriptor, uxNeededSize );
		if( pxDescriptor == NULL )
		{
			return;	/*lint !e904 Return statement before end of function [MISRA 2012 Rule 15.5, advisory]. */
		}
	}
	pxICMPPacket = ipPOINTER_CAST( ICMPPacket_IPv6_t *, pxDescriptor->pucEthernetBuffer );
	xICMPHeader_IPv6 = ipPOINTER_CAST( ICMPHeader_IPv6_t *, &( pxICMPPacket->xICMPHeader_IPv6 ) );

	pxDescriptor->xDataLength = uxNeededSize;

	/* Set the multi-cast MAC-address. */
	xMultiCastMacAddress.ucBytes[ 0 ] = 0x33;
	xMultiCastMacAddress.ucBytes[ 1 ] = 0x33;
	xMultiCastMacAddress.ucBytes[ 2 ] = 0xff;
	xMultiCastMacAddress.ucBytes[ 3 ] = pxIPAddress->ucBytes[ 13 ];
	xMultiCastMacAddress.ucBytes[ 4 ] = pxIPAddress->ucBytes[ 14 ];
	xMultiCastMacAddress.ucBytes[ 5 ] = pxIPAddress->ucBytes[ 15 ];

	/* Set Ethernet header. Source and Destination will be swapped. */
	( void ) memcpy( pxICMPPacket->xEthernetHeader.xSourceAddress.ucBytes, xMultiCastMacAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
	( void ) memcpy( pxICMPPacket->xEthernetHeader.xDestinationAddress.ucBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
	pxICMPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

	/* Set IP-header. */
	pxICMPPacket->xIPHeader.ucVersionTrafficClass = 0x60;
	pxICMPPacket->xIPHeader.ucTrafficClassFlow = 0;
	pxICMPPacket->xIPHeader.usFlowLabel = 0;
	pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( 32U );/*lint !e845: (Info -- The right argument to operator '|' is certain to be 0. */
	pxICMPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
	pxICMPPacket->xIPHeader.ucHopLimit = 255;

	/* Source address "fe80::1" */
	( void ) memset( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, 0, sizeof pxICMPPacket->xIPHeader.xSourceAddress.ucBytes );
	pxICMPPacket->xIPHeader.xSourceAddress.ucBytes[  0 ] = 0xfeU;
	pxICMPPacket->xIPHeader.xSourceAddress.ucBytes[  1 ] = 0x80U;
	pxICMPPacket->xIPHeader.xSourceAddress.ucBytes[ 15 ] = 0x01U;

	//ff02::1:ff5a:afe7
	( void ) memset( xTargetIPAddress.ucBytes, 0, sizeof( xTargetIPAddress.ucBytes ) );
	xTargetIPAddress.ucBytes[  0 ] = 0xff;
	xTargetIPAddress.ucBytes[  1 ] = 0x02;
	xTargetIPAddress.ucBytes[ 11 ] = 0x01;
	xTargetIPAddress.ucBytes[ 12 ] = 0xff;
	xTargetIPAddress.ucBytes[ 13 ] = pxIPAddress->ucBytes[ 13 ];
	xTargetIPAddress.ucBytes[ 14 ] = pxIPAddress->ucBytes[ 14 ];
	xTargetIPAddress.ucBytes[ 15 ] = pxIPAddress->ucBytes[ 15 ];
	( void ) memcpy( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes, xTargetIPAddress.ucBytes, 16 );

	/* Set ICMP header. */
	( void ) memset( xICMPHeader_IPv6, 0, sizeof( *xICMPHeader_IPv6 ) );
	xICMPHeader_IPv6->ucTypeOfMessage = ipICMP_NEIGHBOR_SOLICITATION_IPv6;
	( void ) memcpy( xICMPHeader_IPv6->xIPv6_Address.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
	xICMPHeader_IPv6->ucOptionType = ndICMP_SOURCE_LINK_LAYER_ADDRESS;
	xICMPHeader_IPv6->ucOptionLength = 1;	/* times 8 bytes. */
	( void ) memcpy( xICMPHeader_IPv6->ucOptionBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );

	/* Checmsums. */
	xICMPHeader_IPv6->usChecksum = 0;
	/* calculate the UDP checksum for outgoing package */
	( void ) usGenerateProtocolChecksum( pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength, pdTRUE );

	/* This function will fill in the eth addresses and send the packet */
	vReturnEthernetFrame( pxDescriptor, pdTRUE );
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_RA != 0 )
	void vNDSendRouterSolicitation( NetworkBufferDescriptor_t * const pxNetworkBuffer, IPv6_Address_t *pxIPAddress )
	{
	ICMPPacket_IPv6_t *pxICMPPacket;
	ICMPRouterSolicitation_IPv6_t *xRASolicitationRequest;
	NetworkEndPoint_t *pxEndPoint = pxNetworkBuffer->pxEndPoint;
	size_t uxNeededSize;
	MACAddress_t xMultiCastMacAddress;
	NetworkBufferDescriptor_t *pxDescriptor = pxNetworkBuffer;

		configASSERT( pxEndPoint != NULL );
		uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) );
		if( pxDescriptor->xDataLength < uxNeededSize )
		{
			pxDescriptor = pxDuplicateNetworkBufferWithDescriptor( pxDescriptor, uxNeededSize );
			if( pxDescriptor == NULL )
			{
				return;	/*lint !e904 Return statement before end of function [MISRA 2012 Rule 15.5, advisory]. */
			}
		}
		pxICMPPacket = ipPOINTER_CAST( ICMPPacket_IPv6_t *, pxDescriptor->pucEthernetBuffer );
		xRASolicitationRequest = ipPOINTER_CAST( ICMPRouterSolicitation_IPv6_t *, &( pxICMPPacket->xICMPHeader_IPv6 ) );

		pxDescriptor->xDataLength = uxNeededSize;

		xMultiCastMacAddress.ucBytes[ 0 ] = 0x33;
		xMultiCastMacAddress.ucBytes[ 1 ] = 0x33;
		xMultiCastMacAddress.ucBytes[ 2 ] = 0x00;
		xMultiCastMacAddress.ucBytes[ 3 ] = 0x00;
		xMultiCastMacAddress.ucBytes[ 4 ] = 0x00;
		xMultiCastMacAddress.ucBytes[ 5 ] = 0x02;

		/* Set Ethernet header. Will be swapped. */
		( void ) memcpy( pxICMPPacket->xEthernetHeader.xSourceAddress.ucBytes, xMultiCastMacAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
		( void ) memcpy( pxICMPPacket->xEthernetHeader.xDestinationAddress.ucBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
		pxICMPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

		/* Set IP-header. */
		pxICMPPacket->xIPHeader.ucVersionTrafficClass = 0x60;
		pxICMPPacket->xIPHeader.ucTrafficClassFlow = 0;
		pxICMPPacket->xIPHeader.usFlowLabel = 0;
		pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( sizeof( ICMPRouterSolicitation_IPv6_t ) );/*lint !e845: (Info -- The right argument to operator '|' is certain to be 0. */
		pxICMPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
		pxICMPPacket->xIPHeader.ucHopLimit = 255;

		configASSERT( pxEndPoint != NULL );
		configASSERT( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED );
		( void ) memcpy( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, 16 );

		( void ) memcpy( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes, pxIPAddress->ucBytes, 16 );

		/* Set ICMP header. */
		( void ) memset( xRASolicitationRequest, 0, sizeof( *xRASolicitationRequest ) );
		xRASolicitationRequest->ucTypeOfMessage = ipICMP_ROUTER_SOLICITATION_IPv6;

	/*
		xRASolicitationRequest->ucOptionType = ndICMP_SOURCE_LINK_LAYER_ADDRESS;
		xRASolicitationRequest->ucOptionLength = 1;
		( void ) memcpy( xRASolicitationRequest->ucOptionBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
	*/
		/* Checmsums. */
		xRASolicitationRequest->usChecksum = 0;
		/* calculate the UDP checksum for outgoing package */
		( void ) usGenerateProtocolChecksum( pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength, pdTRUE );

		/* This function will fill in the eth addresses and send the packet */
		vReturnEthernetFrame( pxDescriptor, pdTRUE );
	}
#endif	/* ( ipconfigUSE_RA != 0 ) */
/*-----------------------------------------------------------*/

#if( ipconfigUSE_RA != 0 )
	static void prvReceiveRA( NetworkBufferDescriptor_t * const pxNetworkBuffer )
	{
	ICMPPacket_IPv6_t *pxICMPPacket = ipPOINTER_CAST( ICMPPacket_IPv6_t *, pxNetworkBuffer->pucEthernetBuffer );
	ICMPRouterAdvertisement_IPv6_t *pxAdvertisement = ipPOINTER_CAST( ICMPRouterAdvertisement_IPv6_t *, &( pxICMPPacket->xICMPHeader_IPv6 ) );
	ICMPPrefixOption_IPv6_t *pxPrefixOption = NULL;
	size_t uxIndex;
	size_t uxLast;
	size_t uxICMPSize;
	size_t uxNeededSize;
	uint8_t *pucBytes;

		/* A Router Advertisement was received, handle it here. */
		uxICMPSize = sizeof( ICMPRouterAdvertisement_IPv6_t );
		uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
		if( uxNeededSize > pxNetworkBuffer->xDataLength )
		{
			FreeRTOS_printf( ("Too small\n" ) );
			return;	/*lint !e904 Return statement before end of function [MISRA 2012 Rule 15.5, advisory]. */
		}

		FreeRTOS_printf( ( "RA: Type %02x Srv %02x Checksum %04x Hops %d Flags %02x Life %d\n",
			pxAdvertisement->ucTypeOfMessage,
			pxAdvertisement->ucTypeOfService,
			FreeRTOS_ntohs( pxAdvertisement->usChecksum ),
			pxAdvertisement->ucHopLimit,
			pxAdvertisement->ucFlags,
			FreeRTOS_ntohs( pxAdvertisement->usLifetime ) ) );
		uxIndex = 0;
		/* uxLast points to the first byte after the buffer. */
		uxLast = pxNetworkBuffer->xDataLength - uxNeededSize;
		pucBytes = &( pxNetworkBuffer->pucEthernetBuffer[ uxNeededSize ] );
		while( ( uxIndex + 1U ) < uxLast )
		{
			uint8_t ucType = pucBytes[ uxIndex ];
			size_t uxLength = ( size_t ) pucBytes[ uxIndex + 1U ] * 8U;
			if( uxLast < ( uxIndex + uxLength ) )
			{
				FreeRTOS_printf( ( "RA: Not enough bytes ( %u > %u )\n", ( unsigned ) uxIndex + uxLength, ( unsigned ) uxLast ) );
				break;
			}
			switch( ucType )
			{ 
				case ndICMP_SOURCE_LINK_LAYER_ADDRESS:	/* 1 */
					{
						FreeRTOS_printf( ( "RA: Source = %02x-%02x-%02x-%02x-%02x-%02x\n",
							pucBytes[ uxIndex + 2U ],
							pucBytes[ uxIndex + 3U ],
							pucBytes[ uxIndex + 4U ],
							pucBytes[ uxIndex + 5U ],
							pucBytes[ uxIndex + 6U ],
							pucBytes[ uxIndex + 7U ] ) );
					}
					break;
				case ndICMP_TARGET_LINK_LAYER_ADDRESS:	/* 2 */
					{
					}
					break;
				case ndICMP_PREFIX_INFORMATION:			/* 3 */
					{
					pxPrefixOption = ipPOINTER_CAST( ICMPPrefixOption_IPv6_t *, &( pucBytes[ uxIndex ] ) );

						FreeRTOS_printf( ( "RA: Prefix len %d Life %lu, %lu (%pip)\n",
							pxPrefixOption->ucPrefixLength,
							FreeRTOS_ntohl( pxPrefixOption->ulValidLifeTime ),
							FreeRTOS_ntohl( pxPrefixOption->ulPreferredLifeTime ),
							pxPrefixOption->ucPrefix ) );
					}
					break;
				case ndICMP_REDIRECTED_HEADER:			/* 4 */
					{
					}
					break;
				case ndICMP_MTU_OPTION:					/* 5 */
					{
					uint32_t ulMTU;

						/* ulChar2u32 returns host-endian numbers. */
						ulMTU = ulChar2u32 ( &( pucBytes[ uxIndex + 4 ] ) );/*lint !e9029 Mismatched essential type categories for binary operator [MISRA 2012 Rule 10.4, required]. */
						FreeRTOS_printf( ( "RA: MTU = %lu\n",  ulMTU ) );
					}
					break;
				default:
					{
						FreeRTOS_printf( ( "RA: Type %02x not implemented\n", ucType ) );
					}
					break;
			}
			uxIndex = uxIndex + uxLength;
		}	/* while( ( uxIndex + 1 ) < uxLast ) */
		configASSERT( pxNetworkBuffer->pxInterface != NULL );

		if( pxPrefixOption != NULL )
		{
		NetworkEndPoint_t *pxEndPoint;

			for( pxEndPoint = FreeRTOS_FirstEndPoint( pxNetworkBuffer->pxInterface );
				pxEndPoint != NULL;
				pxEndPoint = FreeRTOS_NextEndPoint( pxNetworkBuffer->pxInterface, pxEndPoint ) )
			{
				if( ( pxEndPoint->bits.bWantRA != pdFALSE_UNSIGNED ) && ( pxEndPoint->xRAData.eRAState == eRAStateWait ) )
				{
					pxEndPoint->ipv6_settings.uxPrefixLength = pxPrefixOption->ucPrefixLength;
					( void ) memcpy( pxEndPoint->ipv6_settings.xPrefix.ucBytes, pxPrefixOption->ucPrefix, ipSIZE_OF_IPv6_ADDRESS );
					( void ) memcpy( pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );

					pxEndPoint->xRAData.bits.bRouterReplied = pdTRUE_UNSIGNED;
					pxEndPoint->xRAData.uxRetryCount = 0UL;
					pxEndPoint->xRAData.ulPreferredLifeTime = FreeRTOS_ntohl( pxPrefixOption->ulPreferredLifeTime );
					/* Force taking a new random IP-address. */
					pxEndPoint->xRAData.bits.bIPAddressInUse = pdTRUE_UNSIGNED;
					pxEndPoint->xRAData.eRAState = eRAStateIPTest;
					vRAProcess( pdFALSE, pxEndPoint );
				}
			}
		}

	}
#endif	/* ( ipconfigUSE_RA != 0 ) */
/*-----------------------------------------------------------*/

#if( ipconfigUSE_RA != 0 )
static BaseType_t prvGetTestAddress( BaseType_t xIndex, IPv6_Address_t *pxIPAddress )
{
	( void ) xIndex;
	( void ) pxIPAddress;
	return 0;
#if 0
BaseType_t xResult;

	/* For testing only: return an IPv6 address that is already taken in the LAN. */
	const char *ip_address[] = {
		"fe80::6816:5e9b:80a0:9edb",	// laptop _HT_
		"fe80::9355:69c7:585a:afe7",	// raspberry
	};
	if( xIndex < ARRAY_SIZE( ip_address ) )
	{
		( void ) FreeRTOS_inet_pton6( ip_address[ xIndex ], pxIPAddress->ucBytes );
		xResult = pdPASS;
	}
	else
	{
		xResult = pdFAIL;
	}

	return xResult;
#endif /* 0 */
}
#endif	/* ( ipconfigUSE_RA != 0 ) */
/*-----------------------------------------------------------*/

#if( ipconfigUSE_RA != 0 )
	static void vRAProcessInit( NetworkEndPoint_t *pxEndPoint )
	{
		pxEndPoint->xRAData.uxRetryCount = 0;
		pxEndPoint->xRAData.eRAState = eRAStateApply;
	}
#endif	/* ( ipconfigUSE_RA != 0 ) */

#if( ipconfigUSE_RA != 0 )
	void vRAProcess( BaseType_t xDoReset, NetworkEndPoint_t *pxEndPoint )
	{
		configASSERT( pxEndPoint != NULL );
		
		if( ( pxEndPoint->bits.bIPv6 == pdFALSE_UNSIGNED ) ||
			( pxEndPoint->bits.bWantRA == pdFALSE_UNSIGNED ) )
		{
			/* For IPv4 end-points, or when RA is not enabled, disable the DHCP/RA timer. */
			vIPSetDHCP_RATimerEnableState( pxEndPoint, pdFALSE );
		}
		else
		{
		eRAState_t eRAState = pxEndPoint->xRAData.eRAState;
		TickType_t uxReloadTime = pdMS_TO_TICKS( 5000UL );
		BaseType_t xSkipLease = pdFALSE;

			if( xDoReset != pdFALSE )
			{
				vRAProcessInit( pxEndPoint );
			}
			switch( pxEndPoint->xRAData.eRAState )
			{
				case eRAStateWait:
					{
						/* A Router Solicitation has been sent, waited for a reply, but no came.
						All replies will be handled in the function prvReceiveRA(). */
						pxEndPoint->xRAData.uxRetryCount++;
						if( pxEndPoint->xRAData.uxRetryCount < ( UBaseType_t ) ipconfigRA_SEARCH_COUNT )
						{
							pxEndPoint->xRAData.eRAState = eRAStateApply;
						}
						else
						{
							FreeRTOS_printf( ( "RA: Giving up waiting for a Router.\n" ) );
							( void ) memcpy( &( pxEndPoint->ipv6_settings ), &( pxEndPoint->ipv6_defaults ), sizeof( pxEndPoint->ipv6_settings ) );

							pxEndPoint->xRAData.bits.bRouterReplied = pdFALSE_UNSIGNED;
							pxEndPoint->xRAData.uxRetryCount = 0UL;
							/* Force taking a new random IP-address. */
							pxEndPoint->xRAData.bits.bIPAddressInUse = pdTRUE_UNSIGNED;
							pxEndPoint->xRAData.eRAState = eRAStateIPTest;
						}
					}
					break;
				case eRAStateIPWait:
					{
						/* A Neighbour Solicitation has been sent, waited for a reply.
						Repeat this 'ipconfigRA_IP_TEST_COUNT' times to be sure. */
						if( pxEndPoint->xRAData.bits.bIPAddressInUse != pdFALSE_UNSIGNED )
						{
							/* Another device has responded with the same IPv4 address. */
							pxEndPoint->xRAData.uxRetryCount = 0UL;
							pxEndPoint->xRAData.eRAState = eRAStateIPTest;
							uxReloadTime = pdMS_TO_TICKS( ipconfigRA_IP_TEST_TIME_OUT_MSEC );
						}
						else if( pxEndPoint->xRAData.uxRetryCount < ( UBaseType_t ) ipconfigRA_IP_TEST_COUNT )
						{
							/* Try again. */
							pxEndPoint->xRAData.uxRetryCount++;
							pxEndPoint->xRAData.eRAState = eRAStateIPTest;
							uxReloadTime = pdMS_TO_TICKS( ipconfigRA_IP_TEST_TIME_OUT_MSEC );
						}
						else
						{
							/* Now it is assumed that there is no other device using the same IP-address. */
							if( pxEndPoint->xRAData.bits.bRouterReplied != pdFALSE_UNSIGNED )
							{
								/* Obtained configuration from a router. */
								uxReloadTime = pdMS_TO_TICKS( 1000UL * pxEndPoint->xRAData.ulPreferredLifeTime );
								pxEndPoint->xRAData.eRAState = eRAStateLease;
								xSkipLease = pdTRUE;
								iptraceRA_SUCCEDEED( &( pxEndPoint->ipv6_settings.xIPAddress ) );
								FreeRTOS_printf( ( "RA: succeeded, using IP address %pip\n", pxEndPoint->ipv6_settings.xIPAddress.ucBytes ) );
							}
							else
							{
								/* Using the default network parameters. */
								pxEndPoint->xRAData.eRAState = eRAStateFailed;

								iptraceRA_REQUESTS_FAILED_USING_DEFAULT_IP_ADDRESS( &( pxEndPoint->ipv6_settings.xIPAddress ) );

								FreeRTOS_printf( ( "RA: failed, using default parameters and IP address %pip\n", pxEndPoint->ipv6_settings.xIPAddress.ucBytes ) );
								/* Disable the timer. */
								uxReloadTime = 0UL;
							}
							/* Now call vIPNetworkUpCalls() to send the network-up event and
							start the ARP timer. */
							vIPNetworkUpCalls( pxEndPoint );
						}
					}
					break;
				case eRAStateApply:
				case eRAStateIPTest:
				case eRAStateLease:
				case eRAStateFailed:
				default:
					{
						/* Other states are handled here below. */
					}
					break;
			}
			switch( pxEndPoint->xRAData.eRAState )
			{
				case eRAStateApply:
					{
					IPv6_Address_t xIPAddress;
					size_t uxNeededSize;
					NetworkBufferDescriptor_t *pxNetworkBuffer;

						/* Send a Router Solicitation to ff:02::2 */
						( void ) memset( xIPAddress.ucBytes, 0, sizeof xIPAddress.ucBytes );
						xIPAddress.ucBytes[  0 ] = 0xff;
						xIPAddress.ucBytes[  1 ] = 0x02;
						xIPAddress.ucBytes[ 15 ] = 0x02;
						uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPRouterSolicitation_IPv6_t ) );
						pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxNeededSize, ndDONT_BLOCK );
						if( pxNetworkBuffer != NULL )
						{
							pxNetworkBuffer->pxEndPoint = pxEndPoint;
							vNDSendRouterSolicitation( pxNetworkBuffer, &( xIPAddress ) );
						}
						FreeRTOS_printf( ( "vRAProcess: Router Solicitation, attempt %lu/%u\n",
										   pxEndPoint->xRAData.uxRetryCount + 1U,
										   ipconfigRA_SEARCH_COUNT ) );
						/* Wait a configurable time for a router advertisement. */
						uxReloadTime = pdMS_TO_TICKS( ipconfigRA_SEARCH_TIME_OUT_MSEC );
						pxEndPoint->xRAData.eRAState = eRAStateWait;
					}
					break;
				case eRAStateWait:
					{
						/* Waiting for a router advertisement. */
						/* Handled here above. */
					}
					break;
				case eRAStateIPTest:	/* Assuming an IP address, test if another device is using it already. */
					{
					size_t uxNeededSize;
					NetworkBufferDescriptor_t *pxNetworkBuffer;

						/* Get an IP-address, using the network prefix and a random host address. */
						if( pxEndPoint->xRAData.bits.bIPAddressInUse != 0U )
						{
						static BaseType_t xUseIndex = 0;

							pxEndPoint->xRAData.bits.bIPAddressInUse = pdFALSE_UNSIGNED;
							if( prvGetTestAddress( xUseIndex, &( pxEndPoint->ipv6_settings.xIPAddress ) ) == pdPASS )
							{
								/* TESTING ONLY */
								xUseIndex++;
							}
							else
							{
								( void ) FreeRTOS_CreateIPv6Address( &pxEndPoint->ipv6_settings.xIPAddress, &pxEndPoint->ipv6_settings.xPrefix, pxEndPoint->ipv6_settings.uxPrefixLength, pdTRUE );
							}
							FreeRTOS_printf( ( "RA: Creating a random IP-address\n" ) );
						}
						FreeRTOS_printf( ( "RA: Neighbour solicitation for %pip\n", pxEndPoint->ipv6_settings.xIPAddress.ucBytes ) );

						uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t ) );
						pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxNeededSize, ndDONT_BLOCK );
						if( pxNetworkBuffer != NULL )
						{
							pxNetworkBuffer->pxEndPoint = pxEndPoint;
							vNDSendNeighbourSolicitation( pxNetworkBuffer, &( pxEndPoint->ipv6_settings.xIPAddress ) );
						}

						uxReloadTime = pdMS_TO_TICKS( 1000UL );
						pxEndPoint->xRAData.eRAState = eRAStateIPWait;
					}
					break;
				case eRAStateIPWait:
					{
						/* Assuming an IP address, test if another device is using it already. */
						/* Handled here above. */
					}
					break;
				case eRAStateLease:
					{
						if( xSkipLease == pdFALSE )
						{
							vRAProcessInit( pxEndPoint );
							uxReloadTime = pdMS_TO_TICKS( 1000UL );
						}
					}
					break;
				case eRAStateFailed:
					{
					}
					break;
				default:
					/* All states were handled. */
					break;
			}
			FreeRTOS_printf( ( "vRAProcess( %ld, %pip) bRouterReplied=%d bIPAddressInUse=%d state %d -> %d\n",
							   xDoReset,
							   pxEndPoint->ipv6_defaults.xIPAddress.ucBytes,
							   pxEndPoint->xRAData.bits.bRouterReplied,
							   pxEndPoint->xRAData.bits.bIPAddressInUse,
							   eRAState,
							   pxEndPoint->xRAData.eRAState ) );
			if( uxReloadTime != 0UL )
			{
				vIPReloadDHCP_RATimer( pxEndPoint, uxReloadTime );
			}
			else
			{
				/* Disable the timer, this function vRAProcess() won't be called anymore for this end-point. */
				FreeRTOS_printf( ( "RA: Disabled timer.\n" ) );
				vIPSetDHCP_RATimerEnableState( pxEndPoint, pdFALSE );
			}
		}
	}
#endif	/* ( ipconfigUSE_RA != 0 ) */
/*-----------------------------------------------------------*/

#if ( ipconfigSUPPORT_OUTGOING_PINGS == 1 )

	BaseType_t FreeRTOS_SendPingRequestIPv6( IPv6_Address_t *pxIPAddress, size_t uxNumberOfBytesToSend, TickType_t uxBlockTimeTicks )
	{
	NetworkBufferDescriptor_t *pxNetworkBuffer;
	EthernetHeader_t *pxEthernetHeader;
	ICMPPacket_IPv6_t *pxICMPPacket;
	ICMPEcho_IPv6_t *pxICMPHeader;
	BaseType_t xReturn = pdFAIL;
	static uint16_t usSequenceNumber = 0;
	uint8_t *pucChar;
	IPStackEvent_t xStackTxEvent = { eStackTxEvent, NULL };
	NetworkEndPoint_t *pxEndPoint;
	size_t uxPacketLength;
	
		pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv6( pxIPAddress );
		if( pxEndPoint == NULL )
		{
			pxEndPoint = FreeRTOS_FindGateWay( ( BaseType_t ) ipTYPE_IPv6 );
			if( pxEndPoint == NULL )
			{
				FreeRTOS_printf( ( "SendPingRequestIPv6: No routing/gw found" ) );
				return 0;	/*lint !e904 Return statement before end of function [MISRA 2012 Rule 15.5, advisory]. */
			}
			FreeRTOS_printf( ( "SendPingRequestIPv6: Using gw %pip", pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes ) );	/* access to 'ipv6_settings' is checked. */
		}
		uxPacketLength = sizeof( EthernetHeader_t ) + sizeof( IPHeader_IPv6_t ) + sizeof( ICMPEcho_IPv6_t ) + uxNumberOfBytesToSend;
		pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( uxPacketLength, uxBlockTimeTicks );

		if( pxNetworkBuffer != NULL )
		{
		BaseType_t xEnoughSpace;

			/* Probably not necessary to clear the buffer. */
			( void ) memset( pxNetworkBuffer->pucEthernetBuffer, 0, pxNetworkBuffer->xDataLength);

			pxNetworkBuffer->pxEndPoint = ipPOINTER_CAST( struct xNetworkEndPoint *, pxEndPoint );
			pxICMPPacket = ipPOINTER_CAST( ICMPPacket_IPv6_t *, pxNetworkBuffer->pucEthernetBuffer );
			if( uxNumberOfBytesToSend < ( ( ipconfigNETWORK_MTU - sizeof( IPHeader_IPv6_t ) ) - sizeof( ICMPEcho_IPv6_t ) ) )
			{
				xEnoughSpace = pdTRUE;
			}
			else
			{
				xEnoughSpace = pdFALSE;
			}
			if( ( uxGetNumberOfFreeNetworkBuffers() >= 3U ) && ( uxNumberOfBytesToSend >= 1U ) && ( xEnoughSpace != pdFALSE ) )
			{
				pxICMPHeader = ipPOINTER_CAST( ICMPEcho_IPv6_t *, &( pxICMPPacket->xICMPHeader_IPv6 ) );
				usSequenceNumber++;

				pxICMPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;

				configASSERT( pxEndPoint != NULL );
				configASSERT( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED );

				pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( sizeof( ICMPEcho_IPv6_t ) + uxNumberOfBytesToSend );
				( void ) memcpy( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
				( void ) memcpy( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS );
				pxICMPPacket->xIPHeader.ucVersionTrafficClass = 0x60;
				pxICMPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
				pxICMPPacket->xIPHeader.ucHopLimit = 128;

				/* Fill in the basic header information. */
				pxICMPHeader->ucTypeOfMessage = ipICMP_PING_REQUEST_IPv6;
				pxICMPHeader->ucTypeOfService = 0;
				pxICMPHeader->usIdentifier = usSequenceNumber;
				pxICMPHeader->usSequenceNumber = usSequenceNumber;

				/* Find the start of the data. */
				pucChar = ( uint8_t * ) pxICMPHeader;
				pucChar = &( pucChar[ sizeof( ICMPEcho_IPv6_t ) ] );

				/* Just memset the data to a fixed value. */
				( void ) memset( pucChar, ( int ) ndECHO_DATA_FILL_BYTE, uxNumberOfBytesToSend );

				/* The message is complete, IP and checksum's are handled by
				vProcessGeneratedUDPPacket */
				pxNetworkBuffer->pucEthernetBuffer[ ipSOCKET_OPTIONS_OFFSET ] = FREERTOS_SO_UDPCKSUM_OUT;
				pxNetworkBuffer->ulIPAddress = 0UL;
				( void ) memcpy( pxNetworkBuffer->xIPv6_Address.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
				/* Let vProcessGeneratedUDPPacket() know that this is an ICMP packet. */
				pxNetworkBuffer->usPort = ipPACKET_CONTAINS_ICMP_DATA;
				pxNetworkBuffer->xDataLength = uxPacketLength;

				pxEthernetHeader = ipPOINTER_CAST( EthernetHeader_t *, pxNetworkBuffer->pucEthernetBuffer );
				pxEthernetHeader->usFrameType = ipIPv6_FRAME_TYPE;

				/* Send to the stack. */
				xStackTxEvent.pvData = pxNetworkBuffer;

				if( xSendEventStructToIPTask( &xStackTxEvent, uxBlockTimeTicks) != pdPASS )
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

static const char *pcMessageType( BaseType_t xType )
{
	const char *pcReturn;
	switch( ( uint8_t ) xType )
	{
		case ipICMP_DEST_UNREACHABLE_IPv6:        pcReturn = "DEST_UNREACHABLE"; break;
		case ipICMP_PACKET_TOO_BIG_IPv6:          pcReturn = "PACKET_TOO_BIG"; break;
		case ipICMP_TIME_EXEEDED_IPv6:            pcReturn = "TIME_EXEEDED"; break;
		case ipICMP_PARAMETER_PROBLEM_IPv6:       pcReturn = "PARAMETER_PROBLEM"; break;
		case ipICMP_PING_REQUEST_IPv6:            pcReturn = "PING_REQUEST"; break;
		case ipICMP_PING_REPLY_IPv6:              pcReturn = "PING_REPLY"; break;
		case ipICMP_ROUTER_SOLICITATION_IPv6:     pcReturn = "ROUTER_SOL"; break;
		case ipICMP_ROUTER_ADVERTISEMENT_IPv6:    pcReturn = "ROUTER_ADV"; break;
		case ipICMP_NEIGHBOR_SOLICITATION_IPv6:   pcReturn = "NEIGHBOR_SOL"; break;
		case ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6:  pcReturn = "NEIGHBOR_ADV"; break;
		default:                                  pcReturn = "UNKNOWN ICMP"; break;
	}
	return pcReturn;
}
/*-----------------------------------------------------------*/

eFrameProcessingResult_t prvProcessICMPMessage_IPv6( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
ICMPPacket_IPv6_t *pxICMPPacket = ipPOINTER_CAST( ICMPPacket_IPv6_t *, pxNetworkBuffer->pucEthernetBuffer );
ICMPHeader_IPv6_t *xICMPHeader_IPv6 = ipPOINTER_CAST( ICMPHeader_IPv6_t *, &( pxICMPPacket->xICMPHeader_IPv6 ) );
NetworkEndPoint_t *pxEndPoint = pxNetworkBuffer->pxEndPoint;
size_t uxNeededSize;

	if( xICMPHeader_IPv6->ucTypeOfMessage != ipICMP_PING_REQUEST_IPv6 )
	{
		FreeRTOS_printf( ( "ICMPv6 %d (%s) from %pip to %pip end-point = %d\n",
			xICMPHeader_IPv6->ucTypeOfMessage,
			pcMessageType( ( BaseType_t ) xICMPHeader_IPv6->ucTypeOfMessage ),
			pxICMPPacket->xIPHeader.xSourceAddress.ucBytes,
			pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes,
			( ( pxEndPoint != NULL ) && ( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED ) ) ? 1 : 0 ) );
	}
	if( ( pxEndPoint != NULL ) && ( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED ) )
	{
		switch( xICMPHeader_IPv6->ucTypeOfMessage )
		{
			default:
			case ipICMP_DEST_UNREACHABLE_IPv6:
			case ipICMP_PACKET_TOO_BIG_IPv6:
			case ipICMP_TIME_EXEEDED_IPv6:
			case ipICMP_PARAMETER_PROBLEM_IPv6:
				/* These message types are not implemented. They are logged here above. */
				break;
			case ipICMP_PING_REQUEST_IPv6 :
				{
				size_t uxICMPSize;
				uint16_t usICMPSize;

					/* Lint would complain about casting '()' immediately. */
					usICMPSize = FreeRTOS_ntohs( pxICMPPacket->xIPHeader.usPayloadLength );
					uxICMPSize = ( size_t ) usICMPSize;
					uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
					if( uxNeededSize > pxNetworkBuffer->xDataLength )
					{
						FreeRTOS_printf( ("Too small\n" ) );
						break;
					}

					xICMPHeader_IPv6->ucTypeOfMessage = ipICMP_PING_REPLY_IPv6;
					prvReturnICMP_IPv6( pxNetworkBuffer, uxICMPSize );
				}
				break;
			#if( ipconfigSUPPORT_OUTGOING_PINGS != 0 )
			case ipICMP_PING_REPLY_IPv6:
				{
				ePingReplyStatus_t eStatus = eSuccess;
				ICMPEcho_IPv6_t * pxICMPEchoHeader = ipPOINTER_CAST( ICMPEcho_IPv6_t *, xICMPHeader_IPv6 );
				size_t uxDataLength, uxCount;
				const uint8_t * pucByte;

					/* Find the total length of the IP packet. */
					uxDataLength = ipNUMERIC_CAST( size_t, FreeRTOS_ntohs( pxICMPPacket->xIPHeader.usPayloadLength ) );
					uxDataLength = uxDataLength - sizeof( *pxICMPEchoHeader );

					/* Find the first byte of the data within the ICMP packet. */
					pucByte = ( const uint8_t * ) pxICMPEchoHeader;
					pucByte = &( pucByte[ sizeof( *pxICMPEchoHeader ) ] );

					/* Check each byte. */
					for( uxCount = 0; uxCount < uxDataLength; uxCount++ )
					{
						if( *pucByte != ( uint8_t ) ipECHO_DATA_FILL_BYTE )
						{
							eStatus = eInvalidData;
							break;
						}

						pucByte++;
					}
					/* Call back into the application to pass it the result. */
					vApplicationPingReplyHook( eStatus, pxICMPEchoHeader->usIdentifier );
				}
				break;
			#endif	/* ( ipconfigSUPPORT_OUTGOING_PINGS != 0 ) */
			case ipICMP_NEIGHBOR_SOLICITATION_IPv6 :
				{
				size_t uxICMPSize;

					uxICMPSize = sizeof( ICMPHeader_IPv6_t );
					uxNeededSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );
					if( uxNeededSize > pxNetworkBuffer->xDataLength )
					{
						FreeRTOS_printf( ("Too small\n" ) );
						break;
					}
					xICMPHeader_IPv6->ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
					xICMPHeader_IPv6->ucTypeOfService = 0;
					xICMPHeader_IPv6->ulReserved = ndICMPv6_FLAG_SOLICITED | ndICMPv6_FLAG_UPDATE;
					xICMPHeader_IPv6->ulReserved = FreeRTOS_htonl( xICMPHeader_IPv6->ulReserved );

					/* Type of option. */
					xICMPHeader_IPv6->ucOptionType = ndICMP_TARGET_LINK_LAYER_ADDRESS;
					/* Length of option in units of 8 bytes. */
					xICMPHeader_IPv6->ucOptionLength = 1;
					( void ) memcpy( xICMPHeader_IPv6->ucOptionBytes, pxEndPoint->xMACAddress.ucBytes, sizeof( MACAddress_t ) );
					pxICMPPacket->xIPHeader.ucHopLimit = 255;
					( void ) memcpy( xICMPHeader_IPv6->xIPv6_Address.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, sizeof( xICMPHeader_IPv6->xIPv6_Address.ucBytes ) );

					prvReturnICMP_IPv6( pxNetworkBuffer, uxICMPSize );
				}
				break;
			case ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6:
				{
					vNDRefreshCacheEntry( ipPOINTER_CAST( MACAddress_t *, xICMPHeader_IPv6->ucOptionBytes ),
										  &( xICMPHeader_IPv6->xIPv6_Address ),
										  pxEndPoint );
					FreeRTOS_printf( ( "NA from %pip\n",
									   xICMPHeader_IPv6->xIPv6_Address.ucBytes ) );

				#if( ipconfigUSE_RA != 0 )
					{
					NetworkInterface_t *pxInterface = pxNetworkBuffer->pxInterface;
					NetworkEndPoint_t *pxPoint;
						for( pxPoint = FreeRTOS_FirstEndPoint( pxInterface );
							pxPoint != NULL;
							pxPoint = FreeRTOS_NextEndPoint( pxInterface, pxPoint ) )
						{
							if( ( pxPoint->bits.bWantRA != pdFALSE_UNSIGNED ) && ( pxPoint->xRAData.eRAState == eRAStateIPWait ) )
							{
								if( memcmp( pxPoint->ipv6_settings.xIPAddress.ucBytes, &( xICMPHeader_IPv6->xIPv6_Address ), ipSIZE_OF_IPv6_ADDRESS ) == 0 )
								{
									pxPoint->xRAData.bits.bIPAddressInUse = pdTRUE_UNSIGNED;
									vIPReloadDHCP_RATimer( pxPoint, 100UL );
								}
							}
						}
					}
				#endif	/* ( ipconfigUSE_RA != 0 ) */
				}
				break;
			case ipICMP_ROUTER_SOLICITATION_IPv6:
				{
				}
				break;
			#if( ipconfigUSE_RA != 0 )
			case ipICMP_ROUTER_ADVERTISEMENT_IPv6:
				{
					prvReceiveRA( pxNetworkBuffer );
				}
				break;
			#endif	/* ( ipconfigUSE_RA != 0 ) */
		}	/* switch( xICMPHeader_IPv6->ucTypeOfMessage ) */
	}	/* if( pxEndPoint != NULL ) */

	return eReleaseBuffer;
//	return eFrameConsumed;
//	return eReturnEthernetFrame;
}
/*-----------------------------------------------------------*/

void FreeRTOS_OutputAdvertiseIPv6( NetworkEndPoint_t *pxEndPoint )
{
NetworkBufferDescriptor_t *pxNetworkBuffer;
ICMPPacket_IPv6_t *pxICMPPacket;
NetworkInterface_t *pxInterface;
ICMPHeader_IPv6_t *pxICMPHeader_IPv6;
size_t uxICMPSize;
size_t xPacketSize;

	xPacketSize = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + sizeof( ICMPHeader_IPv6_t ) );

	/* This is called from the context of the IP event task, so a block time
	must not be used. */
	pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( xPacketSize, ndDONT_BLOCK );
	if( pxNetworkBuffer != NULL )
	{
		pxNetworkBuffer->ulIPAddress = 0;
		pxNetworkBuffer->pxEndPoint = pxEndPoint;

		pxInterface = pxEndPoint->pxNetworkInterface;

		configASSERT( pxInterface != NULL );

		pxICMPPacket = ipPOINTER_CAST( ICMPPacket_IPv6_t *, pxNetworkBuffer->pucEthernetBuffer );
		pxICMPHeader_IPv6 = ipPOINTER_CAST( ICMPHeader_IPv6_t *, &( pxICMPPacket->xICMPHeader_IPv6 ) );

		( void ) memcpy( pxICMPPacket->xEthernetHeader.xDestinationAddress.ucBytes, pcLOCAL_NETWORK_MULTICAST_MAC, ipMAC_ADDRESS_LENGTH_BYTES );
		( void ) memcpy( pxICMPPacket->xEthernetHeader.xSourceAddress.ucBytes, pxEndPoint->xMACAddress.ucBytes, ipMAC_ADDRESS_LENGTH_BYTES );
		pxICMPPacket->xEthernetHeader.usFrameType = ipIPv6_FRAME_TYPE;              /* 12 + 2 = 14 */

		pxICMPPacket->xIPHeader.ucVersionTrafficClass = 0x60;
		pxICMPPacket->xIPHeader.ucTrafficClassFlow = 0;
		pxICMPPacket->xIPHeader.usFlowLabel = 0;

		pxICMPPacket->xIPHeader.usPayloadLength = FreeRTOS_htons( sizeof( ICMPHeader_IPv6_t ) );/*lint !e845: (Info -- The right argument to operator '|' is certain to be 0. */
		pxICMPPacket->xIPHeader.ucNextHeader = ipPROTOCOL_ICMP_IPv6;
		pxICMPPacket->xIPHeader.ucHopLimit = 255;
		( void ) memcpy( pxICMPPacket->xIPHeader.xSourceAddress.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, 16 );
		( void ) memcpy( pxICMPPacket->xIPHeader.xDestinationAddress.ucBytes, pcLOCAL_NETWORK_MULTICAST_IP, 16 );

		uxICMPSize = sizeof( ICMPHeader_IPv6_t );
		pxICMPHeader_IPv6->ucTypeOfMessage = ipICMP_NEIGHBOR_ADVERTISEMENT_IPv6;
		pxICMPHeader_IPv6->ucTypeOfService = 0;
		pxICMPHeader_IPv6->ulReserved = ndICMPv6_FLAG_SOLICITED | ndICMPv6_FLAG_UPDATE;
		pxICMPHeader_IPv6->ulReserved = FreeRTOS_htonl( pxICMPHeader_IPv6->ulReserved );

		/* Type of option. */
		pxICMPHeader_IPv6->ucOptionType = ndICMP_TARGET_LINK_LAYER_ADDRESS;
		/* Length of option in units of 8 bytes. */
		pxICMPHeader_IPv6->ucOptionLength = 1;
		( void ) memcpy( pxICMPHeader_IPv6->ucOptionBytes, pxEndPoint->xMACAddress.ucBytes, sizeof( MACAddress_t ) );
		pxICMPPacket->xIPHeader.ucHopLimit = 255;
		( void ) memcpy( pxICMPHeader_IPv6->xIPv6_Address.ucBytes, pxEndPoint->ipv6_settings.xIPAddress.ucBytes, sizeof( pxICMPHeader_IPv6->xIPv6_Address.ucBytes ) );

		/* Important: tell NIC driver how many bytes must be sent */
		pxNetworkBuffer->xDataLength = ( size_t ) ( ipSIZE_OF_ETH_HEADER + ipSIZE_OF_IPv6_HEADER + uxICMPSize );

		pxICMPHeader_IPv6->usChecksum = 0;
		/* calculate the UDP checksum for outgoing package */
		( void ) usGenerateProtocolChecksum( pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, pdTRUE );

		/* Set the parameter 'bReleaseAfterSend'. */
		( void ) pxInterface->pfOutput( pxInterface, pxNetworkBuffer, pdTRUE );
	}
}
/*-----------------------------------------------------------*/

BaseType_t FreeRTOS_CreateIPv6Address( IPv6_Address_t *pxIPAddress, const IPv6_Address_t *pxPrefix, size_t uxPrefixLength, BaseType_t xDoRandom )
{
uint32_t pulRandom[ 4 ];
uint8_t *pucSource;
BaseType_t xIndex, xResult = pdPASS;

	if( xDoRandom != pdFALSE )
	{
		/* Create an IP-address, based on a net prefix and a random host address. */
		for( xIndex = 0; xIndex < ARRAY_SIZE( pulRandom ); xIndex++ )
		{
			if( xApplicationGetRandomNumber( &( pulRandom[ xIndex ] ) ) == pdFAIL )
			{
				xResult = pdFAIL;
				break;
			}
		}
	}
	else
	{
		( void ) memset( pulRandom, 0, sizeof pulRandom );
	}
	if( xResult == pdPASS )
	{
		configASSERT( ( uxPrefixLength > 0U ) && ( uxPrefixLength < ( 8U * ipSIZE_OF_IPv6_ADDRESS ) ) );
		( void ) memcpy( pxIPAddress->ucBytes, pxPrefix->ucBytes, ( uxPrefixLength + 7U ) / 8U );
		pucSource = ipPOINTER_CAST( uint8_t *, pulRandom );
		size_t uxIndex = uxPrefixLength / 8U;
		if( ( uxPrefixLength % 8U ) != 0U )
		{
		/* uxHostLen is between 1 and 7 bits long. */
		size_t uxHostLen = 8U - ( uxPrefixLength % 8U );
		uint32_t uxHostMask = ( ( ( uint32_t ) 1U ) << uxHostLen ) - 1U;
		uint8_t ucNetMask = ( uint8_t ) ~( uxHostMask );

			pxIPAddress->ucBytes[ uxIndex ] &= ucNetMask;
			pxIPAddress->ucBytes[ uxIndex ] |= ( pucSource[ 0 ] & ( ( uint8_t ) uxHostMask ) );
			pucSource = &( pucSource[ 1 ] );
			uxIndex++;
		}
		if( uxIndex < ipSIZE_OF_IPv6_ADDRESS )
		{
			( void ) memcpy( &( pxIPAddress->ucBytes[ uxIndex ] ), pucSource, ipSIZE_OF_IPv6_ADDRESS - uxIndex );
		}
	}
	return xResult;
}
/*-----------------------------------------------------------*/

#endif /* ipconfigUSE_IPv6 */

