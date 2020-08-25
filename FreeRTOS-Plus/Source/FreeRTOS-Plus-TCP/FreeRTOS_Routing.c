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
	
/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
/*lint -e766 -e595 */
#include "NetworkBufferManagement.h"
#if( ipconfigUSE_LLMNR == 1 )
	#include "FreeRTOS_DNS.h"
#endif /* ipconfigUSE_LLMNR */
#include "FreeRTOS_Routing.h"

/* A list of all network end-points: */
struct xNetworkEndPoint *pxNetworkEndPoints = NULL;

/* A list of all network interfaces: */
struct xNetworkInterface *pxNetworkInterfaces = NULL;

RoutingStats_t xRoutingStats;

/*
 * Add a new IP-address to a Network Interface.  The object pointed to by
 * 'pxEndPoint' must continue to exist.
 */
static NetworkEndPoint_t *FreeRTOS_AddEndPoint( NetworkInterface_t *pxInterface, NetworkEndPoint_t *pxEndPoint );

/*-----------------------------------------------------------*/

NetworkInterface_t *FreeRTOS_AddNetworkInterface( NetworkInterface_t *pxInterface )
{
NetworkInterface_t *pxIterator = NULL;

	/* This interface will be added to the end of the list of interfaces, so
	there is no pxNext yet. */
	pxInterface->pxNext = NULL;

	/* The end point for this interface has not yet been set. */
	/*_RB_ As per other comments, why not set the end point at the same time? */
	pxInterface->pxEndPoint = NULL;

	if( pxNetworkInterfaces == NULL )
	{
		/* No other interfaces are set yet, so this is the first in the list. */
		pxNetworkInterfaces = pxInterface;
	}
	else
	{
		/* Other interfaces are already defined, so iterate to the end of the
		list. */
		/*_RB_ Question - if ipconfigMULTI_INTERFACE is used to define the
		maximum number of interfaces, would it be more efficient to have an
		array of interfaces rather than a linked list of interfaces? */
		pxIterator = pxNetworkInterfaces;
		for( ;; )
		{
			if( pxIterator == pxInterface )
			{
				/* This interface was already added. */
				break;
			}
			if( pxIterator->pxNext == NULL )
			{
				pxIterator->pxNext = pxInterface;
				break;	/*lint !e9011: (Note -- more than one 'break' terminates loop [MISRA 2012 Rule 15.4, advisory]. */
			}
			pxIterator = pxIterator->pxNext;
		}
	}

	return pxInterface;
}
/*-----------------------------------------------------------*/

/* Get the first Network Interface. */
NetworkInterface_t *FreeRTOS_FirstNetworkInterface( void )
{
	return pxNetworkInterfaces;
}
/*-----------------------------------------------------------*/

/* Get the next Network Interface. */
NetworkInterface_t *FreeRTOS_NextNetworkInterface( NetworkInterface_t *pxInterface )
{
NetworkInterface_t *pxReturn;

	if( pxInterface != NULL )
	{
		pxReturn = pxInterface->pxNext;
	}
	else
	{
		pxReturn = NULL;
	}
	return pxReturn;
}
/*-----------------------------------------------------------*/

static NetworkEndPoint_t *FreeRTOS_AddEndPoint( NetworkInterface_t *pxInterface, NetworkEndPoint_t *pxEndPoint )
{
NetworkEndPoint_t *pxIterator = NULL;

	/* This end point will go to the end of the list, so there is no pxNext
	yet. */
	pxEndPoint->pxNext = NULL;

	/* Double link between the NetworkInterface_t that is using the addressing
	defined by this NetworkEndPoint_t structure. */
	pxEndPoint->pxNetworkInterface = pxInterface;
	if( pxInterface->pxEndPoint == NULL )
	{
		/*_RB_ When would pxInterface->pxEndPoint ever not be NULL unless this is called twice? */
		/*_HT_ It may be called twice. */
		pxInterface->pxEndPoint = pxEndPoint;
	}

	if( pxNetworkEndPoints == NULL )
	{
		/* No other end points are defined yet - so this is the first in the
		list. */
		pxNetworkEndPoints = pxEndPoint;
	}
	else
	{
		/* Other end points are already defined so iterate to the end of the
		list. */
		pxIterator = pxNetworkEndPoints;
		for( ;; )
		{
			if( pxIterator == pxEndPoint )
			{
				/* This end-point has already been added to the list. */
				break;
			}
			if( pxIterator->pxNext == NULL )
			{
				pxIterator->pxNext = pxEndPoint;
				break;	/*lint !e9011: (Note -- more than one 'break' terminates loop [MISRA 2012 Rule 15.4, advisory]. */
			}
			pxIterator = pxIterator->pxNext;
		}
	}

#if( ipconfigUSE_IPv6 != 0 )
	if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
	{
		FreeRTOS_printf( ( "FreeRTOS_AddEndPoint: MAC: %02x-%02x IPv6: %pip\n",
			pxEndPoint->xMACAddress.ucBytes[ 4 ],
			pxEndPoint->xMACAddress.ucBytes[ 5 ],
			pxEndPoint->ipv6_defaults.xIPAddress.ucBytes ) );
	}
	else
#endif
	{
		FreeRTOS_printf( ( "FreeRTOS_AddEndPoint: MAC: %02x-%02x IPv4: %lxip\n",
			pxEndPoint->xMACAddress.ucBytes[ 4 ],
			pxEndPoint->xMACAddress.ucBytes[ 5 ],
			FreeRTOS_ntohl( pxEndPoint->ipv4_defaults.ulIPAddress ) ) );
	}

	return pxEndPoint;
}
/*-----------------------------------------------------------*/

NetworkEndPoint_t *FreeRTOS_FirstEndPoint( NetworkInterface_t *pxInterface )
{
NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;

	/* Find and return the NetworkEndPoint_t structure that is associated with
	the pxInterface NetworkInterface_t. *//*_RB_ Could this be made a two way link, so the NetworkEndPoint_t can just be read from the NetworkInterface_t structure?  Looks like there is a pointer in the struct already. */
	while( pxEndPoint != NULL )
	{
		if( ( pxInterface == NULL ) || ( pxEndPoint->pxNetworkInterface == pxInterface ) )
		{
			break;
		}
		pxEndPoint = pxEndPoint->pxNext;
	}

	return pxEndPoint;
}
/*-----------------------------------------------------------*/

/* Get the next end-point.  When pxInterface is null, all end-points can be iterated. */
NetworkEndPoint_t *FreeRTOS_NextEndPoint( NetworkInterface_t *pxInterface, NetworkEndPoint_t *pxEndPoint )
{
NetworkEndPoint_t *pxResult = pxEndPoint;

	if( pxResult != NULL )
	{
		pxResult = pxResult->pxNext;
		while( pxResult != NULL )
		{
			if( ( pxInterface == NULL ) || ( pxResult->pxNetworkInterface == pxInterface ) )
			{
				break;
			}
			pxResult = pxResult->pxNext;
		}
	}

	return pxResult;
}
/*-----------------------------------------------------------*/

/* Find the end-point with given IP-address. */
NetworkEndPoint_t *FreeRTOS_FindEndPointOnIP_IPv4( uint32_t ulIPAddress, uint32_t ulWhere )
{
NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;

	xRoutingStats.ulOnIp++;
	if( ulWhere < ARRAY_SIZE( xRoutingStats.ulLocationsIP ) )
	{
		xRoutingStats.ulLocationsIP[ ulWhere ]++;
	}
	while( pxEndPoint != NULL )
	{
		if( ENDPOINT_IS_IPv4( pxEndPoint ) )
		{
			if( ( ulIPAddress == 0UL ) || ( pxEndPoint->ipv4_settings.ulIPAddress == ulIPAddress ) )/*lint !e506 !e774 */
			{
				break;
			}
		}

		pxEndPoint = pxEndPoint->pxNext;
	}

	return pxEndPoint;
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_IPv6 != 0 )
	/* Find the end-point with given IP-address. */
	NetworkEndPoint_t *FreeRTOS_FindEndPointOnIP_IPv6( const IPv6_Address_t *pxIPAddress )
	{
	NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;

		while( pxEndPoint != NULL )
		{
			if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
			{
				if( xCompareIPv6_Address( &( pxEndPoint->ipv6_settings.xIPAddress ), pxIPAddress, pxEndPoint->ipv6_settings.uxPrefixLength ) == 0 )
				{
					break;
				}
			}
			pxEndPoint = pxEndPoint->pxNext;
		}

		return pxEndPoint;
	}
#endif /* ipconfigUSE_IPv6 */
/*-----------------------------------------------------------*/

NetworkEndPoint_t *FreeRTOS_FindEndPointOnMAC( const MACAddress_t *pxMACAddress, NetworkInterface_t *pxInterface )
{
NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;

	xRoutingStats.ulOnMAC++;
	/*_RB_ Question - would it be more efficient to store the mac addresses in
	uin64_t variables for direct comparison instead of using memcmp()?  [don't
	know if there is a quick way of creating a 64-bit number from the 48-byte
	MAC address without getting junk in the top 2 bytes]. */

	/* Find the end-point with given MAC-address. */
	while( pxEndPoint != NULL )
	{
		if( ( pxInterface == NULL ) || ( pxInterface == pxEndPoint->pxNetworkInterface ) )
		{
			if( memcmp( pxEndPoint->xMACAddress.ucBytes, pxMACAddress->ucBytes, ipMAC_ADDRESS_LENGTH_BYTES ) == 0 )
			{
				break;
			}
		}
		pxEndPoint = pxEndPoint->pxNext;
	}

	return pxEndPoint;
}
/*-----------------------------------------------------------*/

NetworkEndPoint_t *FreeRTOS_FindEndPointOnNetMask( uint32_t ulIPAddress, uint32_t ulWhere )
{
	/* The 'ulWhere' parameter is only for debugging puposes. */
	return FreeRTOS_InterfaceEndPointOnNetMask( NULL, ulIPAddress, ulWhere );
}
/*-----------------------------------------------------------*/

NetworkEndPoint_t *FreeRTOS_InterfaceEndPointOnNetMask( NetworkInterface_t *pxInterface, uint32_t ulIPAddress, uint32_t ulWhere )
{
NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;

	xRoutingStats.ulOnNetMask++;
	if( ulWhere < ARRAY_SIZE( xRoutingStats.ulLocations ) )
	{
		xRoutingStats.ulLocations[ ulWhere ]++;
	}
	/* Find the best fitting end-point to reach a given IP-address. */
	/*_RB_ Presumably then a broadcast reply could go out on a different end point to that on which the broadcast was received - although that should not be an issue if the nodes are on the same LAN it could be an issue if the nodes are on separate LANs. */

	while( pxEndPoint != NULL )
	{
		if( ( pxInterface == NULL ) || ( pxEndPoint->pxNetworkInterface == pxInterface ) )
		{
#if( ipconfigUSE_IPv6 != 0 )
			if( pxEndPoint->bits.bIPv6 == pdFALSE_UNSIGNED )
#endif
			{
				if( ( ulIPAddress & pxEndPoint->ipv4_settings.ulNetMask ) == ( pxEndPoint->ipv4_settings.ulIPAddress & pxEndPoint->ipv4_settings.ulNetMask ) )
				{
					/* Found a match. */
					break;
				}
			}
		}

		pxEndPoint = pxEndPoint->pxNext;
	}

	if( ( pxEndPoint == NULL ) && ( ulWhere != 1UL ) && ( ulWhere != 2UL ) )
	{
		FreeRTOS_printf( ( "FreeRTOS_FindEndPointOnNetMask[%ld]: No match for %lxip\n",
			ulWhere, FreeRTOS_ntohl( ulIPAddress ) ) );
	}

	return pxEndPoint;
}
/*-----------------------------------------------------------*/

/* A helper function to fill in a network end-point,
and add it to a network interface. */
void FreeRTOS_FillEndPoint(	NetworkInterface_t *pxNetworkInterface,
							NetworkEndPoint_t *pxEndPoint,
							const uint8_t ucIPAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
							const uint8_t ucNetMask[ ipIP_ADDRESS_LENGTH_BYTES ],
							const uint8_t ucGatewayAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
							const uint8_t ucDNSServerAddress[ ipIP_ADDRESS_LENGTH_BYTES ],
							const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] )
{
uint32_t ulIPAddress;

	/* Fill in and add an end-point to a network interface.
	The user must make sure that the object pointed to by 'pxEndPoint'
	will remain to exist. */
	( void ) memset( pxEndPoint, 0, sizeof( *pxEndPoint ) );

	/* All is cleared, also the IPv6 flag. */
	/* pxEndPoint->bits.bIPv6 = pdFALSE; */

	ulIPAddress                                         = FreeRTOS_inet_addr_quick( ucIPAddress[ 0 ], ucIPAddress[ 1 ], ucIPAddress[ 2 ], ucIPAddress[ 3 ] );
	pxEndPoint->ipv4_settings.ulNetMask                 = FreeRTOS_inet_addr_quick( ucNetMask[ 0 ], ucNetMask[ 1 ], ucNetMask[ 2 ], ucNetMask[ 3 ] );
	pxEndPoint->ipv4_settings.ulGatewayAddress          = FreeRTOS_inet_addr_quick( ucGatewayAddress[ 0 ], ucGatewayAddress[ 1 ], ucGatewayAddress[ 2 ], ucGatewayAddress[ 3 ] );
	pxEndPoint->ipv4_settings.ulDNSServerAddresses[ 0 ] = FreeRTOS_inet_addr_quick( ucDNSServerAddress[ 0 ], ucDNSServerAddress[ 1 ], ucDNSServerAddress[ 2 ], ucDNSServerAddress[ 3 ] );
	pxEndPoint->ipv4_settings.ulBroadcastAddress        = ulIPAddress | ~( pxEndPoint->ipv4_settings.ulNetMask );

	/* Copy the current values to the default values. */
	( void ) memcpy( &( pxEndPoint->ipv4_defaults ), &( pxEndPoint->ipv4_settings ), sizeof( pxEndPoint->ipv4_defaults ) );

	/* The default IP-address will be used in case DHCP is not used, or also if DHCP has failed, or
	when the user chooses to use the default IP-address. */
	pxEndPoint->ipv4_defaults.ulIPAddress = ulIPAddress;
	
	/* The field 'ipv4_settings.ulIPAddress' will be set later on. */

	( void ) memcpy( pxEndPoint->xMACAddress.ucBytes, ucMACAddress, sizeof( pxEndPoint->xMACAddress ) );
	( void ) FreeRTOS_AddEndPoint( pxNetworkInterface, pxEndPoint );
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_IPv6 != 0 )
	/* Fill-in the end-point structure. */
	void FreeRTOS_FillEndPoint_IPv6( NetworkInterface_t *pxNetworkInterface,
									 NetworkEndPoint_t *pxEndPoint,
									 IPv6_Address_t *pxIPAddress,
									 IPv6_Address_t *pxNetPrefix,
									 size_t uxPrefixLength,
									 IPv6_Address_t *pxGatewayAddress,
									 IPv6_Address_t *pxDNSServerAddress,
									 const uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ] )
	{
		/* Fill in and add an end-point to a network interface.
		Make sure that the object pointed to by 'pxEndPoint'
		will remain to exist. */
		( void ) memset( pxEndPoint, 0, sizeof( *pxEndPoint ) );

		configASSERT( pxIPAddress != NULL );
		configASSERT( ucMACAddress != NULL );

		pxEndPoint->bits.bIPv6 = pdTRUE_UNSIGNED;

		pxEndPoint->ipv6_settings.uxPrefixLength = uxPrefixLength;

		if( pxGatewayAddress != NULL )
		{
			( void ) memcpy( pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, pxGatewayAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
		}
		if( pxDNSServerAddress != NULL )
		{
			( void ) memcpy( pxEndPoint->ipv6_settings.xDNSServerAddresses[ 0 ].ucBytes, pxDNSServerAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
		}
		if( pxNetPrefix != NULL )
		{
			( void ) memcpy( pxEndPoint->ipv6_settings.xPrefix.ucBytes, pxNetPrefix->ucBytes, ipSIZE_OF_IPv6_ADDRESS );
		}

		/* Copy the current values to the default values. */
		( void ) memcpy( &( pxEndPoint->ipv6_defaults ), &( pxEndPoint->ipv6_settings ), sizeof( pxEndPoint->ipv6_defaults ) );

		( void ) memcpy( pxEndPoint->ipv6_defaults.xIPAddress.ucBytes, pxIPAddress->ucBytes, ipSIZE_OF_IPv6_ADDRESS );

		( void ) memcpy( pxEndPoint->xMACAddress.ucBytes, ucMACAddress, ipMAC_ADDRESS_LENGTH_BYTES );
		( void ) FreeRTOS_AddEndPoint( pxNetworkInterface, pxEndPoint );
	}
#endif
/*-----------------------------------------------------------*/

#if( ipconfigUSE_IPv6 != 0 )
	static NetworkEndPoint_t *prvFindFirstAddress_IPv6( void )
	{
		NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;
		while( pxEndPoint != NULL )
		{
			if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
			{
				break;
			}
			pxEndPoint = pxEndPoint->pxNext;
		}
		return pxEndPoint;
	}
#endif /* ipconfigUSE_IPv6 */
/*-----------------------------------------------------------*/

#if( ipconfigUSE_IPv6 != 0 )
	NetworkEndPoint_t *FreeRTOS_FindEndPointOnNetMask_IPv6( IPv6_Address_t *pxIPv6Address )
	{
		( void ) pxIPv6Address;
		/* _HT_ to be worked out later. */
		return prvFindFirstAddress_IPv6();
	}
#endif /* ipconfigUSE_IPv6 */
/*-----------------------------------------------------------*/

/*lint -e9003*/
uint32_t xDoLog = 0UL;/*lint !e9075 (Note -- external symbol 'xDoLog' defined without a prior declaration [MISRA 2012 Rule 8.4, required]. */

NetworkEndPoint_t *FreeRTOS_MatchingEndpoint( NetworkInterface_t *pxNetworkInterface, uint8_t *pucEthernetBuffer )
{
NetworkEndPoint_t *pxEndPoint = NULL;
ProtocolPacket_t *pxPacket = ipPOINTER_CAST( ProtocolPacket_t *, pucEthernetBuffer );	/*lint !e9018 declaration of symbol with union based type [MISRA 2012 Rule 19.2, advisory]. */

	configASSERT( pucEthernetBuffer != NULL );
	/* Check if 'pucEthernetBuffer()' has the expected alignment,
	which is 32-bits + 2. */
	#ifndef _lint
	{
		uint32_t ulAddress = ( uint32_t ) pucEthernetBuffer;
		ulAddress += 2UL;
		configASSERT( ( ulAddress % 4UL ) == 0UL );
	}
	#endif

	//#pragma warning 'name' for logging only, take this away
	const char *name = "";
	
	/* An Ethernet packet has been received. Inspect the contents to see which
	 * defined end-point has the best mathc.
	 */

	/* Some stats while developing. */
	xRoutingStats.ulMatching++;


	/* Probably an ARP packet or a broadcast. */
	switch( pxPacket->xUDPPacket.xEthernetHeader.usFrameType )
	{
#if( ipconfigUSE_IPv6 != 0 )
	case ipIPv6_FRAME_TYPE:
		{
			IPPacket_IPv6_t *pxIPPacket_IPv6 = ipPOINTER_CAST( IPPacket_IPv6_t *, pucEthernetBuffer );

			pxEndPoint = pxNetworkEndPoints;
			while( pxEndPoint != NULL )
			{
				if( ( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED ) &&
					( pxEndPoint->pxNetworkInterface == pxNetworkInterface ) )
				{
					/* This is a IPv6 end-point on the same interface,
					and with a matching IP-address. */
					if( xCompareIPv6_Address( &( pxEndPoint->ipv6_settings.xIPAddress ), &( pxIPPacket_IPv6->xIPHeader.xDestinationAddress ), pxEndPoint->ipv6_settings.uxPrefixLength ) == 0 )
					{
						break;
					}
				}
				pxEndPoint = pxEndPoint->pxNext;
			}
			#if( ipconfigUSE_LLMNR != 0 )
			{
				if( pxEndPoint == NULL )
				{
					if( xCompareIPv6_Address( &( ipLLMNR_IP_ADDR_IPv6 ), &( pxIPPacket_IPv6->xIPHeader.xDestinationAddress ), ( size_t ) 8U * ipSIZE_OF_IPv6_ADDRESS ) == 0 )/*lint !e9029: (Note -- Mismatched essential type categories for binary operator [MISRA 2012 Rule 10.4, required] */
					{
						pxEndPoint = FreeRTOS_FirstEndPoint_IPv6( pxNetworkInterface );
					}
				}
			}
			#endif
		}
		break;
#endif /* ipconfigUSE_IPv6 */
	case ipARP_FRAME_TYPE:
		{
			pxEndPoint = FreeRTOS_FindEndPointOnIP_IPv4( pxPacket->xARPPacket.xARPHeader.ulTargetProtocolAddress, 3UL );
			name = "ARP";
		}
		break;

	case ipIPv4_FRAME_TYPE:
		{
		/* An IPv4 UDP or TCP packet. */
		uint32_t ulIPSourceAddress = pxPacket->xUDPPacket.xIPHeader.ulSourceIPAddress;
		uint32_t ulIPTargetAddress = pxPacket->xUDPPacket.xIPHeader.ulDestinationIPAddress;
		uint32_t ulMatchAddress;
		BaseType_t xIPBroadcast;
		BaseType_t xDone = pdFALSE;

			if( ( FreeRTOS_ntohl( ulIPTargetAddress ) & 0xffuL ) == 0xffuL )
			{
				xIPBroadcast = pdTRUE;
			}
			else
			{
				xIPBroadcast = pdFALSE;
			}
			if( pxPacket->xUDPPacket.xIPHeader.ucProtocol == ( uint8_t ) ipPROTOCOL_UDP )
			{
				name = "UDP";
			}
			else
			{
				name = "TCP";
			}
			if( ulIPTargetAddress == ~0UL )
			{
				ulMatchAddress = ulIPSourceAddress;
			}
			else
			{
				ulMatchAddress = ulIPTargetAddress;
			}
			for( pxEndPoint = FreeRTOS_FirstEndPoint( pxNetworkInterface );
				 pxEndPoint != NULL;
				 pxEndPoint = FreeRTOS_NextEndPoint( pxNetworkInterface, pxEndPoint ) )
			{
				( void ) name;
			#if( ipconfigUSE_IPv6 != 0 )
				if( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED )
				{
					continue;
				}
			#endif /* ( ipconfigUSE_IPv6 != 0 ) */
				if( pxEndPoint->ipv4_settings.ulIPAddress == ulIPTargetAddress  )
				{
					/* The perfect match. */
					xDone = pdTRUE;
				}
				else
				if( ( xIPBroadcast != pdFALSE ) &&
					( ( ( pxEndPoint->ipv4_settings.ulIPAddress ^ ulMatchAddress ) & pxEndPoint->ipv4_settings.ulNetMask ) == 0UL ) )
				{
					xDone = pdTRUE;
				}
				else
				if( xIsIPv4Multicast( ulIPTargetAddress ) != pdFALSE )
				{
					/* Target is a multicast address. */
					xDone = pdTRUE;
				}
				else
				{
					/* This end-point doesn't match with the packet. */
				}
				if( xDone != pdFALSE )
				{
					break;
				}
			}
			if( ( xIPBroadcast != 0 ) && ( pxEndPoint == NULL ) )
			{
				pxEndPoint = FreeRTOS_FirstEndPoint( pxNetworkInterface );
			}
			if( ( xIsIPv4Multicast( ulIPTargetAddress ) == pdFALSE ) && ( xDoLog != 0UL ) )
			{
				xDoLog--;
				FreeRTOS_printf( ( "Compare[%s] %d mine %-16lxip (%02x-%02x) from %-16lxip to %-16lxip (%02x-%02x)\n",
					name,
				//	( unsigned ) xMACBroadcast,
					( unsigned ) xIPBroadcast,
					( pxEndPoint != NULL ) ? FreeRTOS_ntohl( pxEndPoint->ipv4_settings.ulIPAddress ) : 0UL,
					( pxEndPoint != NULL ) ? pxEndPoint->xMACAddress.ucBytes[0] : 0U,
					( pxEndPoint != NULL ) ? pxEndPoint->xMACAddress.ucBytes[1] : 0U,
					FreeRTOS_ntohl( ulIPSourceAddress ),
					FreeRTOS_ntohl( ulIPTargetAddress ),
					pxPacket->xUDPPacket.xEthernetHeader.xDestinationAddress.ucBytes[0],
					pxPacket->xUDPPacket.xEthernetHeader.xDestinationAddress.ucBytes[1] ) );
			}
		}
		break;
	default:
		{
			/* Frame type not supported. */
			FreeRTOS_printf( ( "Frametpye %04x not supported.\n", FreeRTOS_ntohs( pxPacket->xUDPPacket.xEthernetHeader.usFrameType ) ) );
		}
		break;
	}	/* switch usFrameType */

	( void ) name;

/*
	if( ( xDoLog != pdFALSE ) && ( pxEndPoint != NULL ) )
	{
		configPRINTF( ( "Compare[%s] returning %lxip\n", name, ( pxEndPoint != NULL ) ? FreeRTOS_ntohl( pxEndPoint->ulIPAddress ) : 0UL ) );
	}
*/

	return pxEndPoint;
}
/*-----------------------------------------------------------*/

/* Return the default end-point.
xIPType should equal ipTYPE_IPv4 or ipTYPE_IPv6. */

NetworkEndPoint_t *FreeRTOS_FindGateWay( BaseType_t xIPType )
{
	NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;

	while( pxEndPoint != NULL )
	{
	#if( ipconfigUSE_IPv6 == 0 )
		( void ) xIPType;
		if( pxEndPoint->ipv4_settings.ulGatewayAddress != 0UL )	/* access to ipv4_settings is checked. */
		{
			break;
		}
	#else
		if( (xIPType == ( BaseType_t ) ipTYPE_IPv6 ) && ( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED ) )
		{
			/* Check if the IP-address is non-zero. */
			if( memcmp( in6addr_any.ucBytes, pxEndPoint->ipv6_settings.xGatewayAddress.ucBytes, ipSIZE_OF_IPv6_ADDRESS ) != 0 )	/* access to ipv6_settings is checked. */
			{
				break;
			}
		}
		else
		if( ( xIPType == ( BaseType_t ) ipTYPE_IPv4 ) && ( pxEndPoint->bits.bIPv6 == pdFALSE_UNSIGNED ) )
		{
			if( pxEndPoint->ipv4_settings.ulGatewayAddress != 0UL )	/* access to ipv4_settings is checked. */
			{
				break;	/*lint !e9011 more than one 'break' terminates loop [MISRA 2012 Rule 15.4, advisory] */
			}
		}
		else
		{
			/* This end-point is not the right IP-type. */
		}
	#endif	/* ( ipconfigUSE_IPv6 != 0 ) */
		pxEndPoint = pxEndPoint->pxNext;
	}

	return pxEndPoint;
}
/*-----------------------------------------------------------*/

#if( ipconfigUSE_IPv6 != 0 )
	/* Get the first end-point belonging to a given interface.
	When pxInterface is NULL, the very first end-point will be returned. */
	NetworkEndPoint_t *FreeRTOS_FirstEndPoint_IPv6( NetworkInterface_t *pxInterface )
	{
	NetworkEndPoint_t *pxEndPoint = pxNetworkEndPoints;

		while( pxEndPoint != NULL )
		{
			if( ( ( pxInterface == NULL ) || ( pxEndPoint->pxNetworkInterface == pxInterface ) ) && ( pxEndPoint->bits.bIPv6 != pdFALSE_UNSIGNED ) )
			{
				break;
			}
			pxEndPoint = pxEndPoint->pxNext;
		}

		return pxEndPoint;
	}
#endif /* ipconfigUSE_IPv6 */
/*-----------------------------------------------------------*/

NetworkEndPoint_t *pxGetSocketEndpoint( Socket_t xSocket )
{
FreeRTOS_Socket_t *pxSocket = ( FreeRTOS_Socket_t * ) xSocket;
NetworkEndPoint_t *pxResult;

	if( pxSocket != NULL )
	{
		pxResult = pxSocket->pxEndPoint;
	}
	else
	{
		pxResult = NULL;
	}

	return pxResult;	
}
/*-----------------------------------------------------------*/

void vSetSocketEndpoint( Socket_t xSocket, NetworkEndPoint_t *pxEndPoint )
{
FreeRTOS_Socket_t *pxSocket = ( FreeRTOS_Socket_t * ) xSocket;

	pxSocket->pxEndPoint = pxEndPoint;
}
/*-----------------------------------------------------------*/

