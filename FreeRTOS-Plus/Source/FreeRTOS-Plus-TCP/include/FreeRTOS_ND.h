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

#ifndef FREERTOS_ND_H
#define FREERTOS_ND_H

#ifdef __cplusplus
extern "C" {
#endif

/* Application level configuration options. */
#include "FreeRTOSIPConfig.h"
#include "FreeRTOSIPConfigDefaults.h"
#include "IPTraceMacroDefaults.h"

#if( ipconfigUSE_IPv6 != 0 )
/*-----------------------------------------------------------*/
/* Miscellaneous structure and definitions. */
/*-----------------------------------------------------------*/

typedef struct xND_CACHE_TABLE_ROW
{
	IPv6_Address_t xIPAddress;	/* The IP address of an ND cache entry. */
	MACAddress_t xMACAddress;	/* The MAC address of an ND cache entry. */
	struct xNetworkEndPoint *pxEndPoint;
	uint8_t ucAge;				/* A value that is periodically decremented but can also be refreshed by active communication.  The ND cache entry is removed if the value reaches zero. */
    uint8_t ucValid;			/* pdTRUE: xMACAddress is valid, pdFALSE: waiting for ND reply */
} NDCacheRow_t;

/*
 * If ulIPAddress is already in the ND cache table then reset the age of the
 * entry back to its maximum value.  If ulIPAddress is not already in the ND
 * cache table then add it - replacing the oldest current entry if there is not
 * a free space available.
 */
void vNDRefreshCacheEntry( const MACAddress_t * pxMACAddress, const IPv6_Address_t *pxIPAddress, NetworkEndPoint_t *pxEndPoint );

#if( ipconfigUSE_ARP_REMOVE_ENTRY != 0 )

	/*
	 * In some rare cases, it might be useful to remove a ND cache entry of a
	 * known MAC address to make sure it gets refreshed.
	 */
	uint32_t ulNDRemoveCacheEntryByMac( const MACAddress_t * pxMACAddress );

#endif /* ipconfigUSE_ARP_REMOVE_ENTRY != 0 */

/*
 * Look for ulIPAddress in the ND cache.  If the IP address exists, copy the
 * associated MAC address into pxMACAddress, refresh the ND cache entry's
 * age, and return eARPCacheHit.  If the IP address does not exist in the ND
 * cache return eARPCacheMiss.  If the packet cannot be sent for any reason
 * (maybe DHCP is still in process, or the addressing needs a gateway but there
 * isn't a gateway defined) then return eCantSendPacket.
 */
eARPLookupResult_t eNDGetCacheEntry( IPv6_Address_t *pxIPAddress, MACAddress_t * const pxMACAddress, struct xNetworkEndPoint **ppxEndPoint );

#if( ipconfigUSE_ARP_REVERSED_LOOKUP != 0 )

	/* Lookup an IP-address if only the MAC-address is known */
	eARPLookupResult_t eNDGetCacheEntryByMac( MACAddress_t * const pxMACAddress, IPv6_Address_t *pxIPAddress );

#endif
/*
 * Reduce the age count in each entry within the ND cache.  An entry is no
 * longer considered valid and is deleted if its age reaches zero.
 */
void vNDAgeCache( void );

/*
 * Send out an ND request for the IPv6 address contained in pxNetworkBuffer, and
 * add an entry into the ND table that indicates that an ND reply is
 * outstanding so re-transmissions can be generated.
 */
void vNDSendNeighbourSolicitation( NetworkBufferDescriptor_t * const pxNetworkBuffer, IPv6_Address_t *pxIPAddress );

#if( ipconfigUSE_RA != 0 )
	/*
	 * Send out a ROuter Sollicitaion.
	 */
	void vNDSendRouterSolicitation( NetworkBufferDescriptor_t * const pxNetworkBuffer, IPv6_Address_t *pxIPAddress );
#endif	/* ( ipconfigUSE_RA != 0 ) */

#if( ipconfigUSE_RA != 0 )
	/*
	 * Work on the RA/SLAAC processing.
	 */
	void vRAProcess( BaseType_t xDoReset, NetworkEndPoint_t *pxEndPoint );
#endif	/* ( ipconfigUSE_RA != 0 ) */

/*
 * After DHCP is ready and when changing IP address, force a quick send of our new IP
 * address
 */
void vNDSendGratuitous( void );

void FreeRTOS_PrintNDCache( void );

#if( ipconfigUSE_IPv6 != 0 )
	void FreeRTOS_OutputAdvertiseIPv6( NetworkEndPoint_t *pxEndPoint );
	BaseType_t FreeRTOS_SendPingRequestIPv6( IPv6_Address_t *pxIPAddress, size_t uxNumberOfBytesToSend, TickType_t uxBlockTimeTicks );
	BaseType_t FreeRTOS_CreateIPv6Address( IPv6_Address_t *pxIPAddress, const IPv6_Address_t *pxPrefix, size_t uxPrefixLength, BaseType_t xDoRandom );
#endif

#endif /* ipconfigUSE_IPv6 != 0 */

#ifdef __cplusplus
} // extern "C"
#endif

#endif /* FREERTOS_ND_H */













