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

#ifndef FREERTOS_ARP_H
#define FREERTOS_ARP_H

#ifdef __cplusplus
extern "C" {
#endif

/* Application level configuration options. */
#include "FreeRTOSIPConfig.h"
#include "FreeRTOSIPConfigDefaults.h"
#include "IPTraceMacroDefaults.h"

/*-----------------------------------------------------------*/
/* Miscellaneous structure and definitions. */
/*-----------------------------------------------------------*/

typedef struct xARP_CACHE_TABLE_ROW
{
	uint32_t ulIPAddress;		/* The IP address of an ARP cache entry. */
	MACAddress_t xMACAddress;  /* The MAC address of an ARP cache entry. */
	uint8_t ucAge;				/* A value that is periodically decremented but can also be refreshed by active communication.  The ARP cache entry is removed if the value reaches zero. */
    uint8_t ucValid;			/* pdTRUE: xMACAddress is valid, pdFALSE: waiting for ARP reply */
} ARPCacheRow_t;

typedef enum
{
	eARPCacheMiss = 0,			/* 0 An ARP table lookup did not find a valid entry. */
	eARPCacheHit,				/* 1 An ARP table lookup found a valid entry. */
	eCantSendPacket				/* 2 There is no IP address, or an ARP is still in progress, so the packet cannot be sent. */
} eARPLookupResult_t;

typedef enum
{
	eNotFragment = 0,			/* The IP packet being sent is not part of a fragment. */
	eFirstFragment,				/* The IP packet being sent is the first in a set of fragmented packets. */
	eFollowingFragment			/* The IP packet being sent is part of a set of fragmented packets. */
} eIPFragmentStatus_t;

/*
 * If ulIPAddress is already in the ARP cache table then reset the age of the
 * entry back to its maximum value.  If ulIPAddress is not already in the ARP
 * cache table then add it - replacing the oldest current entry if there is not
 * a free space available.
 */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress, const uint32_t ulIPAddress );

#if( ipconfigARP_USE_CLASH_DETECTION != 0 )
	/* Becomes non-zero if another device responded to a gratuitos ARP message. */
	extern BaseType_t xARPHadIPClash;
	/* MAC-address of the other device containing the same IP-address. */
	extern MACAddress_t xARPClashMacAddress;
#endif /* ipconfigARP_USE_CLASH_DETECTION */

#if( ipconfigUSE_ARP_REMOVE_ENTRY != 0 )

	/*
	 * In some rare cases, it might be useful to remove a ARP cache entry of a
	 * known MAC address to make sure it gets refreshed.
	 */
	uint32_t ulARPRemoveCacheEntryByMac( const MACAddress_t * pxMACAddress );

#endif /* ipconfigUSE_ARP_REMOVE_ENTRY != 0 */

/*
 * Look for ulIPAddress in the ARP cache.  If the IP address exists, copy the
 * associated MAC address into pxMACAddress, refresh the ARP cache entry's
 * age, and return eARPCacheHit.  If the IP address does not exist in the ARP
 * cache return eARPCacheMiss.  If the packet cannot be sent for any reason
 * (maybe DHCP is still in process, or the addressing needs a gateway but there
 * isn't a gateway defined) then return eCantSendPacket.
 */
eARPLookupResult_t eARPGetCacheEntry( uint32_t *pulIPAddress, MACAddress_t * const pxMACAddress );

#if( ipconfigUSE_ARP_REVERSED_LOOKUP != 0 )

	/* Lookup an IP-address if only the MAC-address is known */
	eARPLookupResult_t eARPGetCacheEntryByMac( MACAddress_t * const pxMACAddress, uint32_t *pulIPAddress );

#endif
/*
 * Reduce the age count in each entry within the ARP cache.  An entry is no
 * longer considered valid and is deleted if its age reaches zero.
 */
void vARPAgeCache( void );

/*
 * Send out an ARP request for the IP address contained in pxNetworkBuffer, and
 * add an entry into the ARP table that indicates that an ARP reply is
 * outstanding so re-transmissions can be generated.
 */
void vARPGenerateRequestPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );

/*
 * After DHCP is ready and when changing IP address, force a quick send of our new IP
 * address
 */
void vARPSendGratuitous( void );

#ifdef __cplusplus
} // extern "C"
#endif

#endif /* FREERTOS_ARP_H */













