/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "list.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"

/* Include the stubs for APIs. */
#include "memory_assignments.c"
#include "freertos_api.c"

/* We do not need to calculate the actual checksum for the proof to be complete.
 * Neither does the checksum matter for completeness. */
uint16_t usGenerateChecksum( uint16_t usSum, const uint8_t * pucNextData, size_t uxByteCount )
{
	__CPROVER_assert( pucNextData != NULL, "Next data in GenerateChecksum cannot be NULL" );

	uint16_t usChecksum;

	/* Return any random value of checksum since it does not matter for CBMC checks. */
	return usChecksum;
}


/* We do not need to calculate the actual checksum for the proof to be complete.
 * Neither does the checksum matter for completeness. */
uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer, size_t uxBufferLength, BaseType_t xOutgoingPacket )
{
	__CPROVER_assert( pucEthernetBuffer != NULL, "The Ethernet buffer cannot be NULL while generating Protocol Checksum" );
	uint16_t usProtocolChecksum;

	/* Return random value of checksum since it does not matter for CBMC checks. */
	return usProtocolChecksum;
}


/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress, const uint32_t ulIPAddress )
{
	/* pxMACAddress can be NULL or Non-NULL, no need to assert. */
}


/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vARPGenerateRequestPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
	__CPROVER_assert( pxNetworkBuffer != NULL, "The network buffer cannot be NULL." );
}


/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
eARPLookupResult_t eARPGetCacheEntry( uint32_t *pulIPAddress, MACAddress_t * const pxMACAddress )
{
	__CPROVER_assert( pulIPAddress != NULL, "pulIPAddress cannot be NULL" );
	__CPROVER_assert( pxMACAddress != NULL, "pxMACAddress cannot be NULL" );

	eARPLookupResult_t eResult;
	return eResult;
}


void harness()
{
	size_t xRequestedSizeBytes;

	/* Assume that the size of packet must be greater than that of UDP-Packet and less than
	 * that of the Ethernet Frame Size. */
	__CPROVER_assume( xRequestedSizeBytes >= sizeof(UDPPacket_t) && xRequestedSizeBytes <= ipTOTAL_ETHERNET_FRAME_SIZE );

	/* Second parameter is not used from CBMC's perspective. */
	NetworkBufferDescriptor_t * const pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( xRequestedSizeBytes, 0 );

	/* The buffer cannot be NULL for the function call. */
	__CPROVER_assume(pxNetworkBuffer != NULL);
	__CPROVER_assume(pxNetworkBuffer->pucEthernetBuffer != NULL);

	vProcessGeneratedUDPPacket( pxNetworkBuffer );
}
