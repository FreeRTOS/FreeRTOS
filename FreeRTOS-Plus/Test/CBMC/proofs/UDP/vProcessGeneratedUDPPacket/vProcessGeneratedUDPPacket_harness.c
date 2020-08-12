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
//#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_IP_Private.h"

uint16_t usGenerateChecksum( uint16_t usSum, const uint8_t * pucNextData, size_t uxByteCount ) { }

uint16_t usGenerateProtocolChecksum( const uint8_t * const pucEthernetBuffer, size_t uxBufferLength, BaseType_t xOutgoingPacket ) { }

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress, const uint32_t ulIPAddress ) { }

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vARPGenerateRequestPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )         { }

/* Provide a stub for this function. */
eARPLookupResult_t eARPGetCacheEntry( uint32_t *pulIPAddress, MACAddress_t * const pxMACAddress )
{
	eARPLookupResult_t eResult;
	return eResult;
}

/* Implementation of safe malloc */
void *safeMalloc(size_t xWantedSize ){
	if(xWantedSize == 0){
		return NULL;
	}
	uint8_t byte = nondet_uint8_t();
	return byte ? malloc(xWantedSize) : NULL;
}


/* Abstraction of pxGetNetworkBufferWithDescriptor. We assume it to be correctly implemented. */
NetworkBufferDescriptor_t *pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks ){
	NetworkBufferDescriptor_t *pxNetworkBuffer = safeMalloc(sizeof(NetworkBufferDescriptor_t));
	if(pxNetworkBuffer) {
		pxNetworkBuffer->pucEthernetBuffer = safeMalloc(xRequestedSizeBytes);

		__CPROVER_assume(pxNetworkBuffer->xDataLength == ipSIZE_OF_ETH_HEADER + sizeof(int32_t));
	}	
	return pxNetworkBuffer;
}


/* Network Interface function needs to be stubbed out since we do not have an actual network interface. Hence we assume it to be correct. */
BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer, BaseType_t bReleaseAfterSend )
{
	/* Return pdPASS */
	return pdPASS;
}


void harness()
{
	NetworkBufferDescriptor_t * const pxNetworkBuffer = malloc( sizeof( NetworkBufferDescriptor_t ) );

	/* Pointer to the start of the Ethernet frame. It should be able to access the whole Ethernet frame.*/
	pxNetworkBuffer->pucEthernetBuffer = malloc( ipTOTAL_ETHERNET_FRAME_SIZE );

	/* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_t. */
	__CPROVER_assume(pxNetworkBuffer->xDataLength >= sizeof(EthernetHeader_t)  && pxNetworkBuffer->xDataLength <= ipTOTAL_ETHERNET_FRAME_SIZE);

	vProcessGeneratedUDPPacket( &pxNetworkBuffer );
}
