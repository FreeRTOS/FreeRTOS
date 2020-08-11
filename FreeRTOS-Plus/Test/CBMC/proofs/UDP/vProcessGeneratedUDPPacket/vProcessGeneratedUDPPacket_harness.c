/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_UDP_IP.h"

#include "cbmc.h"



/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress, const uint32_t ulIPAddress ) { }

/* This function has been tested separately. Therefore, we assume that the implementation is correct. */
void vARPGenerateRequestPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer )         { }


void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );



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


/* This Proof has been done separately. In 'parsing/ProcessIPPacket'. Hence we assume it to be correct here. */
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket, NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
	eFrameProcessingResult_t result;
	return result;
}


/* Network Interface function needs to be stubbed out since we do not have an actual network interface. Hence we assume it to be correct. */
BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer, BaseType_t bReleaseAfterSend )
{
	/* Return pdPASS */
	return pdPASS;
}


void harness()
{
	NetworkBufferDescriptor_t pxNetworkBuffer;

	void vProcessGeneratedUDPPacket( &pxNetworkBuffer );
}
