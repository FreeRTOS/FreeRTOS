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
#include "FreeRTOS_DHCP.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_ARP.h"

#include "cbmc.h"


/****************************************************************
 * Signature of function under test
 ****************************************************************/

void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );


/* This proof was done before. Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress, const uint32_t ulIPAddress ) { }


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


void harness() {

	NetworkBufferDescriptor_t * const pxNetworkBuffer = malloc(sizeof(NetworkBufferDescriptor_t));

	/* Pointer to the start of the Ethernet frame. It should be able to access the whole Ethernet frame.*/
	pxNetworkBuffer->pucEthernetBuffer = malloc(ipTOTAL_ETHERNET_FRAME_SIZE);

	/* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_t. */
	__CPROVER_assume(pxNetworkBuffer->xDataLength >= sizeof(EthernetHeader_t)  && pxNetworkBuffer->xDataLength <= ipTOTAL_ETHERNET_FRAME_SIZE);

	prvProcessEthernetPacket( pxNetworkBuffer );
}
