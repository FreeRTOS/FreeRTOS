/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"

/* proof is done separately */
BaseType_t xProcessReceivedTCPPacket(NetworkBufferDescriptor_t *pxNetworkBuffer) { }

/* proof is done separately */
BaseType_t xProcessReceivedUDPPacket(NetworkBufferDescriptor_t *pxNetworkBuffer, uint16_t usPort) { }

/* This proof was done before. Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress, const uint32_t ulIPAddress ) { }

eFrameProcessingResult_t publicProcessIPPacket( IPPacket_t * const pxIPPacket, NetworkBufferDescriptor_t * const pxNetworkBuffer);

void harness() {

	NetworkBufferDescriptor_t * const pxNetworkBuffer = malloc(sizeof(NetworkBufferDescriptor_t));
	/* Pointer to the start of the Ethernet frame. It should be able to access the whole Ethernet frame.*/
	pxNetworkBuffer->pucEthernetBuffer = malloc(ipTOTAL_ETHERNET_FRAME_SIZE);
	/* Minimum length of the pxNetworkBuffer->xDataLength is at least the size of the IPPacket_t. */
	__CPROVER_assume(pxNetworkBuffer->xDataLength >= sizeof(IPPacket_t)  && pxNetworkBuffer->xDataLength <= ipTOTAL_ETHERNET_FRAME_SIZE);
	IPPacket_t * const pxIPPacket = malloc(sizeof(IPPacket_t));
	publicProcessIPPacket(pxIPPacket, pxNetworkBuffer);
}
