/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_TCP_IP.h"

/*This proof assumes that pxUDPSocketLookup is implemented correctly. */

/* This proof was done before. Hence we assume it to be correct here. */
void vARPRefreshCacheEntry(const MACAddress_t * pxMACAddress, const uint32_t ulIPAddress) { }

/* This proof was done before. Hence we assume it to be correct here. */
BaseType_t xIsDHCPSocket(Socket_t xSocket) { }

/* This proof was done before. Hence we assume it to be correct here. */
uint32_t ulDNSHandlePacket(NetworkBufferDescriptor_t *pxNetworkBuffer) { }

/* Implementation of safe malloc */
void *safeMalloc(size_t xWantedSize) {
	if(xWantedSize == 0) {
		return NULL;
	}
	uint8_t byte;
	return byte ? malloc(xWantedSize) : NULL;
}

/* Abstraction of pxUDPSocketLookup */
FreeRTOS_Socket_t *pxUDPSocketLookup( UBaseType_t uxLocalPort ) {
	return safeMalloc(sizeof(FreeRTOS_Socket_t));
}

void harness() {
	NetworkBufferDescriptor_t *pxNetworkBuffer = safeMalloc(sizeof(NetworkBufferDescriptor_t));
	if(pxNetworkBuffer) {
		pxNetworkBuffer->pucEthernetBuffer = safeMalloc(sizeof(UDPPacket_t));
	}
	uint16_t usPort;
	if (pxNetworkBuffer && pxNetworkBuffer->pucEthernetBuffer) {
		xProcessReceivedUDPPacket(pxNetworkBuffer, usPort);
	}
}
