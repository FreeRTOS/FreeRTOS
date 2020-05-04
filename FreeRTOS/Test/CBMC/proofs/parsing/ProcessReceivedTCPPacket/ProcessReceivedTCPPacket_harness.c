/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_Stream_Buffer.h"

/* This proof assumes FreeRTOS_socket, pxTCPSocketLookup and 
pxGetNetworkBufferWithDescriptor are implemented correctly.

It also assumes prvSingleStepTCPHeaderOptions, prvCheckOptions, prvTCPPrepareSend,
prvTCPHandleState and prvTCPReturnPacket are correct. These functions are
proved to be correct separately. */

/* Implementation of safe malloc */
void *safeMalloc(size_t xWantedSize ){
	if(xWantedSize == 0){
		return NULL;
	}
	uint8_t byte;
	return byte ? malloc(xWantedSize) : NULL;
}

/* Abstraction of FreeRTOS_socket */
Socket_t FreeRTOS_socket( BaseType_t xDomain, BaseType_t xType, BaseType_t xProtocol) {
	return safeMalloc(sizeof(FreeRTOS_Socket_t));
}

/* Abstraction of pxTCPSocketLookup */
FreeRTOS_Socket_t *pxTCPSocketLookup(uint32_t ulLocalIP, UBaseType_t uxLocalPort, uint32_t ulRemoteIP, UBaseType_t uxRemotePort) {
	FreeRTOS_Socket_t * xRetSocket = safeMalloc(sizeof(FreeRTOS_Socket_t));
	if (xRetSocket) {
		xRetSocket->u.xTCP.txStream = safeMalloc(sizeof(StreamBuffer_t));
		xRetSocket->u.xTCP.pxPeerSocket = safeMalloc(sizeof(StreamBuffer_t));
	}	
	return xRetSocket;
}

/* Abstraction of pxGetNetworkBufferWithDescriptor */
NetworkBufferDescriptor_t *pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks ){
	NetworkBufferDescriptor_t *pxNetworkBuffer = safeMalloc(sizeof(NetworkBufferDescriptor_t));
	if(pxNetworkBuffer) {
		pxNetworkBuffer->pucEthernetBuffer = safeMalloc(xRequestedSizeBytes);
		__CPROVER_assume(pxNetworkBuffer->xDataLength == ipSIZE_OF_ETH_HEADER + sizeof(int32_t));
	}	
	return pxNetworkBuffer;
}

void harness() {
	NetworkBufferDescriptor_t *pxNetworkBuffer = safeMalloc(sizeof(NetworkBufferDescriptor_t));
	if (pxNetworkBuffer) {
		pxNetworkBuffer->pucEthernetBuffer = safeMalloc(sizeof(TCPPacket_t));
	}
	if (pxNetworkBuffer && pxNetworkBuffer->pucEthernetBuffer) {
		xProcessReceivedTCPPacket(pxNetworkBuffer);

	}

}
