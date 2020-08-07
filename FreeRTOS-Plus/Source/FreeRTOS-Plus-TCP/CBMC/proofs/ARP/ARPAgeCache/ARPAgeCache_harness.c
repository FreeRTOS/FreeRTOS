/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"

//We assume that the pxGetNetworkBufferWithDescriptor function is implemented correctly and returns a valid data structure.
//This is the mock to mimic the correct expected bahvior. If this allocation fails, this might invalidate the proof.
NetworkBufferDescriptor_t *pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks ){
	NetworkBufferDescriptor_t *pxNetworkBuffer = (NetworkBufferDescriptor_t *) malloc(sizeof(NetworkBufferDescriptor_t));
	pxNetworkBuffer->pucEthernetBuffer = malloc(xRequestedSizeBytes);
	pxNetworkBuffer->xDataLength = xRequestedSizeBytes;
	return pxNetworkBuffer;
}

void harness()
{
  vARPAgeCache();
}