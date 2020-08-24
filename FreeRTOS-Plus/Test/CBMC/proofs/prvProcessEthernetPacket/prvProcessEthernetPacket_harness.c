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


#include "memory_assignments.c"
#include "freertos_api.c"

/****************************************************************
 * Signature of function under test
 ****************************************************************/
void prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );


/* This proof was done before. Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress, const uint32_t ulIPAddress ) { }


/* This Proof has been done separately. In 'parsing/ProcessIPPacket'. Hence we assume it to be correct here. */
eFrameProcessingResult_t prvProcessIPPacket( IPPacket_t * pxIPPacket, NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
	eFrameProcessingResult_t result;
	return result;
}

void harness() {

	NetworkBufferDescriptor_t * const pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( ipTOTAL_ETHERNET_FRAME_SIZE, 0 );

	/* The network buffer and the ethernet buffer cannot be NULL for this function. */
	__CPROVER_assume( pxNetworkBuffer != NULL );
	__CPROVER_assume( pxNetworkBuffer->pucEthernetBuffer != NULL );

	prvProcessEthernetPacket( pxNetworkBuffer );
}
