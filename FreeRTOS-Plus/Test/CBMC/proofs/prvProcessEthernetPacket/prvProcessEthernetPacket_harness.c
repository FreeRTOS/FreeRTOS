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

#include "memory_assignments.c"
#include "freertos_api.c"

/****************************************************************
 * Signature of function under test
 ****************************************************************/
void __CPROVER_file_local_FreeRTOS_IP_c_prvProcessEthernetPacket( NetworkBufferDescriptor_t * const pxNetworkBuffer );


/* This function has been proved to be memory safe in another proof (in ARP/ARPRefreshCacheEntry). Hence we assume it to be correct here. */
void vARPRefreshCacheEntry( const MACAddress_t * pxMACAddress, const uint32_t ulIPAddress )
{
	/* pxMACAddress can be NULL or non-NULL. No need to assert. */
}

/* This function has been proved to be memory safe in another proof (in ARP/ARPProcessPacket). Hence we assume it to be correct here. */
eFrameProcessingResult_t eARPProcessPacket( ARPPacket_t * const pxARPFrame )
{
	__CPROVER_assert( pxARPFrame != NULL, "pxARPFrame cannot be NULL" );

	eFrameProcessingResult_t eReturn;
	return eReturn;
}

/* This function has been proved to be memory safe in another proof (in parsing/ProcessIPPacket). Hence we assume it to be correct here. */
eFrameProcessingResult_t  __CPROVER_file_local_FreeRTOS_IP_c_prvProcessIPPacket( IPPacket_t * pxIPPacket, NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
	__CPROVER_assert( pxIPPacket != NULL, "pxIPPacket cannot be NULL" );
	__CPROVER_assert( pxNetworkBuffer != NULL, "pxNetworkBuffer cannot be NULL" );

	eFrameProcessingResult_t result;
	return result;
}

void harness() {

	NetworkBufferDescriptor_t * const pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( ipTOTAL_ETHERNET_FRAME_SIZE, 0 );

	/* The network buffer cannot be NULL for this function call. If it is, it will hit an assert in the function. */
	__CPROVER_assume( pxNetworkBuffer != NULL );

	__CPROVER_file_local_FreeRTOS_IP_c_prvProcessEthernetPacket( pxNetworkBuffer );
}
