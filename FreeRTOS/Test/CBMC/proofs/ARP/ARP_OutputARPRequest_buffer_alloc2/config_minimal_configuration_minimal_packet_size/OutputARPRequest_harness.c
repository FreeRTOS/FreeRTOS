/* This harness is linked against
 * libraries/freertos_plus/standard/freertos_plus_tcp/source/portable/BufferManagement/BufferAllocation_2.goto
 */
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
#include "FreeRTOS_ARP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_DHCP.h"
#if( ipconfigUSE_LLMNR == 1 )
	#include "FreeRTOS_DNS.h"
#endif /* ipconfigUSE_LLMNR */
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

void *pvPortMalloc( size_t xWantedSize ){
	return malloc(xWantedSize);
}


void vPortFree( void *pv ){
	free(pv);
}

/*
 * This function function writes a buffer to the network.  We stub it
 * out here, and assume it has no side effects relevant to memory safety.
 */
BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t bReleaseAfterSend ){
	if( bReleaseAfterSend != pdFALSE )
	{
		vReleaseNetworkBufferAndDescriptor( pxDescriptor );
	}
}

void harness()
{
	BaseType_t xRes = xNetworkBuffersInitialise();
	if(xRes == pdPASS){
		uint32_t ulIPAddress;
		FreeRTOS_OutputARPRequest( ulIPAddress );
	}
}

