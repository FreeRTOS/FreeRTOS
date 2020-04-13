/* This harness is linked against
 * libraries/freertos_plus/standard/freertos_plus_tcp/source/portable/BufferManagement/BufferAllocation_1.goto
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

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] ){
	for(int x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++){
		NetworkBufferDescriptor_t *current = &pxNetworkBuffers[x];
		#ifdef ipconfigETHERNET_MINIMUM_PACKET_BYTES
			current->pucEthernetBuffer = malloc(sizeof(ARPPacket_t) + (ipconfigETHERNET_MINIMUM_PACKET_BYTES- sizeof(ARPPacket_t)));
		#else
			current->pucEthernetBuffer = malloc(sizeof(ARPPacket_t));
		#endif
		current->xDataLength = sizeof(ARPPacket_t);
	}
}

/* The code expects that the Semaphore creation relying on pvPortMalloc
   is successful. This is checked by an assert statement, that gets
   triggered when the allocation fails. Nevertheless, the code is perfectly
   guarded against a failing Semaphore allocation. To make the assert pass,
   it is assumed for now, that pvPortMalloc doesn't fail. Using a model allowing
   failures of the allocation might be possible
   after removing the assert in l.105 of BufferAllocation_1.c, from a memory
   safety point of view. */
void *pvPortMalloc( size_t xWantedSize ){
	return malloc(xWantedSize);
}

/*
 * This function is implemented by a third party.
 * After looking through a couple of samples in the demos folder, it seems
 * like the only shared contract is that you want to add the if statement
 * for releasing the buffer to the end. Apart from that, it is up to the vendor,
 * how to write this code out to the network.
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
