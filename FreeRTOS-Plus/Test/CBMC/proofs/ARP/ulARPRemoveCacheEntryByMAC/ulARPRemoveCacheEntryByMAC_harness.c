/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOSIPConfig.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"

#include "cbmc.h"


/* Implementation of safe malloc */
void *safeMalloc(size_t xWantedSize ){
	if(xWantedSize == 0){
		return NULL;
	}
	uint8_t byte = nondet_uint8_t();
	return byte ? malloc(xWantedSize) : NULL;
}


void harness() {

	const MACAddress_t xMACAddress;


	ulARPRemoveCacheEntryByCache( &xMACAddress );
}
