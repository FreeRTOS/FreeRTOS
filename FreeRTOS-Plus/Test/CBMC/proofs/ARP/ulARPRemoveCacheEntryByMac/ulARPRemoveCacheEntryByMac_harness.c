/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"


void harness() {
	const MACAddress_t xMACAddress;

	/* The pointer passed to ulARPRemoveCacheEntryByMac cannot be NULL
	 * (see the API definition). */
	ulARPRemoveCacheEntryByMac( &xMACAddress );
}
