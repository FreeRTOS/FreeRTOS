/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_ARP.h"


void harness() {

	uint8_t u1,u2,u3,u4,u5,u6;

	const MACAddress_t xMACAddress = {u1, u2, u3, u4, u5, u6};

	//__CPROVER_assume( &xMACAddress );

	ulARPRemoveCacheEntryByMac( &xMACAddress );
}
