/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"


void harness() {
	if( ipconfigUSE_DNS_CACHE != 0 ) {
		FreeRTOS_dnsclear();
	}	
	
}
