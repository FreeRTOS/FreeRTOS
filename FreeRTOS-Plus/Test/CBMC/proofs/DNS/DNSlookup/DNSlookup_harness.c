/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"

/* This assumes that the length of the hostname is bounded by MAX_HOSTNAME_LEN. */
void *safeMalloc(size_t xWantedSize) {
	if(xWantedSize == 0) {
		return NULL;
	}
	uint8_t byte;
	return byte ? malloc(xWantedSize) : NULL;
}

void harness() {
	if(ipconfigUSE_DNS_CACHE != 0) {
		size_t len;
		__CPROVER_assume(len >= 0 && len <= MAX_HOSTNAME_LEN);
		char *pcHostName = safeMalloc(len); /* malloc is replaced by safeMalloc */
		if (len && pcHostName) {
			pcHostName[len-1] = NULL;
		}
		if (pcHostName) { /* guarding against NULL pointer */
			FreeRTOS_dnslookup(pcHostName);	
		}
	}	
}
