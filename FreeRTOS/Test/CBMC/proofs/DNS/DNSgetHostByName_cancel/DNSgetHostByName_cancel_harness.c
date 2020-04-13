/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"


/* This proof assumes the length of pcHostName is bounded by MAX_HOSTNAME_LEN. This also abstracts the concurrency. */ 

void vDNSInitialise(void);

void vDNSSetCallBack(const char *pcHostName, void *pvSearchID, FOnDNSEvent pCallbackFunction, TickType_t xTimeout, TickType_t xIdentifier);

void *safeMalloc(size_t xWantedSize) { /* Returns a NULL pointer if the wanted size is 0. */
	if(xWantedSize == 0) {
		return NULL;
	}
	uint8_t byte;
	return byte ? malloc(xWantedSize) : NULL;
}

/* Abstraction of xTaskCheckForTimeOut from task pool. This also abstracts the concurrency. */ 
BaseType_t xTaskCheckForTimeOut(TimeOut_t * const pxTimeOut, TickType_t * const pxTicksToWait) { }

/* Abstraction of xTaskResumeAll from task pool. This also abstracts the concurrency. */ 
BaseType_t xTaskResumeAll(void) { }

/* The function func mimics the callback function.*/ 
void func(const char * pcHostName, void * pvSearchID, uint32_t ulIPAddress) {}

void harness() {
	vDNSInitialise(); /* We initialize the callbacklist in order to be able to check for functions that timed out. */ 
	size_t pvSearchID;
	FOnDNSEvent pCallback = func;
	TickType_t xTimeout;
	TickType_t xIdentifier;
	size_t len;
	__CPROVER_assume(len >= 0 && len <= MAX_HOSTNAME_LEN);
	char *pcHostName = safeMalloc(len); 
	if (len && pcHostName) {
		pcHostName[len-1] = NULL;
	}
	vDNSSetCallBack( pcHostName, &pvSearchID, pCallback, xTimeout, xIdentifier); /* Add an item to be able to check the cancel function if the list is non-empty. */
	FreeRTOS_gethostbyname_cancel(&pvSearchID);
}