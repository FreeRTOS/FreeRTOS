/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_DNS.h"
#include "FreeRTOS_IP_Private.h"

/* This proof assumes the length of pcHostName is bounded by MAX_HOSTNAME_LEN and the size of UDPPayloadBuffer is bounded by
MAX_REQ_SIZE. This also abstracts the concurrency. */

void *safeMalloc(size_t xWantedSize) { /* This returns a NULL pointer if the requested size is 0.
	The implementation of malloc does not return a NULL pointer instead returns a pointer for which there is no memory allocation. */
	if(xWantedSize == 0) {
		return NULL;
	}
	uint8_t byte;
	return byte ? malloc(xWantedSize) : NULL;
}

/* Abstraction of pvPortMalloc which calls safemalloc internally. */
void *pvPortMalloc(size_t xWantedSize) {
	return safeMalloc(xWantedSize);
}

/* Abstraction of FreeRTOS_GetUDPPayloadBuffer.
We always return MAX_REQ_SIZE bytes to keep the proof performant.
This is safe because:
- If the caller requested more bytes, then there is a risk that they
    will write past the end of the returned buffer. This proof
    therefore shows that the code is memory safe even if
    xRequestedSizeBytes > MAX_REQ_SIZE.
- If the caller requested fewer bytes, then they will not be
    iterating past the end of the buffer anyway.*/
void * FreeRTOS_GetUDPPayloadBuffer(size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks ) {
	void *pvReturn = safeMalloc(MAX_REQ_SIZE);
	return pvReturn;
}

/* Abstraction of FreeRTOS_socket. This abstraction allocates a memory of size Socket_t. */
Socket_t FreeRTOS_socket( BaseType_t xDomain, BaseType_t xType, BaseType_t xProtocol ){
	Socket_t xCreatedSocket = safeMalloc(sizeof(Socket_t)); // replacing malloc with safeMalloc
	return xCreatedSocket;
}

/* This function FreeRTOS_gethostbyname_a only uses the return value of prvParseDNSReply. Hence it returns an unconstrained uint32 value */
uint32_t prvParseDNSReply( uint8_t *pucUDPPayloadBuffer,
			   size_t xBufferLength,
			   BaseType_t xExpected ) {}

/* Abstraction of xTaskResumeAll from task pool. This also abstracts the concurrency. */
BaseType_t xTaskResumeAll(void) { }

/* The function func mimics the callback function.*/
void func(const char * pcHostName, void * pvSearchID, uint32_t ulIPAddress) { }

typedef struct xDNS_Callback {
	TickType_t xRemaningTime;		/* Timeout in ms */
	FOnDNSEvent pCallbackFunction;	/* Function to be called when the address has been found or when a timeout has beeen reached */
	TimeOut_t xTimeoutState;
	void *pvSearchID;
	struct xLIST_ITEM xListItem;
	char pcName[ 1 ];
} DNSCallback_t;

void harness() {
	FOnDNSEvent pCallback = func;
	TickType_t xTimeout;
	void *pvSearchID;
	size_t len;
	__CPROVER_assume(len >= 0 && len <= MAX_HOSTNAME_LEN);
	char *pcHostName = safeMalloc(len); // replacing malloc with safeMalloc
	if (len && pcHostName) {
		pcHostName[len-1] = NULL;
	}
	if (pcHostName) { // Guarding against NULL pointer
		FreeRTOS_gethostbyname_a(pcHostName, pCallback, pvSearchID, xTimeout);
	}
}
