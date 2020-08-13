/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"


uint16_t prvGetPrivatePortNumber( BaseType_t xProtocol )
{
	uint16_t usResult;
	return usResult;
}

/* Memory assignment for FreeRTOS_Socket_t */
FreeRTOS_Socket_t * ensure_FreeRTOS_Socket_t_is_allocated () {
	FreeRTOS_Socket_t *pxSocket = malloc(sizeof(FreeRTOS_Socket_t));

	pxSocket->u.xTCP.rxStream = safeMalloc(sizeof(StreamBuffer_t));
	pxSocket->u.xTCP.txStream = safeMalloc(sizeof(StreamBuffer_t));
	pxSocket->u.xTCP.pxPeerSocket = safeMalloc(sizeof(FreeRTOS_Socket_t));

	return pxSocket;
}

void harness()
{
	FreeRTOS_Socket_t *pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
	__CPROVER_assume( pxSocket != NULL );
	__CPROVER_assume( pxSocket != FREERTOS_INVALID_SOCKET )
	
	struct freertos_sockaddr * pxBindAddress = malloc( sizeof( struct freertos_sockaddr ) );

	/* uxAddressLength is not used in this implementation. */
	size_t uxAddressLength;

	BaseType_t xInternal;

	vSocketBind( pxSocket, pxBindAddress, uxAddressLength, xInternal );
}
