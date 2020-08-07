int32_t publicTCPPrepareSend( FreeRTOS_Socket_t *pxSocket, NetworkBufferDescriptor_t **ppxNetworkBuffer, UBaseType_t uxOptionsLength ) {
	prvTCPPrepareSend( pxSocket, ppxNetworkBuffer, uxOptionsLength );
}

BaseType_t publicTCPHandleState( FreeRTOS_Socket_t *pxSocket, NetworkBufferDescriptor_t **ppxNetworkBuffer ) {
	prvTCPHandleState(pxSocket, ppxNetworkBuffer);
}

void publicTCPReturnPacket( FreeRTOS_Socket_t *pxSocket, NetworkBufferDescriptor_t *pxNetworkBuffer,
	uint32_t ulLen, BaseType_t xReleaseAfterSend ) {
	prvTCPReturnPacket(pxSocket, pxNetworkBuffer, ulLen, xReleaseAfterSend );
}
