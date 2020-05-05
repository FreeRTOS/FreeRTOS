eFrameProcessingResult_t publicProcessIPPacket( IPPacket_t * const pxIPPacket, NetworkBufferDescriptor_t * const pxNetworkBuffer ) {
	prvProcessIPPacket(pxIPPacket, pxNetworkBuffer);
}
