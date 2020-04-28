/*
 * FreeRTOS memory safety proofs with CBMC.
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_TCP_IP.h"
#include "FreeRTOS_Stream_Buffer.h"

#include "../../utility/memory_assignments.c"

/* This proof assumes that pxGetNetworkBufferWithDescriptor is implemented correctly. */
int32_t publicTCPPrepareSend( FreeRTOS_Socket_t *pxSocket, NetworkBufferDescriptor_t **ppxNetworkBuffer, UBaseType_t uxOptionsLength );

/* Abstraction of pxGetNetworkBufferWithDescriptor. It creates a buffer. */
NetworkBufferDescriptor_t *pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks ){
	NetworkBufferDescriptor_t *pxBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated ();
	size_t bufferSize = sizeof(NetworkBufferDescriptor_t);
	if (ensure_memory_is_valid(pxBuffer, bufferSize)) {
		/* The code does not expect pucEthernetBuffer to be equal to NULL if
		pxBuffer is not NULL. */
		pxBuffer->pucEthernetBuffer = malloc(xRequestedSizeBytes);
		pxBuffer->xDataLength = xRequestedSizeBytes;
	}
	return pxBuffer;
}

void harness() {
	FreeRTOS_Socket_t *pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
	NetworkBufferDescriptor_t *pxNetworkBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated();
	size_t socketSize = sizeof(FreeRTOS_Socket_t);
	size_t bufferSize = sizeof(TCPPacket_t);
	if (ensure_memory_is_valid(pxNetworkBuffer, sizeof(*pxNetworkBuffer))) {
		pxNetworkBuffer->xDataLength = bufferSize;
		/* The code does not expect pucEthernetBuffer to be equal to NULL if
		pxNetworkBuffer is not NULL. */
		pxNetworkBuffer->pucEthernetBuffer = malloc(bufferSize);
	}
	UBaseType_t uxOptionsLength;
	if(pxSocket) {
		publicTCPPrepareSend(pxSocket, &pxNetworkBuffer, uxOptionsLength );
	}
}
