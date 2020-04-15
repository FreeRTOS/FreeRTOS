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

#include "../../utility/memory_assignments.c"

/* This proof assumes that prvTCPPrepareSend and prvTCPReturnPacket are correct.
These functions are proved to be correct separately. */

BaseType_t publicTCPHandleState( FreeRTOS_Socket_t *pxSocket, NetworkBufferDescriptor_t **ppxNetworkBuffer );

void harness() {
	FreeRTOS_Socket_t *pxSocket = ensure_FreeRTOS_Socket_t_is_allocated();
	size_t socketSize = sizeof(FreeRTOS_Socket_t);
	if (ensure_memory_is_valid(pxSocket, socketSize)) {
		/* ucOptionLength is the number of valid bytes in ulOptionsData[].
		ulOptionsData[] is initialized as uint32_t ulOptionsData[ipSIZE_TCP_OPTIONS/sizeof(uint32_t)].
		This assumption is required for a memcpy function that copies uxOptionsLength
		data from pxTCPHeader->ucOptdata to pxTCPWindow->ulOptionsData.*/
		__CPROVER_assume(pxSocket->u.xTCP.xTCPWindow.ucOptionLength == sizeof(uint32_t) * ipSIZE_TCP_OPTIONS/sizeof(uint32_t));
		/* uxRxWinSize is initialized as size_t. This assumption is required to terminate `while(uxWinSize > 0xfffful)` loop.*/
		__CPROVER_assume(pxSocket->u.xTCP.uxRxWinSize >= 0 && pxSocket->u.xTCP.uxRxWinSize <= sizeof(size_t));
		/* uxRxWinSize is initialized as uint16_t. This assumption is required to terminate `while(uxWinSize > 0xfffful)` loop.*/
		__CPROVER_assume(pxSocket->u.xTCP.usInitMSS == sizeof(uint16_t));
	}

	NetworkBufferDescriptor_t *pxNetworkBuffer = ensure_FreeRTOS_NetworkBuffer_is_allocated();
	size_t bufferSize = sizeof(NetworkBufferDescriptor_t);
	if(ensure_memory_is_valid(pxNetworkBuffer, bufferSize)) {
		pxNetworkBuffer->pucEthernetBuffer = safeMalloc(sizeof(TCPPacket_t));
	}
	if (ensure_memory_is_valid(pxSocket, socketSize) &&
		ensure_memory_is_valid(pxNetworkBuffer, bufferSize) &&
		ensure_memory_is_valid(pxNetworkBuffer->pucEthernetBuffer, sizeof(TCPPacket_t)) &&
		ensure_memory_is_valid(pxSocket->u.xTCP.pxPeerSocket, socketSize)) {

			publicTCPHandleState(pxSocket, &pxNetworkBuffer);

	}
}
