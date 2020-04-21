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
#include "FreeRTOS_ARP.h"


ARPPacket_t xARPPacket;
NetworkBufferDescriptor_t xNetworkBuffer;

/* STUB!
 * We assume that the pxGetNetworkBufferWithDescriptor function is
 * implemented correctly and returns a valid data structure.
 * This is the mock to mimic the expected behavior.
 * If this allocation fails, this might invalidate the proof.
 * FreeRTOS_OutputARPRequest calls pxGetNetworkBufferWithDescriptor
 * to get a NetworkBufferDescriptor. Then it calls vARPGenerateRequestPacket
 * passing this buffer along in the function call. vARPGenerateRequestPacket
 * casts the pointer xNetworkBuffer.pucEthernetBuffer into an ARPPacket_t pointer
 * and writes a complete ARPPacket to it. Therefore the buffer has to be at least of the size
 * of an ARPPacket to gurantee memory safety.
 */
NetworkBufferDescriptor_t *pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks ){
	#ifdef CBMC_PROOF_ASSUMPTION_HOLDS
		#ifdef ipconfigETHERNET_MINIMUM_PACKET_BYTES
			xNetworkBuffer.pucEthernetBuffer = malloc(ipconfigETHERNET_MINIMUM_PACKET_BYTES);
		#else
			xNetworkBuffer.pucEthernetBuffer = malloc(xRequestedSizeBytes);
		#endif
	#else
		uint32_t malloc_size;
		__CPROVER_assert(!__CPROVER_overflow_mult(2, xRequestedSizeBytes));
		__CPROVER_assume(malloc_size > 0 && malloc_size < 2 * xRequestedSizeBytes);
		xNetworkBuffer.pucEthernetBuffer = malloc(malloc_size);
	#endif
	xNetworkBuffer.xDataLength = xRequestedSizeBytes;
	return &xNetworkBuffer;
}


void harness()
{
	uint32_t ulIPAddress;
	FreeRTOS_OutputARPRequest( ulIPAddress );
}
