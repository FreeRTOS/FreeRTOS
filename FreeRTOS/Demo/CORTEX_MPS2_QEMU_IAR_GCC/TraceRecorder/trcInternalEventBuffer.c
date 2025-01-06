/*
 * Trace Recorder for Tracealyzer v4.10.2
 * Copyright 2023 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The implementation of the internal buffer.
 */

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) && (TRC_USE_INTERNAL_BUFFER == 1)

#include <stdio.h>
#include <string.h>
#include <stdarg.h>

static TraceMultiCoreEventBuffer_t *pxInternalEventBuffer TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceInternalEventBufferInitialize(uint8_t* puiBuffer, uint32_t uiSize)
{
	/* uiSize must be larger than sizeof(TraceMultiCoreEventBuffer_t) or there will be no room for any data */
	/* This should never fail */
	TRC_ASSERT(uiSize > sizeof(TraceMultiCoreEventBuffer_t));
	
	/* pxInternalBuffer will be placed at the beginning of the puiBuffer */
	pxInternalEventBuffer = (TraceMultiCoreEventBuffer_t*)puiBuffer;

	/* Send in a an address pointing after the TraceMultiCoreEventBuffer_t */
	/* We need to check this */
	if (xTraceMultiCoreEventBufferInitialize(pxInternalEventBuffer, TRC_EVENT_BUFFER_OPTION_SKIP,
		&puiBuffer[sizeof(TraceMultiCoreEventBuffer_t)], uiSize - sizeof(TraceMultiCoreEventBuffer_t)) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_INTERNAL_EVENT_BUFFER);

	return TRC_SUCCESS;
}

traceResult xTraceInternalEventBufferAlloc(uint32_t uiSize, void **ppvData)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_INTERNAL_EVENT_BUFFER));

	return xTraceMultiCoreEventBufferAlloc(pxInternalEventBuffer, uiSize, ppvData);
}

traceResult xTraceInternalEventBufferAllocCommit(void *pvData, uint32_t uiSize, int32_t *piBytesWritten)
{
	(void)pvData;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_INTERNAL_EVENT_BUFFER));

	return xTraceMultiCoreEventBufferAllocCommit(pxInternalEventBuffer, pvData, uiSize, piBytesWritten);
}

traceResult xTraceInternalEventBufferPush(void *pvData, uint32_t uiSize, int32_t *piBytesWritten)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_INTERNAL_EVENT_BUFFER));
	
	return xTraceMultiCoreEventBufferPush(pxInternalEventBuffer, pvData, uiSize, piBytesWritten);
}

traceResult xTraceInternalEventBufferTransferAll(void)
{
	int32_t iBytesWritten = 0;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_INTERNAL_EVENT_BUFFER));

	return xTraceMultiCoreEventBufferTransferAll(pxInternalEventBuffer, &iBytesWritten);
}

traceResult xTraceInternalEventBufferTransferChunk(void)
{
	int32_t iBytesWritten = 0;
	int32_t iCounter = 0;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_INTERNAL_EVENT_BUFFER));

	do
	{
		if (xTraceMultiCoreEventBufferTransferChunk(pxInternalEventBuffer, TRC_INTERNAL_BUFFER_CHUNK_SIZE, &iBytesWritten) == TRC_FAIL)
		{
			return TRC_FAIL;
		}

		iCounter++;
		/* This will do another loop if TRC_INTERNAL_BUFFER_CHUNK_TRANSFER_AGAIN_SIZE_LIMIT of data was transferred and we haven't already looped TRC_INTERNAL_BUFFER_CHUNK_TRANSFER_AGAIN_COUNT_LIMIT number of times */
	} while (iBytesWritten >= (int32_t)(TRC_INTERNAL_BUFFER_CHUNK_TRANSFER_AGAIN_SIZE_LIMIT) && iCounter < (int32_t)(TRC_INTERNAL_BUFFER_CHUNK_TRANSFER_AGAIN_COUNT_LIMIT));

	return TRC_SUCCESS;
}

traceResult xTraceInternalEventBufferClear()
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_INTERNAL_EVENT_BUFFER));
	
	return xTraceMultiCoreEventBufferClear(pxInternalEventBuffer);
}

#endif
