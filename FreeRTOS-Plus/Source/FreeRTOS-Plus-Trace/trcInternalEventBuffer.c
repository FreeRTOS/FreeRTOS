/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The implementation of the internal buffer.
 */

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#if (TRC_USE_INTERNAL_BUFFER == 1)

#include <stdio.h>
#include <string.h>
#include <stdarg.h>

static TraceMultiCoreEventBuffer_t *pxInternalEventBuffer;

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

traceResult xTraceInternalEventBufferPush(void *pvData, uint32_t uiSize, int32_t *piBytesWritten)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_INTERNAL_EVENT_BUFFER));
	
	return xTraceMultiCoreEventBufferPush(pxInternalEventBuffer, pvData, uiSize, piBytesWritten);
}

traceResult xTraceInternalEventBufferTransfer(int32_t *piBytesWritten)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_INTERNAL_EVENT_BUFFER));
	
	return xTraceMultiCoreEventBufferTransfer(pxInternalEventBuffer, piBytesWritten);
}

traceResult xTraceInternalEventBufferClear()
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_INTERNAL_EVENT_BUFFER));
	
	return xTraceMultiCoreEventBufferClear(pxInternalEventBuffer);
}

#endif /* (TRC_USE_INTERNAL_BUFFER == 1) */

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
