/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The interface for the multi-core event buffer.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

traceResult xTraceMultiCoreEventBufferInitialize(TraceMultiCoreEventBuffer_t* pxTraceMultiCoreEventBuffer, uint32_t uiOptions,
	uint8_t* puiBuffer, uint32_t uiSize)
{
	uint32_t i;

	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != 0);

	/* This should never fail */
	TRC_ASSERT(puiBuffer != 0);

	uint32_t uiBufferSizePerCore = uiSize / TRC_CFG_CORE_COUNT;

	/* This should never fail */
	TRC_ASSERT(uiBufferSizePerCore != 0);

	for (i = 0; i < TRC_CFG_CORE_COUNT; i++)
	{
		/* Set the event buffer pointers to point into the allocated space we have been given, this ensures
		 * a flat memory layout necessary for usage in streaming snaphot. */
		pxTraceMultiCoreEventBuffer->xEventBuffer[i] = (TraceEventBuffer_t*)(&puiBuffer[i * uiBufferSizePerCore]);

		/* Initialize the event buffer structure with its memory buffer placed following its own structure data. */
		/* We need to check this */
		if (xTraceEventBufferInitialize(pxTraceMultiCoreEventBuffer->xEventBuffer[i], uiOptions,
			&puiBuffer[(i * uiBufferSizePerCore) + sizeof(TraceEventBuffer_t)],
			uiBufferSizePerCore - sizeof(TraceEventBuffer_t)) == TRC_FAIL)
		{
			return TRC_FAIL;
		}
	}

	return TRC_SUCCESS;
}

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

traceResult xTraceMultiCoreEventBufferPush(TraceMultiCoreEventBuffer_t* pxTraceMultiCoreEventBuffer,
	void* pvData, uint32_t uiSize, int32_t* piBytesWritten)
{
	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != 0);

	TRC_ASSERT((TRC_CFG_GET_CURRENT_CORE()) < (TRC_CFG_CORE_COUNT));

	return xTraceEventBufferPush(pxTraceMultiCoreEventBuffer->xEventBuffer[TRC_CFG_GET_CURRENT_CORE()], pvData, uiSize, piBytesWritten);
}

#endif

traceResult xTraceMultiCoreEventBufferTransfer(TraceMultiCoreEventBuffer_t* pxTraceMultiCoreEventBuffer, int32_t* piBytesWritten)
{
	int32_t iBytesWritten = 0;
	uint32_t coreId;

	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != 0);

	/* This should never fail */
	TRC_ASSERT(piBytesWritten != 0);

	*piBytesWritten = 0;

	for (coreId = 0; coreId < TRC_CFG_CORE_COUNT; coreId++)
	{
		/* We need to check this */
		if (xTraceEventBufferTransfer(pxTraceMultiCoreEventBuffer->xEventBuffer[coreId], &iBytesWritten) == TRC_FAIL)
		{
			return TRC_FAIL;
		}

		*piBytesWritten += iBytesWritten;
	}

	return TRC_SUCCESS;
}

traceResult xTraceMultiCoreEventBufferClear(TraceMultiCoreEventBuffer_t* pxTraceMultiCoreEventBuffer)
{
	uint32_t coreId;

	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != 0);

	for (coreId = 0; coreId < TRC_CFG_CORE_COUNT; coreId++)
	{
		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEventBufferClear(pxTraceMultiCoreEventBuffer->xEventBuffer[coreId]) == TRC_SUCCESS);
	}

	return TRC_SUCCESS;
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
