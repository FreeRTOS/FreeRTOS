/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The interface for the multi-core event buffer.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

traceResult xTraceMultiCoreEventBufferInitialize(TraceMultiCoreEventBuffer_t* const pxTraceMultiCoreEventBuffer, uint32_t uiOptions,
	uint8_t* puiBuffer, uint32_t uiSize)
{
	uint32_t i;
	uint32_t uiBufferSizePerCore;

	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != (void*)0);

	/* This should never fail */
	TRC_ASSERT(puiBuffer != (void*)0);

	uiBufferSizePerCore = ((uiSize / (uint32_t)(TRC_CFG_CORE_COUNT)) / sizeof(TraceUnsignedBaseType_t)) * sizeof(TraceUnsignedBaseType_t); /* BaseType aligned */

	/* This should never fail */
	TRC_ASSERT(uiBufferSizePerCore != 0u);

	for (i = 0u; i < (uint32_t)(TRC_CFG_CORE_COUNT); i++)
	{
		/* Set the event buffer pointers to point into the allocated space we have been given, this ensures
		 * a flat memory layout necessary for usage in streaming snaphot. */
		pxTraceMultiCoreEventBuffer->xEventBuffer[i] = (TraceEventBuffer_t*)(&puiBuffer[i * uiBufferSizePerCore]); /*cstat !MISRAC2004-11.4 !MISRAC2012-Rule-11.3 Suppress conversion between pointer types checks*/ /*cstat !MISRAC2004-17.4_b We need to access a spcific point in the buffer*/

		/* Initialize the event buffer structure with its memory buffer placed following its own structure data. */
		/* We need to check this */
		if (xTraceEventBufferInitialize(pxTraceMultiCoreEventBuffer->xEventBuffer[i], uiOptions,
			&puiBuffer[(i * uiBufferSizePerCore) + sizeof(TraceEventBuffer_t)], /*cstat !MISRAC2004-17.4_b We need to access a specific point in the buffer*/
			uiBufferSizePerCore - sizeof(TraceEventBuffer_t)) == TRC_FAIL)
		{
			return TRC_FAIL;
		}
	}

	return TRC_SUCCESS;
}

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)
/*cstat !MISRAC2012-Rule-5.1 Yes, these are long names*/
traceResult xTraceMultiCoreEventBufferAlloc(const TraceMultiCoreEventBuffer_t * const pxTraceMultiCoreEventBuffer, uint32_t uiSize,
	void **ppvData)
{
	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != (void*)0);

	TRC_ASSERT((TRC_CFG_GET_CURRENT_CORE()) < (TRC_CFG_CORE_COUNT));

	return xTraceEventBufferAlloc(pxTraceMultiCoreEventBuffer->xEventBuffer[TRC_CFG_GET_CURRENT_CORE()], uiSize, ppvData);
}

/*cstat !MISRAC2012-Rule-5.1 Yes, these are long names*/
traceResult xTraceMultiCoreEventBufferAllocCommit(const TraceMultiCoreEventBuffer_t * const pxTraceMultiCoreEventBuffer, void *pvData, uint32_t uiSize, int32_t *piBytesWritten)
{
	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != (void*)0);

	TRC_ASSERT((TRC_CFG_GET_CURRENT_CORE()) < (TRC_CFG_CORE_COUNT));

	return xTraceEventBufferAllocCommit(pxTraceMultiCoreEventBuffer->xEventBuffer[TRC_CFG_GET_CURRENT_CORE()], pvData, uiSize, piBytesWritten);
}

traceResult xTraceMultiCoreEventBufferPush(const TraceMultiCoreEventBuffer_t* const pxTraceMultiCoreEventBuffer,
	void* pvData, uint32_t uiSize, int32_t* piBytesWritten)
{
	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != (void*)0);

	TRC_ASSERT((TRC_CFG_GET_CURRENT_CORE()) < (TRC_CFG_CORE_COUNT));

	return xTraceEventBufferPush(pxTraceMultiCoreEventBuffer->xEventBuffer[TRC_CFG_GET_CURRENT_CORE()], pvData, uiSize, piBytesWritten);
}

#endif

/*cstat !MISRAC2012-Rule-5.1 Yes, these are long names*/
traceResult xTraceMultiCoreEventBufferTransferAll(const TraceMultiCoreEventBuffer_t* const pxTraceMultiCoreEventBuffer, int32_t* piBytesWritten)
{
	int32_t iBytesWritten = 0;
	uint32_t uiCoreId;

	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != (void*)0);

	/* This should never fail */
	TRC_ASSERT(piBytesWritten != (void*)0);

	*piBytesWritten = 0;

	for (uiCoreId = 0u; uiCoreId < (uint32_t)(TRC_CFG_CORE_COUNT); uiCoreId++)
	{
		/* We need to check this */
		if (xTraceEventBufferTransferAll(pxTraceMultiCoreEventBuffer->xEventBuffer[uiCoreId], &iBytesWritten) == TRC_FAIL)
		{
			return TRC_FAIL;
		}

		*piBytesWritten += iBytesWritten;
	}

	return TRC_SUCCESS;
}

/*cstat !MISRAC2012-Rule-5.1 Yes, these are long names*/
traceResult xTraceMultiCoreEventBufferTransferChunk(const TraceMultiCoreEventBuffer_t* const pxTraceMultiCoreEventBuffer, uint32_t uiChunkSize, int32_t* piBytesWritten)
{
	int32_t iBytesWritten = 0;
	uint32_t uiCoreId;

	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != (void*)0);

	/* This should never fail */
	TRC_ASSERT(piBytesWritten != (void*)0);

	*piBytesWritten = 0;

	for (uiCoreId = 0u; uiCoreId < (uint32_t)(TRC_CFG_CORE_COUNT); uiCoreId++)
	{
		/* We need to check this */
		if (xTraceEventBufferTransferChunk(pxTraceMultiCoreEventBuffer->xEventBuffer[uiCoreId], uiChunkSize, &iBytesWritten) == TRC_FAIL)
		{
			return TRC_FAIL;
		}

		*piBytesWritten += iBytesWritten;
	}

	return TRC_SUCCESS;
}

traceResult xTraceMultiCoreEventBufferClear(const TraceMultiCoreEventBuffer_t* const pxTraceMultiCoreEventBuffer)
{
	uint32_t uiCoreId;

	/* This should never fail */
	TRC_ASSERT(pxTraceMultiCoreEventBuffer != (void*)0);

	for (uiCoreId = 0u; uiCoreId < (uint32_t)(TRC_CFG_CORE_COUNT); uiCoreId++)
	{
		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEventBufferClear(pxTraceMultiCoreEventBuffer->xEventBuffer[uiCoreId]) == TRC_SUCCESS);
	}

	return TRC_SUCCESS;
}

#endif
