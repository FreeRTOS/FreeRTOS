/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for heaps.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) && (TRC_USE_HEAPS == 1)

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceHeapCreate(const char *szName, TraceUnsignedBaseType_t uxCurrent, TraceUnsignedBaseType_t uxHighWaterMark, TraceUnsignedBaseType_t uxMax, TraceHeapHandle_t *pxHeapHandle)
{
	TraceUnsignedBaseType_t uxStates[3];

	uxStates[TRC_HEAP_STATE_INDEX_CURRENT] = uxCurrent;
	uxStates[TRC_HEAP_STATE_INDEX_HIGHWATERMARK] = uxHighWaterMark;
	uxStates[TRC_HEAP_STATE_INDEX_MAX] = uxMax;

	return xTraceObjectRegisterInternal(PSF_EVENT_HEAP_CREATE, (void*)0, szName, 3u, uxStates, TRC_ENTRY_OPTION_HEAP, (TraceObjectHandle_t*)pxHeapHandle);
}

traceResult xTraceHeapAlloc(TraceHeapHandle_t xHeapHandle, void *pvAddress, TraceUnsignedBaseType_t uxSize)
{
	TraceUnsignedBaseType_t uxCurrent, uxHighWaterMark;
	
	if (xHeapHandle == 0)
	{
		/* This can happen */
		return TRC_FAIL;
	}

	/* If the address is null we assume this was a failed alloc attempt */
	if (pvAddress != (void*)0)
	{
		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetState(xHeapHandle, TRC_HEAP_STATE_INDEX_CURRENT, &uxCurrent) == TRC_SUCCESS);

		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetState(xHeapHandle, TRC_HEAP_STATE_INDEX_HIGHWATERMARK, &uxHighWaterMark) == TRC_SUCCESS);

		uxCurrent += uxSize;

		if (uxCurrent > uxHighWaterMark)
		{
			uxHighWaterMark = uxCurrent;
			/* This should never fail */
			TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState(xHeapHandle, TRC_HEAP_STATE_INDEX_HIGHWATERMARK, uxHighWaterMark) == TRC_SUCCESS);
		}

		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState(xHeapHandle, TRC_HEAP_STATE_INDEX_CURRENT, uxCurrent) == TRC_SUCCESS);
	}

	(void)xTraceEventCreate2((pvAddress != (void*)0) ? PSF_EVENT_MALLOC : PSF_EVENT_MALLOC_FAILED, (TraceUnsignedBaseType_t)pvAddress, uxSize);  /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 !MISRAC2012-Rule-11.6 Suppress conversion from pointer to integer check*/

	return TRC_SUCCESS;
}

traceResult xTraceHeapFree(TraceHeapHandle_t xHeapHandle, void *pvAddress, TraceUnsignedBaseType_t uxSize)
{
	TraceUnsignedBaseType_t uxCurrent;

	if (xHeapHandle == 0)
	{
		/* This can happen */
		return TRC_FAIL;
	}

	/* If the address is null we assume this was a failed alloc attempt */
	if (pvAddress != (void*)0)
	{
		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetState(xHeapHandle, TRC_HEAP_STATE_INDEX_CURRENT, &uxCurrent) == TRC_SUCCESS);

		uxCurrent -= uxSize;

		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState(xHeapHandle, TRC_HEAP_STATE_INDEX_CURRENT, uxCurrent) == TRC_SUCCESS);
	}

	(void)xTraceEventCreate2((pvAddress != (void*)0) ? PSF_EVENT_FREE : PSF_EVENT_FREE_FAILED, (TraceUnsignedBaseType_t)pvAddress, uxSize);  /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 !MISRAC2012-Rule-11.6 Suppress conversion from pointer to integer check*/

	return TRC_SUCCESS;
}

#endif
