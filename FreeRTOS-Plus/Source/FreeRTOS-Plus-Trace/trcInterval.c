/*
* Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of intervals.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#define TRC_INTERVAL_STATE_INDEX 0

traceResult xTraceIntervalCreate(const char *szName, TraceIntervalHandle_t *pxIntervalHandle)
{
	TraceObjectHandle_t xObjectHandle;

	/* This should never fail */
	TRC_ASSERT(pxIntervalHandle != 0);

	/* We need to check this */
	if (xTraceObjectRegister(PSF_EVENT_INTERVAL_CREATE, 0, szName, 0, &xObjectHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetOptions((TraceEntryHandle_t)xObjectHandle, TRC_ENTRY_OPTION_INTERVAL) == TRC_SUCCESS);

	*pxIntervalHandle = (TraceIntervalHandle_t)xObjectHandle;
	
	return TRC_SUCCESS;
}

traceResult xTraceIntervalStart(TraceIntervalHandle_t xIntervalHandle)
{
	TraceEventHandle_t xEventHandle = 0;
	
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState((TraceEntryHandle_t)xIntervalHandle, TRC_INTERVAL_STATE_INDEX, 1) == TRC_SUCCESS);

	/* We need to check this */
	if (xTraceEventBegin(PSF_EVENT_INTERVAL_STATECHANGE, sizeof(void*) + sizeof(uint32_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, (void*)xIntervalHandle);
		xTraceEventAdd32(xEventHandle, 1);
		xTraceEventEnd(xEventHandle);
	}

	return TRC_SUCCESS;
}

traceResult xTraceIntervalStop(TraceIntervalHandle_t xIntervalHandle)
{
	TraceEventHandle_t xEventHandle = 0;
	
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState((TraceEntryHandle_t)xIntervalHandle, TRC_INTERVAL_STATE_INDEX, 0) == TRC_SUCCESS);

	/* We need to check this */
	if (xTraceEventBegin(PSF_EVENT_INTERVAL_STATECHANGE, sizeof(void*) + sizeof(uint32_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, (void*)xIntervalHandle);
		xTraceEventAdd32(xEventHandle, 0);
		xTraceEventEnd(xEventHandle);
	}
	
	return TRC_SUCCESS;
}

traceResult xTraceIntervalGetState(TraceIntervalHandle_t xIntervalHandle, TraceUnsignedBaseType_t *puxState)
{
	return xTraceEntryGetState((TraceEntryHandle_t)xIntervalHandle, TRC_INTERVAL_STATE_INDEX, puxState);
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
