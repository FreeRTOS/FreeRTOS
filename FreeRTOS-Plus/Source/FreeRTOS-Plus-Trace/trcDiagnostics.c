/*
* Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of the diagnostics.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

typedef struct TraceDiagnostics
{
	TraceBaseType_t metrics[TRC_DIAGNOSTICS_COUNT];
} TraceDiagnostics_t;

static TraceDiagnostics_t *pxDiagnostics;

traceResult xTraceDiagnosticsInitialize(TraceDiagnosticsBuffer_t *pxBuffer)
{
	uint32_t i;
	
	TRC_ASSERT_EQUAL_SIZE(TraceDiagnosticsBuffer_t, TraceDiagnostics_t);

	/* This should never fail */
	TRC_ASSERT(pxBuffer != 0);

	pxDiagnostics = (TraceDiagnostics_t*)pxBuffer;

	for (i = 0; i < TRC_DIAGNOSTICS_COUNT; i++)
	{
		pxDiagnostics->metrics[i] = 0;
	}

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_DIAGNOSTICS);

	return TRC_SUCCESS;
}

traceResult xTraceDiagnosticsGet(TraceDiagnosticsType_t xType, TraceBaseType_t* pxValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_DIAGNOSTICS));

	/* This should never fail */
	TRC_ASSERT((TraceUnsignedBaseType_t)xType < TRC_DIAGNOSTICS_COUNT);

	/* This should never fail */
	TRC_ASSERT(pxValue != 0);

	*pxValue = pxDiagnostics->metrics[(TraceUnsignedBaseType_t)xType];

	return TRC_SUCCESS;
}

traceResult xTraceDiagnosticsSet(TraceDiagnosticsType_t xType, TraceBaseType_t xValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_DIAGNOSTICS));

	/* This should never fail */
	TRC_ASSERT((TraceUnsignedBaseType_t)xType < TRC_DIAGNOSTICS_COUNT);

	pxDiagnostics->metrics[(TraceUnsignedBaseType_t)xType] = xValue;

	return TRC_SUCCESS;
}

traceResult xTraceDiagnosticsAdd(TraceDiagnosticsType_t xType, TraceBaseType_t xValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_DIAGNOSTICS));

	/* This should never fail */
	TRC_ASSERT((TraceUnsignedBaseType_t)xType < TRC_DIAGNOSTICS_COUNT);

	pxDiagnostics->metrics[(TraceUnsignedBaseType_t)xType] += xValue;

	return TRC_SUCCESS;
}

traceResult xTraceDiagnosticsIncrease(TraceDiagnosticsType_t xType)
{
	return xTraceDiagnosticsAdd(xType, 1);
}

traceResult xTraceDiagnosticsDecrease(TraceDiagnosticsType_t xType)
{
	return xTraceDiagnosticsAdd(xType, -1);
}

traceResult xTraceDiagnosticsSetIfHigher(TraceDiagnosticsType_t xType, TraceBaseType_t xValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_DIAGNOSTICS));

	/* This should never fail */
	TRC_ASSERT((TraceUnsignedBaseType_t)xType < TRC_DIAGNOSTICS_COUNT);

	if (xValue > pxDiagnostics->metrics[xType])
	{
		pxDiagnostics->metrics[(TraceUnsignedBaseType_t)xType] = xValue;
	}

	return TRC_SUCCESS;
}

traceResult xTraceDiagnosticsSetIfLower(TraceDiagnosticsType_t xType, TraceBaseType_t xValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_DIAGNOSTICS));

	/* This should never fail */
	TRC_ASSERT((TraceUnsignedBaseType_t)xType < TRC_DIAGNOSTICS_COUNT);

	if (xValue < pxDiagnostics->metrics[(TraceUnsignedBaseType_t)xType])
	{
		pxDiagnostics->metrics[(TraceUnsignedBaseType_t)xType] = xValue;
	}

	return TRC_SUCCESS;
}

traceResult xTraceDiagnosticsCheckStatus(void)
{
	/* It is probably good if we always check this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_DIAGNOSTICS))
	{
		return TRC_FAIL;
	}

	if (pxDiagnostics->metrics[TRC_DIAGNOSTICS_ENTRY_SLOTS_NO_ROOM] > 0)
	{
		xTraceWarning(TRC_WARNING_ENTRY_TABLE_SLOTS);
		pxDiagnostics->metrics[TRC_DIAGNOSTICS_ENTRY_SLOTS_NO_ROOM] = 0;
	}

	if (pxDiagnostics->metrics[TRC_DIAGNOSTICS_ENTRY_SYMBOL_LONGEST_LENGTH] > (TRC_CFG_ENTRY_SYMBOL_MAX_LENGTH))
	{
		xTraceWarning(TRC_WARNING_ENTRY_SYMBOL_MAX_LENGTH);
		pxDiagnostics->metrics[TRC_DIAGNOSTICS_ENTRY_SYMBOL_LONGEST_LENGTH] = 0;
	}

	if (pxDiagnostics->metrics[TRC_DIAGNOSTICS_BLOB_MAX_BYTES_TRUNCATED] > 0)
	{
		xTraceWarning(TRC_WARNING_EVENT_SIZE_TRUNCATED);
		pxDiagnostics->metrics[TRC_DIAGNOSTICS_BLOB_MAX_BYTES_TRUNCATED] = 0;
	}

	if (pxDiagnostics->metrics[TRC_DIAGNOSTICS_STACK_MONITOR_NO_SLOTS] > 0)
	{
		xTraceWarning(TRC_WARNING_STACKMON_NO_SLOTS);
		pxDiagnostics->metrics[TRC_DIAGNOSTICS_STACK_MONITOR_NO_SLOTS] = 0;
	}

	return TRC_SUCCESS;
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
