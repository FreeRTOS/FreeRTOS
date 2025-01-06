/*
* Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of the diagnostics.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

static TraceDiagnosticsData_t *pxDiagnostics TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceDiagnosticsInitialize(TraceDiagnosticsData_t *pxBuffer)
{
	uint32_t i;
	
	/* This should never fail */
	TRC_ASSERT(pxBuffer != (void*)0);

	pxDiagnostics = pxBuffer;

	for (i = 0u; i < (TRC_DIAGNOSTICS_COUNT); i++)
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
	TRC_ASSERT(pxValue != (void*)0);

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
	if (xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_DIAGNOSTICS) == 0U)
	{
		return TRC_FAIL;
	}

	if (pxDiagnostics->metrics[TRC_DIAGNOSTICS_ENTRY_SLOTS_NO_ROOM] > 0)
	{
		(void)xTraceWarning(TRC_WARNING_ENTRY_TABLE_SLOTS);
		pxDiagnostics->metrics[TRC_DIAGNOSTICS_ENTRY_SLOTS_NO_ROOM] = 0;
	}

	if (pxDiagnostics->metrics[TRC_DIAGNOSTICS_ENTRY_SYMBOL_LONGEST_LENGTH] > (TRC_CFG_ENTRY_SYMBOL_MAX_LENGTH))
	{
		(void)xTraceWarning(TRC_WARNING_ENTRY_SYMBOL_MAX_LENGTH);
		pxDiagnostics->metrics[TRC_DIAGNOSTICS_ENTRY_SYMBOL_LONGEST_LENGTH] = 0;
	}

	if (pxDiagnostics->metrics[TRC_DIAGNOSTICS_BLOB_MAX_BYTES_TRUNCATED] > 0)
	{
		(void)xTraceWarning(TRC_WARNING_EVENT_SIZE_TRUNCATED);
		pxDiagnostics->metrics[TRC_DIAGNOSTICS_BLOB_MAX_BYTES_TRUNCATED] = 0;
	}

	if (pxDiagnostics->metrics[TRC_DIAGNOSTICS_STACK_MONITOR_NO_SLOTS] > 0)
	{
		(void)xTraceWarning(TRC_WARNING_STACKMON_NO_SLOTS);
		pxDiagnostics->metrics[TRC_DIAGNOSTICS_STACK_MONITOR_NO_SLOTS] = 0;
	}

	return TRC_SUCCESS;
}

#endif
