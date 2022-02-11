/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for errors.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

#if (defined(TRC_CFG_TEST_MODE) && (TRC_CFG_TEST_MODE) == 1)

extern inline TraceBaseType_t prvTraceAssertCheckCondition(TraceBaseType_t condition);

#endif

#define TRC_ASSERT_STATE_INDEX_LINE_NUMBER 0

typedef struct TraceAssertInfo
{
	TraceEntryHandle_t xEntry;
} TraceAssertInfo_t;

static TraceAssertInfo_t* pxAssertInfo;

traceResult xTraceAssertInitialize(TraceAssertBuffer_t *pxBuffer)
{
	TRC_ASSERT_EQUAL_SIZE(TraceAssertBuffer_t, TraceAssertInfo_t);

	TRC_ASSERT(pxBuffer != 0);

	pxAssertInfo = (TraceAssertInfo_t*)pxBuffer;
	pxAssertInfo->xEntry = 0;

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_ASSERT);

	return TRC_SUCCESS;
}

void prvTraceAssertCreate(const char* szFilePath, TraceUnsignedBaseType_t uxLineNumber)
{
	TraceBaseType_t i, xLength;
	TraceUnsignedBaseType_t uxEntryLineNumber = 0xFFFFFFFF;
	static TraceUnsignedBaseType_t uxRecursionGuard = 0;

	if (uxRecursionGuard == 0)
	{
		/* Recursion can only get here once */
		uxRecursionGuard = 1;

		if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ASSERT))
		{
			return;
		}

		if (pxAssertInfo->xEntry == 0)
		{
			if (xTraceEntryCreate(&pxAssertInfo->xEntry) == TRC_FAIL)
			{
				return;
			}
		}

		xTraceEntryGetState(pxAssertInfo->xEntry, TRC_ASSERT_STATE_INDEX_LINE_NUMBER, &uxEntryLineNumber);

		/* We only save the first ASSERT information */
		if (uxEntryLineNumber == 0)
		{
			/* Find length */
			for (i = 0; (szFilePath[i] != 0) && (i < 128); i++) {}

			xLength = i;

			/* Find last slash or backslash */
			for (i = xLength - 1; (i >= 0) && ((szFilePath[i] != '\\') && (szFilePath[i] != '/')); i--) {}

			/* We treat the entry as an object and set it's name and state */
			xTraceObjectSetName((TraceObjectHandle_t)pxAssertInfo->xEntry, &szFilePath[i + 1]);
			xTraceObjectSetState((TraceObjectHandle_t)pxAssertInfo->xEntry, uxLineNumber);

			xTraceError(TRC_ERROR_ASSERT);
		}
	}

	xTraceDiagnosticsIncrease(TRC_DIAGNOSTICS_ASSERTS_TRIGGERED);
}

traceResult xTraceAssertGet(TraceStringHandle_t *pxFileNameStringHandle, TraceUnsignedBaseType_t *puxLineNumber)
{
	TRC_ASSERT(pxFileNameStringHandle != 0);
	
	TRC_ASSERT(puxLineNumber != 0);

	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ASSERT))
	{
		return TRC_FAIL;
	}

	*puxLineNumber = 0;
	xTraceEntryGetState(pxAssertInfo->xEntry, TRC_ASSERT_STATE_INDEX_LINE_NUMBER, puxLineNumber);

	if (*puxLineNumber == 0)
	{
		return TRC_FAIL;
	}
	
	/* The string handle can be set to the entry handle */
	*pxFileNameStringHandle = (TraceStringHandle_t)pxAssertInfo->xEntry;

	return TRC_SUCCESS;
}

#endif /* ((TRC_CFG_USE_TRACE_ASSERT) == 1) */

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
