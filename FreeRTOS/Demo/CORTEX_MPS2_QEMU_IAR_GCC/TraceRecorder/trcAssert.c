/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for errors.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) && ((TRC_CFG_USE_TRACE_ASSERT) == 1)

#if (defined(TRC_CFG_TEST_MODE) && (TRC_CFG_TEST_MODE) == 1)

extern inline TraceBaseType_t prvTraceAssertCheckCondition(TraceBaseType_t condition);

#endif

#define TRC_ASSERT_STATE_INDEX_LINE_NUMBER 0u

static TraceAssertData_t* pxAssertData TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceAssertInitialize(TraceAssertData_t *pxBuffer)
{
	TRC_ASSERT(pxBuffer != (void*)0);

	pxAssertData = pxBuffer;
	pxAssertData->xEntry = 0;

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_ASSERT);

	return TRC_SUCCESS;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
void prvTraceAssertCreate(const char* szFilePath, TraceUnsignedBaseType_t uxLineNumber)
{
	TraceBaseType_t i, xLength;
	TraceUnsignedBaseType_t uxEntryLineNumber = 0xFFFFFFFFUL;
	static TraceUnsignedBaseType_t uxRecursionGuard = 0u;

	if (uxRecursionGuard == 0u)
	{
		/* Recursion can only get here once */
		uxRecursionGuard = 1u;

		if (xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ASSERT) == 0U)
		{
			return;
		}

		if (pxAssertData->xEntry == 0)
		{
			if (xTraceEntryCreate(&pxAssertData->xEntry) == TRC_FAIL)
			{
				return;
			}
		}

		(void)xTraceEntryGetState(pxAssertData->xEntry, TRC_ASSERT_STATE_INDEX_LINE_NUMBER, &uxEntryLineNumber);

		/* We only save the first ASSERT information */
		if (uxEntryLineNumber == 0u)
		{
			/* Find length */
			for (i = 0; (szFilePath[i] != (char)0) && (i < 128); i++) {} /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/

			xLength = i;

			/* Find last slash or backslash */
			for (i = xLength - 1; (i >= 0) && ((szFilePath[i] != '\\') && (szFilePath[i] != '/')); i--) {} /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/

			/* We treat the entry as an object and set it's name and state */
			(void)xTraceObjectSetName((TraceObjectHandle_t)pxAssertData->xEntry, &szFilePath[i + 1]); /*cstat !MISRAC2004-17.4_b We need to access a specific character in the string*/
			(void)xTraceObjectSetState((TraceObjectHandle_t)pxAssertData->xEntry, uxLineNumber);

			(void)xTraceError(TRC_ERROR_ASSERT);
		}
	}

	(void)xTraceDiagnosticsIncrease(TRC_DIAGNOSTICS_ASSERTS_TRIGGERED);
}

traceResult xTraceAssertGet(TraceStringHandle_t *pxFileNameStringHandle, TraceUnsignedBaseType_t *puxLineNumber)
{
	TRC_ASSERT(pxFileNameStringHandle != (void*)0);
	
	TRC_ASSERT(puxLineNumber != (void*)0);

	if (xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_ASSERT) == 0U)
	{
		return TRC_FAIL;
	}

	*puxLineNumber = 0u;
	(void)xTraceEntryGetState(pxAssertData->xEntry, TRC_ASSERT_STATE_INDEX_LINE_NUMBER, puxLineNumber);

	if (*puxLineNumber == 0u)
	{
		return TRC_FAIL;
	}
	
	/* The string handle can be set to the entry handle */
	*pxFileNameStringHandle = (TraceStringHandle_t)pxAssertData->xEntry;

	return TRC_SUCCESS;
}

#endif
