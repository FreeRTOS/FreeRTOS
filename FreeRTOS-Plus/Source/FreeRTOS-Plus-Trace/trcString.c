/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for strings.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

traceResult xTraceStringRegister(const char* szString, TraceStringHandle_t *pString)
{
	TraceEntryHandle_t xEntryHandle;
	TraceEventHandle_t xEventHandle = 0;
	uint32_t i = 0, uiLength = 0, uiValue = 0;

	/* This should never fail */
	TRC_ASSERT(szString != 0);
	
	/* This should never fail */
	TRC_ASSERT(pString != 0);

	/* We need to check this */
	if (xTraceEntryCreate(&xEntryHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/* The address to the available symbol table slot is the address we use */
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetSymbol(xEntryHandle, szString) == TRC_SUCCESS);

	*pString = (TraceStringHandle_t)xEntryHandle;

	for (i = 0; (szString[i] != 0) && (i < (TRC_ENTRY_TABLE_SLOT_SYMBOL_SIZE)); i++) {}

	uiLength = i;

	/* We need to check this */
	if (xTraceEventBegin(PSF_EVENT_OBJ_NAME, sizeof(void*) + uiLength, &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, (void*)xEntryHandle);
		xTraceEventAddData(xEventHandle, (void*)szString, uiLength);

		/* Check if we can truncate */
		xTraceEventPayloadRemaining(xEventHandle, &uiValue);
		if (uiValue > 0)
		{
			xTraceEventAdd8(xEventHandle, 0);
		}
		
		xTraceEventEnd(xEventHandle);
	}

	return TRC_SUCCESS;
}

TraceStringHandle_t xTraceRegisterString(const char *name)
{
	TraceStringHandle_t trcStr = 0;
	xTraceStringRegister(name, &trcStr);

	return trcStr;
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
