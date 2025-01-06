/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for strings.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceStringRegister(const char* szString, TraceStringHandle_t *pString)
{
	TraceEntryHandle_t xEntryHandle;
	int32_t i;
	uint32_t uiLength = 0u;

	/* This should never fail */
	TRC_ASSERT(szString != (void*)0);
	
	/* This should never fail */
	TRC_ASSERT(pString != (void*)0);

	/* We need to check this */
	if (xTraceEntryCreate(&xEntryHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	for (i = 0; (szString[i] != (char)0) && (i < (int32_t)(TRC_ENTRY_TABLE_SLOT_SYMBOL_SIZE)); i++) {} /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/

	uiLength = (uint32_t)i;

	/* The address to the available symbol table slot is the address we use */
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetSymbol(xEntryHandle, szString, uiLength) == TRC_SUCCESS);

	*pString = (TraceStringHandle_t)xEntryHandle;

	return xTraceEventCreateData1(PSF_EVENT_OBJ_NAME, (TraceUnsignedBaseType_t)xEntryHandle, (TraceUnsignedBaseType_t*)szString, uiLength + 1);
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
TraceStringHandle_t xTraceRegisterString(const char *name)
{
	TraceStringHandle_t trcStr = 0;
	(void)xTraceStringRegister(name, &trcStr);

	return trcStr;
}

#endif
