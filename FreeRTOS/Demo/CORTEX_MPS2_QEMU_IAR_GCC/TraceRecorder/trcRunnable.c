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

#define TRC_RUNNABLE_STATE_INDEX_OWNER_TASK 0UL

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceRunnableRegister(const char* szName, TraceRunnableRegisterMethod_t uxRegisterMethod, TraceRunnableHandle_t *pxRunnableHandle)
{
	TraceEntryHandle_t xEntryHandle;
	int32_t i;
	uint32_t uiLength = 0u;

	/* This should never fail */
	TRC_ASSERT(szName != (void*)0);

	/* This should never fail */
	TRC_ASSERT(pxRunnableHandle != (void*)0);

	for (i = 0; (szName[i] != (char)0) && (i < (int32_t)(TRC_ENTRY_TABLE_SLOT_SYMBOL_SIZE)); i++) {} /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/

	uiLength = (uint32_t)i;

	if (uxRegisterMethod == TRC_RUNNABLE_REGISTER_METHOD_USE_ENTRY_TABLE)
	{
		/* Check if we have already created an entry previously */
		if (*pxRunnableHandle == (void*)0)
		{
			/* We need to check this */
			if (xTraceEntryCreate(&xEntryHandle) == TRC_FAIL)
			{
				return TRC_FAIL;
			}

			TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetOptions(xEntryHandle, TRC_ENTRY_OPTION_RUNNABLE) == TRC_SUCCESS);
			
			TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState(xEntryHandle, TRC_RUNNABLE_STATE_INDEX_OWNER_TASK, (TraceUnsignedBaseType_t)xTraceTaskGetCurrentReturn()) == TRC_SUCCESS); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 !MISRAC2012-Rule-11.6 We need the address of the task*/

			/* The address to the available symbol table slot is the address we use */
			/* This should never fail */
			TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetSymbol(xEntryHandle, szName, uiLength) == TRC_SUCCESS);

			*pxRunnableHandle = (TraceRunnableHandle_t)xEntryHandle;
		}
	}
	else if (uxRegisterMethod == TRC_RUNNABLE_REGISTER_METHOD_USE_STRING_ADDRESS)
	{
		*pxRunnableHandle = (TraceRunnableHandle_t)szName; /*cstat !MISRAC2004-11.5 !MISRAC2012-Rule-11.8 We need the address of the string*/
	}
	else if (uxRegisterMethod == TRC_RUNNABLE_REGISTER_METHOD_USE_HANDLE_ADDRESS)
	{
		/* The handle address should be a unique value that we can use as handle */
		*pxRunnableHandle = (TraceRunnableHandle_t)pxRunnableHandle;
	}
	else
	{
		return TRC_FAIL;
	}

	return xTraceEventCreateData1(PSF_EVENT_RUNNABLE_REGISTER, (TraceUnsignedBaseType_t)*pxRunnableHandle, (TraceUnsignedBaseType_t*)szName, uiLength + 1);
}

#endif
