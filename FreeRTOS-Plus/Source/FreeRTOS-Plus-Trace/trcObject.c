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

#include <trcTypes.h>

#ifndef TRC_SEND_NAME_ONLY_ON_DELETE
#define TRC_SEND_NAME_ONLY_ON_DELETE 0
#endif

traceResult prvTraceObjectSendState(uint32_t uiEventCode, void* pvObject, TraceUnsignedBaseType_t uxState);
traceResult prvTraceObjectSendNameEvent(void* pvObject, const char* szName);

traceResult xTraceObjectRegisterInternal(uint32_t uiEventCode, void* pvObject, const char* szName, TraceUnsignedBaseType_t uxStateCount, TraceUnsignedBaseType_t uxStates[], TraceUnsignedBaseType_t uxOptions, TraceObjectHandle_t* pxObjectHandle)
{
	TraceEntryHandle_t xEntryHandle;
	TraceEventHandle_t xEventHandle = 0;
	TraceUnsignedBaseType_t i;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* This should never fail */
	TRC_ASSERT(pxObjectHandle != 0);

	/* This should never fail */
	TRC_ASSERT(uxStateCount <= (TRC_ENTRY_TABLE_STATE_COUNT));

	TRACE_ENTER_CRITICAL_SECTION();

	if (pvObject != 0)
	{
		/* An address was supplied */
		if (xTraceEntryCreateWithAddress(pvObject, &xEntryHandle) == TRC_FAIL)
		{
			TRACE_EXIT_CRITICAL_SECTION();

			return TRC_FAIL;
		}
	}
	else
	{
		/* No address was supplied */
		if (xTraceEntryCreate(&xEntryHandle) == TRC_FAIL)
		{
			TRACE_EXIT_CRITICAL_SECTION();

			return TRC_FAIL;
		}
	}

	for (i = 0; i < uxStateCount; i++)
	{
		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState(xEntryHandle, i, uxStates[i]) == TRC_SUCCESS);
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetOptions(xEntryHandle, uxOptions) == TRC_SUCCESS);

	*pxObjectHandle = (TraceObjectHandle_t)xEntryHandle;

	TRACE_EXIT_CRITICAL_SECTION();

	if (szName != 0 && szName[0] != 0)
	{
		/* Not a null or empty string */
		/* This will set the symbol and create an event for it */
		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceObjectSetName((TraceObjectHandle_t)xEntryHandle, szName) == TRC_SUCCESS);
	}

	/* Send the create event, if possible */
	/*We need to check this */
	if (xTraceEventBegin(uiEventCode, sizeof(void*) + uxStateCount * sizeof(TraceUnsignedBaseType_t) + sizeof(TraceUnsignedBaseType_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, pvObject);
		for (i = 0; i < uxStateCount; i++)
		{
			xTraceEventAddUnsignedBaseType(xEventHandle, uxStates[i]);
		}
		xTraceEventAddUnsignedBaseType(xEventHandle, uxOptions);
		xTraceEventEnd(xEventHandle);
	}

	return TRC_SUCCESS;
}

traceResult xTraceObjectRegister(uint32_t uiEventCode, void *pvObject, const char* szName, TraceUnsignedBaseType_t uxState, TraceObjectHandle_t *pxObjectHandle)
{
	TraceEntryHandle_t xEntryHandle;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* This should never fail */
	TRC_ASSERT(pxObjectHandle != 0);

	TRACE_ENTER_CRITICAL_SECTION();

	if (pvObject != 0)
	{
		/* An address was supplied */
		if (xTraceEntryCreateWithAddress(pvObject, &xEntryHandle) == TRC_FAIL)
		{
			TRACE_EXIT_CRITICAL_SECTION();

			return TRC_FAIL;
		}
	}
	else
	{
		/* No address was supplied */
		if (xTraceEntryCreate(&xEntryHandle) == TRC_FAIL)
		{
			TRACE_EXIT_CRITICAL_SECTION();

			return TRC_FAIL;
		}
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState(xEntryHandle, 0, uxState) == TRC_SUCCESS);

	*pxObjectHandle = (TraceObjectHandle_t)xEntryHandle;

	TRACE_EXIT_CRITICAL_SECTION();

	if (szName != 0 && szName[0] != 0)
	{
		/* Not a null or empty string */
		/* This will set the symbol and create an event for it */
		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceObjectSetName((TraceObjectHandle_t)xEntryHandle, szName) == TRC_SUCCESS);
	}

	/* Send the create event, if possible */
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(prvTraceObjectSendState(uiEventCode, pvObject, uxState) == TRC_SUCCESS);

	return TRC_SUCCESS;
}

traceResult xTraceObjectUnregister(TraceObjectHandle_t xObjectHandle, uint32_t uiEventCode, TraceUnsignedBaseType_t uxState)
{
	void* pvObject;
	const char *szName;

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetAddress((TraceEntryHandle_t)xObjectHandle, &pvObject) == TRC_SUCCESS);

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetSymbol((TraceEntryHandle_t)xObjectHandle, &szName) == TRC_SUCCESS);

#if (TRC_SEND_NAME_ONLY_ON_DELETE == 1)
	/* Send name event because this is a delete */
	/* This should never fail */
	TRC_ASSERT(prvTraceObjectSendNameEvent(pvObject, szName) == TRC_SUCCESS);
#endif /* (TRC_SEND_NAME_ONLY_ON_DELETE == 1) */

	/* Send the delete event, if possible */
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(prvTraceObjectSendState(uiEventCode, pvObject, uxState) == TRC_SUCCESS);

	return xTraceEntryDelete(xObjectHandle);
}

traceResult xTraceObjectSetName(TraceObjectHandle_t xObjectHandle, const char* szName)
{
	void* pvObject;

	if (szName == 0)
	{
		szName = "";
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetAddress((TraceEntryHandle_t)xObjectHandle, &pvObject) == TRC_SUCCESS);

#if (TRC_SEND_NAME_ONLY_ON_DELETE == 0)
	/* Send name event now since we don't do it on delete events */
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(prvTraceObjectSendNameEvent(pvObject, szName) == TRC_SUCCESS);
#endif /* (TRC_SEND_NAME_ONLY_ON_DELETE == 0) */

	return xTraceEntrySetSymbol((TraceEntryHandle_t)xObjectHandle, szName);
}

traceResult xTraceObjectRegisterWithoutHandle(uint32_t uiEventCode, void* pvObject, const char* szName, TraceUnsignedBaseType_t uxState)
{
	TraceObjectHandle_t xObjectHandle;

	return xTraceObjectRegister(uiEventCode, pvObject, szName, uxState, &xObjectHandle);
}

traceResult xTraceObjectUnregisterWithoutHandle(uint32_t uiEventCode, void* pvObject, TraceUnsignedBaseType_t uxState)
{
	TraceEntryHandle_t xEntryHandle;
	traceResult xResult;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_ENTER_CRITICAL_SECTION();

	if (xTraceEntryFind(pvObject, &xEntryHandle) == TRC_FAIL)
	{
		TRACE_EXIT_CRITICAL_SECTION();

		return TRC_FAIL;
	}

	xResult = xTraceObjectUnregister((TraceObjectHandle_t)xEntryHandle, uiEventCode, uxState);

	TRACE_EXIT_CRITICAL_SECTION();

	return xResult;
}

traceResult xTraceObjectSetNameWithoutHandle(void* pvObject, const char* szName)
{
	TraceEntryHandle_t xEntryHandle;
	traceResult xResult;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_ENTER_CRITICAL_SECTION();

	if (xTraceEntryFind(pvObject, &xEntryHandle) == TRC_FAIL)
	{
		/* No previous entry found. Create one. */
		if (xTraceEntryCreateWithAddress(pvObject, &xEntryHandle) == TRC_FAIL)
		{
			TRACE_EXIT_CRITICAL_SECTION();

			return TRC_FAIL;
		}
	}

	xResult = xTraceObjectSetName((TraceObjectHandle_t)xEntryHandle, szName);

	TRACE_EXIT_CRITICAL_SECTION();

	return xResult;
}

traceResult xTraceObjectSetSpecificStateWithoutHandle(void* pvObject, uint32_t uiIndex, TraceUnsignedBaseType_t uxState)
{
	TraceEntryHandle_t xEntryHandle;
	traceResult xResult;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_ENTER_CRITICAL_SECTION();

	if (xTraceEntryFind(pvObject, &xEntryHandle) == TRC_FAIL)
	{
		TRACE_EXIT_CRITICAL_SECTION();

		return TRC_FAIL;
	}

	xResult = xTraceObjectSetSpecificState((TraceObjectHandle_t)xEntryHandle, uiIndex, uxState);
	
	TRACE_EXIT_CRITICAL_SECTION();

	return xResult;
}

traceResult xTraceObjectSetOptionsWithoutHandle(void* pvObject, uint32_t uiMask)
{
	TraceEntryHandle_t xEntryHandle;
	traceResult xResult;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_ENTER_CRITICAL_SECTION();

	if (xTraceEntryFind(pvObject, &xEntryHandle) == TRC_FAIL)
	{
		/* No previous entry found. Create one. */
		if (xTraceEntryCreateWithAddress(pvObject, &xEntryHandle) == TRC_FAIL)
		{
			TRACE_EXIT_CRITICAL_SECTION();

			return TRC_FAIL;
		}
	}

	xResult = xTraceObjectSetOptions((TraceObjectHandle_t)xEntryHandle, uiMask);

	TRACE_EXIT_CRITICAL_SECTION();

	return xResult;
}

traceResult prvTraceObjectSendState(uint32_t uiEventCode, void* pvObject, TraceUnsignedBaseType_t uxState)
{
	TraceEventHandle_t xEventHandle = 0;

	if (xTraceEventBegin(uiEventCode, sizeof(void*) + sizeof(TraceUnsignedBaseType_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, pvObject);
		xTraceEventAddUnsignedBaseType(xEventHandle, uxState);
		xTraceEventEnd(xEventHandle);
	}

	return TRC_SUCCESS;
}

traceResult prvTraceObjectSendNameEvent(void* pvObject, const char* szName)
{
	uint32_t i = 0, uiLength = 0, uiValue = 0;
	TraceEventHandle_t xEventHandle = 0;

	for (i = 0; (szName[i] != 0) && (i < (TRC_ENTRY_TABLE_SLOT_SYMBOL_SIZE)); i++) {}

	uiLength = i;

	if (xTraceEventBegin(PSF_EVENT_OBJ_NAME, sizeof(void*) + uiLength, &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, pvObject);
		xTraceEventAddData(xEventHandle, (void*)szName, uiLength);

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

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
