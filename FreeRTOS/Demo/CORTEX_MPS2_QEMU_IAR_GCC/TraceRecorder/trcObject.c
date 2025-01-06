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

#include <trcTypes.h>

#ifndef TRC_SEND_NAME_ONLY_ON_DELETE
#define TRC_SEND_NAME_ONLY_ON_DELETE 0
#endif

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceObjectRegisterInternal(uint32_t uiEventCode, void* const pvObject, const char* szName, TraceUnsignedBaseType_t uxStateCount, const TraceUnsignedBaseType_t uxStates[], TraceUnsignedBaseType_t uxOptions, TraceObjectHandle_t* pxObjectHandle)
{
	TraceEntryHandle_t xEntryHandle;
	TraceUnsignedBaseType_t i;
	void *pvAddress;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* This should never fail */
	TRC_ASSERT(pxObjectHandle != (void*)0);

	/* This should never fail */
	TRC_ASSERT(uxStateCount <= (uint32_t)(TRC_ENTRY_TABLE_STATE_COUNT));

	TRACE_ENTER_CRITICAL_SECTION();

	if (pvObject != (void*)0)
	{
		/* An address was supplied */
		if (xTraceEntryCreateWithAddress(pvObject, &xEntryHandle) == TRC_FAIL)
		{
			TRACE_EXIT_CRITICAL_SECTION();

			return TRC_FAIL;
		}
		
		pvAddress = pvObject;
	}
	else
	{
		/* No address was supplied */
		if (xTraceEntryCreate(&xEntryHandle) == TRC_FAIL)
		{
			TRACE_EXIT_CRITICAL_SECTION();

			return TRC_FAIL;
		}

		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetAddress(xEntryHandle, &pvAddress) == TRC_SUCCESS);
	}

	for (i = 0u; i < uxStateCount; i++)
	{
		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState(xEntryHandle, (uint32_t)i, uxStates[i]) == TRC_SUCCESS);
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetOptions(xEntryHandle, (uint32_t)uxOptions) == TRC_SUCCESS);

	*pxObjectHandle = (TraceObjectHandle_t)xEntryHandle;

	TRACE_EXIT_CRITICAL_SECTION();

	if ((szName != (void*)0) && (szName[0] != (char)0)) /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/
	{
		/* Not a null or empty string */
		/* This will set the symbol and create an event for it */
		/* This should never fail */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceObjectSetName((TraceObjectHandle_t)xEntryHandle, szName) == TRC_SUCCESS);
	}

	switch (uxStateCount)
	{
		case 0:
			xTraceEventCreate1(uiEventCode, (TraceUnsignedBaseType_t)pvAddress);
			break;
		case 1:
			xTraceEventCreate2(uiEventCode, (TraceUnsignedBaseType_t)pvAddress, uxStates[0]);
			break;
		case 2:
			xTraceEventCreate3(uiEventCode, (TraceUnsignedBaseType_t)pvAddress, uxStates[0], uxStates[1]);
			break;
		case 3:
			xTraceEventCreate4(uiEventCode, (TraceUnsignedBaseType_t)pvAddress, uxStates[0], uxStates[1], uxStates[2]);
			break;
		default:
			return TRC_FAIL;
			break;
	}

	return TRC_SUCCESS;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceObjectRegister(uint32_t uiEventCode, void* const pvObject, const char* szName, TraceUnsignedBaseType_t uxState, TraceObjectHandle_t *pxObjectHandle)
{
	return xTraceObjectRegisterInternal(uiEventCode, pvObject, szName, 1u, &uxState, 0u, pxObjectHandle);
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceObjectRegister2(uint32_t uiEventCode, void* const pvObject, const char* szName, TraceUnsignedBaseType_t uxState1, TraceUnsignedBaseType_t uxState2, TraceObjectHandle_t *pxObjectHandle)
{
	TraceUnsignedBaseType_t auxStates[2] = { uxState1, uxState2 };
	return xTraceObjectRegisterInternal(uiEventCode, pvObject, szName, 2u, auxStates, 0u, pxObjectHandle);
}

traceResult xTraceObjectUnregister(TraceObjectHandle_t xObjectHandle, uint32_t uiEventCode, TraceUnsignedBaseType_t uxState)
{
	void* pvObject = (void*)0;
	const char *szName = (void*)0; /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
#if (TRC_SEND_NAME_ONLY_ON_DELETE == 1)
	uint32_t uiLength;
	uint32_t i;
#endif

	/* If asserts are disabled this variable will not get used, this stops warnings. */
	(void)szName;

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetAddress((TraceEntryHandle_t)xObjectHandle, &pvObject) == TRC_SUCCESS);

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetSymbol((TraceEntryHandle_t)xObjectHandle, &szName) == TRC_SUCCESS);

#if (TRC_SEND_NAME_ONLY_ON_DELETE == 1)
	/* Send name event because this is a delete */

	for (i = 0u; (szName[i] != (char)0) && (i < 128u); i++) {} /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/

	uiLength = i;

	/* Send the name event, if possible */
	(void)xTraceEventCreateData1(PSF_EVENT_OBJ_NAME, (TraceUnsignedBaseType_t)pvObject, (TraceUnsignedBaseType_t*)szName, uiLength + 1); /* +1 for termination */
#endif /* (TRC_SEND_NAME_ONLY_ON_DELETE == 1) */

	/* Send the delete event, if possible */
	(void)xTraceEventCreate2(uiEventCode, (TraceUnsignedBaseType_t)(pvObject), uxState);  /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 !MISRAC2012-Rule-11.6 Suppress conversion from pointer to integer check*/

	return xTraceEntryDelete(xObjectHandle);
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceObjectSetName(TraceObjectHandle_t xObjectHandle, const char* szName)
{
	void* pvObject = (void*)0;
	uint32_t uiLength;
	uint32_t i;

    /* If asserts are disabled this variable will not get used, this stops warnings. */
	(void)pvObject;

	if (szName == (void*)0)
	{
		szName = ""; /*cstat !MISRAC2012-Rule-17.8 Suppress modified function parameter check*/
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetAddress((TraceEntryHandle_t)xObjectHandle, &pvObject) == TRC_SUCCESS);

	for (i = 0u; (szName[i] != (char)0) && (i < 128u); i++) {} /*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/ /*cstat !MISRAC2004-17.4_b We need to access every character in the string*/

	uiLength = i;

#if (TRC_SEND_NAME_ONLY_ON_DELETE == 0)
	/* Attempt to send name event now since we don't do it on delete events */
	(void)xTraceEventCreateData1(PSF_EVENT_OBJ_NAME, (TraceUnsignedBaseType_t)pvObject, (TraceUnsignedBaseType_t*)szName, uiLength + 1); /* +1 for termination */
#endif /* (TRC_SEND_NAME_ONLY_ON_DELETE == 0) */

	return xTraceEntrySetSymbol((TraceEntryHandle_t)xObjectHandle, szName, uiLength);
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceObjectRegisterWithoutHandle(uint32_t uiEventCode, void* pvObject, const char* szName, TraceUnsignedBaseType_t uxState)
{
	TraceObjectHandle_t xObjectHandle;

	return xTraceObjectRegisterInternal(uiEventCode, pvObject, szName, 1u, &uxState, 0u, &xObjectHandle);
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceObjectRegisterWithoutHandle2(uint32_t uiEventCode, void* pvObject, const char* szName, TraceUnsignedBaseType_t uxState1, TraceUnsignedBaseType_t uxState2)
{
	TraceObjectHandle_t xObjectHandle;
	TraceUnsignedBaseType_t auxStates[2] = { uxState1, uxState2 };
	
	return xTraceObjectRegisterInternal(uiEventCode, pvObject, szName, 2u, auxStates, 0u, &xObjectHandle);
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

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
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

#endif
