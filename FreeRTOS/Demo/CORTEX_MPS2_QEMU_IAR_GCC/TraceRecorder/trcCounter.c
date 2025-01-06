/*
* Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of intervals.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

static TraceCounterData_t *pxCounterData TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceCounterInitialize(TraceCounterData_t *pxBuffer)
{
	TRC_ASSERT(pxBuffer != (void*)0);

	pxCounterData = pxBuffer;
	
	pxCounterData->xCallbackFunction = 0;
	
	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_COUNTER);
	
	return TRC_SUCCESS;
}

traceResult xTraceCounterSetCallback(const TraceCounterCallback_t xCallback)
{
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_COUNTER));
	
	TRC_ASSERT(xCallback != 0);

	pxCounterData->xCallbackFunction = xCallback;

	return TRC_SUCCESS;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceCounterCreate(const char *szName, TraceBaseType_t xInitialValue, TraceBaseType_t xLowerLimit, TraceBaseType_t xUpperLimit, TraceCounterHandle_t *pxCounterHandle)
{
	TraceObjectHandle_t xObjectHandle;
	TraceUnsignedBaseType_t uxStates[3] = { 0 };

	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_COUNTER));

	/* This should never fail */
	TRC_ASSERT(pxCounterHandle != (void*)0);

	TRC_ASSERT((xInitialValue >= xLowerLimit) && (xInitialValue <= xUpperLimit));

	uxStates[TRC_COUNTER_VALUE_INDEX] = (TraceUnsignedBaseType_t)xInitialValue;
	uxStates[TRC_COUNTER_LOWER_LIMIT_INDEX] = (TraceUnsignedBaseType_t)xLowerLimit;
	uxStates[TRC_COUNTER_UPPER_LIMIT_INDEX] = (TraceUnsignedBaseType_t)xUpperLimit;

	/* We need to check this */
	if (xTraceObjectRegisterInternal(PSF_EVENT_COUNTER_CREATE, (void*)0, szName, 3u, uxStates, TRC_ENTRY_OPTION_COUNTER, &xObjectHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	*pxCounterHandle = (TraceCounterHandle_t)xObjectHandle;
	
	return TRC_SUCCESS;
}

traceResult xTraceCounterSet(TraceCounterHandle_t xCounterHandle, TraceBaseType_t xValue)
{
	TraceBaseType_t xLowerLimit = 0;
	TraceBaseType_t xUpperLimit = 0;

	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_COUNTER));

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceObjectSetSpecificState((TraceEntryHandle_t)xCounterHandle, TRC_COUNTER_VALUE_INDEX, (TraceUnsignedBaseType_t)xValue) == TRC_SUCCESS);

	(void)xTraceEventCreate2(PSF_EVENT_COUNTER_CHANGE, (TraceUnsignedBaseType_t)xCounterHandle, (TraceUnsignedBaseType_t)xValue); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/
	
	/* These should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceCounterGetLowerLimit(xCounterHandle, &xLowerLimit) == TRC_SUCCESS);
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceCounterGetUpperLimit(xCounterHandle, &xUpperLimit) == TRC_SUCCESS);

	if ((xValue < xLowerLimit) || (xValue > xUpperLimit))
	{
		(void)xTraceEventCreate1(PSF_EVENT_COUNTER_LIMIT_EXCEEDED, (TraceUnsignedBaseType_t)xCounterHandle); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/

		if (pxCounterData->xCallbackFunction != 0)
		{
			pxCounterData->xCallbackFunction(xCounterHandle);
		}
	}

	return TRC_SUCCESS;
}

#endif
