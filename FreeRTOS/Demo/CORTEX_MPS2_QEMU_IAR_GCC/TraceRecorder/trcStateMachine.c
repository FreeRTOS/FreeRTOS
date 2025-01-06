/*
* Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of state machines.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#define TRC_STATE_MACHINE_STATE_INDEX 0u
#define TRC_STATE_MACHINE_INDEX 0u

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceStateMachineCreate(const char *szName, TraceStateMachineHandle_t *pxStateMachineHandle)
{
	TraceObjectHandle_t xObjectHandle;

	/* This should never fail */
	TRC_ASSERT(pxStateMachineHandle != (void*)0);

	/* We need to check this */
	if (xTraceObjectRegister(PSF_EVENT_STATEMACHINE_CREATE , (void*)0, szName, 0u, &xObjectHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetOptions((TraceEntryHandle_t)xObjectHandle, (uint32_t)TRC_ENTRY_OPTION_STATE_MACHINE) == TRC_SUCCESS);

	*pxStateMachineHandle = (TraceStateMachineHandle_t)xObjectHandle;
	
	return TRC_SUCCESS;
}

/*cstat !MISRAC2004-6.3 !MISRAC2012-Dir-4.6_a Suppress basic char type usage*/
traceResult xTraceStateMachineStateCreate(TraceStateMachineHandle_t xStateMachineHandle, const char* szName, TraceStateMachineStateHandle_t* pxStateHandle)
{
	TraceObjectHandle_t xObjectHandle;

	/* This should never fail */
	TRC_ASSERT(xStateMachineHandle != 0);

	/* This should never fail */
	TRC_ASSERT(pxStateHandle != (void*)0);

	/* We need to check this */
	if (xTraceObjectRegister(PSF_EVENT_STATEMACHINE_STATE_CREATE, (void*)0, szName, (TraceUnsignedBaseType_t)xStateMachineHandle, &xObjectHandle) == TRC_FAIL) /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetOptions((TraceEntryHandle_t)xObjectHandle, (uint32_t)TRC_ENTRY_OPTION_STATE_MACHINE_STATE) == TRC_SUCCESS);

	*pxStateHandle = (TraceStateMachineHandle_t)xObjectHandle;

	return TRC_SUCCESS;
}

traceResult xTraceStateMachineSetState(TraceStateMachineHandle_t xStateMachineHandle, TraceStateMachineStateHandle_t xStateHandle)
{
	/* This should never fail */
	TRC_ASSERT(xStateMachineHandle != 0);

	/* This should never fail */
	TRC_ASSERT(xStateHandle != 0);

	/* Verify that this state machine state was meant to be used with this state machine */
	/* This should never fail */
	TRC_ASSERT(xStateMachineHandle == (TraceStateMachineHandle_t)xTraceEntryGetStateReturn((TraceEntryHandle_t)xStateHandle, TRC_STATE_MACHINE_INDEX));

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState((TraceEntryHandle_t)xStateMachineHandle, TRC_STATE_MACHINE_STATE_INDEX, (TraceUnsignedBaseType_t)xStateHandle) == TRC_SUCCESS); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/

	(void)xTraceEventCreate2(PSF_EVENT_STATEMACHINE_STATECHANGE, (TraceUnsignedBaseType_t)xStateMachineHandle, (TraceUnsignedBaseType_t)xStateHandle); /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 Suppress conversion from pointer to integer check*/

	return TRC_SUCCESS;
}

#endif
