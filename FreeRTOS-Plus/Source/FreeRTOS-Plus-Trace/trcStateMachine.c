/*
* Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation of state machines.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#define TRC_STATE_MACHINE_STATE_INDEX 0
#define TRC_STATE_MACHINE_INDEX 0

traceResult xTraceStateMachineCreate(const char *szName, TraceStateMachineHandle_t *pxStateMachineHandle)
{
	TraceObjectHandle_t xObjectHandle;

	/* This should never fail */
	TRC_ASSERT(pxStateMachineHandle != 0);

	/* We need to check this */
	if (xTraceObjectRegister(PSF_EVENT_STATEMACHINE_CREATE , 0, szName, 0, &xObjectHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetOptions((TraceEntryHandle_t)xObjectHandle, (uint32_t)TRC_ENTRY_OPTION_STATE_MACHINE) == TRC_SUCCESS);

	*pxStateMachineHandle = (TraceStateMachineHandle_t)xObjectHandle;
	
	return TRC_SUCCESS;
}

traceResult xTraceStateMachineStateCreate(TraceStateMachineHandle_t xStateMachineHandle, const char* szName, TraceStateMachineStateHandle_t* pxStateHandle)
{
	TraceObjectHandle_t xObjectHandle;

	/* This should never fail */
	TRC_ASSERT(xStateMachineHandle != 0);

	/* This should never fail */
	TRC_ASSERT(pxStateHandle != 0);

	/* We need to check this */
	if (xTraceObjectRegister(PSF_EVENT_STATEMACHINE_STATE_CREATE, 0, szName, (TraceUnsignedBaseType_t)xStateMachineHandle, &xObjectHandle) == TRC_FAIL)
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
	TraceEventHandle_t xEventHandle = 0;
	TraceUnsignedBaseType_t uxStateMachine;
	
	/* This should never fail */
	TRC_ASSERT(xStateMachineHandle != 0);

	/* This should never fail */
	TRC_ASSERT(xStateHandle != 0);

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetState((TraceEntryHandle_t)xStateHandle, TRC_STATE_MACHINE_INDEX, &uxStateMachine) == TRC_SUCCESS);

	/* Verify that this state machine state was meant to be used with this state machine */
	/* This should never fail */
	TRC_ASSERT(xStateMachineHandle == (TraceStateMachineHandle_t)uxStateMachine);

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntrySetState((TraceEntryHandle_t)xStateMachineHandle, TRC_STATE_MACHINE_STATE_INDEX, (TraceUnsignedBaseType_t)xStateHandle) == TRC_SUCCESS);

	/* We need to check this */
	if (xTraceEventBegin(PSF_EVENT_STATEMACHINE_STATECHANGE, sizeof(void*) + sizeof(void*), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, (void*)xStateMachineHandle);
		xTraceEventAddPointer(xEventHandle, (void*)xStateHandle);
		xTraceEventEnd(xEventHandle);
	}

	return TRC_SUCCESS;
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
