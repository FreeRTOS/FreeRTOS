/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for tasks.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#ifndef TRC_KERNEL_PORT_KERNEL_CAN_SWITCH_TO_SAME_TASK
#define TRC_KERNEL_PORT_KERNEL_CAN_SWITCH_TO_SAME_TASK 1
#endif

/* Code used for "task address" when no task has started, to indicate "(startup)".
 * This value was used since NULL/0 was already reserved for the idle task. */
#define TRACE_HANDLE_NO_TASK ((void*)2UL)

#define TRC_TASK_STATE_INDEX_PRIORITY		0u

TraceTaskData_t* pxTraceTaskData TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceTaskInitialize(TraceTaskData_t *pxBuffer)
{
	int32_t i;

	/* This should never fail */
	TRC_ASSERT(pxBuffer != (void*)0);

	pxTraceTaskData= pxBuffer;

	for (i = 0; i < (TRC_CFG_CORE_COUNT); i++)
	{
		pxTraceTaskData->coreTasks[i] = TRACE_HANDLE_NO_TASK;  /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 !MISRAC2012-Rule-11.6 Suppress conversion from pointer to integer check*/
	}

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_TASK);

	return TRC_SUCCESS;
}

traceResult xTraceTaskSetPriority(TraceTaskHandle_t xTaskHandle, TraceUnsignedBaseType_t uxPriority)
{
	void *pvTask = (void*)0;

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceObjectSetSpecificState((TraceObjectHandle_t)xTaskHandle, TRC_TASK_STATE_INDEX_PRIORITY, uxPriority) == TRC_SUCCESS);
	
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetAddress((TraceEntryHandle_t)xTaskHandle, &pvTask) == TRC_SUCCESS);

	(void)xTraceEventCreate2(PSF_EVENT_TASK_PRIORITY, (TraceUnsignedBaseType_t)pvTask, uxPriority);  /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 !MISRAC2012-Rule-11.6 Suppress conversion from pointer to integer check*/
	
	return TRC_SUCCESS;
}

traceResult xTraceTaskSetPriorityWithoutHandle(void* pvTask, TraceUnsignedBaseType_t uxPriority)
{
	TraceEntryHandle_t xEntryHandle;
	
	if (xTraceEntryFind(pvTask, &xEntryHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceObjectSetSpecificState((TraceObjectHandle_t)xEntryHandle, TRC_TASK_STATE_INDEX_PRIORITY, uxPriority) == TRC_SUCCESS);

	/* We need to check this */
	(void)xTraceEventCreate2(PSF_EVENT_TASK_PRIORITY, (TraceUnsignedBaseType_t)pvTask, uxPriority);  /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 !MISRAC2012-Rule-11.6 Suppress conversion from pointer to integer check*/

	return TRC_SUCCESS;
}

traceResult xTraceTaskSwitch(void *pvTask, TraceUnsignedBaseType_t uxPriority)
{
	traceResult xResult = TRC_FAIL;
#if (TRC_KERNEL_PORT_KERNEL_CAN_SWITCH_TO_SAME_TASK == 1)
	void* pvCurrent = (void*)0;
#endif

	TRACE_ALLOC_CRITICAL_SECTION();
	
	(void)pvTask;
	(void)uxPriority;

	if (!xTraceIsRecorderInitialized())
	{
		return xResult;
	}

	if (!xTraceIsRecorderEnabled())
	{
		/* Make sure we store the current task, even while recorder isn't enabled */
		xTraceTaskSetCurrent(pvTask);

		return xResult;
	}

	xTraceStateSet(TRC_STATE_IN_TASKSWITCH);

	TRACE_ENTER_CRITICAL_SECTION();

#if (TRC_KERNEL_PORT_KERNEL_CAN_SWITCH_TO_SAME_TASK == 1)
	xTraceTaskGetCurrent(&pvCurrent);
	if (pvCurrent != pvTask)
#endif
	{
		xTraceTaskSetCurrent(pvTask);

		xResult = xTraceEventCreate2(PSF_EVENT_TASK_ACTIVATE, (TraceUnsignedBaseType_t)pvTask, uxPriority);  /*cstat !MISRAC2004-11.3 !MISRAC2012-Rule-11.4 !MISRAC2012-Rule-11.6 Suppress conversion from pointer to integer check*/
	}

	xTraceStateSet(TRC_STATE_IN_APPLICATION);

	TRACE_EXIT_CRITICAL_SECTION();

	return xResult;
}

#endif
