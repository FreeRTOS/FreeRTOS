/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for tasks.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

/* Code used for "task address" when no task has started, to indicate "(startup)".
 * This value was used since NULL/0 was already reserved for the idle task. */
#define TRACE_HANDLE_NO_TASK ((void*)2)

#define TRC_TASK_STATE_INDEX_PRIORITY		0
#define TRC_TASK_STATE_INDEX_UNUSED_STACK	1

TraceTaskInfo_t* pxTraceTaskInfo;

traceResult xTraceTaskInitialize(TraceTaskInfoBuffer_t *pxBuffer)
{
	uint32_t i;

	TRC_ASSERT_EQUAL_SIZE(TraceTaskInfoBuffer_t, TraceTaskInfo_t);

	/* This should never fail */
	TRC_ASSERT(pxBuffer != 0);

	pxTraceTaskInfo = (TraceTaskInfo_t*)pxBuffer;

	for (i = 0; i < TRC_CFG_CORE_COUNT; i++)
	{
		pxTraceTaskInfo->coreTasks[i] = TRACE_HANDLE_NO_TASK;
	}

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_TASK);

	return TRC_SUCCESS;
}

traceResult xTraceTaskUnregister(TraceTaskHandle_t xTaskHandle, TraceUnsignedBaseType_t uxPriority)
{
	void* pvTask;
	
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetAddress((TraceEntryHandle_t)xTaskHandle, &pvTask) == TRC_SUCCESS);
	
	xTraceStackMonitorRemove(pvTask);
	
	return xTraceObjectUnregister((TraceObjectHandle_t)xTaskHandle, PSF_EVENT_TASK_DELETE, uxPriority);
}

traceResult xTraceTaskSetPriority(TraceTaskHandle_t xTaskHandle, TraceUnsignedBaseType_t uxPriority)
{
	TraceEventHandle_t xEventHandle = 0;
	void *pvTask;

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceObjectSetState((TraceObjectHandle_t)xTaskHandle, uxPriority) == TRC_SUCCESS);
	
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEntryGetAddress((TraceEntryHandle_t)xTaskHandle, &pvTask) == TRC_SUCCESS);

	/* We need to check this */
	if (xTraceEventBegin(PSF_EVENT_TASK_PRIORITY, sizeof(void*) + sizeof(uint32_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, pvTask);
		xTraceEventAdd32(xEventHandle, (uint32_t)uxPriority);
		xTraceEventEnd(xEventHandle);
	}
	
	return TRC_SUCCESS;
}

traceResult xTraceTaskSetPriorityWithoutHandle(void* pvTask, TraceUnsignedBaseType_t uxPriority)
{
	TraceEventHandle_t xEventHandle = 0;
	TraceEntryHandle_t xEntryHandle;
	
	if (xTraceEntryFind(pvTask, &xEntryHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceObjectSetState((TraceObjectHandle_t)xEntryHandle, uxPriority) == TRC_SUCCESS);

	/* We need to check this */
	if (xTraceEventBegin(PSF_EVENT_TASK_PRIORITY, sizeof(void*) + sizeof(uint32_t), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, pvTask);
		xTraceEventAdd32(xEventHandle, (uint32_t)uxPriority);
		xTraceEventEnd(xEventHandle);
	}
	
	return TRC_SUCCESS;
}

traceResult xTraceTaskSwitch(void *pvTask, TraceUnsignedBaseType_t uxPriority)
{
	traceResult xResult = TRC_FAIL;
	TraceEventHandle_t xEventHandle = 0;
	void* pvCurrent = 0;
	
	(void)pvTask;
	(void)uxPriority;

	TRACE_ALLOC_CRITICAL_SECTION();

	if (xTraceIsRecorderEnabled() == 0)
	{
		return xResult;
	}

	TRACE_ENTER_CRITICAL_SECTION();

	xTraceStateSet(TRC_STATE_IN_TASKSWITCH);

	xTraceTaskGetCurrent(&pvCurrent);
	if (pvCurrent != pvTask)
	{
		xTraceTaskSetCurrent(pvTask);
		
		if (xTraceEventBegin(PSF_EVENT_TASK_ACTIVATE, sizeof(void*) + sizeof(uint32_t), &xEventHandle) == TRC_SUCCESS)
		{
			xTraceEventAddPointer(xEventHandle, pvTask);
			xTraceEventAdd32(xEventHandle, (uint32_t)uxPriority);
			xTraceEventEnd(xEventHandle);
			xResult = TRC_SUCCESS;
		}
	}

	xTraceStateSet(TRC_STATE_IN_APPLICATION);

	TRACE_EXIT_CRITICAL_SECTION();

	return xResult;
}

#if (TRC_CFG_INCLUDE_READY_EVENTS == 1)
traceResult xTraceTaskReady(void *pvTask)
{
	traceResult xResult = TRC_FAIL;
	TraceEventHandle_t xEventHandle = 0;

	if (xTraceEventBegin(PSF_EVENT_TASK_READY, sizeof(void*), &xEventHandle) == TRC_SUCCESS)
	{
		xTraceEventAddPointer(xEventHandle, pvTask);
		xTraceEventEnd(xEventHandle);
		xResult = TRC_SUCCESS;
	}

	return xResult;
}
#endif /* (TRC_CFG_INCLUDE_READY_EVENTS == 1) */

traceResult xTraceTaskInstanceFinishedNow(void)
{
	TraceEventHandle_t xEventHandle = 0;

	if (xTraceEventBegin(PSF_EVENT_IFE_DIRECT, 0, &xEventHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	xTraceEventEnd(xEventHandle);

	return TRC_SUCCESS;
}

traceResult xTraceTaskInstanceFinishedNext(void)
{
	TraceEventHandle_t xEventHandle = 0;

	if (xTraceEventBegin(PSF_EVENT_IFE_NEXT, 0, &xEventHandle) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	xTraceEventEnd(xEventHandle);

	return TRC_SUCCESS;
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
