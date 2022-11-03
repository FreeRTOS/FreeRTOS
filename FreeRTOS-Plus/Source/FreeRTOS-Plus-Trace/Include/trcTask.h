/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*/

/**
 * @file 
 * 
 * @brief Public trace task APIs.
 */

#ifndef TRC_TASK_H
#define TRC_TASK_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_task_apis Trace Task APIs
 * @ingroup trace_recorder_apis
 * @{
 */

#ifndef TRC_CFG_ENABLE_STACK_MONITOR
#define TRC_CFG_ENABLE_STACK_MONITOR 0
#endif

/**
 * @internal Trace Task Info Structure
 */
typedef struct TraceTaskInfo
{
	void* coreTasks[TRC_CFG_CORE_COUNT];
} TraceTaskInfo_t;

extern TraceTaskInfo_t* pxTraceTaskInfo;

#define TRACE_TASK_INFO_BUFFER_SIZE (sizeof(TraceTaskInfo_t))

/**
 * @internal Trace Task Info Buffer Structure
 */
typedef struct TraceTaskInfoBuffer
{
	uint8_t buffer[TRACE_TASK_INFO_BUFFER_SIZE];
} TraceTaskInfoBuffer_t;

/**
 * @internal Initialize trace task system.
 * 
 * @param[in] pxBuffer Pointer to memory that will be used by the
 * trace task system.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceTaskInitialize(TraceTaskInfoBuffer_t* pxBuffer);

/**
 * @brief Register trace task in the trace.
 * 
 * @param[in] pvTask Task.
 * @param[in] szName Name.
 * @param[in] uxPriority Priority.
 * @param[out] pxTaskHandle Pointer to uninitialized trace task.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskRegister(pvTask, szName, uxPriority, pxTaskHandle) ((((pvTask) != 0) && (xTraceObjectRegister(PSF_EVENT_TASK_CREATE, pvTask, szName, uxPriority, (TraceObjectHandle_t*)(pxTaskHandle)) == TRC_SUCCESS)) ? (xTraceStackMonitorAdd(pvTask), TRC_SUCCESS) : TRC_FAIL)

/**
 * @brief Unregister trace task from trace. 
 * 
 * @param[in] xTaskHandle Pointer to initialized trace task.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceTaskUnregister(TraceTaskHandle_t xTaskHandle, TraceUnsignedBaseType_t uxPriority);

/**
 * @brief Sets trace task name. 
 * 
 * @param[in] pvTask Task.
 * @param[in] szName Name.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskSetName xTraceObjectSetName

/**
 * @brief Sets trace task priority.
 * 
 * @param[in] xTaskHandle Pointer to initialized trace task. 
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceTaskSetPriority(TraceTaskHandle_t xTaskHandle, TraceUnsignedBaseType_t uxPriority);

/**
 * @brief Registers trace task without trace task handle.
 * 
 * @param[in] pvTask Task.
 * @param[in] szName Name.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskRegisterWithoutHandle(pvTask, szName, uxPriority) ((((pvTask) != 0) && (xTraceObjectRegisterWithoutHandle(PSF_EVENT_TASK_CREATE, pvTask, szName, uxPriority) == TRC_SUCCESS)) ? (xTraceStackMonitorAdd(pvTask), TRC_SUCCESS) : TRC_FAIL)

/**
 * @brief Unregisters trace task without trace task handle.
 * 
 * @param[in] pvTask Task.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskUnregisterWithoutHandle(pvTask, uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(xTraceStackMonitorRemove(pvTask), xTraceObjectUnregisterWithoutHandle(PSF_EVENT_TASK_DELETE, pvTask, uxPriority))

/**
 * @brief Sets trace task name without trace task handle.
 * 
 * @param[in] pvTask Task.
 * @param[in] szName Name.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskSetNameWithoutHandle xTraceObjectSetNameWithoutHandle

/**
 * @brief Sets trace task priority without trace task handle.
 * 
 * @param[in] pvTask Task.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceTaskSetPriorityWithoutHandle(void* pvTask, TraceUnsignedBaseType_t uxPriority);

/**
 * @brief Registers trace task switch event.
 * 
 * @param[in] pvTask Task.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceTaskSwitch(void* pvTask, TraceUnsignedBaseType_t uxPriority);

#if (TRC_CFG_INCLUDE_READY_EVENTS == 1)
/**
 * @brief Registers trace task ready event.
 * 
 * @param[in] pvTask Task.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceTaskReady(void* pvTask);
#else
#define xTraceTaskReady(p) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)p, TRC_SUCCESS)
#endif

/**
 * @brief Sets current trace task.
 * 
 * @param[in] pvTask Task.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskSetCurrent(pvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(pxTraceTaskInfo->coreTasks[TRC_CFG_GET_CURRENT_CORE()] = (pvTask), TRC_SUCCESS)

/**
 * @brief Gets current trace task.
 * 
 * @param[out] ppvTask Task.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskGetCurrent(ppvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(ppvTask) = pxTraceTaskInfo->coreTasks[TRC_CFG_GET_CURRENT_CORE()], TRC_SUCCESS)

/**
 * @brief Registers trace task instance finished event.
 * 
 * This routine creates a trace event that ends the current task instance at
 * this very instant. This makes the viewer split the current fragment at 
 * this point and begin a new actor instance, even if no task-switch has 
 * occurred
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceTaskInstanceFinishedNow(void);

/**
 * @brief Marks the current trace task instance as finished on the next
 * kernel call.
 * 
 * If that kernel call is blocking, the instance ends after the blocking event
 * and the corresponding return event is then the start of the next instance.
 * If the kernel call is not blocking, the viewer instead splits the current
 * fragment right before the kernel call, which makes this call the first event
 * of the next instance.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceTaskInstanceFinishedNext(void);

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_TASK_H */
