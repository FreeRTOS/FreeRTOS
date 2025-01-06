/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
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

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

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
 * @internal Trace Task Data Structure
 */
typedef struct TraceTaskData	/* Aligned */
{
	void* coreTasks[TRC_CFG_CORE_COUNT];
} TraceTaskData_t;

extern TraceTaskData_t* pxTraceTaskData;

/**
 * @internal Initialize trace task system.
 * 
 * @param[in] pxBuffer Pointer to memory that will be used by the
 * trace task system.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceTaskInitialize(TraceTaskData_t* pxBuffer);

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
#define xTraceTaskUnregister(xTaskHandle, uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)xTraceStackMonitorRemove(xTraceEntryGetAddressReturn((TraceEntryHandle_t)(xTaskHandle))), xTraceObjectUnregister((TraceObjectHandle_t)(xTaskHandle), PSF_EVENT_TASK_DELETE, uxPriority))

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
#define xTraceTaskUnregisterWithoutHandle(pvTask, uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)xTraceStackMonitorRemove(pvTask), xTraceObjectUnregisterWithoutHandle(PSF_EVENT_TASK_DELETE, pvTask, uxPriority))

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
#define xTraceTaskReady(pvTask) xTraceEventCreate1(PSF_EVENT_TASK_READY, (TraceUnsignedBaseType_t)(pvTask))
#else
#define xTraceTaskReady(p) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)p, TRC_SUCCESS)
#endif

/**
 * @brief Sets current trace task on current core.
 * 
 * @param[in] pvTask Task.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskSetCurrent(pvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(pxTraceTaskData->coreTasks[TRC_CFG_GET_CURRENT_CORE()] = (pvTask), TRC_SUCCESS)

/**
 * @brief Sets current trace task on specific core.
 *
 * @param[in] coreId Core id.
 * @param[in] pvTask Task.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskSetCurrentOnCore(coreId, pvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(pxTraceTaskData->coreTasks[coreId] = (pvTask), TRC_SUCCESS)

/**
 * @brief Gets current trace task on current core.
 * 
 * @param[out] ppvTask Task.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskGetCurrent(ppvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(ppvTask) = pxTraceTaskData->coreTasks[TRC_CFG_GET_CURRENT_CORE()], TRC_SUCCESS)

/**
 * @brief Gets current trace task on specific core.
 *
 * @param[in] coreId Core id.
 * @param[out] ppvTask Task.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceTaskGetCurrentOnCore(coreId, ppvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(ppvTask) = pxTraceTaskData->coreTasks[coreId], TRC_SUCCESS)

 /**
  * @brief Returns current trace task.
  *
  * @returns Current trace task.
  */
#define xTraceTaskGetCurrentReturn() (pxTraceTaskData->coreTasks[TRC_CFG_GET_CURRENT_CORE()])

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
#define xTraceTaskInstanceFinishedNow() xTraceEventCreate0(PSF_EVENT_IFE_DIRECT)

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
#define xTraceTaskInstanceFinishedNext() xTraceEventCreate0(PSF_EVENT_IFE_NEXT)

/** @} */

#ifdef __cplusplus
}
#endif

#else

#define xTraceTaskRegister(__pvTask, ___szName, __uxPriority, __pxTaskHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_5((void)(__pvTask), (void)(__szName), (void)(__uxPriority), (void)(__pxTaskHandle), TRC_SUCCESS)

#define xTraceTaskUnregister(__xTaskHandle, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__xTaskHandle), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceTaskSetName(__xTaskHandle, __szName) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__xTaskHandle), (void)(__szName), TRC_SUCCESS)

#define xTraceTaskSetPriority(__xTaskHandle, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__xTaskHandle), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceTaskRegisterWithoutHandle(__pvTask, __szName, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(__pvTask), (void)(__szName), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceTaskUnregisterWithoutHandle(__pvTask, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__pvTask), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceTaskSetNameWithoutHandle(__pvTask, __szName) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__pvTask), (void)(__szName), TRC_SUCCESS)

#define xTraceTaskSetPriorityWithoutHandle(__pvTask, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__pvTask), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceTaskSwitch(__pvTask, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__pvTask), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceTaskReady(__pvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(__pvTask), TRC_SUCCESS)

#define xTraceTaskSetCurrent(__pvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(__pvTask), TRC_SUCCESS)

#define xTraceTaskSetCurrentOnCore(__coreId, __pvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__coreId), (void)(__pvTask), TRC_SUCCESS)

#define xTraceTaskGetCurrent(__ppvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(__ppvTask), TRC_SUCCESS)

#define xTraceTaskGetCurrentOnCore(__coreId, __ppvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__coreId), (void)(__ppvTask), TRC_SUCCESS)

#define xTraceTaskGetCurrentReturn() (0)

#define xTraceTaskInstanceFinishedNow() (TRC_SUCCESS)

#define xTraceTaskInstanceFinishedNext() (TRC_SUCCESS)

#endif

#endif
