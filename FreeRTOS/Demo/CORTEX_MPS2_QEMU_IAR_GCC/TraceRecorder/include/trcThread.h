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
 * @brief Public trace thread APIs.
 */

#ifndef TRC_THREAD_H
#define TRC_THREAD_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_thread_apis Trace Thread APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @brief Register trace thread in the trace.
 * 
 * @param[in] szName Name.
 * @param[in] uxPriority Priority.
 * @param[in] uxProcess Process address or handle used when registering process.
 * @param[out] pxThreadHandle Pointer to uninitialized trace thread.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceThreadRegister(szName, uxPriority, uxProcess, pxThreadHandle) xTraceObjectRegister2(PSF_EVENT_THREAD_CREATE, (void*)0, szName, uxPriority, (TraceUnsignedBaseType_t)(uxProcess), (TraceObjectHandle_t*)(pxThreadHandle))

/**
 * @brief Registers trace thread without trace thread handle.
 * 
 * @param[in] pvThread Thread.
 * @param[in] szName Name.
 * @param[in] uxPriority Priority.
 * @param[in] uxProcess Process address or handle used when registering process.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceThreadRegisterWithoutHandle(pvThread, szName, uxPriority, uxProcess) xTraceObjectRegisterWithoutHandle2(PSF_EVENT_THREAD_CREATE, (void*)(pvThread), szName, uxPriority, (TraceUnsignedBaseType_t)(uxProcess))

/**
 * @brief Unregister trace thread from trace. 
 * 
 * @param[in] xThreadHandle Pointer to initialized trace thread.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceThreadUnregister(xThreadHandle, uxPriority) xTraceObjectUnregister((TraceObjectHandle_t)(xThreadHandle), PSF_EVENT_THREAD_DELETE, uxPriority)

/**
 * @brief Unregisters trace thread without trace thread handle.
 * 
 * @param[in] pvThread Thread.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceThreadUnregisterWithoutHandle(pvThread, uxPriority) xTraceObjectUnregisterWithoutHandle(PSF_EVENT_THREAD_DELETE, (void*)(pvThread), uxPriority)

/**
 * @brief Sets trace thread priority.
 * 
 * @param[in] xThreadHandle Handle to initialized trace thread.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceThreadSetPriority(xThreadHandle, uxPriority) xTraceTaskSetPriority((TraceTaskHandle_t)(xThreadHandle), uxPriority)

/**
 * @brief Sets trace thread priority without trace thread handle.
 * 
 * @param[in] pvThread Thread.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceThreadSetPriorityWithoutHandle(pvThread, uxPriority) xTraceTaskSetPriorityWithoutHandle(pvThread, uxPriority)

/**
 * @brief Registers trace thread switch event.
 * 
 * @param[in] xThread Thread address or thread handle used when registering thread.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceThreadSwitch(xThread, uxPriority) xTraceTaskSwitch((void*)(xThread), uxPriority)

#if (TRC_CFG_INCLUDE_READY_EVENTS == 1)
/**
 * @brief Registers trace thread ready event.
 * 
 * @param[in] xThread Thread address or thread handle used when registering thread.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceThreadReady(xThread) xTraceTaskReady((void*)(xThread))
#else
#define xTraceThreadReady(xThread) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(xThread), TRC_SUCCESS)
#endif

/** @} */

#ifdef __cplusplus
}
#endif

#else

#define xTraceThreadRegister(___szName, __uxPriority, __uxProcess, __pxThreadHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_5((void)(__szName), (void)(__uxPriority), (void)(__uxProcess), (void)(__pxThreadHandle), TRC_SUCCESS)

#define xTraceThreadRegisterWithoutHandle(__pvThread, __szName, __uxPriority, __uxProcess) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_5((void)(__pvThread), (void)(__szName), (void)(__uxPriority), (void)(__uxProcess), TRC_SUCCESS)

#define xTraceThreadUnregister(__xThreadHandle, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__xThreadHandle), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceThreadUnregisterWithoutHandle(__pvThread, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__pvThread), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceThreadSetPriority(__xThreadHandle, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__xThreadHandle), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceThreadSetPriorityWithoutHandle(__pvThread, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__pvThread), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceThreadSwitch(__pvThread, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__pvThread), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceThreadReady(__pvThread) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(__pvThread), TRC_SUCCESS)

#endif

#endif
