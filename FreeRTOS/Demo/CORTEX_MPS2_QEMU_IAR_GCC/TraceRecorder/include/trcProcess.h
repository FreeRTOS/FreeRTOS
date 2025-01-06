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
 * @brief Public trace process APIs.
 */

#ifndef TRC_PROCESS_H
#define TRC_PROCESS_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_process_apis Trace Process APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @brief Register process in the trace.
 * 
 * @param[in] szName Name.
 * @param[in] uxPriority Priority.
 * @param[out] pxProcessHandle Process handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceProcessRegister(szName, uxPriority, pxProcessHandle) xTraceObjectRegister(PSF_EVENT_PROCESS_CREATE, (void*)0, szName, uxPriority, (TraceObjectHandle_t*)(pxProcessHandle))

/**
 * @brief Register process in the trace.
 * 
 * @param[in] pvProcess Process.
 * @param[in] szName Name.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceProcessRegisterWithoutHandle(pvProcess, szName, uxPriority) xTraceObjectRegisterWithoutHandle(PSF_EVENT_PROCESS_CREATE, (void*)(pvProcess), szName, uxPriority)

/**
 * @brief Unregister process from trace.
 * 
 * @param[in] xProcessHandle Process handle.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceProcessUnregister(xProcessHandle, uxPriority) xTraceObjectUnregister((TraceObjectHandle_t)(xProcessHandle), PSF_EVENT_PROCESS_DELETE, uxPriority)

/**
 * @brief Unregister process from trace.
 * 
 * @param[in] pvProcess Process.
 * @param[in] uxPriority Priority.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceProcessUnregisterWithoutHandle(pvProcess, uxPriority) xTraceObjectUnregisterWithoutHandle(PSF_EVENT_PROCESS_DELETE, (void*)(pvProcess), uxPriority)

/** @} */

#ifdef __cplusplus
}
#endif

#else

#define xTraceProcessRegister(__szName, __uxPriority, __pxProcessHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(__szName), (void)(__uxPriority), (void)(__pxProcessHandle), TRC_SUCCESS)

#define xTraceProcessRegisterWithoutHandle(__pvProcess, __szName, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(__pvProcess), (void)(__szName), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceProcessUnregister(__xProcessHandle, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__xProcessHandle), (void)(__uxPriority), TRC_SUCCESS)

#define xTraceProcessUnregisterWithoutHandle(__pvProcess, __uxPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__pvProcess), (void)(__uxPriority), TRC_SUCCESS)

#endif

#endif
