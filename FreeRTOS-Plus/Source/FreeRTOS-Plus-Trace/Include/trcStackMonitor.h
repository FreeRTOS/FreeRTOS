/*
* Percepio Trace Recorder SDK for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*/

/**
 * @file 
 * 
 * @brief Public trace stack monitor APIs.
 */

#ifndef TRC_STACK_MONITOR_H
#define TRC_STACK_MONITOR_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <stdint.h>
#include <trcRecorder.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_stack_monitor_apis Trace Stack Monitor APIs
 * @ingroup trace_recorder_apis
 * @{
 */

#if (((TRC_CFG_ENABLE_STACK_MONITOR) == 1) && ((TRC_CFG_SCHEDULING_ONLY) == 0))

#define TRACE_STACK_MONITOR_BUFFER_SIZE ((sizeof(void*) + sizeof(TraceUnsignedBaseType_t)) * (TRC_CFG_STACK_MONITOR_MAX_TASKS) + sizeof(uint32_t))

/**
 * @internal Trace Stack Monitor Buffer Structure
 */
typedef struct TraceStackMonitorBuffer
{
	uint32_t buffer[(TRACE_STACK_MONITOR_BUFFER_SIZE) / sizeof(uint32_t)];
} TraceStackMonitorBuffer_t;

/**
 * @internal Initialize trace stack monitor system.
 * 
 * @param[in] pxBuffer Pointer to memory that will be used by the trace
 * stack monitor system.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStackMonitorInitialize(TraceStackMonitorBuffer_t* pxBuffer);

/**
 * @brief Adds task/thread to trace stack monitor.
 * 
 * @param[in] pvTask Task/Thread.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStackMonitorAdd(void* pvTask);

/**
 * @brief Removes task/thread from trace stack monitor.
 * 
 * @param[in] pvTask Task/Thread.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStackMonitorRemove(void* pvTask);

/**
 * @brief Gets trace stack monitor tread/task at index.
 * 
 * @param[in] uiIndex Index.
 * @param[in] ppvTask Task/Thread.
 * @param[out] puxLowWaterMark Low water mark.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStackMonitorGetAtIndex(uint32_t uiIndex, void** ppvTask, TraceUnsignedBaseType_t* puxLowWaterMark);

/**
 * @brief Performs trace stack monitor reporting.
 * 
 * This routine performs a trace stack monitor check and report
 * for TRC_CFG_STACK_MONITOR_MAX_REPORTS number of registered
 * tasks/threads.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStackMonitorReport(void);

#else /* (((TRC_CFG_ENABLE_STACK_MONITOR) == 1) && ((TRC_CFG_SCHEDULING_ONLY) == 0)) */

typedef struct TraceStackMonitorBuffer
{
	uint32_t buffer[1];
} TraceStackMonitorBuffer_t;

#define xTraceStackMonitorInitialize(pxBuffer) ((void)pxBuffer, TRC_SUCCESS)

#define xTraceStackMonitorDiagnosticsGet(xType, puiValue) ((void)xType, puiValue != 0 ? *puiValue = 0 : 0, puiValue != 0 ? TRC_SUCCESS : TRC_FAIL)

#define xTraceStackMonitorDiagnosticsSet(xType, uiValue) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)xType, (void)uiValue, TRC_SUCCESS)

#define xTraceStackMonitorAdd(pvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)pvTask, TRC_SUCCESS)

#define xTraceStackMonitorRemove(pvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)pvTask, TRC_SUCCESS)

#define xTraceStackMonitorGetAtIndex(uiIndex, ppvTask, puxLowWaterMark) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)uiIndex, (void)ppvTask, (void)puxLowWaterMark, TRC_SUCCESS)

#define xTraceStackMonitorReport() TRC_COMMA_EXPR_TO_STATEMENT_EXPR_1(TRC_SUCCESS)

#endif /* (((TRC_CFG_ENABLE_STACK_MONITOR) == 1) && ((TRC_CFG_SCHEDULING_ONLY) == 0)) */

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_STACK_MONITOR_H */
