/*
* Percepio Trace Recorder SDK for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
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

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) && ((TRC_CFG_ENABLE_STACK_MONITOR) == 1) && ((TRC_CFG_SCHEDULING_ONLY) == 0)

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

typedef struct TraceStackMonitorEntry	/* Aligned */
{
	void *pvTask;
	TraceUnsignedBaseType_t uxPreviousLowWaterMark;
} TraceStackMonitorEntry_t;

typedef struct TraceStackMonitorData	/* Aligned */
{
	TraceStackMonitorEntry_t xEntries[TRC_CFG_STACK_MONITOR_MAX_TASKS];

	TraceUnsignedBaseType_t uxEntryCount;
} TraceStackMonitorData_t;

/**
 * @internal Initialize trace stack monitor system.
 * 
 * @param[in] pxBuffer Pointer to memory that will be used by the trace
 * stack monitor system.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStackMonitorInitialize(TraceStackMonitorData_t* pxBuffer);

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

/** @} */

#ifdef __cplusplus
}
#endif

#else

typedef struct TraceStackMonitorData
{
	uint32_t buffer[1];
} TraceStackMonitorData_t;

#define xTraceStackMonitorInitialize(__pxBuffer) ((void)(__pxBuffer), TRC_SUCCESS)

#define xTraceStackMonitorDiagnosticsGet(__xType, __puiValue) ((void)(__xType), (__puiValue) != 0 ? *(__puiValue) = 0 : 0, (__puiValue) != 0 ? TRC_SUCCESS : TRC_FAIL)

#define xTraceStackMonitorDiagnosticsSet(__xType, __uiValue) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(__xType), (void)(__uiValue), TRC_SUCCESS)

#define xTraceStackMonitorAdd(__pvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(__pvTask), TRC_SUCCESS)

#define xTraceStackMonitorRemove(__pvTask) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(__pvTask), TRC_SUCCESS)

#define xTraceStackMonitorGetAtIndex(__uiIndex, __ppvTask, __puxLowWaterMark) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(__uiIndex), (void)_(ppvTask), (void)(__puxLowWaterMark), TRC_SUCCESS)

#define xTraceStackMonitorReport() TRC_COMMA_EXPR_TO_STATEMENT_EXPR_1(TRC_SUCCESS)

#endif

#endif
