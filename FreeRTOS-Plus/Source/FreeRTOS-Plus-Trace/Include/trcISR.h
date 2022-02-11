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
 * @brief Public trace ISR APIs.
 */

#ifndef TRC_ISR_H
#define TRC_ISR_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_isr_apis Trace ISR APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @internal Trace ISR Core Info Structure
 */
typedef struct TraceISRCoreInfo
{
	TraceISRHandle_t handleStack[TRC_CFG_MAX_ISR_NESTING];	/**< */
	int32_t stackIndex;										/**< */
	int32_t isPendingContextSwitch;							/**< */
} TraceISRCoreInfo_t;

/**
 * @internal Trace ISR Info Structure
 */
typedef struct TraceISRInfo
{
	TraceISRCoreInfo_t coreInfos[TRC_CFG_CORE_COUNT]; /* ISR handles */
} TraceISRInfo_t;

/* We expose this to enable faster access */
extern TraceISRInfo_t* pxTraceISRInfo;

#define TRACE_ISR_INFO_BUFFER_SIZE (sizeof(TraceISRInfo_t))

/**
 * @internal Trace ISR Info Buffer
 */
typedef struct TraceISRInfoBuffer
{
	uint8_t buffer[(TRACE_ISR_INFO_BUFFER_SIZE)];	/**< */
} TraceISRInfoBuffer_t;

/**
 * @internal Initialize ISR trace system.
 * 
 * @param[in] pxBuffer Pointer to memory that will be used by the ISR
 * trace system.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceISRInitialize(TraceISRInfoBuffer_t *pxBuffer);

/**
 * @brief Registers trace ISR.
 * 
 * This routine stores a name and priority level for an Interrupt Service Routine,
 * to allow for better visualization. Returns a TraceISRHandle_t used by
 * xTraceISRBegin/xTraceISREnd.
 * 
 * Example:
 * 	#define PRIO_OF_ISR_TIMER1 3 // the hardware priority of the interrupt
 *	TraceISRHandle_t xISRTimer1Handle = 0; // The ID set by the recorder
 *	...
 *	xTraceISRRegister("ISRTimer1", PRIO_OF_ISR_TIMER1, &xISRTimer1Handle);
 *	...
 *	void ISR_handler()
 *	{
 *		xTraceISRBegin(xISRTimer1Handle);
 *		...
 *		xTraceISREnd(0);
 *	}
 * 
 * @param[in] szName Name.
 * @param[in] uiPriority Priority.
 * @param[out] pxISRHandle Pointer to uninitialized ISR trace handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceISRRegister(const char* szName, uint32_t uiPriority, TraceISRHandle_t* pxISRHandle);

/**
 * @brief Registers the beginning of an Interrupt Service Routine.
 * 
 * This routine register the beginning of an ISR using a TraceISRHandle_t.
 * See xTraceISRRegister for and example of using ISR tracing.
 * 
 * @param[in] xISRHandle Pointer to initialized ISR trace handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceISRBegin(TraceISRHandle_t xISRHandle);

/**
 * @brief Registers the end of an Interrupt Service Routine.
 * 
 * This routine register the end of an ISR using a TraceISRHandle_t.
 * See xTraceISRRegister for and example of using ISR tracing.
 * 
 * The parameter uxIsTaskSwitchRequired indicates if the interrupt has requested
 * a task-switch (= 1), e.g., by signaling a semaphore. Otherwise (= 0) the
 * interrupt is assumed to return to the previous context.
 * 
 * @param[in] xIsTaskSwitchRequired Task switch required.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceISREnd(TraceBaseType_t xIsTaskSwitchRequired);

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

/**
 * @brief Gets current trace ISR nesting level.
 * 
 * This routine gets the current trace ISR nesting level for the
 * CPU on which it is called.
 * 
 * @param[out] puiValue Value.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceISRGetCurrentNesting(int32_t* puiValue);

/**
 * @brief 
 * 
 * @return int32_t 
 */
int32_t xTraceISRGetCurrentNestingReturned(void);

/**
 * @brief Gets current ISR trace handle.
 * 
 * @param[out] pxISRHandle ISR Handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceISRGetCurrent(TraceISRHandle_t* pxISRHandle);

#else /* ((TRC_CFG_USE_TRACE_ASSERT) == 1) */

/**
 * @brief Gets current trace ISR nesting level.
 * 
 * This routine gets the current trace ISR nesting level for the
 * CPU on which it is called.
 * 
 * @param[out] puiValue Value.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceISRGetCurrentNesting(puiValue) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(puiValue) = pxTraceISRInfo->coreInfos[TRC_CFG_GET_CURRENT_CORE()].stackIndex, TRC_SUCCESS)

/**
 * @brief 
 * 
 * @return int32_t 
 */
#define xTraceISRGetCurrentNestingReturned() (pxTraceISRInfo->coreInfos[TRC_CFG_GET_CURRENT_CORE()].stackIndex)

/**
 * @brief Gets current trace ISR nesting level.
 * 
 * This routine gets the current trace ISR nesting level for the
 * CPU on which it is called.
 * 
 * @param[out] puiValue Value.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceISRGetCurrent(pxISRHandle) (xTraceISRGetCurrentNestingReturned() >= 0 ? (*(pxISRHandle) = pxTraceISRInfo->coreInfos[TRC_CFG_GET_CURRENT_CORE()].handleStack[xTraceISRGetCurrentNestingReturned()], TRC_SUCCESS) : TRC_FAIL)

#endif /* ((TRC_CFG_USE_TRACE_ASSERT) == 1) */

/** @internal Deprecated - Provides backwards-compability with older recorders for now, will be removed in the future */
TraceISRHandle_t xTraceSetISRProperties(const char* szName, uint32_t uiPriority);

/** @internal Deprecated - Provides backwards-compability with older recorders for now, will be removed in the future */
#define xTraceGetCurrentISRNesting(puiValue) xTraceISRGetCurrentNesting(puiValue)

/** @internal Deprecated - Provides backwards-compability with older recorders for now, will be removed in the future */
#define vTraceStoreISRBegin(xISRHandle) xTraceISRBegin(xISRHandle)

/** @internal Deprecated - Provides backwards-compability with older recorders for now, will be removed in the future */
#define vTraceStoreISREnd(xIsTaskSwitchRequired) xTraceISREnd(xIsTaskSwitchRequired)

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_ISR_H */
