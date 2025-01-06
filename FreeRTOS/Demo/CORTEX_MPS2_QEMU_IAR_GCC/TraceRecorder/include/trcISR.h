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
 * @brief Public trace ISR APIs.
 */

#ifndef TRC_ISR_H
#define TRC_ISR_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

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
 * @internal Trace ISR Core Data Structure
 */
typedef struct TraceISRCoreData	/* Aligned */
{
	TraceISRHandle_t handleStack[TRC_CFG_MAX_ISR_NESTING];	/**< */
	int32_t stackIndex;										/**< */
	uint32_t isPendingContextSwitch;							/**< */
} TraceISRCoreData_t;

/**
 * @internal Trace ISR Data Structure
 */
typedef struct TraceISRData	/* Aligned */
{
	TraceISRCoreData_t cores[TRC_CFG_CORE_COUNT]; /* ISR handles */
} TraceISRData_t;

/* We expose this to enable faster access */
extern TraceISRData_t* pxTraceISRData;

/**
 * @internal Initialize ISR trace system.
 * 
 * @param[in] pxBuffer Pointer to memory that will be used by the ISR
 * trace system.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceISRInitialize(TraceISRData_t *pxBuffer);

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
#define xTraceISRGetCurrentNesting(puiValue) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(puiValue) = pxTraceISRData->cores[TRC_CFG_GET_CURRENT_CORE()].stackIndex, TRC_SUCCESS)

/**
 * @brief 
 * 
 * @return int32_t 
 */
#define xTraceISRGetCurrentNestingReturned() (pxTraceISRData->cores[TRC_CFG_GET_CURRENT_CORE()].stackIndex)

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
#define xTraceISRGetCurrent(pxISRHandle) (xTraceISRGetCurrentNestingReturned() >= 0 ? (*(pxISRHandle) = pxTraceISRData->cores[TRC_CFG_GET_CURRENT_CORE()].handleStack[xTraceISRGetCurrentNestingReturned()], TRC_SUCCESS) : TRC_FAIL)

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

#else

#define xTraceISRRegister(_szName, _uiPriority, _pxISRHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(_szName), (void)(_uiPriority), (void)(_pxISRHandle), TRC_SUCCESS)

#define xTraceISRBegin(_xISRHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(_xISRHandle), TRC_SUCCESS)

#define xTraceISREnd(_xIsTaskSwitchRequired) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(_xIsTaskSwitchRequired), TRC_SUCCESS)

#define xTraceISRGetCurrentNesting(_puiValue) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(_puiValue), 0)

#define xTraceISRGetCurrentNestingReturned() (1)

#define xTraceISRGetCurrent(_pxISRHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(_pxISRHandle), TRC_SUCCESS)

/** @internal Deprecated - Provides backwards-compability with older recorders for now, will be removed in the future */
#define xTraceSetISRProperties(_szName, _uiPriority) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_szName), (void)(_uiPriority), TRC_SUCCESS)

/** @internal Deprecated - Provides backwards-compability with older recorders for now, will be removed in the future */
#define xTraceGetCurrentISRNesting(_puiValue) xTraceISRGetCurrentNesting(_puiValue)

/** @internal Deprecated - Provides backwards-compability with older recorders for now, will be removed in the future */
#define vTraceStoreISRBegin(_xISRHandle) xTraceISRBegin(_xISRHandle)

/** @internal Deprecated - Provides backwards-compability with older recorders for now, will be removed in the future */
#define vTraceStoreISREnd(_xIsTaskSwitchRequired) xTraceISREnd(_xIsTaskSwitchRequired)

#endif

#endif
