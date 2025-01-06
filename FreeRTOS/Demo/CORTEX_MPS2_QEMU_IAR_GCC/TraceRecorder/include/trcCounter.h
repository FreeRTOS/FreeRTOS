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
 * @brief Public trace counter APIs.
 */

#ifndef TRC_COUNTER_H
#define TRC_COUNTER_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#define TRC_COUNTER_VALUE_INDEX 0
#define TRC_COUNTER_LOWER_LIMIT_INDEX 1
#define TRC_COUNTER_UPPER_LIMIT_INDEX 2

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_counter_apis Trace Counter APIs
 * @ingroup trace_recorder_apis
 * @{
 */

typedef struct TraceCounterData /* Aligned */
{
	TraceCounterCallback_t xCallbackFunction;
} TraceCounterData_t;

/**
 * @brief Initializes the Counter trace system
 * 
 * @param[in] pxBuffer Pointer to memory that is used by the counter system
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceCounterInitialize(TraceCounterData_t *pxBuffer);

/**
 * @brief Sets trace counter callback.
 * 
 * @param[in] xCallback Callback
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceCounterSetCallback(TraceCounterCallback_t xCallback);

/**
 * @brief Creates trace counter.
 * 
 * @param[in] szName Name.
 * @param[in] xInitialValue Initial value.
 * @param[in] xLowerLimit Lower limit.
 * @param[in] xUpperLimit Upper limit.
 * @param[out] pxCounterHandle Uninitialized trace counter handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceCounterCreate(const char* szName, TraceBaseType_t xInitialValue, TraceBaseType_t xLowerLimit, TraceBaseType_t xUpperLimit, TraceCounterHandle_t* pxCounterHandle);

/**
 * @brief Adds value to trace counter.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle.
 * @param[in] xValue Value.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceCounterAdd(xCounterHandle, xValue) xTraceCounterSet(xCounterHandle, (TraceBaseType_t)(xTraceEntryGetStateReturn((TraceEntryHandle_t)(xCounterHandle), TRC_COUNTER_VALUE_INDEX)) + (xValue))

/**
 * @brief Sets trace counter value.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle. 
 * @param[in] xValue Value.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceCounterSet(TraceCounterHandle_t xCounterHandle, TraceBaseType_t xValue);

/**
 * @brief Gets trace counter value.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle.
 * @param[out] pxValue Returned value.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceCounterGet(xCounterHandle, pxValue) xTraceEntryGetState((TraceEntryHandle_t)(xCounterHandle), TRC_COUNTER_VALUE_INDEX, (TraceUnsignedBaseType_t*)(pxValue))

/**
 * @brief Increases trace counter value.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceCounterIncrease(xCounterHandle) xTraceCounterAdd(xCounterHandle, 1)

/**
 * @brief Decreases trace counter value.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceCounterDecrease(xCounterHandle) xTraceCounterAdd(xCounterHandle, -1)

/**
 * @brief Gets trace counter upper limit.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle
 * @param[out] pxValue Returned value
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceCounterGetUpperLimit(xCounterHandle, pxValue) xTraceEntryGetState((TraceEntryHandle_t)(xCounterHandle), TRC_COUNTER_UPPER_LIMIT_INDEX, (TraceUnsignedBaseType_t*)(pxValue))

/**
 * @brief Gets trace counter lower limit.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle
 * @param[out] pxValue Returned value
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceCounterGetLowerLimit(xCounterHandle, pxValue) xTraceEntryGetState((TraceEntryHandle_t)(xCounterHandle), TRC_COUNTER_LOWER_LIMIT_INDEX, (TraceUnsignedBaseType_t*)(pxValue))

/**
 * @brief Gets trace counter name.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle.
 * @param[out] pszName Returned name.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceCounterGetName(xCounterHandle, pszName) xTraceEntryGetSymbol((TraceEntryHandle_t)(xCounterHandle), pszName)

/** @} */

#ifdef __cplusplus
}
#endif

#else

#define xTraceCounterSetCallback(_xCallback) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(_xCallback), TRC_SUCCESS)

#define xTraceCounterCreate(_szName, _xInitialValue, _xLowerLimit, _xUpperLimit, _pxCounterHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_6((void)(_szName), (void)(_xInitialValue), (void)(_xLowerLimit), (void)(_xUpperLimit), (void)(_pxCounterHandle), TRC_SUCCESS)

#define xTraceCounterAdd(_xCounterHandle, _xValue) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xCounterHandle), (void)(_xValue), TRC_SUCCESS)

#define xTraceCounterSet(_xCounterHandle, _xValue) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xCounterHandle), (void)(_xValue), TRC_SUCCESS)

#define xTraceCounterGet(_xCounterHandle, _pxValue) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xCounterHandle), (void)(_pxValue), TRC_SUCCESS)

#define xTraceCounterIncrease(_xCounterHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(_xCounterHandle), TRC_SUCCESS)

#define xTraceCounterDecrease(_xCounterHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(_xCounterHandle), TRC_SUCCESS)

#define xTraceCounterGetUpperLimit(_xCounterHandle, _pxValue) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xCounterHandle), (void)(_pxValue), TRC_SUCCESS)

#define xTraceCounterGetLowerLimit(_xCounterHandle, _pxValue) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xCounterHandle), (void)(_pxValue), TRC_SUCCESS)

#define xTraceCounterGetName(_xCounterHandle, _pszName) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xCounterHandle), (void)(_pszName), TRC_SUCCESS)

#endif

#endif
