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
 * @brief Public trace counter APIs.
 */

#ifndef TRC_COUNTER_H
#define TRC_COUNTER_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_counter_apis Trace Counter APIs
 * @ingroup trace_recorder_apis
 * @{
 */

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
traceResult xTraceCounterAdd(TraceCounterHandle_t xCounterHandle, TraceBaseType_t xValue);

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
 * @param[out] pxValue Value.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceCounterGet(TraceCounterHandle_t xCounterHandle, TraceBaseType_t* pxValue);

/**
 * @brief Increases trace counter value.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle. 
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceCounterIncrease(TraceCounterHandle_t xCounterHandle);

/**
 * @brief Decreases trace counter value.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceCounterDecrease(TraceCounterHandle_t xCounterHandle);

/**
 * @brief Gets trace counter upper limit.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle.
 * @param[out] pxValue Value.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceCounterGetUpperLimit(TraceCounterHandle_t xCounterHandle, TraceBaseType_t* pxValue);

/**
 * @brief Gets trace counter lower limit.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle.
 * @param[out] pxValue Value
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceCounterGetLowerLimit(TraceCounterHandle_t xCounterHandle, TraceBaseType_t* pxValue);

/**
 * @brief Gets trace counter name.
 * 
 * @param[in] xCounterHandle Initialized trace counter handle.
 * @param[out] pszName Name.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceCounterGetName(TraceCounterHandle_t xCounterHandle, const char** pszName);

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_COUNTER_H */
