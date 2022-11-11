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
 * @brief Public trace interval APIs.
 */

#ifndef TRC_INTERVAL_H
#define TRC_INTERVAL_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_interval_apis Trace Interval APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @brief Creates trace interval.
 * 
 * @param[in] szName Name.
 * @param[out] pxIntervalHandle Pointer to uninitialized trace interval.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceIntervalCreate(const char *szName, TraceIntervalHandle_t *pxIntervalHandle);

/**
 * @brief Starts trace interval.
 * 
 * @param[in] xIntervalHandle Pointer to initialized trace interval.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceIntervalStart(TraceIntervalHandle_t xIntervalHandle);

/**
 * @brief Stops trace interval.
 * 
 * @param[in] xIntervalHandle Pointer to initialized trace interval.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceIntervalStop(TraceIntervalHandle_t xIntervalHandle);

/**
 * @brief Gets trace interval state.
 * 
 * @param[in] xIntervalHandle Pointer to initialized trace interval.
 * @param[out] puxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceIntervalGetState(TraceIntervalHandle_t xIntervalHandle, uint32_t *puxState);

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_INTERVAL_H */
