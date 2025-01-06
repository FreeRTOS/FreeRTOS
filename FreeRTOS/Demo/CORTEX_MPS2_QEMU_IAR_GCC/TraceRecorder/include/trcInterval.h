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
 * @brief Public trace interval APIs.
 */

#ifndef TRC_INTERVAL_H
#define TRC_INTERVAL_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#ifdef __cplusplus
extern "C" {
#endif

#include <trcTypes.h>

#define TRC_INTERVAL_CHANNEL_SET_INDEX 0u

/**
 * @defgroup trace_interval_apis Trace Interval APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @brief Creates trace interval channel set.
 * 
 * @param[in] szName Name.
 * @param[out] pxIntervalChannelSetHandle Pointer to uninitialized trace interval channel set.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
	traceResult xTraceIntervalChannelSetCreate(const char* szName, TraceIntervalChannelSetHandle_t* pxIntervalChannelSetHandle);

/**
 * @brief Creates trace interval channel.
 * 
 * @param[in] szName Name.
 * @param[in] xIntervalChannelSetHandle Interval set that this channel belongs to.
 * @param[out] pxIntervalChannelHandle Pointer to uninitialized trace interval channel.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceIntervalChannelCreate(const char *szName, TraceIntervalChannelSetHandle_t xIntervalChannelSetHandle, TraceIntervalChannelHandle_t *pxIntervalChannelHandle);

/**
 * @brief Starts trace interval instance.
 * 
 * @param[in] xIntervalChannelHandle Interval handle.
 * @param[in] uxValue Value that can be used to tell instances apart.
 * @param[out] pxIntervalInstanceHandle Pointer to interval instance variable.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceIntervalStart(TraceIntervalChannelHandle_t xIntervalChannelHandle, TraceUnsignedBaseType_t uxValue, TraceIntervalInstanceHandle_t* pxIntervalInstanceHandle);

/**
 * @brief Stops trace interval instance.
 * 
 * @param[in] xIntervalChannelHandle Interval handle.
 * @param[in] xIntervalInstanceHandle Interval instance.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceIntervalStop(TraceIntervalChannelHandle_t xIntervalChannelHandle, TraceIntervalInstanceHandle_t xIntervalInstanceHandle);

/**
 * @brief Gets trace interval channel state.
 * 
 * @param[in] xIntervalChannelHandle Pointer to initialized trace interval.
 * @param[out] puxState State.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
#define xTraceIntervalGetState(xIntervalChannelHandle, puxState) xTraceEntryGetState((TraceEntryHandle_t)(xIntervalChannelHandle), TRC_INTERVAL_CHANNEL_SET_INDEX, puxState)

/** @} */

#ifdef __cplusplus
}
#endif

#else

#define xTraceIntervalChannelSetCreate(_szName, _pxIntervalChannelSetHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_szName), (void)(_pxIntervalChannelSetHandle), TRC_SUCCESS)

#define xTraceIntervalChannelCreate(_szName, _xIntervalChannelSetHandle, _pxIntervalChannelHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(_szName), (void)(_xIntervalChannelSetHandle), (void)(_pxIntervalChannelHandle), TRC_SUCCESS)

#define xTraceIntervalStart(_xIntervalHandle, _uxValue, _pxIntervalInstanceHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)(_xIntervalHandle), (void)(_uxValue), (void)(_pxIntervalInstanceHandle), TRC_SUCCESS)

#define xTraceIntervalStop(_xIntervalHandle, _xIntervalInstanceHandle) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xIntervalHandle), (void)(_xIntervalInstanceHandle), TRC_SUCCESS)

#define xTraceIntervalGetState(_xIntervalHandle, _puxState) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_3((void)(_xIntervalHandle), (void)(_puxState), TRC_SUCCESS)

#endif

#endif
