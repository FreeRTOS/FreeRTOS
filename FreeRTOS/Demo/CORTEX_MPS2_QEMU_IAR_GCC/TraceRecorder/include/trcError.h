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
 * @brief Public trace error APIs.
 */

#ifndef TRC_ERROR_H
#define TRC_ERROR_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_assert_apis Trace Asserts APIs
 * @ingroup trace_recorder_apis
 * @{
 */

typedef struct TraceErrorData	/* Aligned */
{
	uint32_t uiErrorAndWarningFlags;
	uint32_t uiErrorCode;
	TraceStringHandle_t xWarningChannel;
} TraceErrorData_t;

/**
 * @internal Initializes the error system
 *
 * @param[in] pxBuffer Pointer to buffer
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceErrorInitialize(TraceErrorData_t* pxBuffer);

/**
 * @brief Register a warning
 *
 * @param[in] uiErrorCode Label
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceWarning(uint32_t uiErrorCode);

/**
 * @brief Register an error
 *
 * @param[in] uiErrorCode Error code
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceError(uint32_t uiErrorCode);

/**
 * @brief Retrieve the string for the last error
 *
 * @param[out] pszError Error string pointer
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceErrorGetLast(const char** pszError);

/**
 * @brief Clears any errors
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceErrorClear(void);

/** @} */

#ifdef __cplusplus
}
#endif

#endif

#endif