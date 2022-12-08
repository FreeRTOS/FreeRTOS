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
 * @brief Public internal event buffer APIs.
 */

#ifndef TRC_INTERNAL_BUFFER_H
#define TRC_INTERNAL_BUFFER_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#ifndef TRC_USE_INTERNAL_BUFFER
#define TRC_USE_INTERNAL_BUFFER 1
#endif

#if (TRC_USE_INTERNAL_BUFFER == 1)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_internal_event_buffer_apis Trace Internal Event Buffer APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @internal Initializes the internal trace event buffer used by certain stream ports.
 * 
 * @param[in] puiBuffer Pointer to previously allocated memory buffer
 * @param[in] uiSize Size of buffer
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceInternalEventBufferInitialize(uint8_t* puiBuffer, uint32_t uiSize);

/**
 * @brief Pushes data to the internal trace event buffer.
 * 
 * @param[in] pvData Pointer to data
 * @param[in] uiSize Size of data
 * @param[out] piBytesWritten Bytes written.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceInternalEventBufferPush(void *pvData, uint32_t uiSize, int32_t *piBytesWritten);

/**
 * @brief Transfers all internal trace event buffer data using the function 
 * xTraceStreamPortWriteData(...) as defined in trcStreamPort.h.
 *
 * This function is intended to be called by the periodic TzCtrl task with a 
 * suitable delay (e.g. 10-100 ms).
 *
 * In case of errors from the streaming interface, it registers a warning
 * (TRC_WARNING_STREAM_PORT_WRITE) provided by xTraceErrorGetLast().
 * 
 * @param[out] piBytesWritten Bytes written.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceInternalEventBufferTransfer(int32_t *piBytesWritten);

/**
 * @brief Clears all trace events in the internal trace event buffer.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceInternalEventBufferClear(void);

/** @} */

#ifdef __cplusplus
}
#endif

#else /* (TRC_USE_INTERNAL_BUFFER == 1)*/

#define xTraceInternalEventBufferInitialize(puiBuffer, uiSize) ((void)uiSize, puiBuffer != 0 ? TRC_SUCCESS : TRC_FAIL)
#define xTraceInternalEventBufferPush(pvData, uiSize, piBytesWritten) ((void)uiSize, (void)piBytesWritten, pvData != 0 ? TRC_SUCCESS : TRC_FAIL)
#define xTraceInternalEventBufferTransfer(piBytesWritten) ((void)piBytesWritten, TRC_SUCCESS)
#define xTraceInternalEventBufferClear() (void)(TRC_SUCCESS)

#endif /* (TRC_USE_INTERNAL_BUFFER == 1)*/

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_INTERNAL_BUFFER_H */
