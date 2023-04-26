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
 * @brief Public trace event buffer APIs.
 */

#ifndef TRC_EVENT_BUFFER_H
#define TRC_EVENT_BUFFER_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <trcTypes.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @defgroup trace_event_buffer_apis Trace Event Buffer APIs
 * @ingroup trace_recorder_apis
 * @{
 */

/**
 * @def TRC_EVENT_BUFFER_OPTION_SKIP
 * @brief Buffer should skip new events when full
 */
#define TRC_EVENT_BUFFER_OPTION_SKIP		(0U)

/**
 * @def TRC_EVENT_BUFFER_OPTION_OVERWRITE
 * @brief Buffer should overwrite old events when full
 */
#define TRC_EVENT_BUFFER_OPTION_OVERWRITE	(1U)

/**
 * @brief Trace Event Buffer Structure
 */
typedef struct TraceEventBuffer
{
	uint32_t uiHead;				/**< Head index of buffer */
	uint32_t uiTail;				/**< Tail index of buffer */
	uint32_t uiSize;				/**< Buffer size */
	uint32_t uiOptions;				/**< Options (skip/overwrite when full) */
	uint32_t uiDroppedEvents;		/**< Nr of dropped events */
	uint32_t uiFree;				/**< Nr of free bytes */
	uint32_t uiTimerWraparounds;	/**< Nr of timer wraparounds */
	uint8_t* puiBuffer;				/**< Trace Event Buffer: may be NULL */
} TraceEventBuffer_t;

/**
 * @internal Initialize trace event buffer.
 * 
 * This routine initializes a trace event buffer and assigns it a
 * memory area based on the supplied buffer.
 * 
 * Trace event buffer options specifies the buffer behavior regarding
 * old data, the alternatives are TRC_EVENT_BUFFER_OPTION_SKIP and
 * TRC_EVENT_BUFFER_OPTION_OVERWRITE (mutal exclusive).
 *
 * @param[out] pxTraceEventBuffer Pointer to uninitialized trace event buffer.
 * @param[in] uiOptions Trace event buffer options.
 * @param[in] puiBuffer Pointer to buffer that will be used by the trace event buffer.
 * @param[in] uiSize Size of buffer
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEventBufferInitialize(TraceEventBuffer_t * pxTraceEventBuffer, uint32_t uiOptions,
		uint8_t *puiBuffer, uint32_t uiSize);

/**
 * @brief Pushes data into trace event buffer.
 * 
 * This routine attempts to push data into the trace event buffer.
 *
 * @param[in] pxTraceEventBuffer Pointer to initialized trace event buffer.
 * @param[in] pxData Pointer to data that should be pushed into trace event buffer.
 * @param[in] uiSize Size of data.
 * @param[out] piBytesWritten Bytes written.
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEventBufferPush(TraceEventBuffer_t *pxTraceEventBuffer, void *pxData, uint32_t uiSize, int32_t *piBytesWritten);

/**
 * @brief Transfer trace event buffer data through streamport.
 * 
 * This routine will attempt to transfer all existing data in the trace event
 * buffer through the streamport. New data pushed to the trace event buffer
 * during the execution of this routine will not be transfered to 
 * 
 * @param[in] pxTraceEventBuffer Pointer to initialized trace event buffer.
 * @param[out] piBytesWritten Bytes written.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEventBufferTransfer(TraceEventBuffer_t* pxTraceEventBuffer, int32_t* piBytesWritten);

/**
 * @brief Clears all data from event buffer.
 * 
 * @param[in] pxTraceEventBuffer Pointer to initialized trace event buffer.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceEventBufferClear(TraceEventBuffer_t* pxTraceEventBuffer);

/** @} */

#ifdef __cplusplus
}
#endif

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#endif /* TRC_EVENT_BUFFER_H */
