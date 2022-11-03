/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The interface definitions for trace streaming ("stream ports").
 * This "stream port" sets up the recorder to use SEGGER RTT as streaming channel.
 *
 * Note that this stream port is more complex than the typical case, since
 * the J-Link interface uses a separate RAM buffer in SEGGER_RTT.c, instead
 * of the default buffer included in the recorder core. The other stream ports 
 * offer more typical examples of how to define a custom streaming interface.
 */

#ifndef TRC_STREAM_PORT_H
#define TRC_STREAM_PORT_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#ifdef __cplusplus
extern "C" {
#endif

#include <trcTypes.h>
#include <trcStreamPortConfig.h>

#include <SEGGER_RTT_Conf.h>
#include <SEGGER_RTT.h>

#define TRC_USE_INTERNAL_BUFFER (TRC_CFG_STREAM_PORT_USE_INTERNAL_BUFFER)

/* Aligned */
#define TRC_STREAM_PORT_INTERNAL_BUFFER_SIZE ((((TRC_CFG_STREAM_PORT_INTERNAL_BUFFER_SIZE) + sizeof(TraceUnsignedBaseType_t) - 1) / sizeof(TraceUnsignedBaseType_t)) * sizeof(TraceUnsignedBaseType_t))

/* Aligned */
#define TRC_STREAM_PORT_RTT_UP_BUFFER_SIZE ((((TRC_CFG_STREAM_PORT_RTT_UP_BUFFER_SIZE) + sizeof(TraceUnsignedBaseType_t) - 1) / sizeof(TraceUnsignedBaseType_t)) * sizeof(TraceUnsignedBaseType_t))

/* Aligned */
#define TRC_STREAM_PORT_RTT_DOWN_BUFFER_SIZE ((((TRC_CFG_STREAM_PORT_RTT_DOWN_BUFFER_SIZE) + sizeof(TraceUnsignedBaseType_t) - 1) / sizeof(TraceUnsignedBaseType_t)) * sizeof(TraceUnsignedBaseType_t))


/**
 * @brief A structure representing the trace stream port buffer.
 */
typedef struct TraceStreamPortBuffer
{
#if (TRC_USE_INTERNAL_BUFFER == 1)
	uint8_t bufferInternal[TRC_STREAM_PORT_INTERNAL_BUFFER_SIZE];
#endif
	uint8_t bufferUp[TRC_STREAM_PORT_RTT_UP_BUFFER_SIZE];
	uint8_t bufferDown[TRC_STREAM_PORT_RTT_DOWN_BUFFER_SIZE];
} TraceStreamPortBuffer_t;

/**
 * @internal Stream port initialize callback.
 * 
 * This function is called by the recorder as part of its initialization phase.
 * 
 * @param[in] pxBuffer Buffer
 * 
 * @retval TRC_FAIL Initialization failed
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer);

/**
 * @brief Allocates data from the stream port.
 * 
 * @param[in] uiSize Allocation size
 * @param[out] ppvData Allocation data pointer
 * 
 * @retval TRC_FAIL Allocate failed
 * @retval TRC_SUCCESS Success
 */
#define xTraceStreamPortAllocate(uiSize, ppvData) ((void)(uiSize), xTraceStaticBufferGet(ppvData))

/**
 * @brief Commits data to the stream port, depending on the implementation/configuration of the
 * stream port this data might be directly written to the stream port interface, buffered, or
 * something else.
 * 
 * @param[in] pvData Data to commit
 * @param[in] uiSize Data to commit size
 * @param[out] piBytesCommitted Bytes committed
 * 
 * @retval TRC_FAIL Commit failed
 * @retval TRC_SUCCESS Success
 */
#if (TRC_USE_INTERNAL_BUFFER == 1)
#define xTraceStreamPortCommit xTraceInternalEventBufferPush
#else
#define xTraceStreamPortCommit xTraceStreamPortWriteData
#endif

/**
 * @brief Writes data through the stream port interface.
 * 
 * @param[in] pvData Data to write
 * @param[in] uiSize Data to write size
 * @param[out] piBytesWritten Bytes written
 * 
 * @retval TRC_FAIL Write failed
 * @retval TRC_SUCCESS Success
 */
#if (defined(TRC_CFG_STREAM_PORT_RTT_NO_LOCK_WRITE) && TRC_CFG_STREAM_PORT_RTT_NO_LOCK_WRITE == 1)
#define xTraceStreamPortWriteData(pvData, uiSize, piBytesWritten) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(piBytesWritten) = (int32_t)SEGGER_RTT_WriteNoLock((TRC_CFG_STREAM_PORT_RTT_UP_BUFFER_INDEX), (const char*)pvData, uiSize), TRC_SUCCESS)
#else
#define xTraceStreamPortWriteData(pvData, uiSize, piBytesWritten) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2(*(piBytesWritten) = (int32_t)SEGGER_RTT_Write((TRC_CFG_STREAM_PORT_RTT_UP_BUFFER_INDEX), (const char*)pvData, uiSize), TRC_SUCCESS)
#endif

/**
 * @brief Reads data through the stream port interface.
 * 
 * @param[in] pvData Destination data buffer 
 * @param[in] uiSize Destination data buffer size
 * @param[out] piBytesRead Bytes read
 * 
 * @retval TRC_FAIL Read failed
 * @retval TRC_SUCCESS Success
 */
#define xTraceStreamPortReadData(pvData, uiSize, piBytesRead) ((SEGGER_RTT_HASDATA(TRC_CFG_STREAM_PORT_RTT_DOWN_BUFFER_INDEX)) ? (*(piBytesRead) = (int32_t)SEGGER_RTT_Read((TRC_CFG_STREAM_PORT_RTT_DOWN_BUFFER_INDEX), (char*)(pvData), uiSize), TRC_SUCCESS) : TRC_SUCCESS)

traceResult xTraceStreamPortOnEnable(uint32_t uiStartOption);

#define xTraceStreamPortOnDisable() (void)(TRC_SUCCESS)

#define xTraceStreamPortOnTraceBegin() (void)(TRC_SUCCESS)

#define xTraceStreamPortOnTraceEnd() (void)(TRC_SUCCESS)

#ifdef __cplusplus
}
#endif

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/

#endif /* TRC_STREAM_PORT_H */
