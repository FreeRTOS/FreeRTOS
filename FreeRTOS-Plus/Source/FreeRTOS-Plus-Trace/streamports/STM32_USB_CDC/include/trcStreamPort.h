/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The interface definitions for trace streaming ("stream ports").
 * This "stream port" sets up the recorder to use USB CDC as streaming channel.
 * The example is for STM32 using STM32Cube.
 */

#ifndef TRC_STREAM_PORT_H
#define TRC_STREAM_PORT_H

#include <trcTypes.h>
#include <trcStreamPortConfig.h>

#ifdef __cplusplus
extern "C" {
#endif

#define TRC_USE_INTERNAL_BUFFER 1

#define TRC_STREAM_PORT_USB_BUFFER_SIZE ((((TRC_CFG_STREAM_PORT_USB_BUFFER_SIZE) + sizeof(TraceUnsignedBaseType_t) - 1) / sizeof(TraceUnsignedBaseType_t)) * sizeof(TraceUnsignedBaseType_t))
#define TRC_STREAM_PORT_INTERNAL_BUFFER_SIZE ((((TRC_CFG_STREAM_PORT_INTERNAL_BUFFER_SIZE) + sizeof(TraceUnsignedBaseType_t) - 1) / sizeof(TraceUnsignedBaseType_t)) * sizeof(TraceUnsignedBaseType_t))

typedef struct TraceStreamPortBuffer
{
	uint8_t buffer[(TRC_STREAM_PORT_USB_BUFFER_SIZE) + (TRC_STREAM_PORT_INTERNAL_BUFFER_SIZE) + sizeof(TraceUnsignedBaseType_t)];
} TraceStreamPortBuffer_t;

traceResult prvTraceCDCReceive(void* data, uint32_t uiSize, int32_t* piBytesReceived);

traceResult prvTraceCDCTransmit(void* pvData, uint32_t uiSize, int32_t* piBytesSent);

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
#define xTraceStreamPortAllocate(uiSize, ppvData) ((void)uiSize, xTraceStaticBufferGet(ppvData))

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
#define xTraceStreamPortCommit xTraceInternalEventBufferPush

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
#define xTraceStreamPortWriteData prvTraceCDCTransmit

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
#define xTraceStreamPortReadData prvTraceCDCReceive

#define xTraceStreamPortOnEnable(uiStartOption) ((void)(uiStartOption), TRC_SUCCESS)

#define xTraceStreamPortOnDisable() (TRC_SUCCESS)

#define xTraceStreamPortOnTraceBegin() (TRC_SUCCESS)

#define xTraceStreamPortOnTraceEnd() (TRC_SUCCESS)

#ifdef __cplusplus
}
#endif

#endif /* TRC_STREAM_PORT_H */
