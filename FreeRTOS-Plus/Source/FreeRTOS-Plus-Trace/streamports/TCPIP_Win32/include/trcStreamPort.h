/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The interface definitions for trace streaming ("stream ports").
 * This "stream port" sets up the recorder to use TCP/IP as streaming channel.
 * The example is for Windows sockets (Winsock), for use with Windows ports.
 */

#ifndef TRC_STREAM_PORT_H
#define TRC_STREAM_PORT_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <stdint.h>
#include <trcTypes.h>
#include <trcStreamPortConfig.h>

#ifdef __cplusplus
extern "C" {
#endif

#define TRC_USE_INTERNAL_BUFFER (TRC_CFG_STREAM_PORT_USE_INTERNAL_BUFFER)

/**
 * @def TRC_STREAM_PORT_BUFFER_SIZE
 *
 * @brief The buffer size, aligned to base type.
 */
#define TRC_STREAM_PORT_BUFFER_SIZE ((((TRC_CFG_STREAM_PORT_BUFFER_SIZE) + sizeof(TraceUnsignedBaseType_t) - 1) / sizeof(TraceUnsignedBaseType_t)) * sizeof(TraceUnsignedBaseType_t))

typedef struct TraceStreamPortBuffer
{
#if (TRC_USE_INTERNAL_BUFFER)
	uint8_t buffer[(TRC_STREAM_PORT_BUFFER_SIZE)];
#else
	TraceUnsignedBaseType_t buffer[1];
#endif
} TraceStreamPortBuffer_t;

int32_t prvTraceWriteToSocket(void* data, uint32_t size, int32_t* ptrBytesWritten);
int32_t prvTraceReadFromSocket(void* data, uint32_t bufsize, int32_t* ptrBytesRead);

traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer);

#define xTraceStreamPortAllocate(uiSize, ppvData) ((void)(uiSize), xTraceStaticBufferGet(ppvData))

#if (TRC_USE_INTERNAL_BUFFER == 1)
/* Push to internal buffer. It will call on xTraceStreamPortWriteData() periodically. */
#define xTraceStreamPortCommit xTraceInternalEventBufferPush
#else
/* Write directly */
#define xTraceStreamPortCommit xTraceStreamPortWriteData
#endif

#define xTraceStreamPortWriteData(pvData, uiSize, piBytesWritten) (prvTraceWriteToSocket(pvData, uiSize, piBytesWritten) == 0 ? TRC_SUCCESS : TRC_FAIL)

#define xTraceStreamPortReadData(pvData, uiSize, piBytesRead) (prvTraceReadFromSocket(pvData, uiSize, piBytesRead) == 0 ? TRC_SUCCESS : TRC_FAIL)

#define xTraceStreamPortOnEnable(uiStartOption) ((void)(uiStartOption), TRC_SUCCESS)

#define xTraceStreamPortOnDisable() (TRC_SUCCESS)

#define xTraceStreamPortOnTraceBegin() (TRC_SUCCESS)

traceResult xTraceStreamPortOnTraceEnd(void);

#ifdef __cplusplus
}
#endif

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/

#endif /* TRC_STREAM_PORT_H */
