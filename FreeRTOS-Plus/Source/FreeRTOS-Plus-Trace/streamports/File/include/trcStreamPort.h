/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The interface definitions for trace streaming ("stream ports").
 * This "stream port" sets up the recorder to stream the trace to file.
 */

#ifndef TRC_STREAM_PORT_H
#define TRC_STREAM_PORT_H

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <stdint.h>
#include <trcTypes.h>
#include <trcStreamPortConfig.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif
	
#define TRC_USE_INTERNAL_BUFFER (TRC_CFG_STREAM_PORT_USE_INTERNAL_BUFFER)

/* Default file name */
#ifndef TRC_CFG_STREAM_PORT_TRACE_FILE
#define TRC_CFG_STREAM_PORT_TRACE_FILE "trace.psf"
#endif

typedef struct TraceStreamPortFile
{
	FILE* pxFile;
#if (TRC_USE_INTERNAL_BUFFER)
	uint8_t buffer[TRC_STREAM_PORT_BUFFER_SIZE];
#endif
} TraceStreamPortFile_t;

extern TraceStreamPortFile_t* pxStreamPortFile;

#define TRC_STREAM_PORT_BUFFER_SIZE (sizeof(TraceStreamPortFile_t))

typedef struct TraceStreamPortBuffer
{
	uint8_t buffer[TRC_STREAM_PORT_BUFFER_SIZE];
} TraceStreamPortBuffer_t;

traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer);

#define xTraceStreamPortAllocate(uiSize, ppvData) ((void)(uiSize), xTraceStaticBufferGet(ppvData))

#if (TRC_USE_INTERNAL_BUFFER == 1)
/* Push to internal buffer. It will call on xTraceStreamPortWriteData() periodically. */
#define xTraceStreamPortCommit(pvData, uiSize, piBytesCommitted) xTraceInternalEventBufferPush(pvData, uiSize, piBytesCommitted)
#else
/* Write directly to file */
#define xTraceStreamPortCommit(pvData, uiSize, piBytesCommitted) xTraceStreamPortWriteData(pvData, uiSize, piBytesCommitted)
#endif

#define xTraceStreamPortWriteData(pvData, uiSize, piBytesWritten) (*(piBytesWritten) = fwrite(pvData, 1, uiSize, pxStreamPortFile->pxFile), TRC_SUCCESS)

#define xTraceStreamPortReadData(pvData, uiSize, piBytesRead) ((void)(pvData), (void)(uiSize), (void)(piBytesRead), TRC_SUCCESS)

#define xTraceStreamPortOnEnable(uiStartOption) ((void)(uiStartOption), TRC_SUCCESS)

#define xTraceStreamPortOnDisable() (TRC_SUCCESS)

traceResult xTraceStreamPortOnTraceBegin(void);

traceResult xTraceStreamPortOnTraceEnd(void);

#ifdef __cplusplus
}
#endif

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/

#endif /* TRC_STREAM_PORT_H */
