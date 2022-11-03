/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The interface definitions for trace streaming ("stream ports").
 * This "stream port" sets up the recorder to use ARM ITM as streaming channel.
 *
 * To setup Keil uVision for ITM tracing with a Keil ULINKpro (or ULINKplus),
 * see Percepio Application Note PA-021, available at
 * https://percepio.com/2018/05/04/keil-itm-support/
 * 
 * To setup IAR Embedded Workbench for ITM tracing with an IAR I-Jet,
 * see Percepio Application Note PA-023, https://percepio.com/iar
 *
 * NOTE: This stream port may block the application in case the ITM port
 * is not ready for more data (the TPIU FIFO has become full). This is
 * necessary to avoid data loss, as the TPIU FIFO is often quite small.
 *
 * --- Direct vs. Indirect ITM streaming ---
 * Direct streaming: By default, this stream port writes directly to the ITM
 * register mode without any RAM buffer. This assumes you have a fast debug
 * probe, like aKeil ULINKpro or IAR I-Jet, to avoid excessive blocking.
 * In case the ITM blocking appears to disturb your application, make sure your
 * debugger is configured for maximum performance, as described in the above
 * Application Nodes.
 *
 * Indirect streaming: If direct streaming gives too much overhead, you may
 * instead try indirect ITM streaming. This is done by enabling the internal
 * RAM buffer, like below. This reconfigures the recorder to store the events
 * in the internal RAM buffer instead of writing them directly to the ITM port.
 * 
 * Set TRC_STREAM_PORT_USE_INTERNAL_BUFFER to 1 to use the indirect mode.
 *
 * This increases RAM usage but eliminates peaks in the trace data rate.
 * Moreover, the ITM writes are then performed in a separate task (TzCtrl).
 * You find relevant settings (buffer size etc.) in trcStreamingConfig.h.
 *
 * See also https://percepio.com/2018/10/11/tuning-your-custom-trace-streaming 
 *
 * --- One-way vs. Two-way Communication ---
 * The ITM port only provides one-way communication, from target to host.  
 * This is sufficient if you start the tracing from the target application,
 * using vTraceEnable(TRC_START). Just make sure to start the Tracealyzer
 * recording before you start the target system.
 *
 * In case you prefer to interactively start and stop the tracing from the host
 * computer, you need two-way communication to send commands to the recorder.
 * This is possible by writing such "start" and "stop" commands to a special
 * buffer, monitored by the recorder library, using the debugger IDE. 
 * See trcStreamingPort.c and also the example macro for Keil uVision 
 * (Keil-uVision-Tracealyzer-ITM-Exporter.ini).
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

#if (!defined(TRC_CFG_STREAM_PORT_ITM_PORT) || (TRC_CFG_STREAM_PORT_ITM_PORT) < 0) || ((TRC_CFG_STREAM_PORT_ITM_PORT) > 31)
#error "Invalid ITM port defined in trcStreamPortConfig.h."
#endif

/* Important for the ITM port - no RAM buffer, direct writes. In most other ports this can be skipped (default is 1) */
#define TRC_USE_INTERNAL_BUFFER 0

typedef struct TraceStreamPortBuffer
{
	uint8_t buffer[sizeof(TraceUnsignedBaseType_t)];
} TraceStreamPortBuffer_t;

traceResult prvTraceItmWrite(void* ptrData, uint32_t size, int32_t* ptrBytesWritten);
traceResult prvTraceItmRead(void* ptrData, uint32_t uiSize, int32_t* piBytesRead);

traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer);

#define xTraceStreamPortAllocate(uiSize, ppvData) ((void)uiSize, xTraceStaticBufferGet(ppvData))

#define xTraceStreamPortCommit(pvData, uiSize, piBytesCommitted) prvTraceItmWrite(pvData, uiSize, piBytesCommitted)

#define xTraceStreamPortWriteData(pvData, uiSize, piBytesWritten) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_4((void)pvData, (void)uiSize, (void)piBytesWritten, TRC_SUCCESS)

#define xTraceStreamPortReadData(pvData, uiSize, piBytesRead) prvTraceItmRead(pvData, uiSize, piBytesRead)

#define xTraceStreamPortOnEnable(uiStartOption) TRC_COMMA_EXPR_TO_STATEMENT_EXPR_2((void)(uiStartOption), TRC_SUCCESS)

#define xTraceStreamPortOnDisable() TRC_COMMA_EXPR_TO_STATEMENT_EXPR_1(TRC_SUCCESS)

#define xTraceStreamPortOnTraceBegin() TRC_COMMA_EXPR_TO_STATEMENT_EXPR_1(TRC_SUCCESS)

#define xTraceStreamPortOnTraceEnd() TRC_COMMA_EXPR_TO_STATEMENT_EXPR_1(TRC_SUCCESS)

#ifdef __cplusplus
}
#endif

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/

#endif /* TRC_STREAM_PORT_H */
