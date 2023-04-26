/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Supporting functions for trace streaming, used by the "stream ports" 
 * for reading and writing data to the interface.
 *
 * Note that this stream port is more complex than the typical case, since
 * the J-Link interface uses a separate RAM buffer in SEGGER_RTT.c, instead
 * of the default buffer included in the recorder core. The other stream ports 
 * offer more typical examples of how to define a custom streaming interface.
 */
 
#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

typedef struct TraceStreamPortRTT {
#if (TRC_USE_INTERNAL_BUFFER == 1)
	uint8_t bufferInternal[TRC_STREAM_PORT_INTERNAL_BUFFER_SIZE];
#endif
	uint8_t bufferUp[TRC_STREAM_PORT_RTT_UP_BUFFER_SIZE];
	uint8_t bufferDown[TRC_STREAM_PORT_RTT_DOWN_BUFFER_SIZE];
} TraceStreamPortRTT_t;

static TraceStreamPortRTT_t* pxStreamPortRTT;

traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer)
{
	TRC_ASSERT_EQUAL_SIZE(TraceStreamPortBuffer_t, TraceStreamPortRTT_t);

	if (pxBuffer == 0)
	{
		return TRC_FAIL;
	}

	pxStreamPortRTT = (TraceStreamPortRTT_t*)pxBuffer;

#if (TRC_USE_INTERNAL_BUFFER == 1)
	return xTraceInternalEventBufferInitialize(pxStreamPortRTT->bufferInternal, sizeof(pxStreamPortRTT->bufferInternal));
#else
	return TRC_SUCCESS;
#endif
}

traceResult xTraceStreamPortOnEnable(uint32_t uiStartOption)
{
	(void)uiStartOption;

	/* Configure the RTT buffers */
	SEGGER_RTT_ConfigUpBuffer(TRC_CFG_STREAM_PORT_RTT_UP_BUFFER_INDEX, "TzData", pxStreamPortRTT->bufferUp, sizeof(pxStreamPortRTT->bufferUp), TRC_CFG_STREAM_PORT_RTT_MODE);
	SEGGER_RTT_ConfigDownBuffer(TRC_CFG_STREAM_PORT_RTT_DOWN_BUFFER_INDEX, "TzCtrl", pxStreamPortRTT->bufferDown, sizeof(pxStreamPortRTT->bufferDown), TRC_CFG_STREAM_PORT_RTT_MODE);

	return TRC_SUCCESS;
}

#endif

#endif
