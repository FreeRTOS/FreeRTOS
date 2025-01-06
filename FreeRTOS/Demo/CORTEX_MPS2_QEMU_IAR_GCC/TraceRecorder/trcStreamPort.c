/*
* Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* Supporting functions for trace streaming, used by the "stream ports"
* for reading and writing data to the interface.
* This "stream port" sets up the recorder to stream to a Ring Buffer.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

/* Backwards compatibility with plugins */
typedef TraceRingBuffer_t RecorderData;
RecorderData* RecorderDataPtr TRC_CFG_RECORDER_DATA_ATTRIBUTE; /*cstat !MISRAC2004-8.7 !MISRAC2004-8.10 !MISRAC2012-Rule-8.4 !MISRAC2012-Rule-8.7 !MISRAC2012-Rule-8.9_b Suppress global object check*/

TraceStreamPortData_t* pxStreamPortData TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer)
{
	TraceRingBuffer_t* pxRingBuffer;

	TRC_ASSERT_EQUAL_SIZE(TraceStreamPortBuffer_t, TraceStreamPortData_t);
	
	if (pxBuffer == (void*)0)
	{
		return TRC_FAIL;
	}

	pxStreamPortData = (TraceStreamPortData_t*)pxBuffer; /*cstat !MISRAC2004-11.4 !MISRAC2012-Rule-11.3 Suppress conversion between pointer types checks*/
	pxRingBuffer = &pxStreamPortData->xRingBuffer;
	RecorderDataPtr = pxRingBuffer;

	pxRingBuffer->xEventBuffer.uxSize = sizeof(pxRingBuffer->xEventBuffer.uiBuffer);
	
#if (TRC_CFG_STREAM_PORT_RINGBUFFER_MODE == TRC_STREAM_PORT_RINGBUFFER_MODE_OVERWRITE_WHEN_FULL)
	if (xTraceMultiCoreEventBufferInitialize(&pxStreamPortData->xMultiCoreEventBuffer, TRC_EVENT_BUFFER_OPTION_OVERWRITE, pxRingBuffer->xEventBuffer.uiBuffer, sizeof(pxRingBuffer->xEventBuffer.uiBuffer)) == TRC_FAIL)
	{
		return TRC_FAIL;
	}
#else
	if (xTraceMultiCoreEventBufferInitialize(&pxStreamPortData->xMultiCoreEventBuffer, TRC_EVENT_BUFFER_OPTION_SKIP, pxRingBuffer->xEventBuffer.uiBuffer, sizeof(pxRingBuffer->xEventBuffer.uiBuffer)) == TRC_FAIL)
	{
		return TRC_FAIL;
	}
#endif

	if (xTraceHeaderInitialize(&pxRingBuffer->xHeaderBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}
	
	if (xTraceEntryTableInitialize(&pxRingBuffer->xEntryTable) == TRC_FAIL)
	{
		return TRC_FAIL;
	}
	
	if (xTraceTimestampInitialize(&pxRingBuffer->xTimestampInfo) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	pxRingBuffer->END_MARKERS[0] = 0x0AU;
	pxRingBuffer->END_MARKERS[1] = 0x0BU;
	pxRingBuffer->END_MARKERS[2] = 0x0CU;
	pxRingBuffer->END_MARKERS[3] = 0x0DU;
	
	pxRingBuffer->END_MARKERS[4] = 0x71U;
	pxRingBuffer->END_MARKERS[5] = 0x72U;
	pxRingBuffer->END_MARKERS[6] = 0x73U;
	pxRingBuffer->END_MARKERS[7] = 0x74U;
	
	pxRingBuffer->END_MARKERS[8] = 0xF1U;
	pxRingBuffer->END_MARKERS[9] = 0xF2U;
	pxRingBuffer->END_MARKERS[10] = 0xF3U;
	pxRingBuffer->END_MARKERS[11] = 0xF4U;

	pxRingBuffer->START_MARKERS[0] = 0x05U;
	pxRingBuffer->START_MARKERS[1] = 0x06U;
	pxRingBuffer->START_MARKERS[2] = 0x07U;
	pxRingBuffer->START_MARKERS[3] = 0x08U;
	
	pxRingBuffer->START_MARKERS[4] = 0x75U;
	pxRingBuffer->START_MARKERS[5] = 0x76U;
	pxRingBuffer->START_MARKERS[6] = 0x77U;
	pxRingBuffer->START_MARKERS[7] = 0x78U;
	
	pxRingBuffer->START_MARKERS[8] = 0xF5U;
	pxRingBuffer->START_MARKERS[9] = 0xF6U;
	pxRingBuffer->START_MARKERS[10] = 0xF7U;
	pxRingBuffer->START_MARKERS[11] = 0xF8U;
	
	return TRC_SUCCESS;
}

traceResult xTraceStreamPortOnTraceBegin(void)
{
	return xTraceMultiCoreEventBufferClear(&pxStreamPortData->xMultiCoreEventBuffer);
}

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/
