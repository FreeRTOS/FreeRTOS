/*
* Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
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
RecorderData* RecorderDataPtr = 0;

TraceStreamPortData_t* pxStreamPortData;

traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer)
{
	TraceRingBuffer_t* pxRingBuffer;

	TRC_ASSERT_EQUAL_SIZE(TraceStreamPortBuffer_t, TraceStreamPortData_t);
	
	if (pxBuffer == 0)
	{
		return TRC_FAIL;
	}

	pxStreamPortData = (TraceStreamPortData_t*)pxBuffer;
	RecorderDataPtr = pxRingBuffer = &pxStreamPortData->xRingBuffer;

	pxRingBuffer->xEventBuffer.uiSize = sizeof(pxRingBuffer->xEventBuffer.uiBuffer);
	
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
	
	if (xTraceEntryTableInitialize(&pxRingBuffer->xEntryTableBuffer) == TRC_FAIL)
	{
		return TRC_FAIL;
	}
	
	if (xTraceTimestampInitialize(&pxRingBuffer->xTimestampInfo) == TRC_FAIL)
	{
		return TRC_FAIL;
	}

	pxRingBuffer->END_MARKERS[0] = 0x0A;
	pxRingBuffer->END_MARKERS[1] = 0x0B;
	pxRingBuffer->END_MARKERS[2] = 0x0C;
	pxRingBuffer->END_MARKERS[3] = 0x0D;
	
	pxRingBuffer->END_MARKERS[4] = 0x71;
	pxRingBuffer->END_MARKERS[5] = 0x72;
	pxRingBuffer->END_MARKERS[6] = 0x73;
	pxRingBuffer->END_MARKERS[7] = 0x74;
	
	pxRingBuffer->END_MARKERS[8] = 0xF1;
	pxRingBuffer->END_MARKERS[9] = 0xF2;
	pxRingBuffer->END_MARKERS[10] = 0xF3;
	pxRingBuffer->END_MARKERS[11] = 0xF4;

	pxRingBuffer->START_MARKERS[0] = 0x05;
	pxRingBuffer->START_MARKERS[1] = 0x06;
	pxRingBuffer->START_MARKERS[2] = 0x07;
	pxRingBuffer->START_MARKERS[3] = 0x08;
	
	pxRingBuffer->START_MARKERS[4] = 0x75;
	pxRingBuffer->START_MARKERS[5] = 0x76;
	pxRingBuffer->START_MARKERS[6] = 0x77;
	pxRingBuffer->START_MARKERS[7] = 0x78;
	
	pxRingBuffer->START_MARKERS[8] = 0xF5;
	pxRingBuffer->START_MARKERS[9] = 0xF6;
	pxRingBuffer->START_MARKERS[10] = 0xF7;
	pxRingBuffer->START_MARKERS[11] = 0xF8;
	
	return TRC_SUCCESS;
}

traceResult xTraceStreamPortCommit(void* pvData, uint32_t uiSize, int32_t* piBytesCommitted)
{
	if (pvData == 0)
	{
		return TRC_FAIL;
	}

	xTraceMultiCoreEventBufferPush(&pxStreamPortData->xMultiCoreEventBuffer, pvData, uiSize, piBytesCommitted);

#if (TRC_CFG_STREAM_PORT_RINGBUFFER_MODE == TRC_STREAM_PORT_RINGBUFFER_MODE_STOP_WHEN_FULL)
	/* If no bytes was written it means that the buffer is full and we should stop
	 * tracing.
	 */
	if (uiSize > 0 && *piBytesCommitted == 0) {
		xTraceDisable();
		return TRC_FAIL;
	}
#endif

	return TRC_SUCCESS;
}

traceResult xTraceStreamPortOnTraceBegin()
{
	return xTraceMultiCoreEventBufferClear(&pxStreamPortData->xMultiCoreEventBuffer);
}

#endif /*(TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)*/

#endif /*(TRC_USE_TRACEALYZER_RECORDER == 1)*/
