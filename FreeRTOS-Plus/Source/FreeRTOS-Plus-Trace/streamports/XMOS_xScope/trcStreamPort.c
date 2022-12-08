/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Supporting functions for trace streaming, used by the "stream ports" 
 * for reading and writing data to the interface.
 */
 
#include <trcRecorder.h>
#include <xscope.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

typedef struct TraceStreamPortXS {
#if (TRC_USE_INTERNAL_BUFFER == 1)
	uint8_t uiBufferInternal[TRC_STREAM_PORT_INTERNAL_BUFFER_SIZE];
#endif
	uint8_t uiBuffer[4];
} TraceStreamPortXS_t;

static TraceStreamPortXS_t* pxStreamPortXS;

traceResult xTraceStreamPortInitialize(TraceStreamPortBuffer_t* pxBuffer)
{
	TRC_ASSERT_EQUAL_SIZE(TraceStreamPortBuffer_t, TraceStreamPortXS_t);

	if (pxBuffer == 0)
	{
		return TRC_FAIL;
	}

	pxStreamPortXS = (TraceStreamPortXS_t*)pxBuffer;

#if (TRC_USE_INTERNAL_BUFFER == 1)
	return xTraceInternalEventBufferInitialize(pxStreamPortXS->uiBufferInternal, sizeof(pxStreamPortXS->uiBufferInternal));
#else
	return TRC_SUCCESS;
#endif
}

traceResult xTraceStreamPortOnBegin(void)
{
	return TRC_SUCCESS;
}

traceResult xTraceStreamPortOnEnd(void)
{
	return TRC_SUCCESS;
}

traceResult xTraceStreamPortAllocate(uint32_t uiSize, void** ppvData)
{
	(void)uiSize;

	return xTraceStaticBufferGet(ppvData);
}

traceResult xTraceStreamPortCommit(void* pvData, uint32_t uiSize, int32_t* piBytesCommitted)
{
	if (pvData == 0)
	{
		return TRC_FAIL;
	}

#if (TRC_USE_INTERNAL_BUFFER == 1)
	/* Push to internal buffer. It will call on xTraceStreamPortWriteData() periodically. */
	return xTraceInternalEventBufferPush(pvData, uiSize, piBytesCommitted);
#else
	/* Write directly to file */
	return xTraceStreamPortWriteData(pvData, uiSize, piBytesCommitted);
#endif
}

traceResult xTraceStreamPortWriteData(void* pvData, uint32_t uiSize, int32_t* piBytesWritten)
{
	/* xscope_bytes is supposed to be thread safe, so we do not bother with any
	 * critical sections here. */
	xscope_bytes(0, uiSize, (unsigned char*)pvData);

	if (piBytesWritten != 0) {
		/* Since xScope always write all bytes (not all might be received) we flag this as
		 * a full write */
		*piBytesWritten = (int32_t)uiSize;
	}

	return TRC_SUCCESS;
}

traceResult xTraceStreamPortReadData(void* pvData, uint32_t uiSize, int32_t* piBytesRead)
{
	return TRC_SUCCESS;
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */