/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for the event buffer.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

traceResult xTraceEventBufferInitialize(TraceEventBuffer_t* pxTraceEventBuffer, uint32_t uiOptions,
	uint8_t* puiBuffer, uint32_t uiSize)
{
	/* This should never fail */
	TRC_ASSERT(pxTraceEventBuffer != 0);

	/* This should never fail */
	TRC_ASSERT(puiBuffer != 0);

	pxTraceEventBuffer->uiOptions = uiOptions;
	pxTraceEventBuffer->uiHead = 0;
	pxTraceEventBuffer->uiTail = 0;
	pxTraceEventBuffer->uiSize = uiSize;
	pxTraceEventBuffer->uiFree = uiSize;
	pxTraceEventBuffer->puiBuffer = puiBuffer;
	pxTraceEventBuffer->uiTimerWraparounds = 0;

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_EVENT_BUFFER);

	return TRC_SUCCESS;
}

/**
 * @brief Pops the oldest event from the Event Buffer.
 * 
 * @param[in] pxTraceEventBuffer Pointer to initialized trace event buffer.
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
static traceResult prvTraceEventBufferPop(TraceEventBuffer_t *pxTraceEventBuffer)
{
	uint32_t uiFreeSize = 0;

	/* Get size of event we are freeing */
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEventGetSize(((void*)&(pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiTail])), &uiFreeSize) == TRC_SUCCESS);

	pxTraceEventBuffer->uiFree += uiFreeSize;

	/* Update tail to point to the new last event */
	pxTraceEventBuffer->uiTail = (pxTraceEventBuffer->uiTail + uiFreeSize) % pxTraceEventBuffer->uiSize;

	return TRC_SUCCESS;
}

traceResult xTraceEventBufferPush(TraceEventBuffer_t *pxTraceEventBuffer, void *pxData, uint32_t uiDataSize, int32_t *piBytesWritten)
{
	uint32_t uiBufferSize;
	
	/* This should never fail */
	TRC_ASSERT(pxTraceEventBuffer != 0);
	
	/* This should never fail */
	TRC_ASSERT(pxData != 0);
	
	uiBufferSize = pxTraceEventBuffer->uiSize;

	/* Check if the data size is larger than the buffer */
	/* This should never fail */
	TRC_ASSERT(uiDataSize <= uiBufferSize);

	/* Check byte alignment */
	/* This should never fail */
	TRC_ASSERT((uiDataSize % 4) == 0);

	/* Ensure bytes written start at 0 */
	/* This should never fail */
	TRC_ASSERT(piBytesWritten != 0);

	*piBytesWritten = 0;

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceTimestampGetWraparounds(&pxTraceEventBuffer->uiTimerWraparounds) == TRC_SUCCESS);

	/* In ring buffer mode we cannot provide lock free access since the producer modified
	 * the head and tail variables in the same call. This option is only safe when used
	 * with an internal buffer (streaming snapshot) which no consumer accesses.
	 */
	switch (pxTraceEventBuffer->uiOptions)
	{
		case TRC_EVENT_BUFFER_OPTION_OVERWRITE:
		{
			uint32_t uiHead = pxTraceEventBuffer->uiHead;

			/* If there isn't enough space in the buffer pop events until there is */
			while (pxTraceEventBuffer->uiFree < uiDataSize)
			{
				prvTraceEventBufferPop(pxTraceEventBuffer);
			}

			/* Copy data */
			if ((uiBufferSize - uiHead) > uiDataSize)
			{
				TRC_MEMCPY(&pxTraceEventBuffer->puiBuffer[uiHead], pxData, uiDataSize);
			}
			else
			{
				TRC_MEMCPY(&pxTraceEventBuffer->puiBuffer[uiHead], pxData, uiBufferSize - uiHead);
				TRC_MEMCPY(pxTraceEventBuffer->puiBuffer,
							(void*)(&((uint8_t*)pxData)[(uiBufferSize - uiHead)]),
							uiDataSize - (uiBufferSize - uiHead));
			}

			pxTraceEventBuffer->uiFree -= uiDataSize;

			pxTraceEventBuffer->uiHead = (uiHead + uiDataSize) % uiBufferSize;

			*piBytesWritten = uiDataSize;

			break;
		}

		case TRC_EVENT_BUFFER_OPTION_SKIP:
		{
			/* Since a consumer could potentially update tail (free) during the procedure
			 * we have to save it here to avoid problems with the push algorithm.
			 */
			uint32_t uiHead = pxTraceEventBuffer->uiHead;
			uint32_t uiTail = pxTraceEventBuffer->uiTail;

			if (uiHead >= uiTail)
			{
				uint32_t uiFreeSpace = (uiBufferSize - uiHead - sizeof(uint32_t)) + uiTail;

				if (uiFreeSpace < uiDataSize)
				{
					*piBytesWritten = 0;

					return TRC_SUCCESS;
				}

				/* Copy data */
				if ((uiBufferSize - uiHead) > uiDataSize)
				{
					TRC_MEMCPY(&pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiHead], pxData, uiDataSize);
				}
				else
				{
					TRC_MEMCPY(&pxTraceEventBuffer->puiBuffer[uiHead], pxData, uiBufferSize - uiHead);
					TRC_MEMCPY(pxTraceEventBuffer->puiBuffer,
								(void*)(&((uint8_t*)pxData)[(uiBufferSize - uiHead)]),
								uiDataSize - (uiBufferSize - uiHead));
				}

				pxTraceEventBuffer->uiHead = (uiHead + uiDataSize) % uiBufferSize;
			}
			else
			{
				uint32_t uiFreeSpace = uiTail - uiHead - sizeof(uint32_t);

				if (uiFreeSpace < uiDataSize)
				{
					*piBytesWritten = 0;

					return TRC_SUCCESS;
				}

				/* Copy data */
				TRC_MEMCPY(&pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiHead], pxData, uiDataSize);

				pxTraceEventBuffer->uiHead = (uiHead + uiDataSize);
			}

			*piBytesWritten = uiDataSize;

			break;
		}

		default:
		{
			return TRC_FAIL;
		}
	}

	return TRC_SUCCESS;
}

traceResult xTraceEventBufferTransfer(TraceEventBuffer_t* pxTraceEventBuffer, int32_t* piBytesWritten)
{
	int32_t iBytesWritten = 0;
	int32_t iSumBytesWritten = 0;
	uint32_t uiHead;
	uint32_t uiTail;

	/* This should never fail */
	TRC_ASSERT(pxTraceEventBuffer != 0);

	/* This should never fail */
	TRC_ASSERT(piBytesWritten != 0);

	uiHead = pxTraceEventBuffer->uiHead;
	uiTail = pxTraceEventBuffer->uiTail;

	/* Check if core event buffer is empty */
	if (uiHead == uiTail)
	{
		return TRC_SUCCESS;
	}

	/* Check if we can do a direct write or if we have to handle wrapping */
	if (uiHead > uiTail)
	{
		xTraceStreamPortWriteData(&pxTraceEventBuffer->puiBuffer[uiTail], (uiHead - uiTail), &iBytesWritten);

		pxTraceEventBuffer->uiTail = uiHead;
	}
	else
	{
		xTraceStreamPortWriteData(&pxTraceEventBuffer->puiBuffer[uiTail], (pxTraceEventBuffer->uiSize - uiTail), &iBytesWritten);

		iSumBytesWritten += iBytesWritten;

		xTraceStreamPortWriteData(pxTraceEventBuffer->puiBuffer, uiHead, &iBytesWritten);

		pxTraceEventBuffer->uiTail = uiHead;
	}

	iSumBytesWritten += iBytesWritten;

	*piBytesWritten = iSumBytesWritten;

	return TRC_SUCCESS;
}

traceResult xTraceEventBufferClear(TraceEventBuffer_t* pxTraceEventBuffer)
{
	/* This should never fail */
	TRC_ASSERT(pxTraceEventBuffer != 0);

	pxTraceEventBuffer->uiHead = 0;
	pxTraceEventBuffer->uiTail = 0;
	pxTraceEventBuffer->uiFree = pxTraceEventBuffer->uiSize;

	return TRC_SUCCESS;
}

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
