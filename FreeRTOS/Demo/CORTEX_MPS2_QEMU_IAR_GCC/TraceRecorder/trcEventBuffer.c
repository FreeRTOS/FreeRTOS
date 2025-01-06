/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for the event buffer.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

traceResult xTraceEventBufferInitialize(TraceEventBuffer_t* pxTraceEventBuffer, uint32_t uiOptions,
	uint8_t* puiBuffer, uint32_t uiSize)
{
	/* This should never fail */
	TRC_ASSERT(pxTraceEventBuffer != (void*)0);

	/* This should never fail */
	TRC_ASSERT(puiBuffer != (void*)0);

	/* This should never fail */
	TRC_ASSERT(uiSize != 0u);

	pxTraceEventBuffer->uiOptions = uiOptions;
	pxTraceEventBuffer->uiHead = 0u;
	pxTraceEventBuffer->uiTail = 0u;
	pxTraceEventBuffer->uiSize = uiSize;
	pxTraceEventBuffer->uiFree = uiSize;
	pxTraceEventBuffer->puiBuffer = puiBuffer;
	pxTraceEventBuffer->uiSlack = 0u;
	pxTraceEventBuffer->uiNextHead = 0u;
	pxTraceEventBuffer->uiTimerWraparounds = 0u;

	(void)xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_EVENT_BUFFER);

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
	uint32_t uiFreeSize = 0u;

	/* Get size of event we are freeing */
	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceEventGetSize(((void*)&(pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiTail])), &uiFreeSize) == TRC_SUCCESS); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/

	pxTraceEventBuffer->uiFree += uiFreeSize;

	/* Update tail to point to the new last event */
	pxTraceEventBuffer->uiTail = (pxTraceEventBuffer->uiTail + uiFreeSize) % pxTraceEventBuffer->uiSize;

	return TRC_SUCCESS;
}

static traceResult prvTraceEventBufferAllocPop(TraceEventBuffer_t *pxTraceEventBuffer)
{
	uint32_t uiFreeSize = 0u;

	/* Check if tail is in, or at the start of the slack area. We do not want to call
	 * a free when in the slack area since it would read garbage data and free would
	 * become undefined.
	 */
	if (pxTraceEventBuffer->uiTail >= (pxTraceEventBuffer->uiSize - pxTraceEventBuffer->uiSlack))
	{
		/* Tail was in the slack area, wrap back to the start of the buffer. */
		pxTraceEventBuffer->uiTail = 0u;
	}
	else
	{
		/* Get size of event we are freeing (this should never fail) */
		TRC_ASSERT_ALWAYS_EVALUATE(xTraceEventGetSize(((void*)&(pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiTail])), &uiFreeSize) == TRC_SUCCESS); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/

		/* Update tail to point to the new last event */
		pxTraceEventBuffer->uiTail = (pxTraceEventBuffer->uiTail + uiFreeSize) % pxTraceEventBuffer->uiSize;
	}

	return TRC_SUCCESS;
}

traceResult xTraceEventBufferAlloc(TraceEventBuffer_t *pxTraceEventBuffer, uint32_t uiSize, void **ppvData)
{
	uint32_t uiFreeSpace;
	uint32_t uiHead;
	uint32_t uiTail;
	uint32_t uiBufferSize;

	/* This should never fail */
	TRC_ASSERT(pxTraceEventBuffer != (void*)0);
	
	/* This should never fail */
	TRC_ASSERT(ppvData != (void*)0);

	uiBufferSize = pxTraceEventBuffer->uiSize;
	
	TRC_ASSERT(uiBufferSize != 0u);

	/* Check if the data size is larger than the buffer */
	/* This should never fail */
	TRC_ASSERT(uiSize <= uiBufferSize);

	/* Handle overwrite buffer allocation, since this kind of allocation modifies
	 * both head and tail it should only be used for internal buffers without any
	 * flushing calls (Streaming Ringbuffer)
	 */
	if (pxTraceEventBuffer->uiOptions == TRC_EVENT_BUFFER_OPTION_OVERWRITE)
	{
		if (pxTraceEventBuffer->uiHead >= pxTraceEventBuffer->uiTail)
		{
			/* Do we have enough space to directly allocate from the buffer? */
			if ((uiBufferSize - pxTraceEventBuffer->uiHead) > uiSize)
			{
				*ppvData = &pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiHead]; /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/
				pxTraceEventBuffer->uiNextHead = (pxTraceEventBuffer->uiHead  + uiSize) % uiBufferSize;
			}
			/* There wasn't enough space for a direct alloc, handle freeing up
			 * space and wrapping. */
			else
			{
				/* Free space until there is enough space for a contiguous
				 * allocation */
				do
				{
					(void)prvTraceEventBufferAllocPop(pxTraceEventBuffer);
					uiFreeSpace = pxTraceEventBuffer->uiTail - sizeof(uint32_t);
				} while (uiFreeSpace < uiSize);

				/* Calculate slack from the wrapping */
				pxTraceEventBuffer->uiSlack = uiBufferSize - pxTraceEventBuffer->uiHead;

				/* Wrap head */
				pxTraceEventBuffer->uiHead = 0u;

				/* Allocate data */
				*ppvData = pxTraceEventBuffer->puiBuffer;

				pxTraceEventBuffer->uiNextHead = (pxTraceEventBuffer->uiHead  + uiSize) % uiBufferSize;
			}
		}
		else
		{
			uiFreeSpace = pxTraceEventBuffer->uiTail - pxTraceEventBuffer->uiHead - sizeof(uint32_t);

			/* Check if we have to free space */
			if (uiFreeSpace < uiSize)
			{
				/* Check if this is a wrapping alloc */
				if ((pxTraceEventBuffer->uiSize - pxTraceEventBuffer->uiHead) < uiSize)
				{
					/* To avoid uiHead and uiTail from becoming the same we want to
					 * pop any events that would make uiTail equal uiHead before
					 * wrapping the head. */
					do
					{
						(void)prvTraceEventBufferAllocPop(pxTraceEventBuffer);
					} while (pxTraceEventBuffer->uiTail == 0u);

					pxTraceEventBuffer->uiSlack = pxTraceEventBuffer->uiSize - pxTraceEventBuffer->uiHead;
					pxTraceEventBuffer->uiHead = 0u;
				}
				
				do
				{
					(void)prvTraceEventBufferAllocPop(pxTraceEventBuffer);
					uiFreeSpace = pxTraceEventBuffer->uiTail - pxTraceEventBuffer->uiHead - sizeof(uint32_t);
				} while (uiFreeSpace < uiSize);

				if (pxTraceEventBuffer->uiTail == 0u)
				{
					*ppvData = &pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiHead]; /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/
				}
			}

			/* Alloc data */
			*ppvData = &pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiHead]; /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/

			pxTraceEventBuffer->uiNextHead = (pxTraceEventBuffer->uiHead + uiSize);
		}
	}
	else
	{
		/* Since a consumer could potentially update tail (free) during the procedure
		 * we have to save it here to avoid problems with it changing during this call.
		 */
		uiHead = pxTraceEventBuffer->uiHead;
		uiTail = pxTraceEventBuffer->uiTail;

		if (uiHead >= uiTail)
		{
			uiFreeSpace = (uiBufferSize - uiHead - sizeof(uint32_t)) + uiTail;

			if (uiFreeSpace < uiSize)
			{
				*ppvData = 0;

				return TRC_FAIL;
			}

			/* Copy data */
			if ((uiBufferSize - uiHead) > uiSize)
			{
				*ppvData = &pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiHead]; /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/

				pxTraceEventBuffer->uiNextHead = (uiHead + uiSize) % uiBufferSize;
			}
			else
			{
				uiFreeSpace = uiTail;

				if (uiFreeSpace < uiSize)
				{
					*ppvData = 0;

					return TRC_FAIL;
				}

				/* Calculate slack */
				pxTraceEventBuffer->uiSlack = uiBufferSize - uiHead;

				*ppvData = pxTraceEventBuffer->puiBuffer;

				pxTraceEventBuffer->uiNextHead = (uiHead + pxTraceEventBuffer->uiSlack + uiSize) % uiBufferSize;
			}
		}
		else
		{
			uiFreeSpace = uiTail - uiHead - sizeof(uint32_t);

			if (uiFreeSpace < uiSize)
			{
				*ppvData = 0;

				return TRC_FAIL;
			}

			/* Alloc data */
			*ppvData = &pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiHead]; /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/

			pxTraceEventBuffer->uiNextHead = (uiHead + uiSize);
		}
	}

	return TRC_SUCCESS;
}

traceResult xTraceEventBufferAllocCommit(TraceEventBuffer_t *pxTraceEventBuffer, const void *pvData, uint32_t uiSize, int32_t *piBytesWritten)
{
	(void)pvData;

	/* This should never fail */
	TRC_ASSERT_ALWAYS_EVALUATE(xTraceTimestampGetWraparounds(&pxTraceEventBuffer->uiTimerWraparounds) == TRC_SUCCESS);

	/* Advance head location */
	pxTraceEventBuffer->uiHead = pxTraceEventBuffer->uiNextHead;

	/* Update bytes written */
	*piBytesWritten = (int32_t)uiSize;

	return TRC_SUCCESS;
}

traceResult xTraceEventBufferPush(TraceEventBuffer_t *pxTraceEventBuffer, void *pvData, uint32_t uiSize, int32_t *piBytesWritten)
{
	uint32_t uiBufferSize;
	uint32_t uiHead;
	uint32_t uiTail;
	uint32_t uiFreeSpace;
	
	/* This should never fail */
	TRC_ASSERT(pxTraceEventBuffer != (void*)0);
	
	/* This should never fail */
	TRC_ASSERT(pvData != (void*)0);
	
	uiBufferSize = pxTraceEventBuffer->uiSize;
	
	TRC_ASSERT(uiBufferSize != 0u);

	/* Check if the data size is larger than the buffer */
	/* This should never fail */
	TRC_ASSERT(uiSize <= uiBufferSize);

	/* Check byte alignment */
	/* This should never fail */
	TRC_ASSERT((uiSize % 4u) == 0u);

	/* Ensure bytes written start at 0 */
	/* This should never fail */
	TRC_ASSERT(piBytesWritten != (void*)0);

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
			uiHead = pxTraceEventBuffer->uiHead;

			/* If there isn't enough space in the buffer pop events until there is */
			while (pxTraceEventBuffer->uiFree < uiSize)
			{
				(void)prvTraceEventBufferPop(pxTraceEventBuffer);
			}

			/* Copy data */
			if ((uiBufferSize - uiHead) > uiSize)
			{
				TRC_MEMCPY(&pxTraceEventBuffer->puiBuffer[uiHead], pvData, uiSize); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/
			}
			else
			{
				TRC_MEMCPY(&pxTraceEventBuffer->puiBuffer[uiHead], pvData, (uiBufferSize - uiHead)); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/
				TRC_MEMCPY(pxTraceEventBuffer->puiBuffer, (void*)(&((uint8_t*)pvData)[(uiBufferSize - uiHead)]), (uiSize - (uiBufferSize - uiHead))); /*cstat !MISRAC2012-Rule-11.5 Suppress pointer checks*/ /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/
			}

			pxTraceEventBuffer->uiFree -= uiSize;

			pxTraceEventBuffer->uiHead = (uiHead + uiSize) % uiBufferSize;

			*piBytesWritten = (int32_t)uiSize;
			break;
		case TRC_EVENT_BUFFER_OPTION_SKIP:
			/* Since a consumer could potentially update tail (free) during the procedure
			 * we have to save it here to avoid problems with the push algorithm.
			 */
			uiHead = pxTraceEventBuffer->uiHead;
			uiTail = pxTraceEventBuffer->uiTail;

			if (uiHead >= uiTail)
			{
				uiFreeSpace = (uiBufferSize - uiHead - sizeof(uint32_t)) + uiTail;

				if (uiFreeSpace < uiSize)
				{
					*piBytesWritten = 0;

					return TRC_SUCCESS;
				}

				/* Copy data */
				if ((uiBufferSize - uiHead) > uiSize)
				{
					TRC_MEMCPY(&pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiHead], pvData, uiSize); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/
				}
				else
				{
					TRC_MEMCPY(&pxTraceEventBuffer->puiBuffer[uiHead], pvData, (uiBufferSize - uiHead)); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/
					TRC_MEMCPY(pxTraceEventBuffer->puiBuffer, (void*)(&((uint8_t*)pvData)[(uiBufferSize - uiHead)]), (uiSize - (uiBufferSize - uiHead)));  /*cstat !MISRAC2012-Rule-11.5 Suppress pointer checks*/ /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/
				}

				pxTraceEventBuffer->uiHead = (uiHead + uiSize) % uiBufferSize;
			}
			else
			{
				uiFreeSpace = uiTail - uiHead - sizeof(uint32_t);

				if (uiFreeSpace < uiSize)
				{
					*piBytesWritten = 0;

					return TRC_SUCCESS;
				}

				/* Copy data */
				TRC_MEMCPY(&pxTraceEventBuffer->puiBuffer[pxTraceEventBuffer->uiHead], pvData, uiSize); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/

				pxTraceEventBuffer->uiHead = (uiHead + uiSize);
			}

			*piBytesWritten = (int32_t)uiSize;
			break;
		default:
			return TRC_FAIL;
	}

	return TRC_SUCCESS;
}

traceResult xTraceEventBufferTransferAll(TraceEventBuffer_t* pxTraceEventBuffer, int32_t* piBytesWritten)
{
	int32_t iBytesWritten = 0;
	int32_t iSumBytesWritten = 0;
	uint32_t uiHead;
	uint32_t uiTail;
	uint32_t uiSlack;

	/* This should never fail */
	TRC_ASSERT(pxTraceEventBuffer != (void*)0);

	/* This should never fail */
	TRC_ASSERT(piBytesWritten != (void*)0);

	uiHead = pxTraceEventBuffer->uiHead;
	uiTail = pxTraceEventBuffer->uiTail;
	uiSlack = pxTraceEventBuffer->uiSlack;

	/* Check if core event buffer is empty */
	if (uiHead == uiTail)
	{
		/* Make sure this value is set in case it was passed uninitialized. */
		*piBytesWritten = 0;

		return TRC_SUCCESS;
	}

	/* Check if we can do a direct write or if we have to handle wrapping */
	if (uiHead > uiTail)
	{
		/* No wrapping */
		(void)xTraceStreamPortWriteData(&pxTraceEventBuffer->puiBuffer[uiTail], (uiHead - uiTail), &iBytesWritten); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/
	}
	else
	{
		/* Wrapping */

		/* Try to write: tail -> end of buffer */
		(void)xTraceStreamPortWriteData(&pxTraceEventBuffer->puiBuffer[uiTail], (pxTraceEventBuffer->uiSize - uiTail - uiSlack), &iBytesWritten); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/

		/* Did we manage to write all bytes? */
		if ((uint32_t)iBytesWritten == (pxTraceEventBuffer->uiSize - uiTail - uiSlack))
		{
			/* uiTail is moved to start of buffer */
			pxTraceEventBuffer->uiTail = 0u;

			iSumBytesWritten = iBytesWritten;

			/* We zero this here in case it does not get zeroed by the streamport. This isn't really a problem with our
			 * streamports, but there has been cases with custom streamport forgetting to set this to 0 if there is no
			 * data to write. */
			iBytesWritten = 0;

			/* Try to write: start of buffer -> head */
			(void)xTraceStreamPortWriteData(&pxTraceEventBuffer->puiBuffer[0], uiHead, &iBytesWritten); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/
		}
	}
	
	/* Move tail */
	pxTraceEventBuffer->uiTail += (uint32_t)iBytesWritten;
	
	iSumBytesWritten += iBytesWritten;

	*piBytesWritten = iSumBytesWritten;

	return TRC_SUCCESS;
}

traceResult xTraceEventBufferTransferChunk(TraceEventBuffer_t* pxTraceEventBuffer, uint32_t uiChunkSize, int32_t* piBytesWritten)
{
	int32_t iBytesWritten = 0;
	uint32_t uiHead;
	uint32_t uiTail;
	uint32_t uiSlack;
	uint32_t uiBytesToWrite;

	/* This should never fail */
	TRC_ASSERT(pxTraceEventBuffer != (void*)0);

	/* This should never fail */
	TRC_ASSERT(piBytesWritten != (void*)0);

	uiHead = pxTraceEventBuffer->uiHead;
	uiTail = pxTraceEventBuffer->uiTail;
	uiSlack = pxTraceEventBuffer->uiSlack;

	/* Check if core event buffer is empty */
	if (uiHead == uiTail)
	{
		/* Make sure this value is set in case it was passed uninitialized. */
		*piBytesWritten = 0;

		return TRC_SUCCESS;
	}

	/* Check if we can do a direct write or if we have to handle wrapping */
	if (uiHead > uiTail)
	{
		uiBytesToWrite = uiHead - uiTail;
		if (uiBytesToWrite > uiChunkSize)
		{
			uiBytesToWrite = uiChunkSize;
		}

		(void)xTraceStreamPortWriteData(&pxTraceEventBuffer->puiBuffer[uiTail], uiBytesToWrite, &iBytesWritten); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/

		pxTraceEventBuffer->uiTail += (uint32_t)iBytesWritten;
	}
	else
	{
		uiBytesToWrite = pxTraceEventBuffer->uiSize - uiTail - uiSlack;
		if (uiBytesToWrite > uiChunkSize)
		{
			uiBytesToWrite = uiChunkSize;
		}

		(void)xTraceStreamPortWriteData(&pxTraceEventBuffer->puiBuffer[uiTail], uiBytesToWrite, &iBytesWritten); /*cstat !MISRAC2004-17.4_b We need to access a specific part of the buffer*/

		/* Check if we managed to write until the end or not, if we didn't we
		 * add the number of bytes written. If we managed to write the last
		 * segment, reset tail to 0. */
		if ((uiTail + (uint32_t)iBytesWritten) == (pxTraceEventBuffer->uiSize - uiSlack))
		{
			pxTraceEventBuffer->uiTail = 0u;
		}
		else
		{
			pxTraceEventBuffer->uiTail += (uint32_t)iBytesWritten;
		}
	}

	*piBytesWritten = iBytesWritten;

	return TRC_SUCCESS;
}

traceResult xTraceEventBufferClear(TraceEventBuffer_t* pxTraceEventBuffer)
{
	/* This should never fail */
	TRC_ASSERT(pxTraceEventBuffer != (void*)0);

	pxTraceEventBuffer->uiHead = 0u;
	pxTraceEventBuffer->uiTail = 0u;
	pxTraceEventBuffer->uiFree = pxTraceEventBuffer->uiSize;
	pxTraceEventBuffer->uiSlack = 0u;
	pxTraceEventBuffer->uiNextHead = 0u;

	return TRC_SUCCESS;
}

#endif
