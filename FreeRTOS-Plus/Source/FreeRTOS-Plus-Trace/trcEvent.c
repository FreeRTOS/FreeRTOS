/*
* Percepio Trace Recorder for Tracealyzer v4.6.0
* Copyright 2021 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for events.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#define VERIFY_EVENT_SIZE(i) \
	if ((i) > (TRC_MAX_BLOB_SIZE)) \
	{ \
		xTraceDiagnosticsSetIfHigher(TRC_DIAGNOSTICS_BLOB_MAX_BYTES_TRUNCATED, (TraceUnsignedBaseType_t)((i) - (TRC_MAX_BLOB_SIZE))); \
		(i) = TRC_MAX_BLOB_SIZE; \
	}

TraceEventDataTable_t *pxTraceEventDataTable;

int32_t DUMMY_iTraceBytesCommitted;

TRACE_ALLOC_CRITICAL_SECTION();

traceResult xTraceEventInitialize(TraceEventDataBuffer_t* pxBuffer)
{
	TraceCoreEventData_t* pxCoreEventData;
	uint32_t i, j;

	TRC_ASSERT_EQUAL_SIZE(TraceEventDataBuffer_t, TraceEventDataTable_t);

	/* This should never fail */
	TRC_ASSERT(pxBuffer != 0);

	pxTraceEventDataTable = (TraceEventDataTable_t*)pxBuffer;

	for (i = 0; i < TRC_CFG_CORE_COUNT; i++)
	{
		pxCoreEventData = &pxTraceEventDataTable->coreEventData[i];

		pxCoreEventData->eventCounter = 0;

		for (j = 0; j < (TRC_CFG_MAX_ISR_NESTING) + 1; j++)
		{
			RESET_EVENT_DATA(&pxCoreEventData->eventData[j]);
		}
	}

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_EVENT);

	return TRC_SUCCESS;
}

traceResult xTraceEventBeginRawOffline(uint32_t uiSize, TraceEventHandle_t* pxEventHandle)
{
	TraceEventData_t* pxEventData;
	int32_t ISR_nesting;

	/* We need to check this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT))
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT(pxEventHandle != 0);

	TRACE_ENTER_CRITICAL_SECTION();

	xTraceISRGetCurrentNesting(&ISR_nesting);

	/* We add 1 since xTraceISRGetCurrentNesting(...) returns -1 if no ISR is active */
	pxEventData = &pxTraceEventDataTable->coreEventData[TRC_CFG_GET_CURRENT_CORE()].eventData[ISR_nesting + 1];

	/* This should never fail */
	TRC_ASSERT_CUSTOM_ON_FAIL(pxEventData->pvBlob == 0, TRACE_EXIT_CRITICAL_SECTION(); return TRC_FAIL; );

	VERIFY_EVENT_SIZE(uiSize);

	pxEventData->size = ((uiSize + (sizeof(uint32_t) - 1)) / sizeof(uint32_t)) * sizeof(uint32_t);	/* 4-byte align */

	pxEventData->offset = 0;

	/* This can fail and we should handle it */
	if (xTraceStreamPortAllocate(pxEventData->size, &pxEventData->pvBlob) == TRC_FAIL)
	{
		TRACE_EXIT_CRITICAL_SECTION();
		return TRC_FAIL;
	}

	*pxEventHandle = (TraceEventHandle_t)pxEventData;

	return TRC_SUCCESS;
}

traceResult xTraceEventBeginRawOfflineBlocking(uint32_t uiSize, TraceEventHandle_t* pxEventHandle)
{
	TraceEventData_t* pxEventData;
	int32_t ISR_nesting;
	uint32_t uiAttempts = 0;

	/* We need to check this */
	if (!xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT))
	{
		return TRC_FAIL;
	}

	/* This should never fail */
	TRC_ASSERT(pxEventHandle != 0);

	TRACE_ENTER_CRITICAL_SECTION();

	xTraceGetCurrentISRNesting(&ISR_nesting);

	/* We add 1 since xTraceISRGetCurrentNesting(...) returns -1 if no ISR is active */
	pxEventData = &pxTraceEventDataTable->coreEventData[TRC_CFG_GET_CURRENT_CORE()].eventData[ISR_nesting + 1];

	/* This should never fail */
	TRC_ASSERT_CUSTOM_ON_FAIL(pxEventData->pvBlob == 0, TRACE_EXIT_CRITICAL_SECTION(); return TRC_FAIL; );

	VERIFY_EVENT_SIZE(uiSize);

	pxEventData->size = ((uiSize + (sizeof(uint32_t) - 1)) / sizeof(uint32_t)) * sizeof(uint32_t);	/* 4-byte align */

	pxEventData->offset = 0;

	/* This can fail and we should handle it */
	while (xTraceStreamPortAllocate(pxEventData->size, &pxEventData->pvBlob) != TRC_SUCCESS)
	{
		uiAttempts++;
	}

	*pxEventHandle = (TraceEventHandle_t)pxEventData;

	return TRC_SUCCESS;
}

traceResult xTraceEventEndOffline(TraceEventHandle_t xEventHandle)
{
	int32_t iBytesCommitted;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(((TraceEventData_t*)xEventHandle)->pvBlob != 0);

	xTraceStreamPortCommit(((TraceEventData_t*)xEventHandle)->pvBlob, ((TraceEventData_t*)xEventHandle)->size, &iBytesCommitted);

	RESET_EVENT_DATA((TraceEventData_t*)xEventHandle);

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

traceResult xTraceEventEndOfflineBlocking(TraceEventHandle_t xEventHandle)
{
	TraceEventData_t* pxEventData = (TraceEventData_t*)xEventHandle;
	int32_t iBytesCommitted;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(pxEventData != 0);

	while (pxEventData->size > 0)
	{
		iBytesCommitted = 0;
		xTraceStreamPortCommit(pxEventData->pvBlob, pxEventData->size, &iBytesCommitted);

		pxEventData->size -= iBytesCommitted;
		pxEventData->pvBlob = ((uint8_t*)pxEventData->pvBlob) + iBytesCommitted;
	}

	RESET_EVENT_DATA(pxEventData);

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

traceResult xTraceEventAddData(TraceEventHandle_t xEventHandle, void* pvData, uint32_t uiSize)
{
	uint32_t i;

	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(pvData != 0);

	/* This should never fail */
	TRC_ASSERT(((TraceEventData_t*)xEventHandle)->offset + uiSize <= ((TraceEventData_t*)xEventHandle)->size);

	for (i = 0; i < uiSize; i++)
	{
		TRC_EVENT_ADD_8(xEventHandle, ((uint8_t*)pvData)[i]);
	}

	return TRC_SUCCESS;
}

#if ((TRC_CFG_USE_TRACE_ASSERT) == 1)

traceResult xTraceEventGetSize(void *pvAddress, uint32_t* puiSize)
{
	/* This should never fail */
	TRC_ASSERT(pvAddress != 0);
	
	/* This should never fail */
	TRC_ASSERT(puiSize != 0);

	/* This should never fail */
	TRC_ASSERT((sizeof(TraceBaseEvent_t) + (TRC_EVENT_GET_PARAM_COUNT(((TraceBaseEvent_t*)pvAddress)->EventID)) * sizeof(uint32_t)) <= TRC_MAX_BLOB_SIZE);
	
	return TRC_EVENT_GET_SIZE(pvAddress, puiSize);
}

traceResult xTraceEventGetRawData(TraceEventHandle_t xEventHandle, uint32_t uiOffset, uint32_t uiSize, void** ppvData)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(ppvData != 0);

	/* This should never fail */
	TRC_ASSERT(uiOffset + uiSize <= ((TraceEventData_t*)xEventHandle)->size);

	return TRC_EVENT_GET_RAW_DATA(xEventHandle, uiOffset, uiSize, ppvData);
}

traceResult xTraceEventGetPayload(TraceEventHandle_t xEventHandle, uint32_t uiOffset, uint32_t uiSize, void** ppvData)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(ppvData != 0);

	/* This should never fail */
	TRC_ASSERT(uiOffset + uiSize <= ((TraceEventData_t*)xEventHandle)->size);

	return TRC_EVENT_GET_PAYLOAD(xEventHandle, uiOffset, uiSize, ppvData);
}

traceResult xTraceEventPayloadRemaining(TraceEventHandle_t xEventHandle, uint32_t* puiValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(puiValue != 0);

	/* This should never fail */
	TRC_ASSERT(((TraceEventData_t*)xEventHandle)->pvBlob != 0);

	return TRC_EVENT_PAYLOAD_REMAINING(xEventHandle, puiValue);
}

traceResult xTraceEventPayloadUsed(TraceEventHandle_t xEventHandle, uint32_t* puiValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(puiValue != 0);

	/* This should never fail */
	TRC_ASSERT(((TraceEventData_t*)xEventHandle)->pvBlob != 0);

	return TRC_EVENT_PAYLOAD_USED(xEventHandle, puiValue);
}

traceResult xTraceEventPayloadSize(TraceEventHandle_t xEventHandle, uint32_t* puiValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(puiValue != 0);

	/* This should never fail */
	TRC_ASSERT(((TraceEventData_t*)xEventHandle)->pvBlob != 0);

	return TRC_EVENT_PAYLOAD_SIZE(xEventHandle, puiValue);
}

traceResult xTraceEventAddPointer(TraceEventHandle_t xEventHandle, void* pvAddress)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(((TraceEventData_t*)xEventHandle)->offset + sizeof(void*) <= ((TraceEventData_t*)xEventHandle)->size);

	/* Make sure we are writing at void* aligned offset */
	/* This should never fail */
	TRC_ASSERT((((TraceEventData_t*)xEventHandle)->offset & (sizeof(void*) - 1)) == 0);

	return TRC_EVENT_ADD_POINTER(xEventHandle, pvAddress);
}

traceResult xTraceEventAddUnsignedBaseType(TraceEventHandle_t xEventHandle, TraceUnsignedBaseType_t uxValue)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(((TraceEventData_t*)xEventHandle)->offset + sizeof(TraceUnsignedBaseType_t) <= ((TraceEventData_t*)xEventHandle)->size);

	/* Make sure we are writing at TraceUnsignedBaseType_t aligned offset */
	/* This should never fail */
	TRC_ASSERT((((TraceEventData_t*)xEventHandle)->offset & (sizeof(TraceUnsignedBaseType_t) - 1)) == 0);

	return TRC_EVENT_ADD_UNSIGNED_BASE_TYPE(xEventHandle, uxValue);
}

traceResult xTraceEventAdd32(TraceEventHandle_t xEventHandle, uint32_t value)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(((TraceEventData_t*)xEventHandle)->offset + sizeof(uint32_t) <= ((TraceEventData_t*)xEventHandle)->size);

	/* Make sure we are writing at 32-bit aligned offset */
	/* This should never fail */
	TRC_ASSERT((((TraceEventData_t*)xEventHandle)->offset & 3) == 0);

	return TRC_EVENT_ADD_32(xEventHandle, value);
}

traceResult xTraceEventAdd16(TraceEventHandle_t xEventHandle, uint16_t value)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(((TraceEventData_t*)xEventHandle)->offset + sizeof(uint16_t) <= ((TraceEventData_t*)xEventHandle)->size);

	/* Make sure we are writing at 16-bit aligned offset */
	/* This should never fail */
	TRC_ASSERT((((TraceEventData_t*)xEventHandle)->offset & 1) == 0);

	return TRC_EVENT_ADD_16(xEventHandle, value);
}

traceResult xTraceEventAdd8(TraceEventHandle_t xEventHandle, uint8_t value)
{
	/* This should never fail */
	TRC_ASSERT(xTraceIsComponentInitialized(TRC_RECORDER_COMPONENT_EVENT));

	/* This should never fail */
	TRC_ASSERT(xEventHandle != 0);

	/* This should never fail */
	TRC_ASSERT(((TraceEventData_t*)xEventHandle)->offset + sizeof(uint8_t) <= ((TraceEventData_t*)xEventHandle)->size);

	return TRC_EVENT_ADD_8(xEventHandle, value);
}

#endif /* ((TRC_CFG_USE_TRACE_ASSERT) == 1) */

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
