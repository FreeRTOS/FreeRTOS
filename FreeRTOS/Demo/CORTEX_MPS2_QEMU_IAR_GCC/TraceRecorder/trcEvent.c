/*
* Percepio Trace Recorder for Tracealyzer v4.10.2
* Copyright 2023 Percepio AB
* www.percepio.com
*
* SPDX-License-Identifier: Apache-2.0
*
* The implementation for events.
*/

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1) && (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

#include <string.h>

/**
 * @internal Macro helper for setting trace event parameter count.
 */
#define TRC_EVENT_SET_PARAM_COUNT(id, n) ((uint16_t)(((uint16_t)(id)) | ((((uint16_t)(n)) & 0xF) << 12)))

/**
 * @internal Macro helper for getting trace event parameter count.
 */
#define TRC_EVENT_GET_PARAM_COUNT(id) (((id) >> 12u) & 0xFU)

#if (TRC_CFG_CORE_COUNT > 1)
#define TRC_EVENT_SET_EVENT_COUNT(c)  ((uint16_t)(((TRC_CFG_GET_CURRENT_CORE() & 0xF) << 12) | ((uint16_t)(c) & 0xFFF)))
#else
#define TRC_EVENT_SET_EVENT_COUNT(c) ((uint16_t)(c))
#endif

/**
 * @internal Macro optimization for getting trace event size.
 */
#define TRC_EVENT_GET_SIZE(pvAddress, puiSize) (*(uint32_t*)(puiSize) = sizeof(TraceEvent0_t) + (TRC_EVENT_GET_PARAM_COUNT(((TraceEvent0_t*)(pvAddress))->EventID)) * sizeof(TraceBaseType_t), TRC_SUCCESS)

/**
 * @internal Macro helper for setting base event data.
 */
#define SET_BASE_EVENT_DATA(pxEvent, eventId, paramCount, eventCount) \
	( \
		(pxEvent)->EventID = TRC_EVENT_SET_PARAM_COUNT(eventId, paramCount), \
		(pxEvent)->EventCount = TRC_EVENT_SET_EVENT_COUNT(eventCount), \
		xTraceTimestampGet(&(pxEvent)->TS) \
	)

#define TRACE_EVENT_BEGIN_OFFLINE(size) 														\
	TRACE_ENTER_CRITICAL_SECTION();              										\
	pxTraceEventDataTable->coreEventData[TRC_CFG_GET_CURRENT_CORE()].eventCounter++; 	\
	if (xTraceStreamPortAllocate((uint32_t)(size), (void**)&pxEventData) == TRC_FAIL) /*cstat !MISRAC2004-11.4 !MISRAC2012-Rule-11.3 Suppress pointer checks*/ \
	{                                            										\
		TRACE_EXIT_CRITICAL_SECTION();              									\
		return TRC_FAIL; 																\
	} 																					\
	SET_BASE_EVENT_DATA(pxEventData, uiEventCode, ((size) - sizeof(TraceEvent0_t)) / sizeof(TraceUnsignedBaseType_t), pxTraceEventDataTable->coreEventData[TRC_CFG_GET_CURRENT_CORE()].eventCounter); /*cstat !MISRAC2012-Rule-11.5 Suppress pointer checks*/

#define TRACE_EVENT_BEGIN(size) 														\
	/* We need to check this */                  										\
	if (!xTraceIsRecorderEnabled())              										\
	{ 																					\
		return TRC_FAIL;                            									\
	} 																					\
	TRACE_EVENT_BEGIN_OFFLINE(size)


#define TRACE_EVENT_END(size) 															\
	(void)xTraceStreamPortCommit(pxEventData, (uint32_t)(size), &iBytesCommitted); 					\
	TRACE_EXIT_CRITICAL_SECTION(); 														\
	/* We need to use iBytesCommitted for the above call but do not use the value, 		\
	 * remove potential warnings */ 													\
	(void)iBytesCommitted;

#define TRACE_EVENT_ADD_1(__p1)									\
	pxEventData->uxParams[0] = __p1;

#define TRACE_EVENT_ADD_2(__p1, __p2)							\
	TRACE_EVENT_ADD_1(__p1)										\
	pxEventData->uxParams[1] = __p2;

#define TRACE_EVENT_ADD_3(__p1, __p2, __p3)						\
	TRACE_EVENT_ADD_2(__p1, __p2)								\
	pxEventData->uxParams[2] = __p3;

#define TRACE_EVENT_ADD_4(__p1, __p2, __p3, __p4)				\
	TRACE_EVENT_ADD_3(__p1, __p2, __p3)							\
	pxEventData->uxParams[3] = __p4;

#define TRACE_EVENT_ADD_5(__p1, __p2, __p3, __p4, __p5)			\
	TRACE_EVENT_ADD_4(__p1, __p2, __p3, __p4)					\
	pxEventData->uxParams[4] = __p5;

#define TRACE_EVENT_ADD_6(__p1, __p2, __p3, __p4, __p5, __p6)	\
	TRACE_EVENT_ADD_5(__p1, __p2, __p3, __p4, __p5)				\
	pxEventData->uxParams[5] = __p6;

#define TRACE_EVENT_ADD_0_DATA(__pvData, __uxSize) 											\
	memcpy(&((uint8_t*)pxEventData)[sizeof(TraceEvent0_t)], __pvData, __uxSize);

#define TRACE_EVENT_ADD_1_DATA(__p1, __pvData, __uxSize)									\
	TRACE_EVENT_ADD_1(__p1)																	\
	memcpy(&((uint8_t*)pxEventData)[sizeof(TraceEvent1_t)], __pvData, __uxSize);

#define TRACE_EVENT_ADD_2_DATA(__p1, __p2, __pvData, __uxSize)								\
	TRACE_EVENT_ADD_2(__p1, __p2)															\
	memcpy(&((uint8_t*)pxEventData)[sizeof(TraceEvent2_t)], __pvData, __uxSize);

#define TRACE_EVENT_ADD_3_DATA(__p1, __p2, __p3, __pvData, __uxSize)						\
	TRACE_EVENT_ADD_3(__p1, __p2, __p3)														\
	memcpy(&((uint8_t*)pxEventData)[sizeof(TraceEvent3_t)], __pvData, __uxSize);

#define TRACE_EVENT_ADD_4_DATA(__p1, __p2, __p3, __p4, __pvData, __uxSize)					\
	TRACE_EVENT_ADD_4(__p1, __p2, __p3, __p4)												\
	memcpy(&((uint8_t*)pxEventData)[sizeof(TraceEvent4_t)], __pvData, __uxSize);

#define TRACE_EVENT_ADD_5_DATA(__p1, __p2, __p3, __p4, __p5, __pvData, __uxSize)			\
	TRACE_EVENT_ADD_5(__p1, __p2, __p3, __p4, __p5)											\
	memcpy(&((uint8_t*)pxEventData)[sizeof(TraceEvent5_t)], __pvData, __uxSize);

#define TRACE_EVENT_ADD_6_DATA(__p1, __p2, __p3, __p4, __p5, __p6, __pvData, __uxSize)		\
	TRACE_EVENT_ADD_6(__p1, __p2, __p3, __p4, __p5, __p6)									\
	memcpy(&((uint8_t*)pxEventData)[sizeof(TraceEvent6_t)], __pvData, __uxSize);

TraceEventDataTable_t *pxTraceEventDataTable TRC_CFG_RECORDER_DATA_ATTRIBUTE;

traceResult xTraceEventInitialize(TraceEventDataTable_t* pxBuffer)
{
	uint32_t i;

	/* This should never fail */
	TRC_ASSERT(pxBuffer != (void*)0);

	pxTraceEventDataTable = pxBuffer;

	for (i = 0u; i < (uint32_t)(TRC_CFG_CORE_COUNT); i++)
	{
		pxTraceEventDataTable->coreEventData[i].eventCounter = 0u;
	}

	xTraceSetComponentInitialized(TRC_RECORDER_COMPONENT_EVENT);

	return TRC_SUCCESS;
}

traceResult xTraceEventCreate0(uint32_t uiEventCode)
{
	TraceEvent0_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_EVENT_BEGIN(sizeof(TraceEvent0_t));
	TRACE_EVENT_END(sizeof(TraceEvent0_t));

	return TRC_SUCCESS;
}

traceResult xTraceEventCreate1(uint32_t uiEventCode, TraceUnsignedBaseType_t uxParam1)
{
	TraceEvent1_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_EVENT_BEGIN(sizeof(TraceEvent1_t));

	TRACE_EVENT_ADD_1(uxParam1);

	TRACE_EVENT_END(sizeof(TraceEvent1_t));

	return TRC_SUCCESS;
}

traceResult xTraceEventCreate2(uint32_t uiEventCode, TraceUnsignedBaseType_t uxParam1, TraceUnsignedBaseType_t uxParam2)
{
	TraceEvent2_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_EVENT_BEGIN(sizeof(TraceEvent2_t));

	TRACE_EVENT_ADD_2(uxParam1, uxParam2);

	TRACE_EVENT_END(sizeof(TraceEvent2_t));

	return TRC_SUCCESS;
}

traceResult xTraceEventCreate3(uint32_t uiEventCode, TraceUnsignedBaseType_t uxParam1, TraceUnsignedBaseType_t uxParam2, TraceUnsignedBaseType_t uxParam3)
{
	TraceEvent3_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_EVENT_BEGIN(sizeof(TraceEvent3_t));

	TRACE_EVENT_ADD_3(uxParam1, uxParam2, uxParam3);

	TRACE_EVENT_END(sizeof(TraceEvent3_t));

	return TRC_SUCCESS;
}

traceResult xTraceEventCreate4(uint32_t uiEventCode, TraceUnsignedBaseType_t uxParam1, TraceUnsignedBaseType_t uxParam2, TraceUnsignedBaseType_t uxParam3, TraceUnsignedBaseType_t uxParam4)
{
	TraceEvent4_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_EVENT_BEGIN(sizeof(TraceEvent4_t));

	TRACE_EVENT_ADD_4(uxParam1, uxParam2, uxParam3, uxParam4);

	TRACE_EVENT_END(sizeof(TraceEvent4_t));

	return TRC_SUCCESS;
}

traceResult xTraceEventCreate5(uint32_t uiEventCode, TraceUnsignedBaseType_t uxParam1, TraceUnsignedBaseType_t uxParam2, TraceUnsignedBaseType_t uxParam3, TraceUnsignedBaseType_t uxParam4, TraceUnsignedBaseType_t uxParam5)
{
	TraceEvent5_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_EVENT_BEGIN(sizeof(TraceEvent5_t));

	TRACE_EVENT_ADD_5(uxParam1, uxParam2, uxParam3, uxParam4, uxParam5);

	TRACE_EVENT_END(sizeof(TraceEvent5_t));

	return TRC_SUCCESS;
}

traceResult xTraceEventCreate6(uint32_t uiEventCode, TraceUnsignedBaseType_t uxParam1, TraceUnsignedBaseType_t uxParam2, TraceUnsignedBaseType_t uxParam3, TraceUnsignedBaseType_t uxParam4, TraceUnsignedBaseType_t uxParam5, TraceUnsignedBaseType_t uxParam6)
{
	TraceEvent6_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	TRACE_EVENT_BEGIN(sizeof(TraceEvent6_t));

	TRACE_EVENT_ADD_6(uxParam1, uxParam2, uxParam3, uxParam4, uxParam5, uxParam6);

	TRACE_EVENT_END(sizeof(TraceEvent6_t));

	return TRC_SUCCESS;
}

traceResult xTraceEventCreateRawBlocking(const void* pxSource, uint32_t ulSize)
{
	int32_t iBytesCommitted = 0;
	void* pxBuffer = (void*)0;

	TRACE_ALLOC_CRITICAL_SECTION();

	ulSize = TRC_ALIGN_CEIL(ulSize, sizeof(TraceUnsignedBaseType_t));

	TRACE_ENTER_CRITICAL_SECTION();

	pxTraceEventDataTable->coreEventData[TRC_CFG_GET_CURRENT_CORE()].eventCounter++;
	while (xTraceStreamPortAllocate(ulSize, (void**)&pxBuffer) == TRC_FAIL) {}

	memcpy(pxBuffer, pxSource, ulSize);
	while (xTraceStreamPortCommit(pxBuffer, ulSize, &iBytesCommitted) == TRC_FAIL) {}
	(void)iBytesCommitted;

	TRACE_EXIT_CRITICAL_SECTION();

	return TRC_SUCCESS;
}

traceResult xTraceEventCreateDataOffline0(uint32_t uiEventCode, const TraceUnsignedBaseType_t* const puxData, TraceUnsignedBaseType_t uxSize)
{
	TraceEvent0_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* Align payload size and truncate in case it is too big */
	uxSize = TRC_ALIGN_CEIL(uxSize, sizeof(TraceUnsignedBaseType_t));
	if (sizeof(TraceEvent0_t) + uxSize > TRC_MAX_BLOB_SIZE)
	{
		uxSize = TRC_MAX_BLOB_SIZE - sizeof(TraceEvent0_t);
	}

	TRACE_EVENT_BEGIN_OFFLINE(sizeof(TraceEvent0_t) + uxSize);

	TRACE_EVENT_ADD_0_DATA(puxData, uxSize);

	TRACE_EVENT_END(sizeof(TraceEvent0_t) + uxSize);

	return TRC_SUCCESS;
}

traceResult xTraceEventCreateData0(uint32_t uiEventCode, const TraceUnsignedBaseType_t* const puxData, TraceUnsignedBaseType_t uxSize)
{
	TraceEvent0_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* Align payload size and truncate in case it is too big */
	uxSize = TRC_ALIGN_CEIL(uxSize, sizeof(TraceUnsignedBaseType_t));
	if (sizeof(TraceEvent0_t) + uxSize > TRC_MAX_BLOB_SIZE)
	{
		uxSize = TRC_MAX_BLOB_SIZE - sizeof(TraceEvent0_t);
	}

	TRACE_EVENT_BEGIN(sizeof(TraceEvent0_t) + uxSize);

	TRACE_EVENT_ADD_0_DATA(puxData, uxSize);

	TRACE_EVENT_END(sizeof(TraceEvent0_t) + uxSize);

	return TRC_SUCCESS;
}

traceResult xTraceEventCreateData1(
	uint32_t uiEventCode,
	TraceUnsignedBaseType_t uxParam1,
	const TraceUnsignedBaseType_t* const puxData,
	TraceUnsignedBaseType_t uxSize
)
{
	TraceEvent1_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* Align payload size and truncate in case it is too big */
	uxSize = TRC_ALIGN_CEIL(uxSize, sizeof(TraceUnsignedBaseType_t));
	if (sizeof(TraceEvent1_t) + uxSize > TRC_MAX_BLOB_SIZE)
	{
		uxSize = TRC_MAX_BLOB_SIZE - sizeof(TraceEvent1_t);
	}

	TRACE_EVENT_BEGIN(sizeof(TraceEvent1_t) + uxSize);

	TRACE_EVENT_ADD_1_DATA(uxParam1, puxData, uxSize);

	TRACE_EVENT_END(sizeof(TraceEvent1_t) + uxSize);

	return TRC_SUCCESS;
}

traceResult xTraceEventCreateData2(
	uint32_t uiEventCode,
	TraceUnsignedBaseType_t uxParam1,
	TraceUnsignedBaseType_t uxParam2,
	const TraceUnsignedBaseType_t* const puxData,
	TraceUnsignedBaseType_t uxSize
)
{
	TraceEvent2_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* Align payload size and truncate in case it is too big */
	uxSize = TRC_ALIGN_CEIL(uxSize, sizeof(TraceUnsignedBaseType_t));
	if (sizeof(TraceEvent2_t) + uxSize > TRC_MAX_BLOB_SIZE)
	{
		uxSize = TRC_MAX_BLOB_SIZE - sizeof(TraceEvent2_t);
	}

	TRACE_EVENT_BEGIN(sizeof(TraceEvent2_t) + uxSize);

	TRACE_EVENT_ADD_2_DATA(uxParam1, uxParam2, puxData, uxSize);

	TRACE_EVENT_END(sizeof(TraceEvent2_t) + uxSize);

	return TRC_SUCCESS;
}

traceResult xTraceEventCreateData3(
	uint32_t uiEventCode,
	TraceUnsignedBaseType_t uxParam1,
	TraceUnsignedBaseType_t uxParam2,
	TraceUnsignedBaseType_t uxParam3,
	const TraceUnsignedBaseType_t* const puxData,
	TraceUnsignedBaseType_t uxSize
)
{
	TraceEvent3_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* Align payload size and truncate in case it is too big */
	uxSize = TRC_ALIGN_CEIL(uxSize, sizeof(TraceUnsignedBaseType_t));
	if (sizeof(TraceEvent3_t) + uxSize > TRC_MAX_BLOB_SIZE)
	{
		uxSize = TRC_MAX_BLOB_SIZE - sizeof(TraceEvent3_t);
	}

	TRACE_EVENT_BEGIN(sizeof(TraceEvent3_t) + uxSize);

	TRACE_EVENT_ADD_3_DATA(uxParam1, uxParam2, uxParam3, puxData, uxSize);

	TRACE_EVENT_END(sizeof(TraceEvent3_t) + uxSize);

	return TRC_SUCCESS;
}

traceResult xTraceEventCreateData4(
	uint32_t uiEventCode,
	TraceUnsignedBaseType_t uxParam1,
	TraceUnsignedBaseType_t uxParam2,
	TraceUnsignedBaseType_t uxParam3,
	TraceUnsignedBaseType_t uxParam4,
	const TraceUnsignedBaseType_t* const puxData,
	TraceUnsignedBaseType_t uxSize
)
{
	TraceEvent4_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* Align payload size and truncate in case it is too big */
	uxSize = TRC_ALIGN_CEIL(uxSize, sizeof(TraceUnsignedBaseType_t));
	if (sizeof(TraceEvent4_t) + uxSize > TRC_MAX_BLOB_SIZE)
	{
		uxSize = TRC_MAX_BLOB_SIZE - sizeof(TraceEvent4_t);
	}

	TRACE_EVENT_BEGIN(sizeof(TraceEvent4_t) + uxSize);

	TRACE_EVENT_ADD_4_DATA(uxParam1, uxParam2, uxParam3, uxParam4, puxData, uxSize);

	TRACE_EVENT_END(sizeof(TraceEvent4_t) + uxSize);

	return TRC_SUCCESS;
}

traceResult xTraceEventCreateData5(
	uint32_t uiEventCode,
	TraceUnsignedBaseType_t uxParam1,
	TraceUnsignedBaseType_t uxParam2,
	TraceUnsignedBaseType_t uxParam3,
	TraceUnsignedBaseType_t uxParam4,
	TraceUnsignedBaseType_t uxParam5,
	const TraceUnsignedBaseType_t* const puxData,
	TraceUnsignedBaseType_t uxSize
)
{
	TraceEvent5_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* Align payload size and truncate in case it is too big */
	uxSize = TRC_ALIGN_CEIL(uxSize, sizeof(TraceUnsignedBaseType_t));
	if (sizeof(TraceEvent5_t) + uxSize > TRC_MAX_BLOB_SIZE)
	{
		uxSize = TRC_MAX_BLOB_SIZE - sizeof(TraceEvent5_t);
	}

	TRACE_EVENT_BEGIN(sizeof(TraceEvent5_t) + uxSize);

	TRACE_EVENT_ADD_5_DATA(uxParam1, uxParam2, uxParam3, uxParam4, uxParam5, puxData, uxSize);

	TRACE_EVENT_END(sizeof(TraceEvent5_t) + uxSize);

	return TRC_SUCCESS;
}

traceResult xTraceEventCreateData6(
	uint32_t uiEventCode,
	TraceUnsignedBaseType_t uxParam1,
	TraceUnsignedBaseType_t uxParam2,
	TraceUnsignedBaseType_t uxParam3,
	TraceUnsignedBaseType_t uxParam4,
	TraceUnsignedBaseType_t uxParam5,
	TraceUnsignedBaseType_t uxParam6,
	const TraceUnsignedBaseType_t* const puxData,
	TraceUnsignedBaseType_t uxSize
)
{
	TraceEvent6_t* pxEventData = (void*)0;
	int32_t iBytesCommitted = 0;

	TRACE_ALLOC_CRITICAL_SECTION();

	/* Align payload size and truncate in case it is too big */
	uxSize = TRC_ALIGN_CEIL(uxSize, sizeof(TraceUnsignedBaseType_t));
	if (sizeof(TraceEvent6_t) + uxSize > TRC_MAX_BLOB_SIZE)
	{
		uxSize = TRC_MAX_BLOB_SIZE - sizeof(TraceEvent6_t);
	}

	TRACE_EVENT_BEGIN(sizeof(TraceEvent6_t) + uxSize);

	TRACE_EVENT_ADD_6_DATA(uxParam1, uxParam2, uxParam3, uxParam4, uxParam5, uxParam6, puxData, uxSize);

	TRACE_EVENT_END(sizeof(TraceEvent6_t) + uxSize);

	return TRC_SUCCESS;
}

traceResult xTraceEventGetSize(const void* const pvAddress, uint32_t* puiSize)
{
	/* This should never fail */
	TRC_ASSERT(pvAddress != (void*)0);
	
	/* This should never fail */
	TRC_ASSERT(puiSize != (void*)0);

	/* This should never fail */
	TRC_ASSERT((sizeof(TraceEvent0_t) + ((uint32_t)(uint16_t)(TRC_EVENT_GET_PARAM_COUNT(((const TraceEvent0_t*)pvAddress)->EventID)) * sizeof(TraceUnsignedBaseType_t))) <= (uint32_t)(TRC_MAX_BLOB_SIZE)); /*cstat !MISRAC2012-Rule-11.5 Suppress pointer checks*/
	
	return TRC_EVENT_GET_SIZE(pvAddress, puiSize);
}

#endif
