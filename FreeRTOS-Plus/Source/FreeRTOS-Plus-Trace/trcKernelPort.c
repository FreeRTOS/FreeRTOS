/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The FreeRTOS specific parts of the trace recorder
 */

#include <FreeRTOS.h>
#include <trcRecorder.h>

#if (!defined(TRC_USE_TRACEALYZER_RECORDER) && configUSE_TRACE_FACILITY == 1)

#error Trace Recorder: You need to include trcRecorder.h at the end of your FreeRTOSConfig.h!

#endif

#if (defined(TRC_USE_TRACEALYZER_RECORDER) && TRC_USE_TRACEALYZER_RECORDER == 1)

#ifndef TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS

/* TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS is missing in trcConfig.h. */
#error "TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS must be defined in trcConfig.h."

#endif

#ifndef TRC_CFG_INCLUDE_TIMER_EVENTS

/* TRC_CFG_INCLUDE_TIMER_EVENTS is missing in trcConfig.h. */
#error "TRC_CFG_INCLUDE_TIMER_EVENTS must be defined in trcConfig.h."

#endif

#ifndef TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS

/* TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS is missing in trcConfig.h. */
#error "TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS must be defined in trcConfig.h."

#endif

#ifndef TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS

/* TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS is missing in trcConfig.h. Define this as 1 if using FreeRTOS v10 or later and like to trace stream buffer or message buffer events, otherwise 0. */
#error "TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS must be defined in trcConfig.h."

#endif

#if (configUSE_TICKLESS_IDLE != 0 && (TRC_HWTC_TYPE == TRC_OS_TIMER_INCR || TRC_HWTC_TYPE == TRC_OS_TIMER_DECR))
/* 	
	The below error message is to alert you on the following issue:
	
	The hardware port selected in trcConfig.h uses the operating system timer for the 
	timestamping, i.e., the periodic interrupt timer that drives the OS tick interrupt.
			
	When using "tickless idle" mode, the recorder needs an independent time source in
	order to correctly record the durations of the idle times. Otherwise, the trace may appear
	to have a different length than in reality, and the reported CPU load is also affected.
	
	You may override this warning by defining the TRC_CFG_ACKNOWLEDGE_TICKLESS_IDLE_WARNING
	macro in your trcConfig.h file. But then the time scale may be incorrect during
	tickless idle periods.
	
	To get this correct, override the default timestamping by setting TRC_CFG_HARDWARE_PORT
	in trcConfig.h to TRC_HARDWARE_PORT_APPLICATION_DEFINED and define the HWTC macros
	accordingly, using a free running counter or an independent periodic interrupt timer.
	See trcHardwarePort.h for details.
			
	For ARM Cortex-M3, M4 and M7 MCUs this is not an issue, since the recorder uses the 
	DWT cycle counter for timestamping in these cases.		
*/

#ifndef TRC_CFG_ACKNOWLEDGE_TICKLESS_IDLE_WARNING
#error Trace Recorder: This timestamping mode is not recommended with Tickless Idle.
#endif

#endif
	
#include <task.h>
#include <queue.h>

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) || (defined(TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1) && (TRC_CFG_SCHEDULING_ONLY == 0))

#if defined(configSUPPORT_STATIC_ALLOCATION) && (configSUPPORT_STATIC_ALLOCATION == 1)

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0)

static StackType_t stackTzCtrl[TRC_CFG_CTRL_TASK_STACK_SIZE];
static StaticTask_t tcbTzCtrl;

#else

#error "configSUPPORT_STATIC_ALLOCATION not supported before FreeRTOS v9"

#endif

#endif

/* The TzCtrl task - receives commands from Tracealyzer (start/stop) */
static portTASK_FUNCTION(TzCtrl, pvParameters);

#endif

#if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)

/* If the project does not include the FreeRTOS timers, TRC_CFG_INCLUDE_TIMER_EVENTS must be set to 0 */
#include <timers.h>

#endif

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)

/* If the project does not include the FreeRTOS event groups, TRC_CFG_INCLUDE_TIMER_EVENTS must be set to 0 */
#include <event_groups.h>

#endif

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

/* If the project does not include the FreeRTOS stream buffers, TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS must be set to 0 */
#include <stream_buffer.h>

#endif

#if (TRC_CFG_ACKNOWLEDGE_QUEUE_SET_SEND != TRC_ACKNOWLEDGED) && (TRC_CFG_FREERTOS_VERSION == TRC_FREERTOS_VERSION_10_3_0 || TRC_CFG_FREERTOS_VERSION == TRC_FREERTOS_VERSION_10_3_1) && (configUSE_QUEUE_SETS == 1)

#error "When using FreeRTOS v10.3.0 or v10.3.1, please make sure that the trace point in prvNotifyQueueSetContainer() in queue.c is renamed from traceQUEUE_SEND to traceQUEUE_SET_SEND in order to tell them apart from other traceQUEUE_SEND trace points. Then set TRC_CFG_ACKNOWLEDGE_QUEUE_SET_SEND in trcConfig.h to TRC_ACKNOWLEDGED to get rid of this error."

#endif

#if defined(TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1) && (TRC_CFG_SCHEDULING_ONLY == 0)

traceResult xTraceKernelPortGetUnusedStack(void* pvTask, TraceUnsignedBaseType_t* puxUnusedStack)
{
	*puxUnusedStack = uxTaskGetStackHighWaterMark(pvTask);

	return TRC_SUCCESS;
}

#endif

traceResult xTraceKernelPortDelay(uint32_t uiTicks)
{
	vTaskDelay(uiTicks);

	return TRC_SUCCESS;
}

unsigned char xTraceKernelPortIsSchedulerSuspended(void)
{
	/* Assumed to be available in FreeRTOS. According to the FreeRTOS docs,
	INCLUDE_xTaskGetSchedulerState or configUSE_TIMERS must be set to 1 in
	FreeRTOSConfig.h for this function to be available. */

	return xTaskGetSchedulerState() == taskSCHEDULER_SUSPENDED;
}

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

typedef struct TraceKernelPortData
{
	TraceHeapHandle_t xSystemHeapHandle;
	TraceKernelPortTaskHandle_t xTzCtrlHandle;
} TraceKernelPortData_t;

static TraceKernelPortData_t* pxKernelPortData;

#define TRC_PORT_MALLOC(size) pvPortMalloc(size)

traceResult xTraceKernelPortInitialize(TraceKernelPortDataBuffer_t* pxBuffer)
{
	TRC_ASSERT_EQUAL_SIZE(TraceKernelPortDataBuffer_t, TraceKernelPortData_t);
	
	if (pxBuffer == 0)
	{
		return TRC_FAIL;
	}
	
	pxKernelPortData = (TraceKernelPortData_t*)pxBuffer;

	pxKernelPortData->xSystemHeapHandle = 0;
	pxKernelPortData->xTzCtrlHandle = 0;
	
	return TRC_SUCCESS;
}

traceResult xTraceKernelPortEnable(void)
{
	HeapStats_t xHeapStats;
	void* pvAlloc;
	
	if (pxKernelPortData->xSystemHeapHandle == 0)
	{
		/* Some magic to make sure the heap has been initialized! */
		pvAlloc = pvPortMalloc(1);
		if (pvAlloc != 0)
		{
			vPortFree(pvAlloc);
		}

		vPortGetHeapStats(&xHeapStats);
		xTraceHeapCreate("System Heap", configTOTAL_HEAP_SIZE - xHeapStats.xAvailableHeapSpaceInBytes, configTOTAL_HEAP_SIZE - xHeapStats.xMinimumEverFreeBytesRemaining, configTOTAL_HEAP_SIZE, &pxKernelPortData->xSystemHeapHandle);
	}
	
	if (pxKernelPortData->xTzCtrlHandle == 0)
	{
		/* Creates the TzCtrl task - receives trace commands (start, stop, ...) */
#if defined(configSUPPORT_STATIC_ALLOCATION) && (configSUPPORT_STATIC_ALLOCATION == 1)
		pxKernelPortData->xTzCtrlHandle = xTaskCreateStatic(TzCtrl, STRING_CAST("TzCtrl"), TRC_CFG_CTRL_TASK_STACK_SIZE, 0, TRC_CFG_CTRL_TASK_PRIORITY, stackTzCtrl, &tcbTzCtrl);
#else
		xTaskCreate(TzCtrl, STRING_CAST("TzCtrl"), TRC_CFG_CTRL_TASK_STACK_SIZE, 0, TRC_CFG_CTRL_TASK_PRIORITY, &pxKernelPortData->xTzCtrlHandle);
#endif

		if (pxKernelPortData->xTzCtrlHandle == 0)
		{
			xTraceError(TRC_ERROR_TZCTRLTASK_NOT_CREATED);

			return TRC_FAIL;
		}
	}
	
	return TRC_SUCCESS;
}

static portTASK_FUNCTION(TzCtrl, pvParameters)
{
	(void)pvParameters;

	while (1)
	{
		xTraceTzCtrl();

		vTaskDelay(TRC_CFG_CTRL_TASK_DELAY);
	}
}

#if (TRC_CFG_SCHEDULING_ONLY == 0)

void vTraceSetQueueName(void* pvQueue, const char* szName)
{
	xTraceObjectSetNameWithoutHandle(pvQueue, szName);
}

void vTraceSetSemaphoreName(void* pvSemaphore, const char* szName)
{
	xTraceObjectSetNameWithoutHandle(pvSemaphore, szName);
}

void vTraceSetMutexName(void* pvMutex, const char* szName)
{
	xTraceObjectSetNameWithoutHandle(pvMutex, szName);
}

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)

void vTraceSetEventGroupName(void* pvEventGroup, const char* szName)
{
	xTraceObjectSetNameWithoutHandle(pvEventGroup, szName);
}

#endif

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

void vTraceSetStreamBufferName(void* pvStreamBuffer, const char* szName)
{
	xTraceObjectSetNameWithoutHandle(pvStreamBuffer, szName);
}

void vTraceSetMessageBufferName(void* pvMessageBuffer, const char* szName)
{
	xTraceObjectSetNameWithoutHandle(pvMessageBuffer, szName);
}

#endif

#endif

TraceHeapHandle_t xTraceKernelPortGetSystemHeapHandle(void)
{
	return pxKernelPortData->xSystemHeapHandle;
}

#endif

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT)

uint32_t prvTraceGetQueueNumber(void* handle);

#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_8_X_X)

extern unsigned char ucQueueGetQueueNumber(xQueueHandle pxQueue);
extern void vQueueSetQueueNumber(xQueueHandle pxQueue, unsigned char ucQueueNumber);
extern unsigned char ucQueueGetQueueType(xQueueHandle pxQueue);

uint32_t prvTraceGetQueueNumber(void* handle)
{
	return (uint32_t)ucQueueGetQueueNumber(handle);
}

#else

uint32_t prvTraceGetQueueNumber(void* handle)
{
	return (uint32_t)uxQueueGetQueueNumber(handle);
}

#endif

uint8_t prvTraceGetQueueType(void* pvQueue)
{
	// This is either declared in header file in FreeRTOS 8 and later, or as extern above
	return ucQueueGetQueueType(pvQueue);
}

/* Tasks */
uint16_t prvTraceGetTaskNumberLow16(void* pvTask)
{
	return TRACE_GET_LOW16(uxTaskGetTaskNumber(pvTask));
}

uint16_t prvTraceGetTaskNumberHigh16(void* pvTask)
{
	return TRACE_GET_HIGH16(uxTaskGetTaskNumber(pvTask));
}

void prvTraceSetTaskNumberLow16(void* pvTask, uint16_t uiValue)
{
	vTaskSetTaskNumber(pvTask, TRACE_SET_LOW16(uxTaskGetTaskNumber(pvTask), uiValue));
}

void prvTraceSetTaskNumberHigh16(void* pvTask, uint16_t uiValue)
{
	vTaskSetTaskNumber(pvTask, TRACE_SET_HIGH16(uxTaskGetTaskNumber(pvTask), uiValue));
}

uint16_t prvTraceGetQueueNumberLow16(void* pvQueue)
{
	return TRACE_GET_LOW16(prvTraceGetQueueNumber(pvQueue));
}

uint16_t prvTraceGetQueueNumberHigh16(void* pvQueue)
{
	return TRACE_GET_HIGH16(prvTraceGetQueueNumber(pvQueue));
}

void prvTraceSetQueueNumberLow16(void* pvQueue, uint16_t uiValue)
{
	vQueueSetQueueNumber(pvQueue, TRACE_SET_LOW16(prvTraceGetQueueNumber(pvQueue), uiValue));
}

void prvTraceSetQueueNumberHigh16(void* pvQueue, uint16_t uiValue)
{
	vQueueSetQueueNumber(pvQueue, TRACE_SET_HIGH16(prvTraceGetQueueNumber(pvQueue), uiValue));
}

#if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

uint16_t prvTraceGetTimerNumberLow16(void* pvTimer)
{
	return TRACE_GET_LOW16(uxTimerGetTimerNumber(pvTimer));
}

uint16_t prvTraceGetTimerNumberHigh16(void* pvTimer)
{
	return TRACE_GET_HIGH16(uxTimerGetTimerNumber(pvTimer));
}

void prvTraceSetTimerNumberLow16(void* pvTimer, uint16_t uiValue)
{
	vTimerSetTimerNumber(pvTimer, TRACE_SET_LOW16(uxTimerGetTimerNumber(pvTimer), uiValue));
}

void prvTraceSetTimerNumberHigh16(void* pvTimer, uint16_t uiValue)
{
	vTimerSetTimerNumber(pvTimer, TRACE_SET_HIGH16(uxTimerGetTimerNumber(pvTimer), uiValue));
}

#endif

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

uint16_t prvTraceGetEventGroupNumberLow16(void* pvEventGroup)
{
	return TRACE_GET_LOW16(uxEventGroupGetNumber(pvEventGroup));
}

uint16_t prvTraceGetEventGroupNumberHigh16(void* pvEventGroup)
{
	return TRACE_GET_HIGH16(uxEventGroupGetNumber(pvEventGroup));
}

void prvTraceSetEventGroupNumberLow16(void* pvEventGroup, uint16_t uiValue)
{
	vEventGroupSetNumber(pvEventGroup, TRACE_SET_LOW16(uxEventGroupGetNumber(pvEventGroup), uiValue));
}

void prvTraceSetEventGroupNumberHigh16(void* pvEventGroup, uint16_t uiValue)
{
	vEventGroupSetNumber(pvEventGroup, TRACE_SET_HIGH16(uxEventGroupGetNumber(pvEventGroup), uiValue));
}

#endif

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

uint16_t prvTraceGetStreamBufferNumberLow16(void* pvStreamBuffer)
{
	return TRACE_GET_LOW16(uxStreamBufferGetStreamBufferNumber(pvStreamBuffer));
}

uint16_t prvTraceGetStreamBufferNumberHigh16(void* pvStreamBuffer)
{
	return TRACE_GET_HIGH16(uxStreamBufferGetStreamBufferNumber(pvStreamBuffer));
}

void prvTraceSetStreamBufferNumberLow16(void* pvStreamBuffer, uint16_t uiValue)
{
	vStreamBufferSetStreamBufferNumber(pvStreamBuffer, TRACE_SET_LOW16(uxStreamBufferGetStreamBufferNumber(pvStreamBuffer), uiValue));
}

void prvTraceSetStreamBufferNumberHigh16(void* pvStreamBuffer, uint16_t uiValue)
{
	vStreamBufferSetStreamBufferNumber(pvStreamBuffer, TRACE_SET_HIGH16(uxStreamBufferGetStreamBufferNumber(pvStreamBuffer), uiValue));
}

#endif

static TraceKernelPortTaskHandle_t xTzCtrlHandle = 0; /* TzCtrl task TCB */

/* Internal flag to tell the context of tracePEND_FUNC_CALL_FROM_ISR */
int uiInEventGroupSetBitsFromISR = 0;

/**
 * @internal Class reference table
 */
traceObjectClass TraceQueueClassTable[5] = {
	TRACE_CLASS_QUEUE,
	TRACE_CLASS_MUTEX,
	TRACE_CLASS_SEMAPHORE,
	TRACE_CLASS_SEMAPHORE,
	TRACE_CLASS_MUTEX
};

#if (TRC_CFG_SCHEDULING_ONLY == 0)

void vTraceSetQueueName(void* pvQueue, const char* szName)
{
	prvTraceSetObjectName(TRACE_CLASS_QUEUE, TRACE_GET_OBJECT_NUMBER(QUEUE, pvQueue), szName);
}

void vTraceSetSemaphoreName(void* pvSemaphore, const char* szName)
{
	prvTraceSetObjectName(TRACE_CLASS_SEMAPHORE, TRACE_GET_OBJECT_NUMBER(QUEUE, pvSemaphore), szName);
}

void vTraceSetMutexName(void* pvMutex, const char* szName)
{
	prvTraceSetObjectName(TRACE_CLASS_MUTEX, TRACE_GET_OBJECT_NUMBER(QUEUE, pvMutex), szName);
}

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)

void vTraceSetEventGroupName(void* pvEventGroup, const char* szName)
{
	prvTraceSetObjectName(TRACE_CLASS_EVENTGROUP, TRACE_GET_OBJECT_NUMBER(EVENTGROUP, pvEventGroup), szName);
}

#endif

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

void vTraceSetStreamBufferName(void* pvStreamBuffer, const char* szName)
{
	prvTraceSetObjectName(TRACE_CLASS_STREAMBUFFER, TRACE_GET_OBJECT_NUMBER(STREAMBUFFER, pvStreamBuffer), szName);
}

void vTraceSetMessageBufferName(void* pvStreamBuffer, const char* szName)
{
	prvTraceSetObjectName(TRACE_CLASS_MESSAGEBUFFER, TRACE_GET_OBJECT_NUMBER(STREAMBUFFER, pvStreamBuffer), szName);
}

#endif

#endif

void* prvTraceGetCurrentTaskHandle()
{
	return xTaskGetCurrentTaskHandle();
}

traceResult xTraceKernelPortInitialize(TraceKernelPortDataBuffer_t* pxBuffer)
{
	(void)pxBuffer;

	return TRC_SUCCESS;
}

traceResult xTraceKernelPortEnable(void)
{
#if defined(TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1) && (TRC_CFG_SCHEDULING_ONLY == 0)

	if (xTzCtrlHandle == 0)
	{
#if defined(configSUPPORT_STATIC_ALLOCATION) && (configSUPPORT_STATIC_ALLOCATION == 1)

		xTzCtrlHandle = xTaskCreateStatic(TzCtrl, STRING_CAST("TzCtrl"), TRC_CFG_CTRL_TASK_STACK_SIZE, 0, TRC_CFG_CTRL_TASK_PRIORITY, stackTzCtrl, &tcbTzCtrl);

#else

		xTaskCreate(TzCtrl, STRING_CAST("TzCtrl"), TRC_CFG_CTRL_TASK_STACK_SIZE, 0, TRC_CFG_CTRL_TASK_PRIORITY, &xTzCtrlHandle);

#endif
	}

#else

	(void)xTzCtrlHandle;

#endif

	return TRC_SUCCESS;
}

#if defined(TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1) && (TRC_CFG_SCHEDULING_ONLY == 0)

static portTASK_FUNCTION(TzCtrl, pvParameters)
{
	(void)pvParameters;

	while (1)
	{
		if (xTraceIsRecorderEnabled())
		{
			prvReportStackUsage();
		}

		vTaskDelay(TRC_CFG_CTRL_TASK_DELAY);
	}
}

#endif

traceResult xTraceKernelPortInitObjectPropertyTable()
{
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectClasses = TRACE_NCLASSES;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[0] = TRC_CFG_NQUEUE;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[1] = TRC_CFG_NSEMAPHORE;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[2] = TRC_CFG_NMUTEX;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[3] = TRC_CFG_NTASK;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[4] = TRC_CFG_NISR;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[5] = TRC_CFG_NTIMER;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[6] = TRC_CFG_NEVENTGROUP;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[7] = TRC_CFG_NSTREAMBUFFER;
	RecorderDataPtr->ObjectPropertyTable.NumberOfObjectsPerClass[8] = TRC_CFG_NMESSAGEBUFFER;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[0] = TRC_CFG_NAME_LEN_QUEUE;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[1] = TRC_CFG_NAME_LEN_SEMAPHORE;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[2] = TRC_CFG_NAME_LEN_MUTEX;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[3] = TRC_CFG_NAME_LEN_TASK;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[4] = TRC_CFG_NAME_LEN_ISR;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[5] = TRC_CFG_NAME_LEN_TIMER;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[6] = TRC_CFG_NAME_LEN_EVENTGROUP;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[7] = TRC_CFG_NAME_LEN_STREAMBUFFER;
	RecorderDataPtr->ObjectPropertyTable.NameLengthPerClass[8] = TRC_CFG_NAME_LEN_MESSAGEBUFFER;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[0] = PropertyTableSizeQueue;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[1] = PropertyTableSizeSemaphore;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[2] = PropertyTableSizeMutex;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[3] = PropertyTableSizeTask;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[4] = PropertyTableSizeISR;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[5] = PropertyTableSizeTimer;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[6] = PropertyTableSizeEventGroup;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[7] = PropertyTableSizeStreamBuffer;
	RecorderDataPtr->ObjectPropertyTable.TotalPropertyBytesPerClass[8] = PropertyTableSizeMessageBuffer;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[0] = StartIndexQueue;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[1] = StartIndexSemaphore;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[2] = StartIndexMutex;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[3] = StartIndexTask;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[4] = StartIndexISR;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[5] = StartIndexTimer;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[6] = StartIndexEventGroup;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[7] = StartIndexStreamBuffer;
	RecorderDataPtr->ObjectPropertyTable.StartIndexOfClass[8] = StartIndexMessageBuffer;
	RecorderDataPtr->ObjectPropertyTable.ObjectPropertyTableSizeInBytes = TRACE_OBJECT_TABLE_SIZE;

	return TRC_SUCCESS;
}

traceResult xTraceKernelPortInitObjectHandleStack()
{
	uint32_t i = 0;

	objectHandleStacks.indexOfNextAvailableHandle[0] = objectHandleStacks.lowestIndexOfClass[0] = 0;
	objectHandleStacks.indexOfNextAvailableHandle[1] = objectHandleStacks.lowestIndexOfClass[1] = (TRC_CFG_NQUEUE);
	objectHandleStacks.indexOfNextAvailableHandle[2] = objectHandleStacks.lowestIndexOfClass[2] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE);
	objectHandleStacks.indexOfNextAvailableHandle[3] = objectHandleStacks.lowestIndexOfClass[3] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX);
	objectHandleStacks.indexOfNextAvailableHandle[4] = objectHandleStacks.lowestIndexOfClass[4] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK);
	objectHandleStacks.indexOfNextAvailableHandle[5] = objectHandleStacks.lowestIndexOfClass[5] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR);
	objectHandleStacks.indexOfNextAvailableHandle[6] = objectHandleStacks.lowestIndexOfClass[6] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER);
	objectHandleStacks.indexOfNextAvailableHandle[7] = objectHandleStacks.lowestIndexOfClass[7] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP);
	objectHandleStacks.indexOfNextAvailableHandle[8] = objectHandleStacks.lowestIndexOfClass[8] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP) + (TRC_CFG_NSTREAMBUFFER);

	objectHandleStacks.highestIndexOfClass[0] = (TRC_CFG_NQUEUE) - 1;
	objectHandleStacks.highestIndexOfClass[1] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) - 1;
	objectHandleStacks.highestIndexOfClass[2] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) - 1;
	objectHandleStacks.highestIndexOfClass[3] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) - 1;
	objectHandleStacks.highestIndexOfClass[4] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) - 1;
	objectHandleStacks.highestIndexOfClass[5] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) - 1;
	objectHandleStacks.highestIndexOfClass[6] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP) - 1;
	objectHandleStacks.highestIndexOfClass[7] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP) + (TRC_CFG_NSTREAMBUFFER) - 1;
	objectHandleStacks.highestIndexOfClass[8] = (TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP) + (TRC_CFG_NSTREAMBUFFER) + (TRC_CFG_NMESSAGEBUFFER) - 1;

	for (i = 0; i < TRACE_NCLASSES; i++)
	{
		objectHandleStacks.handleCountWaterMarksOfClass[i] = 0;
	}

	for (i = 0; i < TRACE_KERNEL_OBJECT_COUNT; i++)
	{
		objectHandleStacks.objectHandles[i] = 0;
	}

	return TRC_SUCCESS;
}

const char* pszTraceGetErrorNotEnoughHandles(traceObjectClass objectclass)
{
	switch(objectclass)
	{
	case TRACE_CLASS_TASK:
		return "Not enough TASK handles - increase TRC_CFG_NTASK in trcSnapshotConfig.h";
	case TRACE_CLASS_ISR:
		return "Not enough ISR handles - increase TRC_CFG_NISR in trcSnapshotConfig.h";
	case TRACE_CLASS_SEMAPHORE:
		return "Not enough SEMAPHORE handles - increase TRC_CFG_NSEMAPHORE in trcSnapshotConfig.h";
	case TRACE_CLASS_MUTEX:
		return "Not enough MUTEX handles - increase TRC_CFG_NMUTEX in trcSnapshotConfig.h";
	case TRACE_CLASS_QUEUE:
		return "Not enough QUEUE handles - increase TRC_CFG_NQUEUE in trcSnapshotConfig.h";
	case TRACE_CLASS_TIMER:
		return "Not enough TIMER handles - increase TRC_CFG_NTIMER in trcSnapshotConfig.h";
	case TRACE_CLASS_EVENTGROUP:
		return "Not enough EVENTGROUP handles - increase TRC_CFG_NEVENTGROUP in trcSnapshotConfig.h";
	case TRACE_CLASS_STREAMBUFFER:
		return "Not enough STREAMBUFFER handles - increase TRC_CFG_NSTREAMBUFFER in trcSnapshotConfig.h";
	case TRACE_CLASS_MESSAGEBUFFER:
		return "Not enough MESSAGEBUFFER handles - increase TRC_CFG_NMESSAGEBUFFER in trcSnapshotConfig.h";
	default:
		return "pszTraceGetErrorHandles: Invalid objectclass!";
	}
}

#endif

#endif
