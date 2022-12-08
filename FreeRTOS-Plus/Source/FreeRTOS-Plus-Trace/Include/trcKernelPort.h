/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * FreeRTOS specific definitions needed by the trace recorder
 */

#ifndef TRC_KERNEL_PORT_H
#define TRC_KERNEL_PORT_H

#include <trcDefines.h>
#include <FreeRTOS.h>	/* Defines configUSE_TRACE_FACILITY */

#ifdef __cplusplus
extern "C" {
#endif

#define TRC_USE_TRACEALYZER_RECORDER configUSE_TRACE_FACILITY

/* FreeRTOS version codes */
#define FREERTOS_VERSION_NOT_SET				0
#define TRC_FREERTOS_VERSION_7_3_X				1 /* v7.3 is earliest supported.*/
#define TRC_FREERTOS_VERSION_7_4_X				2
#define TRC_FREERTOS_VERSION_7_5_X				3
#define TRC_FREERTOS_VERSION_7_6_X				TRC_FREERTOS_VERSION_7_5_X
#define TRC_FREERTOS_VERSION_8_X_X				4
#define TRC_FREERTOS_VERSION_9_0_0				5
#define TRC_FREERTOS_VERSION_9_0_1				6
#define TRC_FREERTOS_VERSION_9_0_2				7
#define TRC_FREERTOS_VERSION_10_0_0				8
#define TRC_FREERTOS_VERSION_10_0_1				TRC_FREERTOS_VERSION_10_0_0
#define TRC_FREERTOS_VERSION_10_1_0				TRC_FREERTOS_VERSION_10_0_0
#define TRC_FREERTOS_VERSION_10_1_1				TRC_FREERTOS_VERSION_10_0_0
#define TRC_FREERTOS_VERSION_10_2_0				TRC_FREERTOS_VERSION_10_0_0
#define TRC_FREERTOS_VERSION_10_2_1				TRC_FREERTOS_VERSION_10_0_0
#define TRC_FREERTOS_VERSION_10_3_0				9
#define TRC_FREERTOS_VERSION_10_3_1				TRC_FREERTOS_VERSION_10_3_0
#define TRC_FREERTOS_VERSION_10_4_0				10
#define TRC_FREERTOS_VERSION_10_4_1				TRC_FREERTOS_VERSION_10_4_0

/* Legacy FreeRTOS version codes for backwards compatibility with old trace configurations */
#define TRC_FREERTOS_VERSION_7_3				TRC_FREERTOS_VERSION_7_3_X
#define TRC_FREERTOS_VERSION_7_4				TRC_FREERTOS_VERSION_7_4_X
#define TRC_FREERTOS_VERSION_7_5_OR_7_6			TRC_FREERTOS_VERSION_7_5_X
#define TRC_FREERTOS_VERSION_8_X				TRC_FREERTOS_VERSION_8_X_X

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
#define prvGetStreamBufferType(x) ((( StreamBuffer_t * )(x) )->ucFlags & sbFLAGS_IS_MESSAGE_BUFFER)
#else
#define prvGetStreamBufferType(x) 0
#endif

/* Added mainly for our internal testing. This makes it easier to create test applications that 
   runs on multiple FreeRTOS versions. */
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_8_X_X)
	/* FreeRTOS v7.x */	
	#define STRING_CAST(x) ( (signed char*) x )
	#define TickType portTickType
	#define TaskType xTaskHandle
#else
	/* FreeRTOS v8.0 and later */
	#define STRING_CAST(x) x
	#define TraceKernelPortTickType_t TickType_t
	#define TraceKernelPortTaskHandle_t TaskHandle_t
#endif

#if (defined(TRC_USE_TRACEALYZER_RECORDER)) && (TRC_USE_TRACEALYZER_RECORDER == 1)

#define TRC_PLATFORM_CFG "FreeRTOS"
#define TRC_PLATFORM_CFG_MAJOR 1
#define TRC_PLATFORM_CFG_MINOR 0
#define TRC_PLATFORM_CFG_PATCH 0

#if defined(TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1) && (TRC_CFG_SCHEDULING_ONLY == 0)

/* Required for stack monitoring */
#undef INCLUDE_uxTaskGetStackHighWaterMark
#define INCLUDE_uxTaskGetStackHighWaterMark 1

#endif

/* INCLUDE_xTaskGetCurrentTaskHandle must be set to 1 for tracing to work properly */
#undef INCLUDE_xTaskGetCurrentTaskHandle
#define INCLUDE_xTaskGetCurrentTaskHandle 1

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)
#include <trcHeap.h>

#define TRC_KERNEL_PORT_BUFFER_SIZE (sizeof(TraceHeapHandle_t) + sizeof(void*))
#elif (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT)
#define TRC_KERNEL_PORT_BUFFER_SIZE (sizeof(TraceUnsignedBaseType_t))
#endif

/**
 * @internal The kernel port data buffer
 */
typedef struct TraceKernelPortDataBuffer
{
	uint8_t buffer[TRC_KERNEL_PORT_BUFFER_SIZE];
} TraceKernelPortDataBuffer_t;

/**
 * @internal Initializes the kernel port
 * 
 * @param[in] pxBuffer Kernel port data buffer
 *
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceKernelPortInitialize(TraceKernelPortDataBuffer_t* pxBuffer);

/**
 * @internal Enables the kernel port
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceKernelPortEnable(void);

/**
 * @internal Calls on FreeRTOS vTaskDelay(...)
 *
 * @param[in] uiTicks Tick count to delay
 * 
 * @retval TRC_FAIL Failure
 * @retval TRC_SUCCESS Success
 */
traceResult xTraceKernelPortDelay(uint32_t uiTicks);

/**
 * @internal Query if FreeRTOS scheduler is suspended
 *
 * @retval 1 Scheduler suspended
 * @retval 0 Scheduler not suspended
 */
unsigned char xTraceKernelPortIsSchedulerSuspended(void);

/**
 * @brief Kernel specific way to properly allocate critical sections
 */
#define TRC_KERNEL_PORT_ALLOC_CRITICAL_SECTION() 

/**
 * @brief Kernel specific way to properly allocate critical sections
 */
#define TRC_KERNEL_PORT_ENTER_CRITICAL_SECTION() portENTER_CRITICAL()

/**
 * @brief Kernel specific way to properly allocate critical sections
 */
#define TRC_KERNEL_PORT_EXIT_CRITICAL_SECTION() portEXIT_CRITICAL()

/**
* @brief Kernel specific way to set interrupt mask
*/
#define TRC_KERNEL_PORT_SET_INTERRUPT_MASK() ((TraceBaseType_t)portSET_INTERRUPT_MASK_FROM_ISR())

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)

/**
 * @brief Kernel specific way to clear interrupt mask
 */
#define TRC_KERNEL_PORT_CLEAR_INTERRUPT_MASK(xMask) portCLEAR_INTERRUPT_MASK_FROM_ISR((UBaseType_t)(xMask))

#else

/**
 * @brief Kernel specific way to clear interrupt mask
 */
#define TRC_KERNEL_PORT_CLEAR_INTERRUPT_MASK(xMask) portCLEAR_INTERRUPT_MASK_FROM_ISR((unsigned portBASE_TYPE)xMask)
#endif

#if (TRC_CFG_SCHEDULING_ONLY == 0)

/**
 * @brief Set the queue name
 *
 * @param[in] pvQueue Queue pointer
 * @param[in] szName Queue name
 */
void vTraceSetQueueName(void* pvQueue, const char* szName);

/**
 * @brief Set the semaphore name
 *
 * @param[in] pvSemaphore Semaphore pointer
 * @param[in] szName Semaphore name
 */
void vTraceSetSemaphoreName(void* pvSemaphore, const char* szName);

/**
 * @brief Set the mutex name
 *
 * @param[in] pvMutex Mutex pointer
 * @param[in] szName Mutex name
 */
void vTraceSetMutexName(void* pvMutex, const char* szName);

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1)

/**
 * @brief Set the event group name
 *
 * @param[in] pvEventGroup Event group pointer
 * @param[in] szName Event group name
 */
void vTraceSetEventGroupName(void* pvEventGroup, const char* szName);

#else

/**
 * @brief Disabled by TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS
 */
#define vTraceSetEventGroupName(__pvEventGroup, __szName) ((void)(__pvEventGroup), (void)(__szName))

#endif

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1)

/**
 * @brief Set the stream buffer name
 *
 * @param[in] pvStreamBuffer Stream buffer pointer
 * @param[in] szName Stream buffer name
 */
void vTraceSetStreamBufferName(void* pvStreamBuffer, const char* szName);

/**
 * @brief Set the message buffer name
 *
 * @param[in] pvMessageBuffer Message buffer pointer
 * @param[in] szName Message buffer name
 */
void vTraceSetMessageBufferName(void* pvMessageBuffer, const char* szName);

#else

/**
 * @brief Disabled by TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS
 */
#define vTraceSetStreamBufferName(__pvStreamBuffer, __szName) ((void)(__pvStreamBuffer), (void)(__szName))

/**
 * @brief Disabled by TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS
 */
#define vTraceSetMessageBufferName(__pvMessageBuffer, __szName) ((void)(__pvMessageBuffer), (void)(__szName))

#endif

#if defined(TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1)

 /**
  * @internal Retrieves the unused stack for a task
  *
  * @param[in] pvTask Task pointer
  * @param[out] puxUnusedStack The unused stack
  *
  * @retval TRC_FAIL Failure
  * @retval TRC_SUCCESS Success
  */
traceResult xTraceKernelPortGetUnusedStack(void* pvTask, TraceUnsignedBaseType_t *puxUnusedStack);

#endif

#else

/**
 * @brief Disabled by TRC_CFG_SCHEDULING_ONLY
 */
#define vTraceSetQueueName(__pvQueue, __szName) ((void)(__pvQueue), (void)(__szName))

/**
 * @brief Disabled by TRC_CFG_SCHEDULING_ONLY
 */
#define vTraceSetSemaphoreName(__pvSemaphore, __szName) ((void)(__pvSemaphore), (void)(__szName))

/**
 * @brief Disabled by TRC_CFG_SCHEDULING_ONLY
 */
#define vTraceSetMutexName(__pvMutex, __szName) ((void)(__pvMutex), (void)(__szName))

/**
 * @brief Disabled by TRC_CFG_SCHEDULING_ONLY
 */
#define vTraceSetEventGroupName(__pvEventGroup, __szName) ((void)(__pvEventGroup), (void)(__szName))

/**
 * @brief Disabled by TRC_CFG_SCHEDULING_ONLY
 */
#define vTraceSetStreamBufferName(__pvStreamBuffer, __szName) ((void)(__pvStreamBuffer), (void)(__szName))

/**
 * @brief Disabled by TRC_CFG_SCHEDULING_ONLY
 */
#define vTraceSetMessageBufferName(__pvMessageBuffer, __szName) ((void)(__pvMessageBuffer), (void)(__szName))

/**
 * @brief Disabled by TRC_CFG_SCHEDULING_ONLY
 */
#define xTraceKernelPortGetUnusedStack(pvTask, puxUnusedStack) ((void)(pvTask), (void)(puxUnusedStack))

#endif

#if (((TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT) && (TRC_CFG_INCLUDE_ISR_TRACING == 1)) || (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING))

/* Required for ISR tracing and Streaming */
#undef INCLUDE_xTaskGetSchedulerState
#define INCLUDE_xTaskGetSchedulerState 1

#endif

/**
 * @internal Legacy ID used by Tracealyzer to identify FreeRTOS traces
 */
#define TRACE_KERNEL_VERSION 0x1AA1

/**
 * @internal Kernel specific tick rate frequency definition
 */
#define TRC_TICK_RATE_HZ configTICK_RATE_HZ /* Defined in "FreeRTOS.h" */

/**
 * @internal Kernel specific CPU clock frequency definition
 */
#define TRACE_CPU_CLOCK_HZ configCPU_CLOCK_HZ /* Defined in "FreeRTOSConfig.h" */

/**
 * @internal Kernel specific malloc definition
 */
#define TRACE_MALLOC(size) pvPortMalloc(size) 	

#if (defined(configUSE_TIMERS) && (configUSE_TIMERS == 1))

#undef INCLUDE_xTimerGetTimerDaemonTaskHandle
#define INCLUDE_xTimerGetTimerDaemonTaskHandle 1

#endif

#if (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_XMOS_XCOREAI)

#undef TRC_CFG_CORE_COUNT
#define TRC_CFG_CORE_COUNT configNUM_CORES

#undef TRC_CFG_GET_CURRENT_CORE
#define TRC_CFG_GET_CURRENT_CORE() rtos_core_id_get()

#endif

#if (TRC_CFG_FREERTOS_VERSION == TRC_FREERTOS_VERSION_9_0_1)

/**
 * @brief Fix for FreeRTOS v9.0.1 to correctly identify xQueuePeek events.
 *
 * In FreeRTOS v9.0.1, the below trace hooks are incorrectly used from three
 * different functions. This as the earlier function xQueueGenericReceive
 * has been replaced by xQueuePeek, xQueueSemaphoreTake and xQueueReceive.
 *
 * xQueueGenericReceive had a parameter "xJustPeeking", used by the trace hooks
 * to tell between xQueuePeek events and others. This is no longer present, so
 * we need another way to correctly identify peek events. Since all three
 * functions call the same trace macros, the context of these macro is unknown.
 *
 * We therefore check the __LINE__ macro inside of the trace macros. This gives
 * the line number of queue.c, where the macros are used. This can be used to
 * tell if the context is xQueuePeek or another function.
 * __LINE__ is a standard compiler feature since ancient times, so it should
 * work on all common compilers.
 *
 * This might seem as a quite brittle and unusual solution, but works in this
 * particular case and is only for FreeRTOS v9.0.1.
 * Future versions of FreeRTOS should not need this fix, as we have submitted
 * a correction of queue.c with individual trace macros for each function.
 */
#define isQueueReceiveHookActuallyPeek (__LINE__ > 1674) /* Half way between the closes trace points */

#elif (TRC_CFG_FREERTOS_VERSION <= TRC_FREERTOS_VERSION_9_0_0)

/**
 * @brief Is receive actually a peek
 */
#define isQueueReceiveHookActuallyPeek xJustPeeking

#elif (TRC_CFG_FREERTOS_VERSION > TRC_FREERTOS_VERSION_9_0_1)

/**
 * @brief Is never a peek for this FreeRTOS version
 */
#define isQueueReceiveHookActuallyPeek (__LINE__ < 0) /* instead of pdFALSE to fix a warning of "constant condition" */

#endif

/* Helpers needed to correctly expand names */
#define TZ__CAT2(a,b) a ## b
#define TZ__CAT(a,b) TZ__CAT2(a, b)

/*
 * The following xQueueGiveFromISR macro hacks make sure xQueueGiveFromISR also has a xCopyPosition parameter
 */

/* Expands name if this header is included... uxQueueType must be a macro that only exists in queue.c or whatever, and it must expand to nothing or to something that's valid in identifiers */
#define xQueueGiveFromISR(a,b) TZ__CAT(xQueueGiveFromISR__, uxQueueType) (a,b)

/* If in queue.c, the "uxQueueType" macro expands to "pcHead". queueSEND_TO_BACK is the value we need to send in */
#define xQueueGiveFromISR__pcHead(__a, __b) MyWrapper_xQueueGiveFromISR(__a, __b, const BaseType_t xCopyPosition); \
BaseType_t xQueueGiveFromISR(__a, __b) { return MyWrapper_xQueueGiveFromISR(xQueue, pxHigherPriorityTaskWoken, queueSEND_TO_BACK); } \
BaseType_t MyWrapper_xQueueGiveFromISR(__a, __b, const BaseType_t xCopyPosition)

/* If not in queue.c, "uxQueueType" isn't expanded */
#define xQueueGiveFromISR__uxQueueType(__a, __b) xQueueGiveFromISR(__a,__b)

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT)

/**
 * @internal Kernel specific way to get current task handle
 */
#define TRACE_GET_CURRENT_TASK() prvTraceGetCurrentTaskHandle()

extern uint16_t CurrentFilterMask;
extern uint16_t CurrentFilterGroup;

/**
 * @internal Get specific queue type
 *
 * @param[in] pvQueue Queue handle
 *
 * @returns uint8_t Queue type
 */
uint8_t prvTraceGetQueueType(void* pvQueue);

/**
 * @internal Retrieve lower 16-bit of task number
 *
 * @param[in] pvTask Task handle
 *
 * @returns uint16_t Lower 16-bit of task number
 */
uint16_t prvTraceGetTaskNumberLow16(void* pvTask);

/**
 * @internal Retrieve upper 16-bit of task number
 *
 * @param[in] pvTask Task handle
 *
 * @returns uint16_t Upper 16-bit of task number
 */
uint16_t prvTraceGetTaskNumberHigh16(void* pvTask);

/**
 * @internal Set lower 16-bit of task number
 *
 * @param[in] pvTask Task handle
 * @param[in] uiValue Value
 */
void prvTraceSetTaskNumberLow16(void* pvTask, uint16_t uiValue);

/**
 * @internal Set upper 16-bit of task number
 *
 * @param[in] pvTask Task handle
 * @param[in] uiValue Value
 */
void prvTraceSetTaskNumberHigh16(void* pvTask, uint16_t uiValue);

/**
 * @internal Retrieve lower 16-bit of queue number
 *
 * @param[in] pvQueue Queue handle
 *
 * @returns uint16_t Lower 16-bit of queue number
 */
uint16_t prvTraceGetQueueNumberLow16(void* pvQueue);

/**
 * @internal Retrieve upper 16-bit of queue number
 *
 * @param[in] pvQueuevQueue handle
 *
 * @returns uint16_t Upper 16-bit of queue number
 */
uint16_t prvTraceGetQueueNumberHigh16(void* pvQueue);


/**
 * @internal Set lower 16-bit of queue number
 *
 * @param[in] pvQueue Queue handle
 * @param[in] uiValue Value
 */
void prvTraceSetQueueNumberLow16(void* pvQueue, uint16_t uiValue);


/**
 * @internal Set upper 16-bit of queue number
 *
 * @param[in] pvQueue Queue handle
 * @param[in] uiValue Value
 */
void prvTraceSetQueueNumberHigh16(void* pvQueue, uint16_t uiValue);

#if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

/**
 * @internal Retrieve lower 16-bit of timer number
 *
 * @param[in] pvTimer Timer handle
 *
 * @returns uint16_t Lower 16-bit of timer number
 */
uint16_t prvTraceGetTimerNumberLow16(void* pvTimer);

/**
 * @internal Retrieve upper 16-bit of timer number
 *
 * @param[in] pvTimer Timer handle
 *
 * @returns uint16_t Upper 16-bit of timer number
 */
uint16_t prvTraceGetTimerNumberHigh16(void* pvTimer);

/**
 * @internal Set lower 16-bit of timer number
 *
 * @param[in] pvTimer Timer handle
 * @param[in] uiValue Value
 */
void prvTraceSetTimerNumberLow16(void* pvTimer, uint16_t uiValue);

/**
 * @internal Set upper 16-bit of timer number
 *
 * @param[in] pvTimer Timer handle
 * @param[in] uiValue Value
 */
void prvTraceSetTimerNumberHigh16(void* pvTimer, uint16_t uiValue);

#endif

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

/**
 * @internal Retrieve lower 16-bit of event group number
 *
 * @param[in] pvEventGroup Event group handle
 *
 * @returns uint16_t Lower 16-bit of event group number
 */
uint16_t prvTraceGetEventGroupNumberLow16(void* pvEventGroup);

/**
 * @internal Retrieve upper 16-bit of event group number
 *
 * @param[in] pvEventGroup Event group handle
 *
 * @returns uint16_t Upper 16-bit of event group number
 */
uint16_t prvTraceGetEventGroupNumberHigh16(void* pvEventGroup);

/**
 * @internal Set lower 16-bit of event group number
 *
 * @param[in] pvEventGroup Event group handle
 * @param[in] uiValue Value
 */
void prvTraceSetEventGroupNumberLow16(void* pvEventGroup, uint16_t uiValue);

/**
 * @internal Set upper 16-bit of event group number
 *
 * @param[in] pvEventGroup Event group handle
 * @param[in] uiValue Value
 */
void prvTraceSetEventGroupNumberHigh16(void* handle, uint16_t value);

#endif

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

/**
 * @internal Retrieve lower 16-bit of stream buffer number
 *
 * @param[in] pvStreamBuffer Stream buffer handle
 *
 * @returns uint16_t Lower 16-bit of stream buffer number
 */
uint16_t prvTraceGetStreamBufferNumberLow16(void* pvStreamBuffer);

/**
 * @internal Retrieve upper 16-bit of stream buffer number
 *
 * @param[in] pvStreamBuffer Stream buffer handle
 *
 * @returns uint16_t Upper 16-bit of stream buffer number
 */
uint16_t prvTraceGetStreamBufferNumberHigh16(void* pvStreamBuffer);

/**
 * @internal Set lower 16-bit of stream buffer number
 *
 * @param[in] pvStreamBuffer Stream buffer handle
 * @param[in] uiValue Value
 */
void prvTraceSetStreamBufferNumberLow16(void* pvStreamBuffer, uint16_t uiValue);

/**
 * @internal Set upper 16-bit of stream buffer number
 *
 * @param[in] pvStreamBuffer Stream buffer handle
 * @param[in] uiValue Value
 */
void prvTraceSetStreamBufferNumberHigh16(void* pvStreamBuffer, uint16_t uiValue);

#endif

/**
 * @brief Retrieve filter of task
 *
 * @param[in] pxTask Task handle
 *
 * @returns uint16_t Task filter
 */
#define TRACE_GET_TASK_FILTER(pxTask) prvTraceGetTaskNumberHigh16((void*)pxTask)

/**
 * @brief Set filter of task
 *
 * @param[in] pxTask Task handle
 * @param[in] group Group
 */
#define TRACE_SET_TASK_FILTER(pxTask, group) prvTraceSetTaskNumberHigh16((void*)pxTask, group)

/**
 * @brief Retrieve filter of queue
 *
 * @param[in] pxQueue Queue handle
 *
 * @returns uint16_t Queue filter
 */
#define TRACE_GET_QUEUE_FILTER(pxQueue) prvTraceGetQueueNumberHigh16((void*)pxQueue)

/**
 * @brief Set filter of queue
 *
 * @param[in] pxQueue Queue handle
 * @param[in] group Group
 */
#define TRACE_SET_QUEUE_FILTER(pxQueue, group) prvTraceSetQueueNumberHigh16((void*)pxQueue, group)

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

/**
 * @brief Retrieve filter of event group
 *
 * @param[in] pxEventGroup Queue handle
 *
 * @returns uint16_t Queue filter
 */
#define TRACE_GET_EVENTGROUP_FILTER(pxEventGroup) prvTraceGetEventGroupNumberHigh16((void*)pxEventGroup)

/**
 * @brief Set filter of event group
 *
 * @param[in] pxEventGroup Queue handle
 * @param[in] group Group
 */
#define TRACE_SET_EVENTGROUP_FILTER(pxEventGroup, group) prvTraceSetEventGroupNumberHigh16((void*)pxEventGroup, group)

#else

/**
 * @brief Disabled by TRC_CFG_FREERTOS_VERSION
 */
#define TRACE_GET_EVENTGROUP_FILTER(pxEventGroup) ((void)(pxEventGroup), 1)

/**
 * @brief Disabled by TRC_CFG_FREERTOS_VERSION
 */
#define TRACE_SET_EVENTGROUP_FILTER(pxEventGroup, group) ((void)(pxEventGroup), (void)(group))

#endif

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)

/**
 * @brief Retrieve filter of timer
 *
 * @param[in] pxEventGroup Timer handle
 *
 * @returns uint16_t Timer filter
 */
#define TRACE_GET_TIMER_FILTER(pxTimer) prvTraceGetTimerNumberHigh16((void*)pxTimer)

/**
 * @brief Set filter of timer
 *
 * @param[in] pxTimer Timer handle
 * @param[in] group Group
 */
#define TRACE_SET_TIMER_FILTER(pxTimer, group) prvTraceSetTimerNumberHigh16((void*)pxTimer, group)

#else

/**
 * @brief Disabled by TRC_CFG_FREERTOS_VERSION
 */
#define TRACE_GET_TIMER_FILTER(pxTimer) ((void)(pxTimer), 1)

/**
 * @brief Disabled by TRC_CFG_FREERTOS_VERSION
 */
#define TRACE_SET_TIMER_FILTER(pxTimer, group) ((void)(pxTimer), (void)(group))

#endif

/**
 * @brief Retrieve filter of stream buffer
 *
 * @param[in] pxStreamBuffer Stream buffer handle
 *
 * @returns uint16_t Timer filter
 */
#define TRACE_GET_STREAMBUFFER_FILTER(pxStreamBuffer) prvTraceGetStreamBufferNumberHigh16((void*)pxStreamBuffer)

/**
 * @brief Set filter of stream buffer
 *
 * @param[in] pxStreamBuffer Stream buffer handle
 * @param[in] group Group
 */
#define TRACE_SET_STREAMBUFFER_FILTER(pxStreamBuffer, group) prvTraceSetStreamBufferNumberHigh16((void*)pxStreamBuffer, group)

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)

/**
 * @internal Get object filter
 */
#define TRACE_GET_OBJECT_FILTER(CLASS, pxObject) TRACE_GET_##CLASS##_FILTER(pxObject)

/**
 * @internal Set object filter
 */
#define TRACE_SET_OBJECT_FILTER(CLASS, pxObject, group) TRACE_SET_##CLASS##_FILTER(pxObject, group)

#else

/**
 * @internal Disabled by TRC_CFG_FREERTOS_VERSION
 */
#define TRACE_GET_OBJECT_FILTER(CLASS, pxObject) 0xFFFF

/**
 * @internal Disabled by TRC_CFG_FREERTOS_VERSION
 */
#define TRACE_SET_OBJECT_FILTER(CLASS, pxObject, group)

#endif

/* The object classes */
#define TRACE_NCLASSES 9
#define TRACE_CLASS_QUEUE ((traceObjectClass)0)
#define TRACE_CLASS_SEMAPHORE ((traceObjectClass)1)
#define TRACE_CLASS_MUTEX ((traceObjectClass)2)
#define TRACE_CLASS_TASK ((traceObjectClass)3)
#define TRACE_CLASS_ISR ((traceObjectClass)4)
#define TRACE_CLASS_TIMER ((traceObjectClass)5)
#define TRACE_CLASS_EVENTGROUP ((traceObjectClass)6)
#define TRACE_CLASS_STREAMBUFFER ((traceObjectClass)7)
#define TRACE_CLASS_MESSAGEBUFFER ((traceObjectClass)8)

/* Definitions for Object Table */
#define TRACE_KERNEL_OBJECT_COUNT ((TRC_CFG_NQUEUE) + (TRC_CFG_NSEMAPHORE) + (TRC_CFG_NMUTEX) + (TRC_CFG_NTASK) + (TRC_CFG_NISR) + (TRC_CFG_NTIMER) + (TRC_CFG_NEVENTGROUP) + (TRC_CFG_NSTREAMBUFFER) + (TRC_CFG_NMESSAGEBUFFER))

/* Queue properties (except name):	current number of message in queue */
#define PropertyTableSizeQueue		((TRC_CFG_NAME_LEN_QUEUE) + 1)

/* Semaphore properties (except name): state (signaled = 1, cleared = 0) */
#define PropertyTableSizeSemaphore	((TRC_CFG_NAME_LEN_SEMAPHORE) + 1)

/* Mutex properties (except name):	owner (task handle, 0 = free) */
#define PropertyTableSizeMutex		((TRC_CFG_NAME_LEN_MUTEX) + 1)

/* Task properties (except name):	Byte 0: Current priority
									Byte 1: state (if already active)
									Byte 2: legacy, not used
									Byte 3: legacy, not used */
#define PropertyTableSizeTask		((TRC_CFG_NAME_LEN_TASK) + 4)

/* ISR properties:					Byte 0: priority
									Byte 1: state (if already active) */
#define PropertyTableSizeISR		((TRC_CFG_NAME_LEN_ISR) + 2)

/* TRC_CFG_NTIMER properties:				Byte 0: state (unused for now) */
#define PropertyTableSizeTimer		((TRC_CFG_NAME_LEN_TIMER) + 1)

/* TRC_CFG_NEVENTGROUP properties:			Byte 0-3: state (unused for now)*/
#define PropertyTableSizeEventGroup	((TRC_CFG_NAME_LEN_EVENTGROUP) + 4)

/* TRC_CFG_NSTREAMBUFFER properties:			Byte 0-3: state (unused for now)*/
#define PropertyTableSizeStreamBuffer	((TRC_CFG_NAME_LEN_STREAMBUFFER) + 4)

/* TRC_CFG_NMESSAGEBUFFER properties:			Byte 0-3: state (unused for now)*/
#define PropertyTableSizeMessageBuffer	((TRC_CFG_NAME_LEN_MESSAGEBUFFER) + 4)


/* The layout of the byte array representing the Object Property Table */
#define StartIndexQueue			(0)
#define StartIndexSemaphore		(StartIndexQueue		+ (TRC_CFG_NQUEUE)			* PropertyTableSizeQueue)
#define StartIndexMutex			(StartIndexSemaphore 	+ (TRC_CFG_NSEMAPHORE)		* PropertyTableSizeSemaphore)
#define StartIndexTask			(StartIndexMutex		+ (TRC_CFG_NMUTEX)			* PropertyTableSizeMutex)
#define StartIndexISR			(StartIndexTask			+ (TRC_CFG_NTASK)			* PropertyTableSizeTask)
#define StartIndexTimer			(StartIndexISR			+ (TRC_CFG_NISR)			* PropertyTableSizeISR)
#define StartIndexEventGroup	(StartIndexTimer		+ (TRC_CFG_NTIMER)			* PropertyTableSizeTimer)
#define StartIndexStreamBuffer	(StartIndexEventGroup	+ (TRC_CFG_NEVENTGROUP)		* PropertyTableSizeEventGroup)
#define StartIndexMessageBuffer	(StartIndexStreamBuffer	+ (TRC_CFG_NSTREAMBUFFER)	* PropertyTableSizeStreamBuffer)

/* Number of bytes used by the object table */
#define TRACE_OBJECT_TABLE_SIZE	(StartIndexMessageBuffer + (TRC_CFG_NMESSAGEBUFFER) * PropertyTableSizeMessageBuffer)

/* Flag to tell the context of tracePEND_FUNC_CALL_FROM_ISR */
extern int uiInEventGroupSetBitsFromISR;

/**
 * @internal Initialized the object property table
 */
traceResult xTraceKernelPortInitObjectPropertyTable(void);

/**
 * @internal Initialized the object handle stack
 */
traceResult xTraceKernelPortInitObjectHandleStack(void);

/**
 * @internal Retrieve error string
 */
const char* pszTraceGetErrorNotEnoughHandles(traceObjectClass objectclass);

/**
 * @internal Retrieve current task handle
 */
void* prvTraceGetCurrentTaskHandle(void);

extern traceObjectClass TraceQueueClassTable[5];


/*** Event codes for snapshot mode - must match Tracealyzer config files ******/

#define NULL_EVENT					(0x00UL)

/*******************************************************************************
 * EVENTGROUP_DIV
 *
 * Miscellaneous events.
 ******************************************************************************/
#define EVENTGROUP_DIV				(NULL_EVENT + 1UL)					/*0x01*/
#define DIV_XPS						(EVENTGROUP_DIV + 0UL)				/*0x01*/
#define DIV_TASK_READY				(EVENTGROUP_DIV + 1UL)				/*0x02*/
#define DIV_NEW_TIME				(EVENTGROUP_DIV + 2UL)				/*0x03*/

/*******************************************************************************
 * EVENTGROUP_TS
 *
 * Events for storing task-switches and interrupts. The RESUME events are
 * generated if the task/interrupt is already marked active.
 ******************************************************************************/
#define EVENTGROUP_TS				(EVENTGROUP_DIV + 3UL)				/*0x04*/
#define TS_ISR_BEGIN				(EVENTGROUP_TS + 0UL)				/*0x04*/
#define TS_ISR_RESUME				(EVENTGROUP_TS + 1UL)				/*0x05*/
#define TS_TASK_BEGIN				(EVENTGROUP_TS + 2UL)				/*0x06*/
#define TS_TASK_RESUME				(EVENTGROUP_TS + 3UL)				/*0x07*/

/*******************************************************************************
 * EVENTGROUP_OBJCLOSE_NAME
 *
 * About Close Events
 * When an object is evicted from the object property table (object close), two
 * internal events are stored (EVENTGROUP_OBJCLOSE_NAME and
 * EVENTGROUP_OBJCLOSE_PROP), containing the handle-name mapping and object
 * properties valid up to this point.
 ******************************************************************************/
#define EVENTGROUP_OBJCLOSE_NAME_TRCSUCCESS	(EVENTGROUP_TS + 4UL)		/*0x08*/

/*******************************************************************************
 * EVENTGROUP_OBJCLOSE_PROP
 *
 * The internal event carrying properties of deleted objects
 * The handle and object class of the closed object is not stored in this event,
 * but is assumed to be the same as in the preceding CLOSE event. Thus, these
 * two events must be generated from within a critical section.
 * When queues are closed, arg1 is the "state" property (i.e., number of
 * buffered messages/signals).
 * When actors are closed, arg1 is priority, arg2 is handle of the "instance
 * finish" event, and arg3 is event code of the "instance finish" event.
 * In this case, the lower three bits is the object class of the instance finish
 * handle. The lower three bits are not used (always zero) when queues are
 * closed since the queue type is given in the previous OBJCLOSE_NAME event.
 ******************************************************************************/
#define EVENTGROUP_OBJCLOSE_PROP_TRCSUCCESS	(EVENTGROUP_OBJCLOSE_NAME_TRCSUCCESS + 8UL)	/*0x10*/

/*******************************************************************************
 * EVENTGROUP_CREATE
 *
 * The events in this group are used to log Kernel object creations.
 * The lower three bits in the event code gives the object class, i.e., type of
 * create operation (task, queue, semaphore, etc).
 ******************************************************************************/
#define EVENTGROUP_CREATE_OBJ_TRCSUCCESS	(EVENTGROUP_OBJCLOSE_PROP_TRCSUCCESS + 8UL)	/*0x18*/

/*******************************************************************************
 * EVENTGROUP_SEND
 *
 * The events in this group are used to log Send/Give events on queues,
 * semaphores and mutexes The lower three bits in the event code gives the
 * object class, i.e., what type of object that is operated on (queue, semaphore
 * or mutex).
 ******************************************************************************/
#define EVENTGROUP_SEND_TRCSUCCESS	(EVENTGROUP_CREATE_OBJ_TRCSUCCESS + 8UL)	/*0x20*/

/*******************************************************************************
 * EVENTGROUP_RECEIVE
 *
 * The events in this group are used to log Receive/Take events on queues,
 * semaphores and mutexes. The lower three bits in the event code gives the
 * object class, i.e., what type of object that is operated on (queue, semaphore
 * or mutex).
 ******************************************************************************/
#define EVENTGROUP_RECEIVE_TRCSUCCESS	(EVENTGROUP_SEND_TRCSUCCESS + 8UL)		/*0x28*/

/* Send/Give operations, from ISR */
#define EVENTGROUP_SEND_FROM_ISR_TRCSUCCESS \
									(EVENTGROUP_RECEIVE_TRCSUCCESS + 8UL)		/*0x30*/

/* Receive/Take operations, from ISR */
#define EVENTGROUP_RECEIVE_FROM_ISR_TRCSUCCESS \
							(EVENTGROUP_SEND_FROM_ISR_TRCSUCCESS + 8UL)			/*0x38*/

/* "Failed" event type versions of above (timeout, failed allocation, etc) */
#define EVENTGROUP_KSE_TRCFAILED \
							(EVENTGROUP_RECEIVE_FROM_ISR_TRCSUCCESS + 8UL)		/*0x40*/

/* Failed create calls - memory allocation failed */
#define EVENTGROUP_CREATE_OBJ_TRCFAILED	(EVENTGROUP_KSE_TRCFAILED)				/*0x40*/

/* Failed send/give - timeout! */
#define EVENTGROUP_SEND_TRCFAILED		(EVENTGROUP_CREATE_OBJ_TRCFAILED + 8UL)	/*0x48*/

/* Failed receive/take - timeout! */
#define EVENTGROUP_RECEIVE_TRCFAILED	 (EVENTGROUP_SEND_TRCFAILED + 8UL)		/*0x50*/

/* Failed non-blocking send/give - queue full */
#define EVENTGROUP_SEND_FROM_ISR_TRCFAILED (EVENTGROUP_RECEIVE_TRCFAILED + 8UL) /*0x58*/

/* Failed non-blocking receive/take - queue empty */
#define EVENTGROUP_RECEIVE_FROM_ISR_TRCFAILED \
								 (EVENTGROUP_SEND_FROM_ISR_TRCFAILED + 8UL)		/*0x60*/

/* Events when blocking on receive/take */
#define EVENTGROUP_RECEIVE_TRCBLOCK \
							(EVENTGROUP_RECEIVE_FROM_ISR_TRCFAILED + 8UL)		/*0x68*/

/* Events when blocking on send/give */
#define EVENTGROUP_SEND_TRCBLOCK	(EVENTGROUP_RECEIVE_TRCBLOCK + 8UL)			/*0x70*/

/* Events on queue peek (receive) */
#define EVENTGROUP_PEEK_TRCSUCCESS	(EVENTGROUP_SEND_TRCBLOCK + 8UL)			/*0x78*/

/* Events on object delete (vTaskDelete or vQueueDelete) */
#define EVENTGROUP_DELETE_OBJ_TRCSUCCESS	(EVENTGROUP_PEEK_TRCSUCCESS + 8UL)	/*0x80*/

/* Other events - object class is implied: TASK */
#define EVENTGROUP_OTHERS	(EVENTGROUP_DELETE_OBJ_TRCSUCCESS + 8UL)			/*0x88*/
#define TASK_DELAY_UNTIL	(EVENTGROUP_OTHERS + 0UL)						/*0x88*/
#define TASK_DELAY			(EVENTGROUP_OTHERS + 1UL)						/*0x89*/
#define TASK_SUSPEND		(EVENTGROUP_OTHERS + 2UL)						/*0x8A*/
#define TASK_RESUME			(EVENTGROUP_OTHERS + 3UL)						/*0x8B*/
#define TASK_RESUME_FROM_ISR	(EVENTGROUP_OTHERS + 4UL)					/*0x8C*/
#define TASK_PRIORITY_SET		(EVENTGROUP_OTHERS + 5UL)					/*0x8D*/
#define TASK_PRIORITY_INHERIT	(EVENTGROUP_OTHERS + 6UL)					/*0x8E*/
#define TASK_PRIORITY_DISINHERIT	(EVENTGROUP_OTHERS + 7UL)				/*0x8F*/

#define EVENTGROUP_MISC_PLACEHOLDER	(EVENTGROUP_OTHERS + 8UL)				/*0x90*/
#define PEND_FUNC_CALL		(EVENTGROUP_MISC_PLACEHOLDER+0UL)				/*0x90*/
#define PEND_FUNC_CALL_FROM_ISR (EVENTGROUP_MISC_PLACEHOLDER+1UL)			/*0x91*/
#define PEND_FUNC_CALL_TRCFAILED (EVENTGROUP_MISC_PLACEHOLDER+2UL)			/*0x92*/
#define PEND_FUNC_CALL_FROM_ISR_TRCFAILED (EVENTGROUP_MISC_PLACEHOLDER+3UL)	/*0x93*/
#define MEM_MALLOC_SIZE (EVENTGROUP_MISC_PLACEHOLDER+4UL)					/*0x94*/
#define MEM_MALLOC_ADDR (EVENTGROUP_MISC_PLACEHOLDER+5UL)					/*0x95*/
#define MEM_FREE_SIZE (EVENTGROUP_MISC_PLACEHOLDER+6UL)						/*0x96*/
#define MEM_FREE_ADDR (EVENTGROUP_MISC_PLACEHOLDER+7UL)						/*0x97*/

/* User events */
#define EVENTGROUP_USEREVENT (EVENTGROUP_MISC_PLACEHOLDER + 8UL)			/*0x98*/
#define USER_EVENT (EVENTGROUP_USEREVENT + 0UL)

/* Allow for 0-15 arguments (the number of args is added to event code) */
#define USER_EVENT_LAST (EVENTGROUP_USEREVENT + 15UL)						/*0xA7*/

/*******************************************************************************
 * XTS Event - eXtended TimeStamp events
 * The timestamps used in the recorder are "differential timestamps" (DTS), i.e.
 * the time since the last stored event. The DTS fields are either 1 or 2 bytes
 * in the other events, depending on the bytes available in the event struct.
 * If the time since the last event (the DTS) is larger than allowed for by
 * the DTS field of the current event, an XTS event is inserted immediately
 * before the original event. The XTS event contains up to 3 additional bytes
 * of the DTS value - the higher bytes of the true DTS value. The lower 1-2
 * bytes are stored in the normal DTS field.
 * There are two types of XTS events, XTS8 and XTS16. An XTS8 event is stored
 * when there is only room for 1 byte (8 bit) DTS data in the original event,
 * which means a limit of 0xFF (255UL). The XTS16 is used when the original event
 * has a 16 bit DTS field and thereby can handle values up to 0xFFFF (65535UL).
 *
 * Using a very high frequency time base can result in many XTS events.
 * Preferably, the time between two OS ticks should fit in 16 bits, i.e.,
 * at most 65535. If your time base has a higher frequency, you can define
 * the TRACE
 ******************************************************************************/

#define EVENTGROUP_SYS (EVENTGROUP_USEREVENT + 16UL)						/*0xA8*/
#define XTS8 (EVENTGROUP_SYS + 0UL)											/*0xA8*/
#define XTS16 (EVENTGROUP_SYS + 1UL)										/*0xA9*/
#define EVENT_BEING_WRITTEN (EVENTGROUP_SYS + 2UL)							/*0xAA*/
#define RESERVED_DUMMY_CODE (EVENTGROUP_SYS + 3UL)							/*0xAB*/
#define LOW_POWER_BEGIN (EVENTGROUP_SYS + 4UL)								/*0xAC*/
#define LOW_POWER_END (EVENTGROUP_SYS + 5UL)								/*0xAD*/
#define XID (EVENTGROUP_SYS + 6UL)											/*0xAE*/
#define XTS16L (EVENTGROUP_SYS + 7UL)										/*0xAF*/

#define EVENTGROUP_TIMER (EVENTGROUP_SYS + 8UL)								/*0xB0*/
#define TIMER_CREATE (EVENTGROUP_TIMER + 0UL)								/*0xB0*/
#define TIMER_START (EVENTGROUP_TIMER + 1UL)								/*0xB1*/
#define TIMER_RST (EVENTGROUP_TIMER + 2UL)									/*0xB2*/
#define TIMER_STOP (EVENTGROUP_TIMER + 3UL)									/*0xB3*/
#define TIMER_CHANGE_PERIOD (EVENTGROUP_TIMER + 4UL)						/*0xB4*/
#define TIMER_DELETE_OBJ (EVENTGROUP_TIMER + 5UL)							/*0xB5*/
#define TIMER_START_FROM_ISR (EVENTGROUP_TIMER + 6UL)						/*0xB6*/
#define TIMER_RESET_FROM_ISR (EVENTGROUP_TIMER + 7UL)						/*0xB7*/
#define TIMER_STOP_FROM_ISR (EVENTGROUP_TIMER + 8UL)						/*0xB8*/

#define TIMER_CREATE_TRCFAILED (EVENTGROUP_TIMER + 9UL)						/*0xB9*/
#define TIMER_START_TRCFAILED (EVENTGROUP_TIMER + 10UL)						/*0xBA*/
#define TIMER_RESET_TRCFAILED (EVENTGROUP_TIMER + 11UL)						/*0xBB*/
#define TIMER_STOP_TRCFAILED (EVENTGROUP_TIMER + 12UL)						/*0xBC*/
#define TIMER_CHANGE_PERIOD_TRCFAILED (EVENTGROUP_TIMER + 13UL)				/*0xBD*/
#define TIMER_DELETE_TRCFAILED (EVENTGROUP_TIMER + 14UL)					/*0xBE*/
#define TIMER_START_FROM_ISR_TRCFAILED (EVENTGROUP_TIMER + 15UL)			/*0xBF*/
#define TIMER_RESET_FROM_ISR_TRCFAILED (EVENTGROUP_TIMER + 16UL)			/*0xC0*/
#define TIMER_STOP_FROM_ISR_TRCFAILED (EVENTGROUP_TIMER + 17UL)				/*0xC1*/

#define EVENTGROUP_EG (EVENTGROUP_TIMER + 18UL)								/*0xC2*/
#define EVENT_GROUP_CREATE (EVENTGROUP_EG + 0UL)							/*0xC2*/
#define EVENT_GROUP_CREATE_TRCFAILED (EVENTGROUP_EG + 1UL)					/*0xC3*/
#define EVENT_GROUP_SYNC_TRCBLOCK (EVENTGROUP_EG + 2UL)						/*0xC4*/
#define EVENT_GROUP_SYNC_END (EVENTGROUP_EG + 3UL)							/*0xC5*/
#define EVENT_GROUP_WAIT_BITS_TRCBLOCK (EVENTGROUP_EG + 4UL)				/*0xC6*/
#define EVENT_GROUP_WAIT_BITS_END (EVENTGROUP_EG + 5UL)						/*0xC7*/
#define EVENT_GROUP_CLEAR_BITS (EVENTGROUP_EG + 6UL)						/*0xC8*/
#define EVENT_GROUP_CLEAR_BITS_FROM_ISR (EVENTGROUP_EG + 7UL)				/*0xC9*/
#define EVENT_GROUP_SET_BITS (EVENTGROUP_EG + 8UL)							/*0xCA*/
#define EVENT_GROUP_DELETE_OBJ (EVENTGROUP_EG + 9UL)						/*0xCB*/
#define EVENT_GROUP_SYNC_END_TRCFAILED (EVENTGROUP_EG + 10UL)				/*0xCC*/
#define EVENT_GROUP_WAIT_BITS_END_TRCFAILED (EVENTGROUP_EG + 11UL)			/*0xCD*/
#define EVENT_GROUP_SET_BITS_FROM_ISR (EVENTGROUP_EG + 12UL)				/*0xCE*/
#define EVENT_GROUP_SET_BITS_FROM_ISR_TRCFAILED (EVENTGROUP_EG + 13UL)		/*0xCF*/

#define TASK_INSTANCE_FINISHED_NEXT_KSE (EVENTGROUP_EG + 14UL)				/*0xD0*/
#define TASK_INSTANCE_FINISHED_DIRECT (EVENTGROUP_EG + 15UL)				/*0xD1*/

#define TRACE_TASK_NOTIFY_GROUP (EVENTGROUP_EG + 16UL)						/*0xD2*/
#define TRACE_TASK_NOTIFY (TRACE_TASK_NOTIFY_GROUP + 0UL)					/*0xD2*/
#define TRACE_TASK_NOTIFY_TAKE (TRACE_TASK_NOTIFY_GROUP + 1UL)				/*0xD3*/
#define TRACE_TASK_NOTIFY_TAKE_TRCBLOCK (TRACE_TASK_NOTIFY_GROUP + 2UL)		/*0xD4*/
#define TRACE_TASK_NOTIFY_TAKE_TRCFAILED (TRACE_TASK_NOTIFY_GROUP + 3UL)	/*0xD5*/
#define TRACE_TASK_NOTIFY_WAIT (TRACE_TASK_NOTIFY_GROUP + 4UL)				/*0xD6*/
#define TRACE_TASK_NOTIFY_WAIT_TRCBLOCK (TRACE_TASK_NOTIFY_GROUP + 5UL)		/*0xD7*/
#define TRACE_TASK_NOTIFY_WAIT_TRCFAILED (TRACE_TASK_NOTIFY_GROUP + 6UL)	/*0xD8*/
#define TRACE_TASK_NOTIFY_FROM_ISR (TRACE_TASK_NOTIFY_GROUP + 7UL)			/*0xD9*/
#define TRACE_TASK_NOTIFY_GIVE_FROM_ISR (TRACE_TASK_NOTIFY_GROUP + 8UL)		/*0xDA*/

#define TIMER_EXPIRED (TRACE_TASK_NOTIFY_GROUP + 9UL)						/*0xDB*/

 /* Events on queue peek (receive) */
#define EVENTGROUP_PEEK_TRCBLOCK	(TRACE_TASK_NOTIFY_GROUP + 10UL)		/*0xDC*/
/* peek block on queue:			0xDC	*/
/* peek block on semaphore:		0xDD	*/
/* peek block on mutex:			0xDE	*/

/* Events on queue peek (receive) */
#define EVENTGROUP_PEEK_TRCFAILED	(EVENTGROUP_PEEK_TRCBLOCK + 3UL)		/*0xDF*/
/* peek failed on queue:		0xDF	*/
/* peek failed on semaphore:	0xE0	*/
/* peek failed on mutex:		0xE1	*/

#define EVENTGROUP_STREAMBUFFER_DIV							(EVENTGROUP_PEEK_TRCFAILED + 3UL)			/*0xE2*/
#define TRACE_STREAMBUFFER_RESET							(EVENTGROUP_STREAMBUFFER_DIV + 0)			/*0xE2*/
#define TRACE_MESSAGEBUFFER_RESET							(EVENTGROUP_STREAMBUFFER_DIV + 1UL)			/*0xE3*/
#define TRACE_STREAMBUFFER_OBJCLOSE_NAME_TRCSUCCESS			(EVENTGROUP_STREAMBUFFER_DIV + 2UL)			/*0xE4*/
#define TRACE_MESSAGEBUFFER_OBJCLOSE_NAME_TRCSUCCESS		(EVENTGROUP_STREAMBUFFER_DIV + 3UL)			/*0xE5*/
#define TRACE_STREAMBUFFER_OBJCLOSE_PROP_TRCSUCCESS			(EVENTGROUP_STREAMBUFFER_DIV + 4UL)			/*0xE6*/
#define TRACE_MESSAGEBUFFER_OBJCLOSE_PROP_TRCSUCCESS		(EVENTGROUP_STREAMBUFFER_DIV + 5UL)			/*0xE7*/

#define EVENTGROUP_MALLOC_FAILED							(EVENTGROUP_STREAMBUFFER_DIV + 6UL)			/*0xE8*/
#define MEM_MALLOC_SIZE_TRCFAILED							(EVENTGROUP_MALLOC_FAILED + 0UL)			/*0xE8*/
#define MEM_MALLOC_ADDR_TRCFAILED							(EVENTGROUP_MALLOC_FAILED + 1UL)			/*0xE9*/

/* The following are using previously "lost" event codes */
#define TRACE_STREAMBUFFER_CREATE_OBJ_TRCSUCCESS			(EVENTGROUP_CREATE_OBJ_TRCSUCCESS + 4UL)		/*0x1C*/
#define TRACE_STREAMBUFFER_CREATE_OBJ_TRCFAILED				(EVENTGROUP_CREATE_OBJ_TRCFAILED + 4UL)			/*0x44*/
#define TRACE_STREAMBUFFER_DELETE_OBJ_TRCSUCCESS			(EVENTGROUP_DELETE_OBJ_TRCSUCCESS + 4UL)		/*0x84*/
#define TRACE_STREAMBUFFER_SEND_TRCSUCCESS					(EVENTGROUP_SEND_TRCSUCCESS + 3UL)				/*0x23*/
#define TRACE_STREAMBUFFER_SEND_TRCBLOCK					(EVENTGROUP_SEND_TRCBLOCK + 3UL)				/*0x73*/
#define TRACE_STREAMBUFFER_SEND_TRCFAILED					(EVENTGROUP_SEND_TRCFAILED + 3UL)				/*0x4B*/
#define TRACE_STREAMBUFFER_RECEIVE_TRCSUCCESS				(EVENTGROUP_RECEIVE_TRCSUCCESS + 3UL)			/*0x2B*/
#define TRACE_STREAMBUFFER_RECEIVE_TRCBLOCK					(EVENTGROUP_RECEIVE_TRCBLOCK + 3UL)				/*0x6B*/
#define TRACE_STREAMBUFFER_RECEIVE_TRCFAILED				(EVENTGROUP_RECEIVE_TRCFAILED + 3UL)			/*0x53*/
#define TRACE_STREAMBUFFER_SEND_FROM_ISR_TRCSUCCESS			(EVENTGROUP_SEND_FROM_ISR_TRCSUCCESS + 3UL)		/*0x33*/
#define TRACE_STREAMBUFFER_SEND_FROM_ISR_TRCFAILED			(EVENTGROUP_SEND_FROM_ISR_TRCFAILED + 3UL)		/*0x5B*/
#define TRACE_STREAMBUFFER_RECEIVE_FROM_ISR_TRCSUCCESS		(EVENTGROUP_RECEIVE_FROM_ISR_TRCSUCCESS + 3UL)	/*0x3B*/
#define TRACE_STREAMBUFFER_RECEIVE_FROM_ISR_TRCFAILED		(EVENTGROUP_RECEIVE_FROM_ISR_TRCFAILED + 3UL)	/*0x63*/

/* The following are using previously "lost" event codes. These macros aren't even directly referenced, instead we do (equivalent STREAMBUFFER code) + 1. */
#define TRACE_MESSAGEBUFFER_CREATE_OBJ_TRCSUCCESS			(EVENTGROUP_CREATE_OBJ_TRCSUCCESS + 5UL)		/*0x1D*/
#define TRACE_MESSAGEBUFFER_CREATE_OBJ_TRCFAILED			(EVENTGROUP_CREATE_OBJ_TRCFAILED + 5UL)			/*0x45*/
#define TRACE_MESSAGEBUFFER_DELETE_OBJ_TRCSUCCESS			(EVENTGROUP_DELETE_OBJ_TRCSUCCESS + 5UL)		/*0x85*/
#define TRACE_MESSAGEBUFFER_SEND_TRCSUCCESS					(EVENTGROUP_SEND_TRCSUCCESS + 4UL)				/*0x24*/
#define TRACE_MESSAGEBUFFER_SEND_TRCBLOCK					(EVENTGROUP_SEND_TRCBLOCK + 4UL)				/*0x74*/
#define TRACE_MESSAGEBUFFER_SEND_TRCFAILED					(EVENTGROUP_SEND_TRCFAILED + 4UL)				/*0x4C*/
#define TRACE_MESSAGEBUFFER_RECEIVE_TRCSUCCESS				(EVENTGROUP_RECEIVE_TRCSUCCESS + 4UL)			/*0x2C*/
#define TRACE_MESSAGEBUFFER_RECEIVE_TRCBLOCK				(EVENTGROUP_RECEIVE_TRCBLOCK + 4UL)				/*0x6C*/
#define TRACE_MESSAGEBUFFER_RECEIVE_TRCFAILED				(EVENTGROUP_RECEIVE_TRCFAILED + 4UL)			/*0x54*/
#define TRACE_MESSAGEBUFFER_SEND_FROM_ISR_TRCSUCCESS		(EVENTGROUP_SEND_FROM_ISR_TRCSUCCESS + 4UL)		/*0x34*/
#define TRACE_MESSAGEBUFFER_SEND_FROM_ISR_TRCFAILED			(EVENTGROUP_SEND_FROM_ISR_TRCFAILED + 4UL)		/*0x5C*/
#define TRACE_MESSAGEBUFFER_RECEIVE_FROM_ISR_TRCSUCCESS		(EVENTGROUP_RECEIVE_FROM_ISR_TRCSUCCESS + 4UL)	/*0x3C*/
#define TRACE_MESSAGEBUFFER_RECEIVE_FROM_ISR_TRCFAILED		(EVENTGROUP_RECEIVE_FROM_ISR_TRCFAILED + 4UL)	/*0x64*/

#define TRACE_QUEUE_SEND_TO_FRONT_TRCSUCCESS				(EVENTGROUP_SEND_TRCSUCCESS + 5UL)				/*0x25*/
#define TRACE_QUEUE_SEND_TO_FRONT_TRCBLOCK					(EVENTGROUP_SEND_TRCBLOCK + 5UL)				/*0x75*/
#define TRACE_QUEUE_SEND_TO_FRONT_TRCFAILED					(EVENTGROUP_SEND_TRCFAILED + 5UL)				/*0x4D*/
#define TRACE_QUEUE_SEND_TO_FRONT_FROM_ISR_TRCSUCCESS		(EVENTGROUP_SEND_FROM_ISR_TRCSUCCESS + 5UL)		/*0x35*/
#define TRACE_QUEUE_SEND_TO_FRONT_FROM_ISR_TRCFAILED		(EVENTGROUP_SEND_FROM_ISR_TRCFAILED + 5UL)		/*0x5D*/

#define TRACE_UNUSED_STACK									(EVENTGROUP_MALLOC_FAILED + 2UL)				/*0xEA*/

/* LAST EVENT (0xEA) */

/****************************
* MACROS TO GET TRACE CLASS *
****************************/
#define TRACE_GET_TRACE_CLASS_FROM_TASK_CLASS(kernelClass) (TRACE_CLASS_TASK)
#define TRACE_GET_TRACE_CLASS_FROM_TASK_OBJECT(pxObject) (TRACE_CLASS_TASK)

#define TRACE_GET_TRACE_CLASS_FROM_QUEUE_CLASS(kernelClass) TraceQueueClassTable[kernelClass]
#define TRACE_GET_TRACE_CLASS_FROM_QUEUE_OBJECT(pxObject) TRACE_GET_TRACE_CLASS_FROM_QUEUE_CLASS(prvTraceGetQueueType(pxObject))

#define TRACE_GET_TRACE_CLASS_FROM_TIMER_CLASS(kernelClass) (TRACE_CLASS_TIMER)
#define TRACE_GET_TRACE_CLASS_FROM_TIMER_OBJECT(pxObject) (TRACE_CLASS_TIMER)

#define TRACE_GET_TRACE_CLASS_FROM_EVENTGROUP_CLASS(kernelClass) (TRACE_CLASS_EVENTGROUP)
#define TRACE_GET_TRACE_CLASS_FROM_EVENTGROUP_OBJECT(pxObject) (TRACE_CLASS_EVENTGROUP)

/* TRACE_GET_TRACE_CLASS_FROM_STREAMBUFFER_CLASS can only be accessed with a parameter indicating if it is a MessageBuffer */
#define TRACE_GET_TRACE_CLASS_FROM_STREAMBUFFER_CLASS(xIsMessageBuffer) (xIsMessageBuffer == 1 ? TRACE_CLASS_MESSAGEBUFFER : TRACE_CLASS_STREAMBUFFER)
#define TRACE_GET_TRACE_CLASS_FROM_STREAMBUFFER_OBJECT(pxObject) (prvGetStreamBufferType(pxObject) == 1 ? TRACE_CLASS_MESSAGEBUFFER : TRACE_CLASS_STREAMBUFFER)

/* Generic versions */
#define TRACE_GET_CLASS_TRACE_CLASS(CLASS, kernelClass) TRACE_GET_TRACE_CLASS_FROM_##CLASS##_CLASS(kernelClass)
#define TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject) TRACE_GET_TRACE_CLASS_FROM_##CLASS##_OBJECT(pxObject)

/******************************
* MACROS TO GET OBJECT NUMBER *
******************************/
#define TRACE_GET_TASK_NUMBER(pxTCB) (traceHandle)(prvTraceGetTaskNumberLow16(pxTCB))
#define TRACE_SET_TASK_NUMBER(pxTCB) prvTraceSetTaskNumberLow16(pxTCB, prvTraceGetObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(TASK, pxTCB)));

#define TRACE_GET_QUEUE_NUMBER(queue) ( ( traceHandle ) prvTraceGetQueueNumberLow16(queue) )
#define TRACE_SET_QUEUE_NUMBER(queue) prvTraceSetQueueNumberLow16(queue, (uint16_t)prvTraceGetObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(QUEUE, queue)));

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
#define TRACE_GET_TIMER_NUMBER(tmr) ( ( traceHandle ) prvTraceGetTimerNumberLow16(tmr) )
#define TRACE_SET_TIMER_NUMBER(tmr) prvTraceSetTimerNumberLow16(tmr, (uint16_t)prvTraceGetObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(TIMER, tmr)));
#else /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */
#define TRACE_GET_TIMER_NUMBER(tmr) ( ( traceHandle ) ((Timer_t*)tmr)->uxTimerNumber )
#define TRACE_SET_TIMER_NUMBER(tmr) ((Timer_t*)tmr)->uxTimerNumber = prvTraceGetObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(TIMER, tmr));
#endif /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
#define TRACE_GET_EVENTGROUP_NUMBER(eg) ( ( traceHandle ) prvTraceGetEventGroupNumberLow16(eg) )
#define TRACE_SET_EVENTGROUP_NUMBER(eg) prvTraceSetEventGroupNumberLow16(eg, (uint16_t)prvTraceGetObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(EVENTGROUP, eg)));
#else /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */
#define TRACE_GET_EVENTGROUP_NUMBER(eg) ( ( traceHandle ) uxEventGroupGetNumber(eg) )
#define TRACE_SET_EVENTGROUP_NUMBER(eg) ((EventGroup_t*)eg)->uxEventGroupNumber = prvTraceGetObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(EVENTGROUP, eg));
#endif /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */


#define TRACE_GET_STREAMBUFFER_NUMBER(sb) ( ( traceHandle ) prvTraceGetStreamBufferNumberLow16(sb) )
#define TRACE_SET_STREAMBUFFER_NUMBER(sb) prvTraceSetStreamBufferNumberLow16(sb, (uint16_t)prvTraceGetObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(STREAMBUFFER, sb)));

/* Generic versions */
#define TRACE_GET_OBJECT_NUMBER(CLASS, pxObject) TRACE_GET_##CLASS##_NUMBER(pxObject)
#define TRACE_SET_OBJECT_NUMBER(CLASS, pxObject) TRACE_SET_##CLASS##_NUMBER(pxObject)

/******************************
* MACROS TO GET EVENT CODES   *
******************************/
#define TRACE_GET_TASK_CLASS_EVENT_CODE(SERVICE, RESULT, kernelClass) (uint8_t)(EVENTGROUP_##SERVICE##_##RESULT + TRACE_GET_CLASS_TRACE_CLASS(TASK, kernelClass))
#define TRACE_GET_QUEUE_CLASS_EVENT_CODE(SERVICE, RESULT, kernelClass) (uint8_t)(EVENTGROUP_##SERVICE##_##RESULT + TRACE_GET_CLASS_TRACE_CLASS(QUEUE, kernelClass))
#define TRACE_GET_TIMER_CLASS_EVENT_CODE(SERVICE, RESULT, kernelClass) -- THIS IS NOT USED --
#define TRACE_GET_EVENTGROUP_CLASS_EVENT_CODE(SERVICE, RESULT, kernelClass) -- THIS IS NOT USED --
#define TRACE_GET_STREAMBUFFER_CLASS_EVENT_CODE(SERVICE, RESULT, isMessageBuffer) (uint8_t)(TRACE_STREAMBUFFER_##SERVICE##_##RESULT + (uint8_t)isMessageBuffer)

#define TRACE_GET_TASK_OBJECT_EVENT_CODE(SERVICE, RESULT, pxTCB) (uint8_t)(EVENTGROUP_##SERVICE##_##RESULT + TRACE_CLASS_TASK)
#define TRACE_GET_QUEUE_OBJECT_EVENT_CODE(SERVICE, RESULT, pxObject) (uint8_t)(EVENTGROUP_##SERVICE##_##RESULT + TRACE_GET_OBJECT_TRACE_CLASS(QUEUE, pxObject))
#define TRACE_GET_TIMER_OBJECT_EVENT_CODE(SERVICE, RESULT, UNUSED) -- THIS IS NOT USED --
#define TRACE_GET_EVENTGROUP_OBJECT_EVENT_CODE(SERVICE, RESULT, UNUSED) -- THIS IS NOT USED --
#define TRACE_GET_STREAMBUFFER_OBJECT_EVENT_CODE(SERVICE, RESULT, pxObject) (uint8_t)(TRACE_STREAMBUFFER_##SERVICE##_##RESULT + prvGetStreamBufferType(pxObject))

/* Generic versions */
#define TRACE_GET_CLASS_EVENT_CODE(SERVICE, RESULT, CLASS, kernelClass) TRACE_GET_##CLASS##_CLASS_EVENT_CODE(SERVICE, RESULT, kernelClass)
#define TRACE_GET_OBJECT_EVENT_CODE(SERVICE, RESULT, CLASS, pxObject) TRACE_GET_##CLASS##_OBJECT_EVENT_CODE(SERVICE, RESULT, pxObject)

/******************************
* SPECIAL MACROS FOR TASKS    *
******************************/
#define TRACE_GET_TASK_PRIORITY(pxTCB) ((uint8_t)pxTCB->uxPriority)
#define TRACE_GET_TASK_NAME(pxTCB) ((char*)pxTCB->pcTaskName)

/*** The trace macros for snapshot mode **************************************/	

/* A macro that will update the tick count when returning from tickless idle */
#undef traceINCREASE_TICK_COUNT
#define traceINCREASE_TICK_COUNT( xCount ) 

/* Called for each task that becomes ready */
#undef traceMOVED_TASK_TO_READY_STATE
#define traceMOVED_TASK_TO_READY_STATE( pxTCB ) \
	trcKERNEL_HOOKS_MOVED_TASK_TO_READY_STATE(pxTCB);

/* Called on each OS tick. Will call uiPortGetTimestamp to make sure it is called at least once every OS tick. */
#undef traceTASK_INCREMENT_TICK

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_3_0)

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || xPendedTicks == 0) { trcKERNEL_HOOKS_INCREMENT_TICK(); } \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE) { trcKERNEL_HOOKS_NEW_TIME(DIV_NEW_TIME, xTickCount + 1); }
	
#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_5_X)

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxPendedTicks == 0) { trcKERNEL_HOOKS_INCREMENT_TICK(); } \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE) { trcKERNEL_HOOKS_NEW_TIME(DIV_NEW_TIME, xTickCount + 1); }

#else

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxMissedTicks == 0) { trcKERNEL_HOOKS_INCREMENT_TICK(); } \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE) { trcKERNEL_HOOKS_NEW_TIME(DIV_NEW_TIME, xTickCount + 1); }

#endif

extern volatile uint32_t uiTraceSystemState;

/* Called on each task-switch */
#undef traceTASK_SWITCHED_IN
#define traceTASK_SWITCHED_IN() \
	uiTraceSystemState = TRC_STATE_IN_TASKSWITCH; \
	trcKERNEL_HOOKS_TASK_SWITCH(TRACE_GET_CURRENT_TASK()); \
	uiTraceSystemState = TRC_STATE_IN_APPLICATION;

/* Called on vTaskCreate */
#undef traceTASK_CREATE
#define traceTASK_CREATE(pxNewTCB) \
	if (pxNewTCB != 0) \
	{ \
		trcKERNEL_HOOKS_TASK_CREATE(TRACE_GET_OBJECT_EVENT_CODE(CREATE_OBJ, TRCSUCCESS, TASK, pxNewTCB), TASK, pxNewTCB); \
		prvAddTaskToStackMonitor(pxNewTCB); \
	}

/* Called in vTaskCreate, if it fails (typically if the stack can not be allocated) */
#undef traceTASK_CREATE_FAILED
#define traceTASK_CREATE_FAILED() \
	trcKERNEL_HOOKS_OBJECT_CREATE_FAILED(TRACE_GET_CLASS_EVENT_CODE(CREATE_OBJ, TRCFAILED, TASK, NOT_USED), TRACE_GET_CLASS_TRACE_CLASS(TASK, NOT_USED))

/* Called on vTaskDelete */
#undef traceTASK_DELETE
#define traceTASK_DELETE( pxTaskToDelete ) \
	{ TRACE_ALLOC_CRITICAL_SECTION(); \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_TASK_DELETE(TRACE_GET_OBJECT_EVENT_CODE(DELETE_OBJ, TRCSUCCESS, TASK, pxTaskToDelete), TRACE_GET_OBJECT_EVENT_CODE(OBJCLOSE_NAME, TRCSUCCESS, TASK, pxTaskToDelete), TRACE_GET_OBJECT_EVENT_CODE(OBJCLOSE_PROP, TRCSUCCESS, TASK, pxTaskToDelete), pxTaskToDelete); \
	prvRemoveTaskFromStackMonitor(pxTaskToDelete); \
	TRACE_EXIT_CRITICAL_SECTION(); }

#if (TRC_CFG_SCHEDULING_ONLY == 0)

#if defined(configUSE_TICKLESS_IDLE) && (configUSE_TICKLESS_IDLE != 0)

#undef traceLOW_POWER_IDLE_BEGIN
#define traceLOW_POWER_IDLE_BEGIN() \
	{ \
		extern uint32_t trace_disable_timestamp; \
		prvTraceStoreLowPower(0); \
		trace_disable_timestamp = 1; \
	}

#undef traceLOW_POWER_IDLE_END
#define traceLOW_POWER_IDLE_END() \
	{ \
		extern uint32_t trace_disable_timestamp; \
		trace_disable_timestamp = 0; \
		prvTraceStoreLowPower(1); \
	}

#endif

/* Called on vTaskSuspend */
#undef traceTASK_SUSPEND
#define traceTASK_SUSPEND( pxTaskToSuspend ) \
	trcKERNEL_HOOKS_TASK_SUSPEND(TASK_SUSPEND, pxTaskToSuspend);

/* Called from special case with timer only */
#undef traceTASK_DELAY_SUSPEND
#define traceTASK_DELAY_SUSPEND( pxTaskToSuspend ) \
	trcKERNEL_HOOKS_TASK_SUSPEND(TASK_SUSPEND, pxTaskToSuspend); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

/* Called on vTaskDelay - note the use of FreeRTOS variable xTicksToDelay */
#undef traceTASK_DELAY
#define traceTASK_DELAY() \
	trcKERNEL_HOOKS_TASK_DELAY(TASK_DELAY, pxCurrentTCB, xTicksToDelay); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

/* Called on vTaskDelayUntil - note the use of FreeRTOS variable xTimeToWake */
#undef traceTASK_DELAY_UNTIL
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0)

#define traceTASK_DELAY_UNTIL(xTimeToWake) \
	trcKERNEL_HOOKS_TASK_DELAY(TASK_DELAY_UNTIL, pxCurrentTCB, xTimeToWake); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();
#else

#define traceTASK_DELAY_UNTIL() \
	trcKERNEL_HOOKS_TASK_DELAY(TASK_DELAY_UNTIL, pxCurrentTCB, xTimeToWake); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

#endif

/* Called in xQueueCreate, and thereby for all other object based on queues, such as semaphores. */
#undef traceQUEUE_CREATE
#define traceQUEUE_CREATE( pxNewQueue ) \
	trcKERNEL_HOOKS_OBJECT_CREATE(TRACE_GET_OBJECT_EVENT_CODE(CREATE_OBJ, TRCSUCCESS, QUEUE, pxNewQueue), QUEUE, pxNewQueue);

/* Called in xQueueCreate, if the queue creation fails */
#undef traceQUEUE_CREATE_FAILED
#define traceQUEUE_CREATE_FAILED( queueType ) \
	trcKERNEL_HOOKS_OBJECT_CREATE_FAILED(TRACE_GET_CLASS_EVENT_CODE(CREATE_OBJ, TRCFAILED, QUEUE, queueType), TRACE_GET_CLASS_TRACE_CLASS(QUEUE, queueType))

/* Called on vQueueDelete */
#undef traceQUEUE_DELETE
#define traceQUEUE_DELETE( pxQueue ) \
	{ TRACE_ALLOC_CRITICAL_SECTION(); \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_OBJECT_DELETE(TRACE_GET_OBJECT_EVENT_CODE(DELETE_OBJ, TRCSUCCESS, QUEUE, pxQueue), TRACE_GET_OBJECT_EVENT_CODE(OBJCLOSE_NAME, TRCSUCCESS, QUEUE, pxQueue), TRACE_GET_OBJECT_EVENT_CODE(OBJCLOSE_PROP, TRCSUCCESS, QUEUE, pxQueue), QUEUE, pxQueue); \
	TRACE_EXIT_CRITICAL_SECTION(); }

/* This macro is not necessary as of FreeRTOS v9.0.0 */
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0)

/* Called in xQueueCreateMutex, and thereby also from xSemaphoreCreateMutex and xSemaphoreCreateRecursiveMutex */
#undef traceCREATE_MUTEX
#define traceCREATE_MUTEX( pxNewQueue ) \
	trcKERNEL_HOOKS_OBJECT_CREATE(TRACE_GET_OBJECT_EVENT_CODE(CREATE_OBJ, TRCSUCCESS, QUEUE, pxNewQueue), QUEUE, pxNewQueue);
	
/* Called in xQueueCreateMutex when the operation fails (when memory allocation fails) */
#undef traceCREATE_MUTEX_FAILED
#define traceCREATE_MUTEX_FAILED() \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_NUMERIC_PARAM_ONLY(TRACE_GET_CLASS_EVENT_CODE(CREATE_OBJ, TRCFAILED, QUEUE, queueQUEUE_TYPE_MUTEX), 0);

#endif

/* Called when the Mutex can not be given, since not holder */
#undef traceGIVE_MUTEX_RECURSIVE_FAILED
#define traceGIVE_MUTEX_RECURSIVE_FAILED( pxMutex ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(SEND, TRCFAILED, QUEUE, pxMutex), QUEUE, pxMutex);

/* Called when a message is sent to a queue */	/* CS IS NEW ! */
#undef traceQUEUE_SEND
#define traceQUEUE_SEND( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(xCopyPosition == queueSEND_TO_BACK ? (TRACE_GET_OBJECT_EVENT_CODE(SEND, TRCSUCCESS, QUEUE, pxQueue)) : TRACE_QUEUE_SEND_TO_FRONT_TRCSUCCESS, QUEUE, pxQueue); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(QUEUE, pxQueue, TRACE_GET_OBJECT_TRACE_CLASS(QUEUE, pxQueue) == TRACE_CLASS_MUTEX ? (uint8_t)0 : (uint8_t)(pxQueue->uxMessagesWaiting + 1));

/* Called when a message is sent to a queue set */
#undef traceQUEUE_SET_SEND
#define traceQUEUE_SET_SEND( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(SEND, TRCSUCCESS, QUEUE, pxQueue), QUEUE, pxQueue); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(QUEUE, pxQueue, (uint8_t)(pxQueue->uxMessagesWaiting + 1));

/* Called when a message failed to be sent to a queue (timeout) */
#undef traceQUEUE_SEND_FAILED
#define traceQUEUE_SEND_FAILED( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(xCopyPosition == queueSEND_TO_BACK ? (TRACE_GET_OBJECT_EVENT_CODE(SEND, TRCFAILED, QUEUE, pxQueue)) : TRACE_QUEUE_SEND_TO_FRONT_TRCFAILED, QUEUE, pxQueue);

/* Called when the task is blocked due to a send operation on a full queue */
#undef traceBLOCKING_ON_QUEUE_SEND
#define traceBLOCKING_ON_QUEUE_SEND( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(xCopyPosition == queueSEND_TO_BACK ? (TRACE_GET_OBJECT_EVENT_CODE(SEND, TRCBLOCK, QUEUE, pxQueue)) : TRACE_QUEUE_SEND_TO_FRONT_TRCBLOCK, QUEUE, pxQueue);

/* Called when a message is received from a queue */
#undef traceQUEUE_RECEIVE
#define traceQUEUE_RECEIVE( pxQueue ) \
	if (isQueueReceiveHookActuallyPeek) \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(PEEK, TRCSUCCESS, QUEUE, pxQueue), QUEUE, pxQueue); \
	} \
	else \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(RECEIVE, TRCSUCCESS, QUEUE, pxQueue), QUEUE, pxQueue); \
	} \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(QUEUE, pxQueue, TRACE_GET_OBJECT_TRACE_CLASS(QUEUE, pxQueue) == TRACE_CLASS_MUTEX ? (uint8_t)TRACE_GET_TASK_NUMBER(TRACE_GET_CURRENT_TASK()) : (uint8_t)(pxQueue->uxMessagesWaiting - 1));

/* Called when a receive operation on a queue fails (timeout) */
#undef traceQUEUE_RECEIVE_FAILED
#define traceQUEUE_RECEIVE_FAILED( pxQueue ) \
	if (isQueueReceiveHookActuallyPeek) \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(PEEK, TRCFAILED, QUEUE, pxQueue), QUEUE, pxQueue); \
	} \
	else \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(RECEIVE, TRCFAILED, QUEUE, pxQueue), QUEUE, pxQueue); \
	}

/* Called when the task is blocked due to a receive operation on an empty queue */
#undef traceBLOCKING_ON_QUEUE_RECEIVE
#define traceBLOCKING_ON_QUEUE_RECEIVE( pxQueue ) \
	if (isQueueReceiveHookActuallyPeek) \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(PEEK, TRCBLOCK, QUEUE, pxQueue), QUEUE, pxQueue); \
	} \
	else \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(RECEIVE, TRCBLOCK, QUEUE, pxQueue), QUEUE, pxQueue); \
	} \
	if (TRACE_GET_OBJECT_TRACE_CLASS(QUEUE, pxQueue) != TRACE_CLASS_MUTEX) \
	{ \
		trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED(); \
	}

/* Called on xQueuePeek */
#undef traceQUEUE_PEEK
#define traceQUEUE_PEEK( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(PEEK, TRCSUCCESS, QUEUE, pxQueue), QUEUE, pxQueue);

/* Called on xQueuePeek fail/timeout (added in FreeRTOS v9.0.2) */
#undef traceQUEUE_PEEK_FAILED
#define traceQUEUE_PEEK_FAILED( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(PEEK, TRCFAILED, QUEUE, pxQueue), QUEUE, pxQueue);

/* Called on xQueuePeek blocking (added in FreeRTOS v9.0.2) */
#undef traceBLOCKING_ON_QUEUE_PEEK
#define traceBLOCKING_ON_QUEUE_PEEK( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(PEEK, TRCBLOCK, QUEUE, pxQueue), QUEUE, pxQueue); \
	if (TRACE_GET_OBJECT_TRACE_CLASS(QUEUE, pxQueue) != TRACE_CLASS_MUTEX) \
	{ \
		trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED(); \
	}

/* Called when a message is sent from interrupt context, e.g., using xQueueSendFromISR */
#undef traceQUEUE_SEND_FROM_ISR
#define traceQUEUE_SEND_FROM_ISR( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_FROM_ISR(xCopyPosition == queueSEND_TO_BACK ? (TRACE_GET_OBJECT_EVENT_CODE(SEND_FROM_ISR, TRCSUCCESS, QUEUE, pxQueue)) : TRACE_QUEUE_SEND_TO_FRONT_FROM_ISR_TRCSUCCESS, QUEUE, pxQueue); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(QUEUE, pxQueue, (uint8_t)(pxQueue->uxMessagesWaiting + 1));

/* Called when a message send from interrupt context fails (since the queue was full) */
#undef traceQUEUE_SEND_FROM_ISR_FAILED
#define traceQUEUE_SEND_FROM_ISR_FAILED( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_FROM_ISR(xCopyPosition == queueSEND_TO_BACK ? (TRACE_GET_OBJECT_EVENT_CODE(SEND_FROM_ISR, TRCFAILED, QUEUE, pxQueue)) : TRACE_QUEUE_SEND_TO_FRONT_FROM_ISR_TRCFAILED, QUEUE, pxQueue);

/* Called when a message is received in interrupt context, e.g., using xQueueReceiveFromISR */
#undef traceQUEUE_RECEIVE_FROM_ISR
#define traceQUEUE_RECEIVE_FROM_ISR( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_FROM_ISR(TRACE_GET_OBJECT_EVENT_CODE(RECEIVE_FROM_ISR, TRCSUCCESS, QUEUE, pxQueue), QUEUE, pxQueue); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(QUEUE, pxQueue, (uint8_t)(pxQueue->uxMessagesWaiting - 1));

/* Called when a message receive from interrupt context fails (since the queue was empty) */
#undef traceQUEUE_RECEIVE_FROM_ISR_FAILED
#define traceQUEUE_RECEIVE_FROM_ISR_FAILED( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_FROM_ISR(TRACE_GET_OBJECT_EVENT_CODE(RECEIVE_FROM_ISR, TRCFAILED, QUEUE, pxQueue), QUEUE, pxQueue);

#undef traceQUEUE_REGISTRY_ADD
#define traceQUEUE_REGISTRY_ADD(object, name) prvTraceSetObjectName(TRACE_GET_OBJECT_TRACE_CLASS(QUEUE, object), TRACE_GET_OBJECT_NUMBER(QUEUE, object), name);

/* Called in vTaskPrioritySet */
#undef traceTASK_PRIORITY_SET
#define traceTASK_PRIORITY_SET( pxTask, uxNewPriority ) \
	trcKERNEL_HOOKS_TASK_PRIORITY_CHANGE(TASK_PRIORITY_SET, pxTask, uxNewPriority);

/* Called in vTaskPriorityInherit, which is called by Mutex operations */
#undef traceTASK_PRIORITY_INHERIT
#define traceTASK_PRIORITY_INHERIT( pxTask, uxNewPriority ) \
	trcKERNEL_HOOKS_TASK_PRIORITY_CHANGE(TASK_PRIORITY_INHERIT, pxTask, uxNewPriority);

/* Called in vTaskPriorityDisinherit, which is called by Mutex operations */
#undef traceTASK_PRIORITY_DISINHERIT
#define traceTASK_PRIORITY_DISINHERIT( pxTask, uxNewPriority ) \
	trcKERNEL_HOOKS_TASK_PRIORITY_CHANGE(TASK_PRIORITY_DISINHERIT, pxTask, uxNewPriority);

/* Called in vTaskResume */
#undef traceTASK_RESUME
#define traceTASK_RESUME( pxTaskToResume ) \
	trcKERNEL_HOOKS_TASK_RESUME(TASK_RESUME, pxTaskToResume);

/* Called in vTaskResumeFromISR */
#undef traceTASK_RESUME_FROM_ISR
#define traceTASK_RESUME_FROM_ISR( pxTaskToResume ) \
	trcKERNEL_HOOKS_TASK_RESUME_FROM_ISR(TASK_RESUME_FROM_ISR, pxTaskToResume);


#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)

#if (TRC_CFG_INCLUDE_MEMMANG_EVENTS == 1)

extern void vTraceStoreMemMangEvent(uint32_t ecode, uint32_t address, int32_t size);

/* MALLOC and FREE are always stored, no matter if they happen inside filtered task */
#undef traceMALLOC
#define traceMALLOC( pvAddress, uiSize ) \
	if (pvAddress != 0) \
	{ \
		vTraceStoreMemMangEvent(MEM_MALLOC_SIZE, ( uint32_t ) pvAddress, (int32_t)uiSize); \
	} \
	else \
	{ \
		vTraceStoreMemMangEvent(MEM_MALLOC_SIZE_TRCFAILED, ( uint32_t ) pvAddress, (int32_t)uiSize); \
	}

#undef traceFREE
#define traceFREE( pvAddress, uiSize ) \
	vTraceStoreMemMangEvent(MEM_FREE_SIZE, ( uint32_t ) pvAddress, -((int32_t)uiSize));

#endif

#if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1)

/* Called in timer.c - xTimerCreate */
#undef traceTIMER_CREATE
#define traceTIMER_CREATE(tmr) \
	trcKERNEL_HOOKS_OBJECT_CREATE(TIMER_CREATE, TIMER, tmr);

#undef traceTIMER_CREATE_FAILED
#define traceTIMER_CREATE_FAILED() \
	trcKERNEL_HOOKS_OBJECT_CREATE_FAILED(TIMER_CREATE_TRCFAILED, TRACE_GET_CLASS_TRACE_CLASS(TIMER, NOT_USED))

/* Note that xCommandID can never be tmrCOMMAND_EXECUTE_CALLBACK (-1) since the trace macro is not called in that case */
#undef traceTIMER_COMMAND_SEND
#define traceTIMER_COMMAND_SEND(tmr, xCommandID, xOptionalValue, xReturn) \
	if (xCommandID > tmrCOMMAND_START_DONT_TRACE) \
	{ \
		if (xCommandID == tmrCOMMAND_CHANGE_PERIOD) \
		{ \
			if (xReturn == pdPASS) { \
				trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TIMER_CHANGE_PERIOD, TIMER, tmr, xOptionalValue); \
			} \
			else \
			{ \
				trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TIMER_CHANGE_PERIOD_TRCFAILED, TIMER, tmr, xOptionalValue); \
			} \
		} \
		else if ((xCommandID == tmrCOMMAND_DELETE) && (xReturn == pdPASS)) \
		{ \
			trcKERNEL_HOOKS_OBJECT_DELETE(TIMER_DELETE_OBJ, EVENTGROUP_OBJCLOSE_NAME_TRCSUCCESS + TRACE_GET_OBJECT_TRACE_CLASS(TIMER, tmr), EVENTGROUP_OBJCLOSE_PROP_TRCSUCCESS + TRACE_GET_OBJECT_TRACE_CLASS(TIMER, tmr), TIMER, tmr); \
		} \
		else \
		{ \
			trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(EVENTGROUP_TIMER + (uint32_t)xCommandID + ((xReturn == pdPASS) ? 0 : (TIMER_CREATE_TRCFAILED - TIMER_CREATE)), TIMER, tmr, xOptionalValue); \
		}\
	}

#undef traceTIMER_EXPIRED
#define traceTIMER_EXPIRED(tmr) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TIMER_EXPIRED, TIMER, tmr);

#endif

#if (TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS == 1)

#undef tracePEND_FUNC_CALL
#define tracePEND_FUNC_CALL(func, arg1, arg2, ret) \
	if (ret == pdPASS){ \
		trcKERNEL_HOOKS_KERNEL_SERVICE(PEND_FUNC_CALL, TASK, xTimerGetTimerDaemonTaskHandle() ); \
	} \
	else \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE(PEND_FUNC_CALL_TRCFAILED, TASK, xTimerGetTimerDaemonTaskHandle() ); \
	}

#undef tracePEND_FUNC_CALL_FROM_ISR
#define tracePEND_FUNC_CALL_FROM_ISR(func, arg1, arg2, ret) \
	if (! uiInEventGroupSetBitsFromISR) \
		prvTraceStoreKernelCall(PEND_FUNC_CALL_FROM_ISR, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTimerGetTimerDaemonTaskHandle()) ); \
	uiInEventGroupSetBitsFromISR = 0;

#endif

#endif

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1)

#undef traceEVENT_GROUP_CREATE
#define traceEVENT_GROUP_CREATE(eg) \
	trcKERNEL_HOOKS_OBJECT_CREATE(EVENT_GROUP_CREATE, EVENTGROUP, eg)

#undef traceEVENT_GROUP_CREATE_FAILED
#define traceEVENT_GROUP_CREATE_FAILED() \
	trcKERNEL_HOOKS_OBJECT_CREATE_FAILED(EVENT_GROUP_CREATE_TRCFAILED, TRACE_GET_CLASS_TRACE_CLASS(EVENTGROUP, NOT_USED))

#undef traceEVENT_GROUP_DELETE
#define traceEVENT_GROUP_DELETE(eg) \
	{ TRACE_ALLOC_CRITICAL_SECTION(); \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_OBJECT_DELETE(EVENT_GROUP_DELETE_OBJ, EVENTGROUP_OBJCLOSE_NAME_TRCSUCCESS + TRACE_GET_OBJECT_TRACE_CLASS(EVENTGROUP, eg), EVENTGROUP_OBJCLOSE_NAME_TRCSUCCESS + TRACE_GET_OBJECT_TRACE_CLASS(EVENTGROUP, eg), EVENTGROUP, eg); \
	TRACE_EXIT_CRITICAL_SECTION(); }

#undef traceEVENT_GROUP_SYNC_BLOCK
#define traceEVENT_GROUP_SYNC_BLOCK(eg, bitsToSet, bitsToWaitFor) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(EVENT_GROUP_SYNC_TRCBLOCK, EVENTGROUP, eg, bitsToWaitFor);

#undef traceEVENT_GROUP_SYNC_END
#define traceEVENT_GROUP_SYNC_END(eg, bitsToSet, bitsToWaitFor, wasTimeout) \
	if (wasTimeout) \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(EVENT_GROUP_SYNC_END_TRCFAILED, EVENTGROUP, eg, bitsToWaitFor); \
	} \
	else \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(EVENT_GROUP_SYNC_END, EVENTGROUP, eg, bitsToWaitFor); \
	}

#undef traceEVENT_GROUP_WAIT_BITS_BLOCK
#define traceEVENT_GROUP_WAIT_BITS_BLOCK(eg, bitsToWaitFor) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(EVENT_GROUP_WAIT_BITS_TRCBLOCK, EVENTGROUP, eg, bitsToWaitFor); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

#undef traceEVENT_GROUP_WAIT_BITS_END
#define traceEVENT_GROUP_WAIT_BITS_END(eg, bitsToWaitFor, wasTimeout) \
	if (wasTimeout) \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(EVENT_GROUP_WAIT_BITS_END_TRCFAILED, EVENTGROUP, eg, bitsToWaitFor); \
	} \
	else \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(EVENT_GROUP_WAIT_BITS_END, EVENTGROUP, eg, bitsToWaitFor); \
	}

#undef traceEVENT_GROUP_CLEAR_BITS
#define traceEVENT_GROUP_CLEAR_BITS(eg, bitsToClear) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(EVENT_GROUP_CLEAR_BITS, EVENTGROUP, eg, bitsToClear);

#undef traceEVENT_GROUP_CLEAR_BITS_FROM_ISR
#define traceEVENT_GROUP_CLEAR_BITS_FROM_ISR(eg, bitsToClear) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM_FROM_ISR(EVENT_GROUP_CLEAR_BITS_FROM_ISR, EVENTGROUP, eg, bitsToClear);

#undef traceEVENT_GROUP_SET_BITS
#define traceEVENT_GROUP_SET_BITS(eg, bitsToSet) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(EVENT_GROUP_SET_BITS, EVENTGROUP, eg, bitsToSet);

#undef traceEVENT_GROUP_SET_BITS_FROM_ISR
#define traceEVENT_GROUP_SET_BITS_FROM_ISR(eg, bitsToSet) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM_FROM_ISR(EVENT_GROUP_SET_BITS_FROM_ISR, EVENTGROUP, eg, bitsToSet); \
	uiInEventGroupSetBitsFromISR = 1;

#endif

#undef traceTASK_NOTIFY_TAKE
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0)

#define traceTASK_NOTIFY_TAKE() \
	if (pxCurrentTCB->eNotifyState == eNotified){ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE, TASK, pxCurrentTCB, xTicksToWait); \
	} \
	else{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE_TRCFAILED, TASK, pxCurrentTCB, xTicksToWait); \
	}

#elif (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY_TAKE() \
	if (pxCurrentTCB->ucNotifyState == taskNOTIFICATION_RECEIVED){ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE, TASK, pxCurrentTCB, xTicksToWait); \
	}else{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE_TRCFAILED, TASK, pxCurrentTCB, xTicksToWait);}

#else

#define traceTASK_NOTIFY_TAKE(index) \
	if (pxCurrentTCB->ucNotifyState[index] == taskNOTIFICATION_RECEIVED){ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE, TASK, pxCurrentTCB, xTicksToWait); \
	}else{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE_TRCFAILED, TASK, pxCurrentTCB, xTicksToWait);}

#endif

#undef traceTASK_NOTIFY_TAKE_BLOCK
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY_TAKE_BLOCK() \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE_TRCBLOCK, TASK, pxCurrentTCB, xTicksToWait); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

#else

#define traceTASK_NOTIFY_TAKE_BLOCK(index) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE_TRCBLOCK, TASK, pxCurrentTCB, xTicksToWait); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

#endif

#undef traceTASK_NOTIFY_WAIT
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0)

#define traceTASK_NOTIFY_WAIT() \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxCurrentTCB) & CurrentFilterMask) \
	{ \
		if (pxCurrentTCB->eNotifyState == eNotified) \
			prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
		else \
			prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT_TRCFAILED, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
	}

#elif (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY_WAIT() \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxCurrentTCB) & CurrentFilterMask) \
	{ \
		if (pxCurrentTCB->ucNotifyState == taskNOTIFICATION_RECEIVED) \
			prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
		else \
			prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT_TRCFAILED, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
	}

#else

#define traceTASK_NOTIFY_WAIT(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxCurrentTCB) & CurrentFilterMask) \
	{ \
		if (pxCurrentTCB->ucNotifyState[index] == taskNOTIFICATION_RECEIVED) \
			prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
		else \
			prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT_TRCFAILED, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
	}

#endif

#undef traceTASK_NOTIFY_WAIT_BLOCK
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY_WAIT_BLOCK() \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxCurrentTCB) & CurrentFilterMask) \
		prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT_TRCBLOCK, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

#else

#define traceTASK_NOTIFY_WAIT_BLOCK(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxCurrentTCB) & CurrentFilterMask) \
		prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT_TRCBLOCK, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

#endif

#undef traceTASK_NOTIFY
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
			prvTraceStoreKernelCall(TRACE_TASK_NOTIFY, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));

#else

#define traceTASK_NOTIFY(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
			prvTraceStoreKernelCall(TRACE_TASK_NOTIFY, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));

#endif

#undef traceTASK_NOTIFY_FROM_ISR
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY_FROM_ISR() \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreKernelCall(TRACE_TASK_NOTIFY_FROM_ISR, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));

#else

#define traceTASK_NOTIFY_FROM_ISR(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreKernelCall(TRACE_TASK_NOTIFY_FROM_ISR, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));

#endif
	
#undef traceTASK_NOTIFY_GIVE_FROM_ISR
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY_GIVE_FROM_ISR() \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreKernelCall(TRACE_TASK_NOTIFY_GIVE_FROM_ISR, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));

#else

#define traceTASK_NOTIFY_GIVE_FROM_ISR(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreKernelCall(TRACE_TASK_NOTIFY_GIVE_FROM_ISR, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));

#endif

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1)

#undef traceSTREAM_BUFFER_CREATE
#define traceSTREAM_BUFFER_CREATE( pxStreamBuffer, xIsMessageBuffer ) \
	trcKERNEL_HOOKS_OBJECT_CREATE(TRACE_GET_OBJECT_EVENT_CODE(CREATE_OBJ, TRCSUCCESS, STREAMBUFFER, pxStreamBuffer), STREAMBUFFER, pxStreamBuffer);

#undef traceSTREAM_BUFFER_CREATE_FAILED
#define traceSTREAM_BUFFER_CREATE_FAILED( xIsMessageBuffer ) \
	trcKERNEL_HOOKS_OBJECT_CREATE_FAILED(TRACE_GET_CLASS_EVENT_CODE(CREATE_OBJ, TRCFAILED, STREAMBUFFER, xIsMessageBuffer), TRACE_GET_CLASS_TRACE_CLASS(STREAMBUFFER, xIsMessageBuffer))
	
#undef traceSTREAM_BUFFER_CREATE_STATIC_FAILED
#define traceSTREAM_BUFFER_CREATE_STATIC_FAILED( xReturn, xIsMessageBuffer ) \
	traceSTREAM_BUFFER_CREATE_FAILED( xIsMessageBuffer )

#undef traceSTREAM_BUFFER_DELETE
#define traceSTREAM_BUFFER_DELETE( xStreamBuffer ) \
	trcKERNEL_HOOKS_OBJECT_DELETE(TRACE_GET_OBJECT_EVENT_CODE(DELETE_OBJ, TRCSUCCESS, STREAMBUFFER, xStreamBuffer), TRACE_GET_OBJECT_EVENT_CODE(OBJCLOSE_NAME, TRCSUCCESS, STREAMBUFFER, xStreamBuffer), TRACE_GET_OBJECT_EVENT_CODE(OBJCLOSE_PROP, TRCSUCCESS, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer);

#undef traceSTREAM_BUFFER_RESET
#define traceSTREAM_BUFFER_RESET( xStreamBuffer ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(prvGetStreamBufferType(xStreamBuffer) > 0 ? TRACE_MESSAGEBUFFER_RESET : TRACE_STREAMBUFFER_RESET, STREAMBUFFER, xStreamBuffer); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(STREAMBUFFER, xStreamBuffer, 0);

#undef traceSTREAM_BUFFER_SEND
#define traceSTREAM_BUFFER_SEND( xStreamBuffer, xReturn ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(SEND, TRCSUCCESS, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(STREAMBUFFER, xStreamBuffer, prvBytesInBuffer(xStreamBuffer));
	
#undef traceBLOCKING_ON_STREAM_BUFFER_SEND
#define traceBLOCKING_ON_STREAM_BUFFER_SEND( xStreamBuffer ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(SEND, TRCBLOCK, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer);

#undef traceSTREAM_BUFFER_SEND_FAILED
#define traceSTREAM_BUFFER_SEND_FAILED( xStreamBuffer ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(SEND, TRCFAILED, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer);

#undef traceSTREAM_BUFFER_RECEIVE
#define traceSTREAM_BUFFER_RECEIVE( xStreamBuffer, xReceivedLength ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(RECEIVE, TRCSUCCESS, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(STREAMBUFFER, xStreamBuffer, prvBytesInBuffer(xStreamBuffer));


#undef traceBLOCKING_ON_STREAM_BUFFER_RECEIVE
#define traceBLOCKING_ON_STREAM_BUFFER_RECEIVE( xStreamBuffer ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(RECEIVE, TRCBLOCK, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer);

#undef traceSTREAM_BUFFER_RECEIVE_FAILED
#define traceSTREAM_BUFFER_RECEIVE_FAILED( xStreamBuffer ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(TRACE_GET_OBJECT_EVENT_CODE(RECEIVE, TRCFAILED, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer);

#undef traceSTREAM_BUFFER_SEND_FROM_ISR
#define traceSTREAM_BUFFER_SEND_FROM_ISR( xStreamBuffer, xReturn ) \
	if( xReturn > ( size_t ) 0 ) \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_FROM_ISR(TRACE_GET_OBJECT_EVENT_CODE(SEND_FROM_ISR, TRCSUCCESS, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer); \
		trcKERNEL_HOOKS_SET_OBJECT_STATE(STREAMBUFFER, xStreamBuffer, prvBytesInBuffer(xStreamBuffer)); \
	} \
	else \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_FROM_ISR(TRACE_GET_OBJECT_EVENT_CODE(SEND_FROM_ISR, TRCFAILED, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer); \
	}

#undef traceSTREAM_BUFFER_RECEIVE_FROM_ISR
#define traceSTREAM_BUFFER_RECEIVE_FROM_ISR( xStreamBuffer, xReceivedLength ) \
	if( xReceivedLength > ( size_t ) 0 ) \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_FROM_ISR(TRACE_GET_OBJECT_EVENT_CODE(RECEIVE_FROM_ISR, TRCSUCCESS, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer); \
		trcKERNEL_HOOKS_SET_OBJECT_STATE(STREAMBUFFER, xStreamBuffer, prvBytesInBuffer(xStreamBuffer)); \
	} \
	else \
	{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_FROM_ISR(TRACE_GET_OBJECT_EVENT_CODE(RECEIVE_FROM_ISR, TRCFAILED, STREAMBUFFER, xStreamBuffer), STREAMBUFFER, xStreamBuffer); \
	}

#endif

#endif

#endif

#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

TraceHeapHandle_t xTraceKernelPortGetSystemHeapHandle(void);

/*************************************************************************/
/* KERNEL SPECIFIC OBJECT CONFIGURATION									 */
/*************************************************************************/

/*******************************************************************************
 * The event codes - should match the offline config file.
 ******************************************************************************/

/*** Event codes for streaming - should match the Tracealyzer config file *****/
#define PSF_EVENT_NULL_EVENT								0x00

#define PSF_EVENT_TRACE_START								0x01
#define PSF_EVENT_TS_CONFIG									0x02
#define PSF_EVENT_OBJ_NAME									0x03
#define PSF_EVENT_TASK_PRIORITY								0x04
#define PSF_EVENT_TASK_PRIO_INHERIT							0x05
#define PSF_EVENT_TASK_PRIO_DISINHERIT						0x06
#define PSF_EVENT_DEFINE_ISR								0x07

#define PSF_EVENT_TASK_CREATE								0x10
#define PSF_EVENT_QUEUE_CREATE								0x11
#define PSF_EVENT_SEMAPHORE_BINARY_CREATE					0x12
#define PSF_EVENT_MUTEX_CREATE								0x13
#define PSF_EVENT_TIMER_CREATE								0x14
#define PSF_EVENT_EVENTGROUP_CREATE							0x15
#define PSF_EVENT_SEMAPHORE_COUNTING_CREATE					0x16
#define PSF_EVENT_MUTEX_RECURSIVE_CREATE					0x17
#define PSF_EVENT_STREAMBUFFER_CREATE						0x18
#define PSF_EVENT_MESSAGEBUFFER_CREATE						0x19

#define PSF_EVENT_TASK_DELETE								0x20
#define PSF_EVENT_QUEUE_DELETE								0x21
#define PSF_EVENT_SEMAPHORE_DELETE							0x22
#define PSF_EVENT_MUTEX_DELETE								0x23
#define PSF_EVENT_TIMER_DELETE								0x24
#define PSF_EVENT_EVENTGROUP_DELETE							0x25
#define PSF_EVENT_STREAMBUFFER_DELETE						0x28
#define PSF_EVENT_MESSAGEBUFFER_DELETE						0x29

#define PSF_EVENT_TASK_READY								0x30
#define PSF_EVENT_NEW_TIME									0x31
#define PSF_EVENT_NEW_TIME_SCHEDULER_SUSPENDED				0x32
#define PSF_EVENT_ISR_BEGIN									0x33
#define PSF_EVENT_ISR_RESUME								0x34
#define PSF_EVENT_TS_BEGIN									0x35
#define PSF_EVENT_TS_RESUME									0x36
#define PSF_EVENT_TASK_ACTIVATE								0x37

#define PSF_EVENT_MALLOC									0x38
#define PSF_EVENT_FREE										0x39

#define PSF_EVENT_LOWPOWER_BEGIN							0x3A
#define PSF_EVENT_LOWPOWER_END								0x3B

#define PSF_EVENT_IFE_NEXT									0x3C
#define PSF_EVENT_IFE_DIRECT								0x3D

#define PSF_EVENT_TASK_CREATE_FAILED						0x40
#define PSF_EVENT_QUEUE_CREATE_FAILED						0x41
#define PSF_EVENT_SEMAPHORE_BINARY_CREATE_FAILED			0x42
#define PSF_EVENT_MUTEX_CREATE_FAILED						0x43
#define PSF_EVENT_TIMER_CREATE_FAILED						0x44
#define PSF_EVENT_EVENTGROUP_CREATE_FAILED					0x45
#define PSF_EVENT_SEMAPHORE_COUNTING_CREATE_FAILED			0x46
#define PSF_EVENT_MUTEX_RECURSIVE_CREATE_FAILED				0x47
#define PSF_EVENT_STREAMBUFFER_CREATE_FAILED				0x49
#define PSF_EVENT_MESSAGEBUFFER_CREATE_FAILED				0x4A

#define PSF_EVENT_TIMER_DELETE_FAILED						0x48

#define PSF_EVENT_QUEUE_SEND								0x50
#define PSF_EVENT_SEMAPHORE_GIVE							0x51
#define PSF_EVENT_MUTEX_GIVE								0x52

#define PSF_EVENT_QUEUE_SEND_FAILED							0x53
#define PSF_EVENT_SEMAPHORE_GIVE_FAILED						0x54
#define PSF_EVENT_MUTEX_GIVE_FAILED							0x55

#define PSF_EVENT_QUEUE_SEND_BLOCK							0x56
#define PSF_EVENT_SEMAPHORE_GIVE_BLOCK						0x57
#define PSF_EVENT_MUTEX_GIVE_BLOCK							0x58

#define PSF_EVENT_QUEUE_SEND_FROMISR						0x59
#define PSF_EVENT_SEMAPHORE_GIVE_FROMISR					0x5A

#define PSF_EVENT_QUEUE_SEND_FROMISR_FAILED					0x5C
#define PSF_EVENT_SEMAPHORE_GIVE_FROMISR_FAILED				0x5D

#define PSF_EVENT_QUEUE_RECEIVE								0x60
#define PSF_EVENT_SEMAPHORE_TAKE							0x61
#define PSF_EVENT_MUTEX_TAKE								0x62

#define PSF_EVENT_QUEUE_RECEIVE_FAILED						0x63
#define PSF_EVENT_SEMAPHORE_TAKE_FAILED						0x64
#define PSF_EVENT_MUTEX_TAKE_FAILED							0x65

#define PSF_EVENT_QUEUE_RECEIVE_BLOCK						0x66
#define PSF_EVENT_SEMAPHORE_TAKE_BLOCK						0x67
#define PSF_EVENT_MUTEX_TAKE_BLOCK							0x68

#define PSF_EVENT_QUEUE_RECEIVE_FROMISR						0x69
#define PSF_EVENT_SEMAPHORE_TAKE_FROMISR					0x6A

#define PSF_EVENT_QUEUE_RECEIVE_FROMISR_FAILED				0x6C
#define PSF_EVENT_SEMAPHORE_TAKE_FROMISR_FAILED				0x6D

#define PSF_EVENT_QUEUE_PEEK								0x70
#define PSF_EVENT_SEMAPHORE_PEEK							0x71
#define PSF_EVENT_MUTEX_PEEK								0x72

#define PSF_EVENT_QUEUE_PEEK_FAILED							0x73
#define PSF_EVENT_SEMAPHORE_PEEK_FAILED						0x74	
#define PSF_EVENT_MUTEX_PEEK_FAILED							0x75

#define PSF_EVENT_QUEUE_PEEK_BLOCK							0x76
#define PSF_EVENT_SEMAPHORE_PEEK_BLOCK						0x77
#define PSF_EVENT_MUTEX_PEEK_BLOCK							0x78

#define PSF_EVENT_TASK_DELAY_UNTIL							0x79
#define PSF_EVENT_TASK_DELAY								0x7A
#define PSF_EVENT_TASK_SUSPEND								0x7B
#define PSF_EVENT_TASK_RESUME								0x7C
#define PSF_EVENT_TASK_RESUME_FROMISR						0x7D

#define PSF_EVENT_TIMER_PENDFUNCCALL						0x80
#define PSF_EVENT_TIMER_PENDFUNCCALL_FROMISR				0x81
#define PSF_EVENT_TIMER_PENDFUNCCALL_FAILED					0x82
#define PSF_EVENT_TIMER_PENDFUNCCALL_FROMISR_FAILED			0x83

#define PSF_EVENT_USER_EVENT								0x90

#define PSF_EVENT_TIMER_START								0xA0
#define PSF_EVENT_TIMER_RESET								0xA1
#define PSF_EVENT_TIMER_STOP								0xA2
#define PSF_EVENT_TIMER_CHANGEPERIOD						0xA3
#define PSF_EVENT_TIMER_START_FROMISR						0xA4
#define PSF_EVENT_TIMER_RESET_FROMISR						0xA5
#define PSF_EVENT_TIMER_STOP_FROMISR						0xA6
#define PSF_EVENT_TIMER_CHANGEPERIOD_FROMISR				0xA7
#define PSF_EVENT_TIMER_START_FAILED						0xA8
#define PSF_EVENT_TIMER_RESET_FAILED						0xA9
#define PSF_EVENT_TIMER_STOP_FAILED							0xAA
#define PSF_EVENT_TIMER_CHANGEPERIOD_FAILED					0xAB
#define PSF_EVENT_TIMER_START_FROMISR_FAILED				0xAC
#define PSF_EVENT_TIMER_RESET_FROMISR_FAILED				0xAD
#define PSF_EVENT_TIMER_STOP_FROMISR_FAILED					0xAE
#define PSF_EVENT_TIMER_CHANGEPERIOD_FROMISR_FAILED			0xAF

#define PSF_EVENT_EVENTGROUP_SYNC							0xB0
#define PSF_EVENT_EVENTGROUP_WAITBITS						0xB1
#define PSF_EVENT_EVENTGROUP_CLEARBITS						0xB2
#define PSF_EVENT_EVENTGROUP_CLEARBITS_FROMISR				0xB3
#define PSF_EVENT_EVENTGROUP_SETBITS						0xB4
#define PSF_EVENT_EVENTGROUP_SETBITS_FROMISR				0xB5
#define PSF_EVENT_EVENTGROUP_SYNC_BLOCK						0xB6
#define PSF_EVENT_EVENTGROUP_WAITBITS_BLOCK					0xB7
#define PSF_EVENT_EVENTGROUP_SYNC_FAILED					0xB8
#define PSF_EVENT_EVENTGROUP_WAITBITS_FAILED				0xB9

#define PSF_EVENT_QUEUE_SEND_FRONT							0xC0
#define PSF_EVENT_QUEUE_SEND_FRONT_FAILED					0xC1
#define PSF_EVENT_QUEUE_SEND_FRONT_BLOCK					0xC2
#define PSF_EVENT_QUEUE_SEND_FRONT_FROMISR					0xC3
#define PSF_EVENT_QUEUE_SEND_FRONT_FROMISR_FAILED			0xC4
#define PSF_EVENT_MUTEX_GIVE_RECURSIVE						0xC5
#define PSF_EVENT_MUTEX_GIVE_RECURSIVE_FAILED				0xC6
#define PSF_EVENT_MUTEX_TAKE_RECURSIVE						0xC7
#define PSF_EVENT_MUTEX_TAKE_RECURSIVE_FAILED				0xC8

#define PSF_EVENT_TASK_NOTIFY								0xC9
#define PSF_EVENT_TASK_NOTIFY_WAIT							0xCA
#define PSF_EVENT_TASK_NOTIFY_WAIT_BLOCK					0xCB
#define PSF_EVENT_TASK_NOTIFY_WAIT_FAILED					0xCC
#define PSF_EVENT_TASK_NOTIFY_FROM_ISR						0xCD

#define PSF_EVENT_TIMER_EXPIRED								0xD2

#define PSF_EVENT_STREAMBUFFER_SEND							0xD3
#define PSF_EVENT_STREAMBUFFER_SEND_BLOCK					0xD4
#define PSF_EVENT_STREAMBUFFER_SEND_FAILED					0xD5
#define PSF_EVENT_STREAMBUFFER_RECEIVE						0xD6
#define PSF_EVENT_STREAMBUFFER_RECEIVE_BLOCK				0xD7
#define PSF_EVENT_STREAMBUFFER_RECEIVE_FAILED				0xD8
#define PSF_EVENT_STREAMBUFFER_SEND_FROM_ISR				0xD9
#define PSF_EVENT_STREAMBUFFER_SEND_FROM_ISR_FAILED			0xDA
#define PSF_EVENT_STREAMBUFFER_RECEIVE_FROM_ISR				0xDB
#define PSF_EVENT_STREAMBUFFER_RECEIVE_FROM_ISR_FAILED		0xDC
#define PSF_EVENT_STREAMBUFFER_RESET						0xDD

#define PSF_EVENT_MESSAGEBUFFER_SEND						0xDE
#define PSF_EVENT_MESSAGEBUFFER_SEND_BLOCK					0xDF
#define PSF_EVENT_MESSAGEBUFFER_SEND_FAILED					0xE0
#define PSF_EVENT_MESSAGEBUFFER_RECEIVE						0xE1
#define PSF_EVENT_MESSAGEBUFFER_RECEIVE_BLOCK				0xE2
#define PSF_EVENT_MESSAGEBUFFER_RECEIVE_FAILED				0xE3
#define PSF_EVENT_MESSAGEBUFFER_SEND_FROM_ISR				0xE4
#define PSF_EVENT_MESSAGEBUFFER_SEND_FROM_ISR_FAILED		0xE5
#define PSF_EVENT_MESSAGEBUFFER_RECEIVE_FROM_ISR			0xE6
#define PSF_EVENT_MESSAGEBUFFER_RECEIVE_FROM_ISR_FAILED		0xE7
#define PSF_EVENT_MESSAGEBUFFER_RESET						0xE8

#define PSF_EVENT_MALLOC_FAILED								0xE9
#define PSF_EVENT_FREE_FAILED								0xEA

#define PSF_EVENT_UNUSED_STACK								0xEB

#define PSF_EVENT_STATEMACHINE_STATE_CREATE					0xEC
#define PSF_EVENT_STATEMACHINE_CREATE						0xED
#define PSF_EVENT_STATEMACHINE_STATECHANGE					0xEE

#define PSF_EVENT_INTERVAL_CREATE							0xEF
#define PSF_EVENT_INTERVAL_STATECHANGE						0xF0

#define PSF_EVENT_EXTENSION_CREATE							0xF1

#define PSF_EVENT_HEAP_CREATE								0xF2

#define PSF_EVENT_COUNTER_CREATE							0xF3
#define PSF_EVENT_COUNTER_CHANGE							0xF4
#define PSF_EVENT_COUNTER_LIMIT_EXCEEDED					0xF5

#define PSF_EVENT_MUTEX_TAKE_RECURSIVE_BLOCK				0xF6

#define TRC_EVENT_LAST_ID									PSF_EVENT_COUNTER_LIMIT_EXCEEDED

/*** The trace macros for streaming ******************************************/

/* A macro that will update the tick count when returning from tickless idle */
#undef traceINCREASE_TICK_COUNT
/* Note: This can handle time adjustments of max 2^32 ticks, i.e., 35 seconds at 120 MHz. Thus, tick-less idle periods longer than 2^32 ticks will appear "compressed" on the time line.*/
#define traceINCREASE_TICK_COUNT( xCount ) { uint32_t uiTraceTickCount; xTraceTimestampGetOsTickCount(&uiTraceTickCount); xTraceTimestampSetOsTickCount(uiTraceTickCount + (xCount)); }

#if (TRC_CFG_INCLUDE_OSTICK_EVENTS == 1)

#define OS_TICK_EVENT(uxSchedulerSuspended, xTickCount) if ((uxSchedulerSuspended) == (unsigned portBASE_TYPE) pdFALSE) { prvTraceStoreEvent_Param(PSF_EVENT_NEW_TIME, (uint32_t)(xTickCount)); }

#else

#define OS_TICK_EVENT(uxSchedulerSuspended, xTickCount)

#endif

/* Called on each OS tick. Will call uiPortGetTimestamp to make sure it is called at least once every OS tick. */
#undef traceTASK_INCREMENT_TICK
#if TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_3_0

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || xPendedTicks == 0) { xTraceTimestampSetOsTickCount((xTickCount) + 1); } \
	OS_TICK_EVENT(uxSchedulerSuspended, (xTickCount) + 1)

#elif TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_5_X

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxPendedTicks == 0) { xTraceTimestampSetOsTickCount(xTickCount + 1); } \
	OS_TICK_EVENT(uxSchedulerSuspended, xTickCount + 1)

#else

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxMissedTicks == 0) { xTraceTimestampSetOsTickCount(xTickCount + 1); } \
	OS_TICK_EVENT(uxSchedulerSuspended, xTickCount + 1)

#endif

/* Called on each task-switch */
#undef traceTASK_SWITCHED_IN
#define traceTASK_SWITCHED_IN() \
	xTraceTaskSwitch(pxCurrentTCB, pxCurrentTCB->uxPriority)

/* Called for each task that becomes ready */
#undef traceMOVED_TASK_TO_READY_STATE
#define traceMOVED_TASK_TO_READY_STATE( pxTCB ) \
	xTraceTaskReady(pxTCB)

#undef traceTASK_CREATE
#if TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0

#define traceTASK_CREATE(pxNewTCB) \
	if ((pxNewTCB) != 0) \
	{ \
		xTraceTaskRegisterWithoutHandle((void*)(pxNewTCB), (pxNewTCB)->pcTaskName, (pxNewTCB)->uxPriority); \
	}

#else

#define traceTASK_CREATE(pxNewTCB) \
	if (pxNewTCB != 0) \
	{ \
		xTraceTaskRegisterWithoutHandle((void*)pxNewTCB, (const char*)pcName, (uint32_t)uxPriority); \
	}

#endif

/* Called in vTaskCreate, if it fails (typically if the stack can not be allocated) */
#undef traceTASK_CREATE_FAILED
#define traceTASK_CREATE_FAILED() \
	prvTraceStoreEvent_None(PSF_EVENT_TASK_CREATE_FAILED)

/* Called on vTaskDelete */
#undef traceTASK_DELETE				// We don't allow for filtering out "delete" events. They are important and not very frequent. Moreover, we can't exclude create events, so this should be symmetrical.
#define traceTASK_DELETE( pxTaskToDelete ) \
	xTraceTaskUnregisterWithoutHandle(pxTaskToDelete, (pxTaskToDelete)->uxPriority)

#if (TRC_CFG_SCHEDULING_ONLY == 0)

#if (defined(configUSE_TICKLESS_IDLE) && configUSE_TICKLESS_IDLE != 0)

#undef traceLOW_POWER_IDLE_BEGIN
#define traceLOW_POWER_IDLE_BEGIN() \
	prvTraceStoreEvent_Param(PSF_EVENT_LOWPOWER_BEGIN, xExpectedIdleTime)

#undef traceLOW_POWER_IDLE_END
#define traceLOW_POWER_IDLE_END() \
	prvTraceStoreEvent_None(PSF_EVENT_LOWPOWER_END)

#endif

/* Called on vTaskSuspend */
#undef traceTASK_SUSPEND
#define traceTASK_SUSPEND( pxTaskToSuspend ) \
	prvTraceStoreEvent_Handle(PSF_EVENT_TASK_SUSPEND, pxTaskToSuspend)

/* Called on vTaskDelay - note the use of FreeRTOS variable xTicksToDelay */
#undef traceTASK_DELAY
#define traceTASK_DELAY() \
	prvTraceStoreEvent_Param(PSF_EVENT_TASK_DELAY, xTicksToDelay)

/* Called on vTaskDelayUntil - note the use of FreeRTOS variable xTimeToWake */
#undef traceTASK_DELAY_UNTIL
#if TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0

#define traceTASK_DELAY_UNTIL(xTimeToWake) \
	prvTraceStoreEvent_Param(PSF_EVENT_TASK_DELAY_UNTIL, (xTimeToWake))

#else

#define traceTASK_DELAY_UNTIL() \
	prvTraceStoreEvent_Param(PSF_EVENT_TASK_DELAY_UNTIL, xTimeToWake)

#endif

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0)

#define traceQUEUE_CREATE_HELPER() \
		case queueQUEUE_TYPE_MUTEX: \
			xTraceObjectRegisterWithoutHandle(PSF_EVENT_MUTEX_CREATE, (void*)pxNewQueue, "", 0); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			xTraceObjectRegisterWithoutHandle(PSF_EVENT_MUTEX_RECURSIVE_CREATE, (void*)pxNewQueue, "", 0); \
			break;

#else

#define traceQUEUE_CREATE_HELPER()

#endif

/* Called in xQueueCreate, and thereby for all other object based on queues, such as semaphores. */
#undef traceQUEUE_CREATE
#define traceQUEUE_CREATE( pxNewQueue )\
	switch ((pxNewQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			xTraceObjectRegisterWithoutHandle(PSF_EVENT_QUEUE_CREATE, (void*)(pxNewQueue), "", (uint32_t)uxQueueLength); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
			xTraceObjectRegisterWithoutHandle(PSF_EVENT_SEMAPHORE_BINARY_CREATE, (void*)(pxNewQueue), "", 0); \
			break; \
		traceQUEUE_CREATE_HELPER() \
	}

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0)

#define traceQUEUE_CREATE_FAILED_HELPER() \
		case queueQUEUE_TYPE_MUTEX: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_MUTEX_CREATE_FAILED, 0, 0); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_MUTEX_RECURSIVE_CREATE_FAILED, 0, 0); \
			break;

#else

#define traceQUEUE_CREATE_FAILED_HELPER()

#endif

/* Called in xQueueCreate, if the queue creation fails */
#undef traceQUEUE_CREATE_FAILED
#define traceQUEUE_CREATE_FAILED( queueType ) \
	switch (queueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_QUEUE_CREATE_FAILED, 0, uxQueueLength); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_BINARY_CREATE_FAILED, 0, 0); \
			break; \
		traceQUEUE_CREATE_FAILED_HELPER() \
	}

#undef traceQUEUE_DELETE			// We don't allow for filtering out "delete" events. They are important and not very frequent. Moreover, we can't exclude create events, so this should be symmetrical.
#define traceQUEUE_DELETE( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			xTraceObjectUnregisterWithoutHandle(PSF_EVENT_QUEUE_DELETE, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			xTraceObjectUnregisterWithoutHandle(PSF_EVENT_MUTEX_DELETE, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
			xTraceObjectUnregisterWithoutHandle(PSF_EVENT_SEMAPHORE_DELETE, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
	}

/* Called in xQueueCreateCountingSemaphore, if the queue creation fails */
#undef traceCREATE_COUNTING_SEMAPHORE
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)

#define traceCREATE_COUNTING_SEMAPHORE() \
	xTraceObjectRegisterWithoutHandle(PSF_EVENT_SEMAPHORE_COUNTING_CREATE, (void*)xHandle, "", (uint32_t)uxMaxCount)

#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_5_X)

#define traceCREATE_COUNTING_SEMAPHORE() \
	xTraceObjectRegisterWithoutHandle(PSF_EVENT_SEMAPHORE_COUNTING_CREATE, (void*)xHandle, "", uxInitialCount)

#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_4_X)

#define traceCREATE_COUNTING_SEMAPHORE() \
	xTraceObjectRegisterWithoutHandle(PSF_EVENT_SEMAPHORE_COUNTING_CREATE, (void*)xHandle, "", uxCountValue)

#else

#define traceCREATE_COUNTING_SEMAPHORE() \
	xTraceObjectRegisterWithoutHandle(PSF_EVENT_SEMAPHORE_COUNTING_CREATE, (void*)pxHandle, "", uxCountValue)

#endif

#undef traceCREATE_COUNTING_SEMAPHORE_FAILED
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)

#define traceCREATE_COUNTING_SEMAPHORE_FAILED() \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_COUNTING_CREATE_FAILED, 0, uxMaxCount)

#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_5_X)

#define traceCREATE_COUNTING_SEMAPHORE_FAILED() \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_COUNTING_CREATE_FAILED, 0, uxInitialCount)

#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_4_X)

#define traceCREATE_COUNTING_SEMAPHORE_FAILED() \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_COUNTING_CREATE_FAILED, 0, uxCountValue)

#else

#define traceCREATE_COUNTING_SEMAPHORE_FAILED() \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_COUNTING_CREATE_FAILED, 0, uxCountValue)

#endif


/* This macro is not necessary as of FreeRTOS v9.0.0 */
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0)

/* Called in xQueueCreateMutex, and thereby also from xSemaphoreCreateMutex and xSemaphoreCreateRecursiveMutex */
#undef traceCREATE_MUTEX
#define traceCREATE_MUTEX( pxNewQueue ) \
	switch (pxNewQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_MUTEX: \
			xTraceObjectRegisterWithoutHandle(PSF_EVENT_MUTEX_CREATE, (void*)(pxNewQueue), "", 0); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			xTraceObjectRegisterWithoutHandle(PSF_EVENT_MUTEX_RECURSIVE_CREATE, (void*)(pxNewQueue), "", 0); \
			break; \
	}

/* Called in xQueueCreateMutex when the operation fails (when memory allocation fails) */
#undef traceCREATE_MUTEX_FAILED
#define traceCREATE_MUTEX_FAILED() \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_MUTEX_CREATE_FAILED, 0, 0)
#endif /* (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0) */

/* Called when the Mutex can not be given, since not holder */
#undef traceGIVE_MUTEX_RECURSIVE_FAILED
#define traceGIVE_MUTEX_RECURSIVE_FAILED( pxMutex ) \
	prvTraceStoreEvent_Handle(PSF_EVENT_MUTEX_GIVE_RECURSIVE_FAILED, (void*)(pxMutex))

/* Called when a message is sent to a queue */	/* CS IS NEW ! */
#undef traceQUEUE_SEND
#define traceQUEUE_SEND( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParam(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND : PSF_EVENT_QUEUE_SEND_FRONT, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting + 1); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_GIVE, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting + 1); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
			prvTraceStoreEvent_Handle(PSF_EVENT_MUTEX_GIVE, (void*)(pxQueue)); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent_Handle(PSF_EVENT_MUTEX_GIVE_RECURSIVE, (void*)(pxQueue)); \
			break; \
	}

#undef traceQUEUE_SET_SEND
#define traceQUEUE_SET_SEND( pxQueue ) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_QUEUE_SEND, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting + 1)

/* Called when a message failed to be sent to a queue (timeout) */
#undef traceQUEUE_SEND_FAILED
#define traceQUEUE_SEND_FAILED( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParam(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_FAILED : PSF_EVENT_QUEUE_SEND_FRONT_FAILED, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_GIVE_FAILED, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent_Handle(PSF_EVENT_MUTEX_GIVE_FAILED, (void*)(pxQueue)); \
			break; \
	}

/* Called when the task is blocked due to a send operation on a full queue */
#undef traceBLOCKING_ON_QUEUE_SEND
#define traceBLOCKING_ON_QUEUE_SEND( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParam(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_BLOCK : PSF_EVENT_QUEUE_SEND_FRONT_BLOCK, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_GIVE_BLOCK, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent_Handle(PSF_EVENT_MUTEX_GIVE_BLOCK, (void*)(pxQueue)); \
			break; \
	}

/* Called when a message is sent from interrupt context, e.g., using xQueueSendFromISR */
#undef traceQUEUE_SEND_FROM_ISR
#define traceQUEUE_SEND_FROM_ISR( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParam(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_FROMISR : PSF_EVENT_QUEUE_SEND_FRONT_FROMISR, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting + 1); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_GIVE_FROMISR, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting + 1); \
			break; \
	}

/* Called when a message send from interrupt context fails (since the queue was full) */
#undef traceQUEUE_SEND_FROM_ISR_FAILED
#define traceQUEUE_SEND_FROM_ISR_FAILED( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParam(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_FROMISR_FAILED : PSF_EVENT_QUEUE_SEND_FRONT_FROMISR_FAILED, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_GIVE_FROMISR_FAILED, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
	}

/* Called when a message is received from a queue */
#undef traceQUEUE_RECEIVE
#define traceQUEUE_RECEIVE( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			if (isQueueReceiveHookActuallyPeek) \
			{ \
				prvTraceStoreEvent_HandleParamParam(PSF_EVENT_QUEUE_PEEK, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting - 1); \
			} \
			else\
			{ \
				prvTraceStoreEvent_HandleParamParam(PSF_EVENT_QUEUE_RECEIVE, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting - 1); \
			} \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			if (isQueueReceiveHookActuallyPeek) \
			{ \
				prvTraceStoreEvent_HandleParamParam(PSF_EVENT_SEMAPHORE_PEEK, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting - 1); \
			} \
			else \
			{ \
				prvTraceStoreEvent_HandleParamParam(PSF_EVENT_SEMAPHORE_TAKE, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting - 1); \
			} \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
			prvTraceStoreEvent_HandleParam(isQueueReceiveHookActuallyPeek ? PSF_EVENT_MUTEX_PEEK : PSF_EVENT_MUTEX_TAKE, (void*)(pxQueue), xTicksToWait); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent_HandleParam(isQueueReceiveHookActuallyPeek ? PSF_EVENT_MUTEX_PEEK : PSF_EVENT_MUTEX_TAKE_RECURSIVE, (void*)(pxQueue), xTicksToWait); \
			break; \
	}

/* Called when a receive operation on a queue fails (timeout) */
#undef traceQUEUE_RECEIVE_FAILED
#define traceQUEUE_RECEIVE_FAILED( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParamParam(isQueueReceiveHookActuallyPeek ? PSF_EVENT_QUEUE_PEEK_FAILED : PSF_EVENT_QUEUE_RECEIVE_FAILED, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParamParam(isQueueReceiveHookActuallyPeek ? PSF_EVENT_SEMAPHORE_PEEK_FAILED : PSF_EVENT_SEMAPHORE_TAKE_FAILED, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
			prvTraceStoreEvent_HandleParam(isQueueReceiveHookActuallyPeek ? PSF_EVENT_MUTEX_PEEK_FAILED : PSF_EVENT_MUTEX_TAKE_FAILED, (void*)(pxQueue), xTicksToWait); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent_HandleParam(isQueueReceiveHookActuallyPeek ? PSF_EVENT_MUTEX_PEEK_FAILED : PSF_EVENT_MUTEX_TAKE_RECURSIVE_FAILED, (void*)(pxQueue), xTicksToWait); \
			break; \
	}

/* Called when the task is blocked due to a receive operation on an empty queue */
#undef traceBLOCKING_ON_QUEUE_RECEIVE
#define traceBLOCKING_ON_QUEUE_RECEIVE( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParamParam(isQueueReceiveHookActuallyPeek ? PSF_EVENT_QUEUE_PEEK_BLOCK : PSF_EVENT_QUEUE_RECEIVE_BLOCK, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParamParam(isQueueReceiveHookActuallyPeek ? PSF_EVENT_SEMAPHORE_PEEK_BLOCK : PSF_EVENT_SEMAPHORE_TAKE_BLOCK, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
			prvTraceStoreEvent_HandleParam(isQueueReceiveHookActuallyPeek ? PSF_EVENT_MUTEX_PEEK_BLOCK : PSF_EVENT_MUTEX_TAKE_BLOCK, (void*)(pxQueue), xTicksToWait); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent_HandleParam(isQueueReceiveHookActuallyPeek ? PSF_EVENT_MUTEX_PEEK_BLOCK : PSF_EVENT_MUTEX_TAKE_RECURSIVE_BLOCK, (void*)(pxQueue), xTicksToWait); \
			break; \
	}

#if (TRC_CFG_FREERTOS_VERSION > TRC_FREERTOS_VERSION_9_0_1)

/* Called when a peek operation on a queue fails (timeout) */
#undef traceQUEUE_PEEK_FAILED
#define traceQUEUE_PEEK_FAILED( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParamParam(PSF_EVENT_QUEUE_PEEK_FAILED, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParamParam(PSF_EVENT_SEMAPHORE_PEEK_FAILED, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_MUTEX_PEEK_FAILED, (void*)(pxQueue), xTicksToWait); \
			break; \
	}

/* Called when the task is blocked due to a peek operation on an empty queue */
#undef traceBLOCKING_ON_QUEUE_PEEK
#define traceBLOCKING_ON_QUEUE_PEEK( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParamParam(PSF_EVENT_QUEUE_PEEK_BLOCK, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParamParam(PSF_EVENT_SEMAPHORE_PEEK_BLOCK, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_MUTEX_PEEK_BLOCK, (void*)(pxQueue), xTicksToWait); \
			break; \
	}

#endif

/* Called when a message is received in interrupt context, e.g., using xQueueReceiveFromISR */
#undef traceQUEUE_RECEIVE_FROM_ISR
#define traceQUEUE_RECEIVE_FROM_ISR( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_QUEUE_RECEIVE_FROMISR, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting - 1); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_TAKE_FROMISR, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting - 1); \
			break; \
	}

/* Called when a message receive from interrupt context fails (since the queue was empty) */
#undef traceQUEUE_RECEIVE_FROM_ISR_FAILED
#define traceQUEUE_RECEIVE_FROM_ISR_FAILED( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_QUEUE_RECEIVE_FROMISR_FAILED, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_SEMAPHORE_TAKE_FROMISR_FAILED, (void*)(pxQueue), (pxQueue)->uxMessagesWaiting); \
			break; \
	}

/* Called on xQueuePeek */
#undef traceQUEUE_PEEK
#define traceQUEUE_PEEK( pxQueue ) \
	switch ((pxQueue)->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			prvTraceStoreEvent_HandleParamParam(PSF_EVENT_QUEUE_PEEK, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			prvTraceStoreEvent_HandleParamParam(PSF_EVENT_SEMAPHORE_PEEK, (void*)(pxQueue), xTicksToWait, (pxQueue)->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent_HandleParam(PSF_EVENT_MUTEX_PEEK, (void*)(pxQueue), xTicksToWait); \
			break; \
	}

/* Called in vTaskPrioritySet */
#undef traceTASK_PRIORITY_SET
#define traceTASK_PRIORITY_SET( pxTask, uxNewPriority ) \
	xTraceTaskSetPriorityWithoutHandle(pxTask, uxNewPriority)
	
/* Called in vTaskPriorityInherit, which is called by Mutex operations */
#undef traceTASK_PRIORITY_INHERIT
#define traceTASK_PRIORITY_INHERIT( pxTask, uxNewPriority ) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_TASK_PRIO_INHERIT, (void*)(pxTask), uxNewPriority)

/* Called in vTaskPriorityDisinherit, which is called by Mutex operations */
#undef traceTASK_PRIORITY_DISINHERIT
#define traceTASK_PRIORITY_DISINHERIT( pxTask, uxNewPriority ) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_TASK_PRIO_DISINHERIT, (void*)(pxTask), uxNewPriority)

/* Called in vTaskResume */
#undef traceTASK_RESUME
#define traceTASK_RESUME( pxTaskToResume ) \
	prvTraceStoreEvent_Handle(PSF_EVENT_TASK_RESUME, (void*)(pxTaskToResume))

/* Called in vTaskResumeFromISR */
#undef traceTASK_RESUME_FROM_ISR
#define traceTASK_RESUME_FROM_ISR( pxTaskToResume ) \
	prvTraceStoreEvent_Handle(PSF_EVENT_TASK_RESUME_FROMISR, (void*)(pxTaskToResume))

#if (TRC_CFG_INCLUDE_MEMMANG_EVENTS == 1)

#undef traceMALLOC
#define traceMALLOC( pvAddress, uiSize ) \
	if (xTraceIsRecorderEnabled()) \
	{ \
		xTraceHeapAlloc(xTraceKernelPortGetSystemHeapHandle(), pvAddress, uiSize); \
	}

#undef traceFREE
#define traceFREE( pvAddress, uiSize ) \
	if (xTraceIsRecorderEnabled()) \
	{ \
		xTraceHeapFree(xTraceKernelPortGetSystemHeapHandle(), pvAddress, uiSize); \
	}

#endif

#if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1)

/* Called in timer.c - xTimerCreate */
#undef traceTIMER_CREATE
#define traceTIMER_CREATE(tmr) \
	xTraceObjectRegisterWithoutHandle(PSF_EVENT_TIMER_CREATE, (void*)(tmr), (const char*)(tmr)->pcTimerName, (uint32_t)(tmr)->xTimerPeriodInTicks)

#undef traceTIMER_CREATE_FAILED
#define traceTIMER_CREATE_FAILED() \
	prvTraceStoreEvent_None(PSF_EVENT_TIMER_CREATE_FAILED);

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)

#define traceTIMER_COMMAND_SEND_8_0_CASES(tmr) \
		case tmrCOMMAND_RESET: \
			prvTraceStoreEvent_HandleParam((xReturn == pdPASS) ? PSF_EVENT_TIMER_RESET : PSF_EVENT_TIMER_RESET_FAILED, (void*)(tmr), xOptionalValue); \
			break; \
		case tmrCOMMAND_START_FROM_ISR: \
			prvTraceStoreEvent_HandleParam((xReturn == pdPASS) ? PSF_EVENT_TIMER_START_FROMISR : PSF_EVENT_TIMER_START_FROMISR_FAILED, (void*)(tmr), xOptionalValue); \
			break; \
		case tmrCOMMAND_RESET_FROM_ISR: \
			prvTraceStoreEvent_HandleParam((xReturn == pdPASS) ? PSF_EVENT_TIMER_RESET_FROMISR : PSF_EVENT_TIMER_RESET_FROMISR_FAILED, (void*)(tmr), xOptionalValue); \
			break; \
		case tmrCOMMAND_STOP_FROM_ISR: \
			prvTraceStoreEvent_HandleParam((xReturn == pdPASS) ? PSF_EVENT_TIMER_STOP_FROMISR : PSF_EVENT_TIMER_STOP_FROMISR_FAILED, (void*)(tmr), xOptionalValue); \
			break; \
		case tmrCOMMAND_CHANGE_PERIOD_FROM_ISR: \
			prvTraceStoreEvent_HandleParam((xReturn == pdPASS) ? PSF_EVENT_TIMER_CHANGEPERIOD_FROMISR : PSF_EVENT_TIMER_CHANGEPERIOD_FROMISR_FAILED, (void*)(tmr), xOptionalValue); \
			break;
#else

#define traceTIMER_COMMAND_SEND_8_0_CASES(tmr)

#endif

/* Note that xCommandID can never be tmrCOMMAND_EXECUTE_CALLBACK (-1) since the trace macro is not called in that case */
#undef traceTIMER_COMMAND_SEND
#define traceTIMER_COMMAND_SEND(tmr, xCommandID, xOptionalValue, xReturn) \
	switch(xCommandID) \
	{ \
		case tmrCOMMAND_START: \
			prvTraceStoreEvent_Handle(((xReturn) == pdPASS) ? PSF_EVENT_TIMER_START : PSF_EVENT_TIMER_START_FAILED, (void*)(tmr)); \
			break; \
		case tmrCOMMAND_STOP: \
			prvTraceStoreEvent_Handle(((xReturn) == pdPASS) ? PSF_EVENT_TIMER_STOP : PSF_EVENT_TIMER_STOP_FAILED, (void*)(tmr)); \
			break; \
		case tmrCOMMAND_CHANGE_PERIOD: \
			prvTraceStoreEvent_HandleParam(((xReturn) == pdPASS) ? PSF_EVENT_TIMER_CHANGEPERIOD : PSF_EVENT_TIMER_CHANGEPERIOD_FAILED, (void*)(tmr), xOptionalValue); \
			break; \
		case tmrCOMMAND_DELETE: \
			xTraceObjectUnregisterWithoutHandle(((xReturn) == pdPASS) ? PSF_EVENT_TIMER_DELETE : PSF_EVENT_TIMER_DELETE_FAILED, (void*)(tmr), 0); \
			break; \
		traceTIMER_COMMAND_SEND_8_0_CASES(tmr) \
	}

#undef traceTIMER_EXPIRED
#define traceTIMER_EXPIRED(tmr) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_TIMER_EXPIRED, (void*)(tmr), (uint32_t)((tmr)->pxCallbackFunction))

#endif


#if (TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS == 1)

#undef tracePEND_FUNC_CALL
#define tracePEND_FUNC_CALL(func, arg1, arg2, ret) \
	prvTraceStoreEvent_Param(((ret) == pdPASS) ? PSF_EVENT_TIMER_PENDFUNCCALL : PSF_EVENT_TIMER_PENDFUNCCALL_FAILED, (uint32_t)(func))

#undef tracePEND_FUNC_CALL_FROM_ISR
#define tracePEND_FUNC_CALL_FROM_ISR(func, arg1, arg2, ret) \
	prvTraceStoreEvent_Param(((ret) == pdPASS) ? PSF_EVENT_TIMER_PENDFUNCCALL_FROMISR : PSF_EVENT_TIMER_PENDFUNCCALL_FROMISR_FAILED, (uint32_t)(func))

#endif

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1)

#undef traceEVENT_GROUP_CREATE
#define traceEVENT_GROUP_CREATE(eg)  \
	xTraceObjectRegisterWithoutHandle(PSF_EVENT_EVENTGROUP_CREATE, (void*)(eg), 0, (uint32_t)(eg)->uxEventBits)

#undef traceEVENT_GROUP_DELETE
#define traceEVENT_GROUP_DELETE(eg) \
	xTraceObjectUnregisterWithoutHandle(PSF_EVENT_EVENTGROUP_DELETE, (void*)(eg), (uint32_t)(eg)->uxEventBits)

#undef traceEVENT_GROUP_CREATE_FAILED
#define traceEVENT_GROUP_CREATE_FAILED() \
	prvTraceStoreEvent_None(PSF_EVENT_EVENTGROUP_CREATE_FAILED)

#undef traceEVENT_GROUP_SYNC_BLOCK
#define traceEVENT_GROUP_SYNC_BLOCK(eg, bitsToSet, bitsToWaitFor) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_EVENTGROUP_SYNC_BLOCK, (void*)(eg), bitsToWaitFor)

#undef traceEVENT_GROUP_SYNC_END
#define traceEVENT_GROUP_SYNC_END(eg, bitsToSet, bitsToWaitFor, wasTimeout) \
	prvTraceStoreEvent_HandleParam(((wasTimeout) != pdTRUE) ? PSF_EVENT_EVENTGROUP_SYNC : PSF_EVENT_EVENTGROUP_SYNC_FAILED, (void*)(eg), bitsToWaitFor)

#undef traceEVENT_GROUP_WAIT_BITS_BLOCK
#define traceEVENT_GROUP_WAIT_BITS_BLOCK(eg, bitsToWaitFor) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_EVENTGROUP_WAITBITS_BLOCK, (void*)(eg), bitsToWaitFor)

#undef traceEVENT_GROUP_WAIT_BITS_END
#define traceEVENT_GROUP_WAIT_BITS_END(eg, bitsToWaitFor, wasTimeout) \
	prvTraceStoreEvent_HandleParam(((wasTimeout) != pdTRUE) ? PSF_EVENT_EVENTGROUP_WAITBITS : PSF_EVENT_EVENTGROUP_WAITBITS_FAILED, (void*)(eg), bitsToWaitFor)

#undef traceEVENT_GROUP_CLEAR_BITS
#define traceEVENT_GROUP_CLEAR_BITS(eg, bitsToClear) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_EVENTGROUP_CLEARBITS, (void*)(eg), bitsToClear)

#undef traceEVENT_GROUP_CLEAR_BITS_FROM_ISR
#define traceEVENT_GROUP_CLEAR_BITS_FROM_ISR(eg, bitsToClear) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_EVENTGROUP_CLEARBITS_FROMISR, (void*)(eg), bitsToClear)

#undef traceEVENT_GROUP_SET_BITS
#define traceEVENT_GROUP_SET_BITS(eg, bitsToSet) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_EVENTGROUP_SETBITS, (void*)(eg), bitsToSet)

#undef traceEVENT_GROUP_SET_BITS_FROM_ISR
#define traceEVENT_GROUP_SET_BITS_FROM_ISR(eg, bitsToSet) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_EVENTGROUP_SETBITS_FROMISR, (void*)(eg), bitsToSet)

#endif

#undef traceTASK_NOTIFY
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY(index) \
	prvTraceStoreEvent_Handle(PSF_EVENT_TASK_NOTIFY, (void*)xTaskToNotify)

#else

#define traceTASK_NOTIFY() \
	prvTraceStoreEvent_Handle(PSF_EVENT_TASK_NOTIFY, (void*)xTaskToNotify)

#endif

#undef traceTASK_NOTIFY_FROM_ISR
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY_FROM_ISR(index) \
	prvTraceStoreEvent_Handle(PSF_EVENT_TASK_NOTIFY_FROM_ISR, (void*)xTaskToNotify)

#else

#define traceTASK_NOTIFY_FROM_ISR() \
	prvTraceStoreEvent_Handle(PSF_EVENT_TASK_NOTIFY_FROM_ISR, (void*)xTaskToNotify)

#endif

/* NOTIFY and NOTIFY_GIVE will be handled identically */
#undef traceTASK_NOTIFY_GIVE_FROM_ISR
#define traceTASK_NOTIFY_GIVE_FROM_ISR traceTASK_NOTIFY_FROM_ISR

#undef traceTASK_NOTIFY_WAIT
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY_WAIT(index) \
	prvTraceStoreEvent_HandleParam(pxCurrentTCB->ucNotifyState[index] == taskNOTIFICATION_RECEIVED ? PSF_EVENT_TASK_NOTIFY_WAIT : PSF_EVENT_TASK_NOTIFY_WAIT_FAILED, (void*)pxCurrentTCB, xTicksToWait)

#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0)

#define traceTASK_NOTIFY_WAIT() \
	prvTraceStoreEvent_HandleParam(pxCurrentTCB->ucNotifyState == taskNOTIFICATION_RECEIVED ? PSF_EVENT_TASK_NOTIFY_WAIT : PSF_EVENT_TASK_NOTIFY_WAIT_FAILED, (void*)pxCurrentTCB, xTicksToWait)

#else

#define traceTASK_NOTIFY_WAIT() \
	prvTraceStoreEvent_HandleParam(pxCurrentTCB->eNotifyState == eNotified ? PSF_EVENT_TASK_NOTIFY_WAIT : PSF_EVENT_TASK_NOTIFY_WAIT_FAILED, (void*)pxCurrentTCB, xTicksToWait)

#endif

/* WAIT and TAKE will be handled identically */
#undef traceTASK_NOTIFY_TAKE
#define traceTASK_NOTIFY_TAKE traceTASK_NOTIFY_WAIT

#undef traceTASK_NOTIFY_WAIT_BLOCK
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)

#define traceTASK_NOTIFY_WAIT_BLOCK(index) \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_TASK_NOTIFY_WAIT_BLOCK, (void*)pxCurrentTCB, xTicksToWait)

#else

#define traceTASK_NOTIFY_WAIT_BLOCK() \
	prvTraceStoreEvent_HandleParam(PSF_EVENT_TASK_NOTIFY_WAIT_BLOCK, (void*)pxCurrentTCB, xTicksToWait)

#endif

/* WAIT_BLOCK and TAKE_BLOCK will be handled identically */
#undef traceTASK_NOTIFY_TAKE_BLOCK
#define traceTASK_NOTIFY_TAKE_BLOCK traceTASK_NOTIFY_WAIT_BLOCK

#undef traceQUEUE_REGISTRY_ADD
#define traceQUEUE_REGISTRY_ADD(object, name) \
	xTraceObjectSetNameWithoutHandle(object, (const char*)(name));

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1)

#undef traceSTREAM_BUFFER_CREATE
#define traceSTREAM_BUFFER_CREATE( pxStreamBuffer, xIsMessageBuffer ) \
	xTraceObjectRegisterWithoutHandle((xIsMessageBuffer) == 1 ? PSF_EVENT_MESSAGEBUFFER_CREATE : PSF_EVENT_STREAMBUFFER_CREATE, (void*)(pxStreamBuffer), "", (uint32_t)xBufferSizeBytes)

#undef traceSTREAM_BUFFER_CREATE_FAILED
#define traceSTREAM_BUFFER_CREATE_FAILED( xIsMessageBuffer ) \
	prvTraceStoreEvent_HandleParam((xIsMessageBuffer) == 1 ? PSF_EVENT_MESSAGEBUFFER_CREATE_FAILED : PSF_EVENT_STREAMBUFFER_CREATE_FAILED, 0 , xBufferSizeBytes)

#undef traceSTREAM_BUFFER_CREATE_STATIC_FAILED
#define traceSTREAM_BUFFER_CREATE_STATIC_FAILED( xReturn, xIsMessageBuffer ) \
	traceSTREAM_BUFFER_CREATE_FAILED( xIsMessageBuffer )

#undef traceSTREAM_BUFFER_DELETE
#define traceSTREAM_BUFFER_DELETE( xStreamBuffer ) \
	xTraceObjectUnregisterWithoutHandle(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_DELETE : PSF_EVENT_STREAMBUFFER_DELETE, (void*)(xStreamBuffer), prvBytesInBuffer(xStreamBuffer));

#undef traceSTREAM_BUFFER_RESET
#define traceSTREAM_BUFFER_RESET( xStreamBuffer ) \
	prvTraceStoreEvent_HandleParam(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RESET : PSF_EVENT_STREAMBUFFER_RESET, (void*)(xStreamBuffer), 0)

#undef traceSTREAM_BUFFER_SEND
#define traceSTREAM_BUFFER_SEND( xStreamBuffer, xReturn ) \
	prvTraceStoreEvent_HandleParam(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_SEND : PSF_EVENT_STREAMBUFFER_SEND, (void*)(xStreamBuffer), prvBytesInBuffer(xStreamBuffer))

#undef traceBLOCKING_ON_STREAM_BUFFER_SEND
#define traceBLOCKING_ON_STREAM_BUFFER_SEND( xStreamBuffer ) \
	prvTraceStoreEvent_Handle(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_SEND_BLOCK : PSF_EVENT_STREAMBUFFER_SEND_BLOCK, (void*)(xStreamBuffer))

#undef traceSTREAM_BUFFER_SEND_FAILED
#define traceSTREAM_BUFFER_SEND_FAILED( xStreamBuffer ) \
	prvTraceStoreEvent_Handle(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_SEND_FAILED : PSF_EVENT_STREAMBUFFER_SEND_FAILED, (void*)(xStreamBuffer))

#undef traceSTREAM_BUFFER_RECEIVE
#define traceSTREAM_BUFFER_RECEIVE( xStreamBuffer, xReceivedLength ) \
	prvTraceStoreEvent_HandleParam(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RECEIVE: PSF_EVENT_STREAMBUFFER_RECEIVE, (void*)(xStreamBuffer), prvBytesInBuffer(xStreamBuffer))

#undef traceBLOCKING_ON_STREAM_BUFFER_RECEIVE
#define traceBLOCKING_ON_STREAM_BUFFER_RECEIVE( xStreamBuffer ) \
	prvTraceStoreEvent_Handle(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RECEIVE_BLOCK: PSF_EVENT_STREAMBUFFER_RECEIVE_BLOCK, (void*)(xStreamBuffer))

#undef traceSTREAM_BUFFER_RECEIVE_FAILED
#define traceSTREAM_BUFFER_RECEIVE_FAILED( xStreamBuffer ) \
	prvTraceStoreEvent_Handle(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RECEIVE_FAILED: PSF_EVENT_STREAMBUFFER_RECEIVE_FAILED, (void*)(xStreamBuffer))

#undef traceSTREAM_BUFFER_SEND_FROM_ISR
#define traceSTREAM_BUFFER_SEND_FROM_ISR( xStreamBuffer, xReturn ) \
	if ( (xReturn) > ( size_t ) 0 ) \
	{ \
		prvTraceStoreEvent_HandleParam(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_SEND_FROM_ISR : PSF_EVENT_STREAMBUFFER_SEND_FROM_ISR, (void*)(xStreamBuffer), prvBytesInBuffer(xStreamBuffer)); \
	} \
	else \
	{ \
		prvTraceStoreEvent_Handle(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_SEND_FROM_ISR_FAILED : PSF_EVENT_STREAMBUFFER_SEND_FROM_ISR_FAILED, (void*)(xStreamBuffer)); \
	}

#undef traceSTREAM_BUFFER_RECEIVE_FROM_ISR
#define traceSTREAM_BUFFER_RECEIVE_FROM_ISR( xStreamBuffer, xReceivedLength ) \
	if ( (xReceivedLength) > ( size_t ) 0 ) \
	{ \
		prvTraceStoreEvent_HandleParam(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RECEIVE_FROM_ISR : PSF_EVENT_STREAMBUFFER_RECEIVE_FROM_ISR, (void*)(xStreamBuffer), prvBytesInBuffer(xStreamBuffer)); \
	} \
	else \
	{ \
		prvTraceStoreEvent_Handle(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RECEIVE_FROM_ISR_FAILED : PSF_EVENT_STREAMBUFFER_RECEIVE_FROM_ISR_FAILED, (void*)(xStreamBuffer)); \
	}

#endif

#endif

#endif

#else
	
/* When recorder is disabled */
#define vTraceSetQueueName(object, name)
#define vTraceSetSemaphoreName(object, name)
#define vTraceSetMutexName(object, name)
#define vTraceSetEventGroupName(object, name)
#define vTraceSetStreamBufferName(object, name)
#define vTraceSetMessageBufferName(object, name)
	
#endif

#ifdef __cplusplus
}
#endif

#endif /* TRC_KERNEL_PORT_H */
