/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v4.4.0
 * Percepio AB, www.percepio.com
 *
 * Terms of Use
 * This file is part of the trace recorder library (RECORDER), which is the 
 * intellectual property of Percepio AB (PERCEPIO) and provided under a
 * license as follows.
 * The RECORDER may be used free of charge for the purpose of recording data
 * intended for analysis in PERCEPIO products. It may not be used or modified
 * for other purposes without explicit permission from PERCEPIO.
 * You may distribute the RECORDER in its original source code form, assuming
 * this text (terms of use, disclaimer, copyright notice) is unchanged. You are
 * allowed to distribute the RECORDER with minor modifications intended for
 * configuration or porting of the RECORDER, e.g., to allow using it on a 
 * specific processor, processor family or with a specific communication
 * interface. Any such modifications should be documented directly below
 * this comment block.  
 *
 * Disclaimer
 * The RECORDER is being delivered to you AS IS and PERCEPIO makes no warranty
 * as to its use or performance. PERCEPIO does not and cannot warrant the 
 * performance or results you may obtain by using the RECORDER or documentation.
 * PERCEPIO make no warranties, express or implied, as to noninfringement of
 * third party rights, merchantability, or fitness for any particular purpose.
 * In no event will PERCEPIO, its technology partners, or distributors be liable
 * to you for any consequential, incidental or special damages, including any
 * lost profits or lost savings, even if a representative of PERCEPIO has been
 * advised of the possibility of such damages, or for any claim by any third
 * party. Some jurisdictions do not allow the exclusion or limitation of
 * incidental, consequential or special damages, or the exclusion of implied
 * warranties or limitations on how long an implied warranty may last, so the
 * above limitations may not apply to you.
 *
 * FreeRTOS-specific definitions needed by the trace recorder
 *
 * <LICENSE INFO>
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2018.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRC_KERNEL_PORT_H
#define TRC_KERNEL_PORT_H

#include "FreeRTOS.h"	/* Defines configUSE_TRACE_FACILITY */
#include "trcPortDefines.h"

#ifdef __cplusplus
extern "C" {
#endif

#define TRC_USE_TRACEALYZER_RECORDER configUSE_TRACE_FACILITY

/*** FreeRTOS version codes **************************************************/
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
#define prvGetStreamBufferType(x) ((( StreamBuffer_t * )x )->ucFlags & sbFLAGS_IS_MESSAGE_BUFFER)
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
	#define TickType TickType_t
	#define TaskType TaskHandle_t
#endif



#if (defined(TRC_USE_TRACEALYZER_RECORDER)) && (TRC_USE_TRACEALYZER_RECORDER == 1)

#if defined(TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1) && (TRC_CFG_SCHEDULING_ONLY == 0)
	/* Required for this feature */
#undef INCLUDE_uxTaskGetStackHighWaterMark
#define INCLUDE_uxTaskGetStackHighWaterMark 1
#endif /* defined(TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1) && (TRC_CFG_SCHEDULING_ONLY == 0) */

/*******************************************************************************
 * INCLUDE_xTaskGetCurrentTaskHandle must be set to 1 for tracing to work properly
 ******************************************************************************/
#undef INCLUDE_xTaskGetCurrentTaskHandle
#define INCLUDE_xTaskGetCurrentTaskHandle 1

#if (TRC_CFG_SCHEDULING_ONLY == 0)
/*******************************************************************************
 * vTraceSetQueueName(void* object, const char* name)
 *
 * Parameter object: pointer to the Queue that shall be named
 * Parameter name: the name to set (const string literal)
 *
 * Sets a name for Queue objects for display in Tracealyzer.
 ******************************************************************************/
void vTraceSetQueueName(void* object, const char* name);

/*******************************************************************************
 * vTraceSetSemaphoreName(void* object, const char* name)
 *
 * Parameter object: pointer to the Semaphore that shall be named
 * Parameter name: the name to set (const string literal)
 *
 * Sets a name for Semaphore objects for display in Tracealyzer.
 ******************************************************************************/
void vTraceSetSemaphoreName(void* object, const char* name);

/*******************************************************************************
 * vTraceSetMutexName(void* object, const char* name)
 *
 * Parameter object: pointer to the Mutex that shall be named
 * Parameter name: the name to set (const string literal)
 *
 * Sets a name for Semaphore objects for display in Tracealyzer.
 ******************************************************************************/
void vTraceSetMutexName(void* object, const char* name);

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1)
/*******************************************************************************
* vTraceSetEventGroupName(void* object, const char* name)
*
* Parameter object: pointer to the EventGroup that shall be named
* Parameter name: the name to set (const string literal)
*
* Sets a name for EventGroup objects for display in Tracealyzer.
******************************************************************************/
void vTraceSetEventGroupName(void* object, const char* name);
#else /* (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1) */
#define vTraceSetEventGroupName(object, name) /* Do nothing */
#endif /* (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1) */

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1)
/*******************************************************************************
* vTraceSetStreamBufferName(void* object, const char* name)
*
* Parameter object: pointer to the StreamBuffer that shall be named
* Parameter name: the name to set (const string literal)
*
* Sets a name for StreamBuffer objects for display in Tracealyzer.
******************************************************************************/
void vTraceSetStreamBufferName(void* object, const char* name);
#else /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1) */
#define vTraceSetStreamBufferName(object, name) /* Do nothing */
#endif /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1) */

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1)
/*******************************************************************************
 * vTraceSetMessageBufferName(void* object, const char* name)
 *
 * Parameter object: pointer to the MessageBuffer that shall be named
 * Parameter name: the name to set (const string literal)
 *
 * Sets a name for MessageBuffer objects for display in Tracealyzer.
 ******************************************************************************/
void vTraceSetMessageBufferName(void* object, const char* name);
#else /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1) */
#define vTraceSetMessageBufferName(object, name) /* Do nothing */
#endif /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1) */

#if defined (TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1)
void prvAddTaskToStackMonitor(void* task);
void prvRemoveTaskFromStackMonitor(void* task);
#else /* defined (TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1) */
#define prvAddTaskToStackMonitor(task)
#define prvRemoveTaskFromStackMonitor(task)
#endif /* defined (TRC_CFG_ENABLE_STACK_MONITOR) && (TRC_CFG_ENABLE_STACK_MONITOR == 1) */

#else /* (TRC_CFG_SCHEDULING_ONLY == 0) */

#define vTraceSetQueueName(object, name) /* Do nothing */
#define vTraceSetSemaphoreName(object, name) /* Do nothing */
#define vTraceSetMutexName(object, name) /* Do nothing */
#define vTraceSetEventGroupName(object, name) /* Do nothing */
#define vTraceSetStreamBufferName(object, name) /* Do nothing */
#define vTraceSetMessageBufferName(object, name) /* Do nothing */
#define prvAddTaskToStackMonitor(task) /* Do nothing */
#define prvRemoveTaskFromStackMonitor(task) /* Do nothing */

#endif /* (TRC_CFG_SCHEDULING_ONLY == 0) */

/*******************************************************************************
 * Note: Setting names for event groups is difficult to support, this has been 
 * excluded intentionally. This since we don't know if event_groups.c is 
 * included in the build, so referencing it from the recorder may cause errors.
 ******************************************************************************/

/* Gives the currently executing task (wrapper for RTOS-specific function) */
void* prvTraceGetCurrentTaskHandle(void);

#if (((TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT) && (TRC_CFG_INCLUDE_ISR_TRACING == 1)) || (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING))
/* Tells if the scheduler currently is suspended (task-switches can't occur) */
unsigned char prvTraceIsSchedulerSuspended(void);

/*******************************************************************************
 * INCLUDE_xTaskGetSchedulerState must be set to 1 for tracing to work properly
 ******************************************************************************/
#undef INCLUDE_xTaskGetSchedulerState
#define INCLUDE_xTaskGetSchedulerState 1

#endif /* (((TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT) && (TRC_CFG_INCLUDE_ISR_TRACING == 1)) || (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)) */

#define TRACE_KERNEL_VERSION 0x1AA1
#define TRACE_TICK_RATE_HZ configTICK_RATE_HZ /* Defined in "FreeRTOS.h" */
#define TRACE_CPU_CLOCK_HZ configCPU_CLOCK_HZ /* Defined in "FreeRTOSConfig.h" */
#define TRACE_GET_CURRENT_TASK() prvTraceGetCurrentTaskHandle()

#define TRACE_GET_OS_TICKS() (uiTraceTickCount) /* Streaming only */

/* If using dynamic allocation of snapshot trace buffer... */
#define TRACE_MALLOC(size) pvPortMalloc(size) 	

#if defined(configUSE_TIMERS)
#if (configUSE_TIMERS == 1)
#undef INCLUDE_xTimerGetTimerDaemonTaskHandle
#define INCLUDE_xTimerGetTimerDaemonTaskHandle 1
#endif /* configUSE_TIMERS == 1*/
#endif /* configUSE_TIMERS */

/* For ARM Cortex-M devices - assumes the ARM CMSIS API is available */
#if (defined (__CORTEX_M))	
	#define TRACE_ALLOC_CRITICAL_SECTION() uint32_t __irq_status;
	#define TRACE_ENTER_CRITICAL_SECTION() {__irq_status = __get_PRIMASK(); __set_PRIMASK(1);} /* PRIMASK disables ALL interrupts - allows for tracing in any ISR */
	#define TRACE_EXIT_CRITICAL_SECTION() {__set_PRIMASK(__irq_status);}
#endif

#if (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_ARM_CORTEX_A9) || (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_XILINX_ZyncUltraScaleR5)

	/**************************************************************************
	 * Disables "FreeRTOS-enabled" interrupts only , i.e. with priorities up to
	 * configMAX_API_CALL_INTERRUPT_PRIORITY. Don't add tracing in ISRs with
	 * greater priority.
	 *************************************************************************/

	extern int cortex_a9_r5_enter_critical(void);
	extern void cortex_a9_r5_exit_critical(int irq_already_masked_at_enter);

	#define TRACE_ALLOC_CRITICAL_SECTION() uint32_t __irq_mask_status;

	#define TRACE_ENTER_CRITICAL_SECTION() { __irq_mask_status = cortex_a9_r5_enter_critical(); }

	#define TRACE_EXIT_CRITICAL_SECTION() { cortex_a9_r5_exit_critical(__irq_mask_status); }

#endif

#if ( (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_Renesas_RX600) || (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_MICROCHIP_PIC24_PIC32))
	#define TRACE_ALLOC_CRITICAL_SECTION() int __irq_status;
	#define TRACE_ENTER_CRITICAL_SECTION() {__irq_status = portSET_INTERRUPT_MASK_FROM_ISR();}
	#define TRACE_EXIT_CRITICAL_SECTION() {portCLEAR_INTERRUPT_MASK_FROM_ISR(__irq_status);}
#endif

#if (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_Altera_NiosII)
	#include "system.h"
	#include "sys/alt_irq.h"
	#define TRACE_ALLOC_CRITICAL_SECTION() alt_irq_context __irq_status;
	#define TRACE_ENTER_CRITICAL_SECTION(){__irq_status = alt_irq_disable_all();}
	#define TRACE_EXIT_CRITICAL_SECTION() {alt_irq_enable_all(__irq_status);}
#endif

#if (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_Win32)
    /* In the Win32 port, there are no real interrupts, so we can use the normal critical sections */
	#define TRACE_ALLOC_CRITICAL_SECTION()
	#define TRACE_ENTER_CRITICAL_SECTION() portENTER_CRITICAL()
	#define TRACE_EXIT_CRITICAL_SECTION() portEXIT_CRITICAL()
#endif

#if (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_POWERPC_Z4)
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)
    /* FreeRTOS v8.0 or later */    
	#define TRACE_ALLOC_CRITICAL_SECTION() UBaseType_t __irq_status;
    #define TRACE_ENTER_CRITICAL_SECTION() {__irq_status = portSET_INTERRUPT_MASK_FROM_ISR();}
    #define TRACE_EXIT_CRITICAL_SECTION() {portCLEAR_INTERRUPT_MASK_FROM_ISR(__irq_status);}
#else 
	/* FreeRTOS v7.x */
    #define TRACE_ALLOC_CRITICAL_SECTION() unsigned portBASE_TYPE __irq_status;
    #define TRACE_ENTER_CRITICAL_SECTION() {__irq_status = portSET_INTERRUPT_MASK_FROM_ISR();}
    #define TRACE_EXIT_CRITICAL_SECTION() {portCLEAR_INTERRUPT_MASK_FROM_ISR(__irq_status);}
#endif
#endif

#ifndef TRACE_ENTER_CRITICAL_SECTION
	#error "This hardware port has no definition for critical sections! See http://percepio.com/2014/10/27/how-to-define-critical-sections-for-the-recorder/"
#endif


#if (TRC_CFG_FREERTOS_VERSION == TRC_FREERTOS_VERSION_9_0_1)
	/******************************************************************************
	* Fix for FreeRTOS v9.0.1 to correctly identify xQueuePeek events.
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
	******************************************************************************/
#define isQueueReceiveHookActuallyPeek (__LINE__ > 1674) /* Half way between the closes trace points */

#elif (TRC_CFG_FREERTOS_VERSION <= TRC_FREERTOS_VERSION_9_0_0)
#define isQueueReceiveHookActuallyPeek xJustPeeking

#elif (TRC_CFG_FREERTOS_VERSION > TRC_FREERTOS_VERSION_9_0_1)
#define isQueueReceiveHookActuallyPeek (__LINE__ < 0) /* instead of pdFALSE to fix a warning of "constant condition" */

#endif

extern uint16_t CurrentFilterMask;

extern uint16_t CurrentFilterGroup;

uint8_t prvTraceGetQueueType(void* handle);
uint16_t prvTraceGetTaskNumberLow16(void* handle);
uint16_t prvTraceGetTaskNumberHigh16(void* handle);
void prvTraceSetTaskNumberLow16(void* handle, uint16_t value);
void prvTraceSetTaskNumberHigh16(void* handle, uint16_t value);

uint16_t prvTraceGetQueueNumberLow16(void* handle);
uint16_t prvTraceGetQueueNumberHigh16(void* handle);
void prvTraceSetQueueNumberLow16(void* handle, uint16_t value);
void prvTraceSetQueueNumberHigh16(void* handle, uint16_t value);

#if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
uint16_t prvTraceGetTimerNumberLow16(void* handle);
uint16_t prvTraceGetTimerNumberHigh16(void* handle);
void prvTraceSetTimerNumberLow16(void* handle, uint16_t value);
void prvTraceSetTimerNumberHigh16(void* handle, uint16_t value);
#endif /* (TRC_CFG_INCLUDE_TIMER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
uint16_t prvTraceGetEventGroupNumberLow16(void* handle);
uint16_t prvTraceGetEventGroupNumberHigh16(void* handle);
void prvTraceSetEventGroupNumberLow16(void* handle, uint16_t value);
void prvTraceSetEventGroupNumberHigh16(void* handle, uint16_t value);
#endif /* (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
uint16_t prvTraceGetStreamBufferNumberLow16(void* handle);
uint16_t prvTraceGetStreamBufferNumberHigh16(void* handle);
void prvTraceSetStreamBufferNumberLow16(void* handle, uint16_t value);
void prvTraceSetStreamBufferNumberHigh16(void* handle, uint16_t value);
#endif /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1 && TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#define TRACE_GET_TASK_FILTER(pxTask) prvTraceGetTaskNumberHigh16((void*)pxTask)
#define TRACE_SET_TASK_FILTER(pxTask, group) prvTraceSetTaskNumberHigh16((void*)pxTask, group)

#define TRACE_GET_QUEUE_FILTER(pxObject) prvTraceGetQueueNumberHigh16((void*)pxObject)
#define TRACE_SET_QUEUE_FILTER(pxObject, group) prvTraceSetQueueNumberHigh16((void*)pxObject, group)

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
#define TRACE_GET_EVENTGROUP_FILTER(pxObject) prvTraceGetEventGroupNumberHigh16((void*)pxObject)
#define TRACE_SET_EVENTGROUP_FILTER(pxObject, group) prvTraceSetEventGroupNumberHigh16((void*)pxObject, group)
#else /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */
/* FreeRTOS versions before v10.0 does not support filtering for event groups */
#define TRACE_GET_EVENTGROUP_FILTER(pxObject) 1
#define TRACE_SET_EVENTGROUP_FILTER(pxObject, group) 
#endif /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0)
#define TRACE_GET_TIMER_FILTER(pxObject) prvTraceGetTimerNumberHigh16((void*)pxObject)
#define TRACE_SET_TIMER_FILTER(pxObject, group) prvTraceSetTimerNumberHigh16((void*)pxObject, group)
#else /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */
/* FreeRTOS versions before v10.0 does not support filtering for timers */
#define TRACE_GET_TIMER_FILTER(pxObject) 1
#define TRACE_SET_TIMER_FILTER(pxObject, group) 
#endif /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_0_0) */

#define TRACE_GET_STREAMBUFFER_FILTER(pxObject) prvTraceGetStreamBufferNumberHigh16((void*)pxObject)
#define TRACE_SET_STREAMBUFFER_FILTER(pxObject, group) prvTraceSetStreamBufferNumberHigh16((void*)pxObject, group)

/* We can only support filtering if FreeRTOS is at least v8.0 */
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)
#define TRACE_GET_OBJECT_FILTER(CLASS, pxObject) TRACE_GET_##CLASS##_FILTER(pxObject)
#define TRACE_SET_OBJECT_FILTER(CLASS, pxObject, group) TRACE_SET_##CLASS##_FILTER(pxObject, group)
#else /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X) */
#define TRACE_GET_OBJECT_FILTER(CLASS, pxObject) 0xFFFF
#define TRACE_SET_OBJECT_FILTER(CLASS, pxObject, group) 
#endif /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X) */

/* Helpers needed to correctly expand names */
#define TZ__CAT2(a,b) a ## b
#define TZ__CAT(a,b) TZ__CAT2(a, b)

/**************************************************************************/
/* Makes sure xQueueGiveFromISR also has a xCopyPosition parameter        */
/**************************************************************************/

/* Expands name if this header is included... uxQueueType must be a macro that only exists in queue.c or whatever, and it must expand to nothing or to something that's valid in identifiers */
#define xQueueGiveFromISR(a,b) TZ__CAT(xQueueGiveFromISR__, uxQueueType) (a,b)

/* If in queue.c, the "uxQueueType" macro expands to "pcHead". queueSEND_TO_BACK is the value we need to send in */
#define xQueueGiveFromISR__pcHead(__a, __b) MyWrapper_xQueueGiveFromISR(__a, __b, const BaseType_t xCopyPosition); \
BaseType_t xQueueGiveFromISR(__a, __b) { return MyWrapper_xQueueGiveFromISR(xQueue, pxHigherPriorityTaskWoken, queueSEND_TO_BACK); } \
BaseType_t MyWrapper_xQueueGiveFromISR(__a, __b, const BaseType_t xCopyPosition)

/* If not in queue.c, "uxQueueType" isn't expanded */
#define xQueueGiveFromISR__uxQueueType(__a, __b) xQueueGiveFromISR(__a,__b)

/**************************************************************************/
/* End of xQueueGiveFromISR fix                                           */
/**************************************************************************/

/******************************************************************************/
/*** Definitions for Snapshot mode ********************************************/
/******************************************************************************/
#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT)

/*** The object classes *******************************************************/

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

/*** Definitions for Object Table ********************************************/
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

/* Initialization of the object property table */
void vTraceInitObjectPropertyTable(void);

/* Initialization of the handle mechanism, see e.g, prvTraceGetObjectHandle */
void vTraceInitObjectHandleStack(void);

/* Returns the "Not enough handles" error message for the specified object class */
const char* pszTraceGetErrorNotEnoughHandles(traceObjectClass objectclass);

void* prvTraceGetCurrentTaskHandle(void);

/******************************************************************************
 * TraceQueueClassTable
 * Translates a FreeRTOS QueueType into trace objects classes (TRACE_CLASS_).
 * Has one entry for each QueueType, gives TRACE_CLASS ID.
 ******************************************************************************/			
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
	if (pxNewTCB != NULL) \
	{ \
		trcKERNEL_HOOKS_TASK_CREATE(TRACE_GET_OBJECT_EVENT_CODE(CREATE_OBJ, TRCSUCCESS, TASK, pxNewTCB), TASK, pxNewTCB); \
		prvAddTaskToStackMonitor(pxNewTCB); \
	}

/* Called in vTaskCreate, if it fails (typically if the stack can not be allocated) */
#undef traceTASK_CREATE_FAILED
#define traceTASK_CREATE_FAILED() \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_NUMERIC_PARAM_ONLY(TRACE_GET_CLASS_EVENT_CODE(CREATE_OBJ, TRCFAILED, TASK, NOT_USED), 0);

/* Called on vTaskDelete */
#undef traceTASK_DELETE
#define traceTASK_DELETE( pxTaskToDelete ) \
	{ TRACE_ALLOC_CRITICAL_SECTION(); \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_TASK_DELETE(TRACE_GET_OBJECT_EVENT_CODE(DELETE_OBJ, TRCSUCCESS, TASK, pxTaskToDelete), TRACE_GET_OBJECT_EVENT_CODE(OBJCLOSE_NAME, TRCSUCCESS, TASK, pxTaskToDelete), TRACE_GET_OBJECT_EVENT_CODE(OBJCLOSE_PROP, TRCSUCCESS, TASK, pxTaskToDelete), pxTaskToDelete); \
	prvRemoveTaskFromStackMonitor(pxTaskToDelete); \
	TRACE_EXIT_CRITICAL_SECTION(); }

#if (TRC_CFG_SCHEDULING_ONLY == 0)

#if defined(configUSE_TICKLESS_IDLE)
#if (configUSE_TICKLESS_IDLE != 0)

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

#endif /* (configUSE_TICKLESS_IDLE != 0) */
#endif /* defined(configUSE_TICKLESS_IDLE)  */

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
#if TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0
#define traceTASK_DELAY_UNTIL(xTimeToWake) \
	trcKERNEL_HOOKS_TASK_DELAY(TASK_DELAY_UNTIL, pxCurrentTCB, xTimeToWake); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0 */
#define traceTASK_DELAY_UNTIL() \
	trcKERNEL_HOOKS_TASK_DELAY(TASK_DELAY_UNTIL, pxCurrentTCB, xTimeToWake); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0 */

/* Called in xQueueCreate, and thereby for all other object based on queues, such as semaphores. */
#undef traceQUEUE_CREATE
#define traceQUEUE_CREATE( pxNewQueue ) \
	trcKERNEL_HOOKS_OBJECT_CREATE(TRACE_GET_OBJECT_EVENT_CODE(CREATE_OBJ, TRCSUCCESS, QUEUE, pxNewQueue), QUEUE, pxNewQueue);

/* Called in xQueueCreate, if the queue creation fails */
#undef traceQUEUE_CREATE_FAILED
#define traceQUEUE_CREATE_FAILED( queueType ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_NUMERIC_PARAM_ONLY(TRACE_GET_CLASS_EVENT_CODE(CREATE_OBJ, TRCFAILED, QUEUE, queueType), 0);

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
#endif /* (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0) */

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

#endif /* (TRC_CFG_INCLUDE_MEMMANG_EVENTS == 1) */

#if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1)

/* Called in timer.c - xTimerCreate */
#undef traceTIMER_CREATE
#define traceTIMER_CREATE(tmr) \
	trcKERNEL_HOOKS_OBJECT_CREATE(TIMER_CREATE, TIMER, tmr);

#undef traceTIMER_CREATE_FAILED
#define traceTIMER_CREATE_FAILED() \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_NUMERIC_PARAM_ONLY(TIMER_CREATE_TRCFAILED, 0);

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

#endif /* (TRC_CFG_INCLUDE_TIMER_EVENTS == 1) */

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

#endif /* (TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS == 1) */

#endif /* (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X) */

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1)

#undef traceEVENT_GROUP_CREATE
#define traceEVENT_GROUP_CREATE(eg) \
	trcKERNEL_HOOKS_OBJECT_CREATE(EVENT_GROUP_CREATE, EVENTGROUP, eg);

#undef traceEVENT_GROUP_CREATE_FAILED
#define traceEVENT_GROUP_CREATE_FAILED() \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_NUMERIC_PARAM_ONLY(EVENT_GROUP_CREATE_TRCFAILED, 0);

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

#endif /* (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1) */

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
#else /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0 */
#define traceTASK_NOTIFY_TAKE(index) \
	if (pxCurrentTCB->ucNotifyState[index] == taskNOTIFICATION_RECEIVED){ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE, TASK, pxCurrentTCB, xTicksToWait); \
	}else{ \
		trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE_TRCFAILED, TASK, pxCurrentTCB, xTicksToWait);}
#endif /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0 */

#undef traceTASK_NOTIFY_TAKE_BLOCK
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY_TAKE_BLOCK() \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE_TRCBLOCK, TASK, pxCurrentTCB, xTicksToWait); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();
#else /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY_TAKE_BLOCK(index) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_PARAM(TRACE_TASK_NOTIFY_TAKE_TRCBLOCK, TASK, pxCurrentTCB, xTicksToWait); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();
#endif /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0 */

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
#else /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0 */
#define traceTASK_NOTIFY_WAIT(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxCurrentTCB) & CurrentFilterMask) \
	{ \
		if (pxCurrentTCB->ucNotifyState[index] == taskNOTIFICATION_RECEIVED) \
			prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
		else \
			prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT_TRCFAILED, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
	}
#endif /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0 */

#undef traceTASK_NOTIFY_WAIT_BLOCK
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY_WAIT_BLOCK() \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxCurrentTCB) & CurrentFilterMask) \
		prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT_TRCBLOCK, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();
#else /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY_WAIT_BLOCK(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxCurrentTCB) & CurrentFilterMask) \
		prvTraceStoreKernelCallWithParam(TRACE_TASK_NOTIFY_WAIT_TRCBLOCK, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(pxCurrentTCB), xTicksToWait); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();
#endif /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0 */

#undef traceTASK_NOTIFY
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
			prvTraceStoreKernelCall(TRACE_TASK_NOTIFY, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));
#else /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
			prvTraceStoreKernelCall(TRACE_TASK_NOTIFY, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));
#endif /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0 */

#undef traceTASK_NOTIFY_FROM_ISR
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY_FROM_ISR() \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreKernelCall(TRACE_TASK_NOTIFY_FROM_ISR, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));
#else /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY_FROM_ISR(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreKernelCall(TRACE_TASK_NOTIFY_FROM_ISR, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));
#endif /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0 */
	
#undef traceTASK_NOTIFY_GIVE_FROM_ISR
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY_GIVE_FROM_ISR() \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreKernelCall(TRACE_TASK_NOTIFY_GIVE_FROM_ISR, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));
#else /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY_GIVE_FROM_ISR(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreKernelCall(TRACE_TASK_NOTIFY_GIVE_FROM_ISR, TRACE_CLASS_TASK, TRACE_GET_TASK_NUMBER(xTaskToNotify));
#endif /* TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_10_4_0 */

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1)

#undef traceSTREAM_BUFFER_CREATE
#define traceSTREAM_BUFFER_CREATE( pxStreamBuffer, xIsMessageBuffer ) \
	trcKERNEL_HOOKS_OBJECT_CREATE(TRACE_GET_OBJECT_EVENT_CODE(CREATE_OBJ, TRCSUCCESS, STREAMBUFFER, pxStreamBuffer), STREAMBUFFER, pxStreamBuffer);

#undef traceSTREAM_BUFFER_CREATE_FAILED
#define traceSTREAM_BUFFER_CREATE_FAILED( xIsMessageBuffer ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE_WITH_NUMERIC_PARAM_ONLY(TRACE_GET_CLASS_EVENT_CODE(CREATE_OBJ, TRCFAILED, STREAMBUFFER, xIsMessageBuffer), 0);
	
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

#endif /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1) */

#endif /* (TRC_CFG_SCHEDULING_ONLY == 0) */

#endif /*#if TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_SNAPSHOT */

/******************************************************************************/
/*** Definitions for Streaming mode *******************************************/
/******************************************************************************/
#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)

/*******************************************************************************
* vTraceStoreKernelObjectName
*
* Set the name for a kernel object (defined by its address).
******************************************************************************/			
void vTraceStoreKernelObjectName(void* object, const char* name); 

/*******************************************************************************
* prvIsNewTCB
*
* Tells if this task is already executing, or if there has been a task-switch.
* Assumed to be called within a trace hook in kernel context.
*******************************************************************************/
uint32_t prvIsNewTCB(void* pNewTCB);

#define TRACE_GET_CURRENT_TASK() prvTraceGetCurrentTaskHandle()

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
#define PSF_EVENT_TASK_NOTIFY_TAKE							0xCA
#define PSF_EVENT_TASK_NOTIFY_TAKE_BLOCK					0xCB
#define PSF_EVENT_TASK_NOTIFY_TAKE_FAILED					0xCC
#define PSF_EVENT_TASK_NOTIFY_WAIT							0xCD
#define PSF_EVENT_TASK_NOTIFY_WAIT_BLOCK					0xCE
#define PSF_EVENT_TASK_NOTIFY_WAIT_FAILED					0xCF
#define PSF_EVENT_TASK_NOTIFY_FROM_ISR						0xD0
#define PSF_EVENT_TASK_NOTIFY_GIVE_FROM_ISR					0xD1

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

#define PSF_EVENT_UNUSED_STACK								0xEA

/*** The trace macros for streaming ******************************************/

/* A macro that will update the tick count when returning from tickless idle */
#undef traceINCREASE_TICK_COUNT
/* Note: This can handle time adjustments of max 2^32 ticks, i.e., 35 seconds at 120 MHz. Thus, tick-less idle periods longer than 2^32 ticks will appear "compressed" on the time line.*/
#define traceINCREASE_TICK_COUNT( xCount ) { extern uint32_t uiTraceTickCount; uiTraceTickCount += xCount; }

#if (TRC_CFG_INCLUDE_OSTICK_EVENTS == 1)
#define OS_TICK_EVENT(uxSchedulerSuspended, xTickCount) if (uxSchedulerSuspended == (unsigned portBASE_TYPE) pdFALSE) { prvTraceStoreEvent1(PSF_EVENT_NEW_TIME, (uint32_t)(xTickCount + 1)); }
#else
#define OS_TICK_EVENT(uxSchedulerSuspended, xTickCount) 
#endif

/* Called on each OS tick. Will call uiPortGetTimestamp to make sure it is called at least once every OS tick. */
#undef traceTASK_INCREMENT_TICK
#if TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_3_0

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || xPendedTicks == 0) { extern uint32_t uiTraceTickCount; uiTraceTickCount++; } \
	OS_TICK_EVENT(uxSchedulerSuspended, xTickCount)

#elif TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_5_X

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxPendedTicks == 0) { extern uint32_t uiTraceTickCount; uiTraceTickCount++; } \
	OS_TICK_EVENT(uxSchedulerSuspended, xTickCount)

#else

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxMissedTicks == 0) { extern uint32_t uiTraceTickCount; uiTraceTickCount++; } \
	OS_TICK_EVENT(uxSchedulerSuspended, xTickCount)

#endif

extern volatile uint32_t uiTraceSystemState;

/* Called on each task-switch */
#undef traceTASK_SWITCHED_IN
#define traceTASK_SWITCHED_IN() \
	uiTraceSystemState = TRC_STATE_IN_TASKSWITCH; \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
	{ \
		if (prvIsNewTCB(pxCurrentTCB)) \
		{ \
			prvTraceStoreEvent2(PSF_EVENT_TASK_ACTIVATE, (uint32_t)pxCurrentTCB, pxCurrentTCB->uxPriority); \
		} \
	} \
	uiTraceSystemState = TRC_STATE_IN_APPLICATION;

/* Called for each task that becomes ready */
#if (TRC_CFG_INCLUDE_READY_EVENTS == 1)
#undef traceMOVED_TASK_TO_READY_STATE
#define traceMOVED_TASK_TO_READY_STATE( pxTCB ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxTCB) & CurrentFilterMask) \
		prvTraceStoreEvent1(PSF_EVENT_TASK_READY, (uint32_t)pxTCB);
#endif

#undef traceTASK_CREATE
#if TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0
#define traceTASK_CREATE(pxNewTCB) \
	if (pxNewTCB != NULL) \
	{ \
		prvAddTaskToStackMonitor(pxNewTCB); \
		prvTraceSaveObjectSymbol(pxNewTCB, pxNewTCB->pcTaskName); \
		prvTraceSaveObjectData(pxNewTCB, pxNewTCB->uxPriority); \
		prvTraceStoreStringEvent(1, PSF_EVENT_OBJ_NAME, pxNewTCB->pcTaskName, pxNewTCB); \
		TRACE_SET_OBJECT_FILTER(TASK, pxNewTCB, CurrentFilterGroup); \
		if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
			if (TRACE_GET_OBJECT_FILTER(TASK, pxNewTCB) & CurrentFilterMask) \
				prvTraceStoreEvent2(PSF_EVENT_TASK_CREATE, (uint32_t)pxNewTCB, pxNewTCB->uxPriority); \
	}
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0 */
#define traceTASK_CREATE(pxNewTCB) \
	if (pxNewTCB != NULL) \
	{ \
		prvAddTaskToStackMonitor(pxNewTCB); \
		prvTraceSaveObjectSymbol(pxNewTCB, (const char*)pcName); \
		prvTraceSaveObjectData(pxNewTCB, uxPriority); \
		prvTraceStoreStringEvent(1, PSF_EVENT_OBJ_NAME, (const char*)pcName, pxNewTCB); \
		TRACE_SET_OBJECT_FILTER(TASK, pxNewTCB, CurrentFilterGroup); \
		if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
			if (TRACE_GET_OBJECT_FILTER(TASK, pxNewTCB) & CurrentFilterMask) \
				prvTraceStoreEvent2(PSF_EVENT_TASK_CREATE, (uint32_t)pxNewTCB, uxPriority); \
	}
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0 */

/* Called in vTaskCreate, if it fails (typically if the stack can not be allocated) */
#undef traceTASK_CREATE_FAILED
#define traceTASK_CREATE_FAILED() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent0(PSF_EVENT_TASK_CREATE_FAILED);

/* Called on vTaskDelete */
#undef traceTASK_DELETE				// We don't allow for filtering out "delete" events. They are important and not very frequent. Moreover, we can't exclude create events, so this should be symmetrical.
#define traceTASK_DELETE( pxTaskToDelete ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, pxTaskToDelete) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_TASK_DELETE, (uint32_t)pxTaskToDelete, (pxTaskToDelete != NULL) ? (pxTaskToDelete->uxPriority) : 0); \
	prvTraceDeleteSymbol(pxTaskToDelete); \
	prvTraceDeleteObjectData(pxTaskToDelete); \
	prvRemoveTaskFromStackMonitor(pxTaskToDelete);

#if (TRC_CFG_SCHEDULING_ONLY == 0)

#if (defined(configUSE_TICKLESS_IDLE) && configUSE_TICKLESS_IDLE != 0)

#undef traceLOW_POWER_IDLE_BEGIN
#define traceLOW_POWER_IDLE_BEGIN() \
	{ \
		prvTraceStoreEvent1(PSF_EVENT_LOWPOWER_BEGIN, xExpectedIdleTime); \
	}

#undef traceLOW_POWER_IDLE_END
#define traceLOW_POWER_IDLE_END() \
	{ \
		prvTraceStoreEvent0(PSF_EVENT_LOWPOWER_END); \
	}

#endif /* (defined(configUSE_TICKLESS_IDLE) && configUSE_TICKLESS_IDLE != 0) */

/* Called on vTaskSuspend */
#undef traceTASK_SUSPEND
#define traceTASK_SUSPEND( pxTaskToSuspend ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, pxTaskToSuspend) & CurrentFilterMask) \
			prvTraceStoreEvent1(PSF_EVENT_TASK_SUSPEND, (uint32_t)pxTaskToSuspend);

/* Called on vTaskDelay - note the use of FreeRTOS variable xTicksToDelay */
#undef traceTASK_DELAY
#define traceTASK_DELAY() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent1(PSF_EVENT_TASK_DELAY, xTicksToDelay);

/* Called on vTaskDelayUntil - note the use of FreeRTOS variable xTimeToWake */
#undef traceTASK_DELAY_UNTIL
#if TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0
#define traceTASK_DELAY_UNTIL(xTimeToWake) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent1(PSF_EVENT_TASK_DELAY_UNTIL, (uint32_t)xTimeToWake);
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0 */
#define traceTASK_DELAY_UNTIL() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent1(PSF_EVENT_TASK_DELAY_UNTIL, (uint32_t)xTimeToWake);
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0 */

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0)
#define traceQUEUE_CREATE_HELPER() \
		case queueQUEUE_TYPE_MUTEX: \
			prvTraceStoreEvent1(PSF_EVENT_MUTEX_CREATE, (uint32_t)pxNewQueue); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent1(PSF_EVENT_MUTEX_RECURSIVE_CREATE, (uint32_t)pxNewQueue); \
			break;
#else
#define traceQUEUE_CREATE_HELPER()
#endif /* (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0) */

/* Called in xQueueCreate, and thereby for all other object based on queues, such as semaphores. */
#undef traceQUEUE_CREATE
#define traceQUEUE_CREATE( pxNewQueue )\
	TRACE_SET_OBJECT_FILTER(QUEUE, pxNewQueue, CurrentFilterGroup); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
	{ \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxNewQueue) & CurrentFilterMask) \
		{ \
			switch (pxNewQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					prvTraceStoreEvent2(PSF_EVENT_QUEUE_CREATE, (uint32_t)pxNewQueue, uxQueueLength); \
					break; \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
					prvTraceStoreEvent1(PSF_EVENT_SEMAPHORE_BINARY_CREATE, (uint32_t)pxNewQueue); \
					break; \
				traceQUEUE_CREATE_HELPER() \
			} \
		} \
	}

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0)
#define traceQUEUE_CREATE_FAILED_HELPER() \
		case queueQUEUE_TYPE_MUTEX: \
			prvTraceStoreEvent1(PSF_EVENT_MUTEX_CREATE_FAILED, 0); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			prvTraceStoreEvent1(PSF_EVENT_MUTEX_RECURSIVE_CREATE_FAILED, 0); \
			break;
#else
#define traceQUEUE_CREATE_FAILED_HELPER()
#endif /* (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0) */

/* Called in xQueueCreate, if the queue creation fails */
#undef traceQUEUE_CREATE_FAILED
#define traceQUEUE_CREATE_FAILED( queueType ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
	{ \
		switch (queueType) \
		{ \
			case queueQUEUE_TYPE_BASE: \
				prvTraceStoreEvent2(PSF_EVENT_QUEUE_CREATE_FAILED, 0, uxQueueLength); \
				break; \
			case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
				prvTraceStoreEvent1(PSF_EVENT_SEMAPHORE_BINARY_CREATE_FAILED, 0); \
				break; \
			traceQUEUE_CREATE_FAILED_HELPER() \
		} \
	}

#undef traceQUEUE_DELETE			// We don't allow for filtering out "delete" events. They are important and not very frequent. Moreover, we can't exclude create events, so this should be symmetrical.
#define traceQUEUE_DELETE( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
	{ \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
		{ \
			switch (pxQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					prvTraceStoreEvent2(PSF_EVENT_QUEUE_DELETE, (uint32_t)pxQueue, (pxQueue != NULL) ? (pxQueue->uxMessagesWaiting) : 0); \
					break; \
				case queueQUEUE_TYPE_MUTEX: \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					prvTraceStoreEvent2(PSF_EVENT_MUTEX_DELETE, (uint32_t)pxQueue, (pxQueue != NULL) ? (pxQueue->uxMessagesWaiting) : 0); \
					break; \
				case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
					prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_DELETE, (uint32_t)pxQueue, (pxQueue != NULL) ? (pxQueue->uxMessagesWaiting) : 0); \
					break; \
			} \
		} \
	} \
	prvTraceDeleteSymbol(pxQueue);

/* Called in xQueueCreateCountingSemaphore, if the queue creation fails */
#undef traceCREATE_COUNTING_SEMAPHORE
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)
#define traceCREATE_COUNTING_SEMAPHORE() \
	TRACE_SET_OBJECT_FILTER(QUEUE, xHandle, CurrentFilterGroup); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, xHandle) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_COUNTING_CREATE, (uint32_t)xHandle, uxMaxCount)
#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_5_X)
#define traceCREATE_COUNTING_SEMAPHORE() \
	TRACE_SET_OBJECT_FILTER(QUEUE, xHandle, CurrentFilterGroup); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, xHandle) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_COUNTING_CREATE, (uint32_t)xHandle, uxInitialCount);
#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_4_X)
#define traceCREATE_COUNTING_SEMAPHORE() \
	TRACE_SET_OBJECT_FILTER(QUEUE, xHandle, CurrentFilterGroup); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, xHandle) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_COUNTING_CREATE, (uint32_t)xHandle, uxCountValue);
#else
#define traceCREATE_COUNTING_SEMAPHORE() \
	TRACE_SET_OBJECT_FILTER(QUEUE, pxHandle, CurrentFilterGroup); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxHandle) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_COUNTING_CREATE, (uint32_t)pxHandle, uxCountValue);
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X */

#undef traceCREATE_COUNTING_SEMAPHORE_FAILED
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)
#define traceCREATE_COUNTING_SEMAPHORE_FAILED() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_COUNTING_CREATE_FAILED, 0, uxMaxCount);
#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_5_X)
#define traceCREATE_COUNTING_SEMAPHORE_FAILED() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_COUNTING_CREATE_FAILED, 0, uxInitialCount);
#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_7_4_X)
#define traceCREATE_COUNTING_SEMAPHORE_FAILED() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_COUNTING_CREATE_FAILED, 0, uxCountValue);
#else
#define traceCREATE_COUNTING_SEMAPHORE_FAILED() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_COUNTING_CREATE_FAILED, 0, uxCountValue);
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X */


/* This macro is not necessary as of FreeRTOS v9.0.0 */
#if (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0)
/* Called in xQueueCreateMutex, and thereby also from xSemaphoreCreateMutex and xSemaphoreCreateRecursiveMutex */
#undef traceCREATE_MUTEX
#define traceCREATE_MUTEX( pxNewQueue ) \
	TRACE_SET_OBJECT_FILTER(QUEUE, pxNewQueue, CurrentFilterGroup); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
	{ \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxNewQueue) & CurrentFilterMask) \
		{ \
			switch (pxNewQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_MUTEX: \
					prvTraceStoreEvent1(PSF_EVENT_MUTEX_CREATE, (uint32_t)pxNewQueue); \
					break; \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					prvTraceStoreEvent1(PSF_EVENT_MUTEX_RECURSIVE_CREATE, (uint32_t)pxNewQueue); \
					break; \
			} \
		}\
	}

/* Called in xQueueCreateMutex when the operation fails (when memory allocation fails) */
#undef traceCREATE_MUTEX_FAILED
#define traceCREATE_MUTEX_FAILED() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent1(PSF_EVENT_MUTEX_CREATE_FAILED, 0);
#endif /* (TRC_CFG_FREERTOS_VERSION < TRC_FREERTOS_VERSION_9_0_0) */

/* Called when a message is sent to a queue */	/* CS IS NEW ! */
#undef traceQUEUE_SEND
#define traceQUEUE_SEND( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
			switch (pxQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					prvTraceStoreEvent2(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND : PSF_EVENT_QUEUE_SEND_FRONT, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting + 1); \
					break; \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
				case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
					prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_GIVE, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting + 1); \
					break; \
				case queueQUEUE_TYPE_MUTEX: \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					prvTraceStoreEvent1(PSF_EVENT_MUTEX_GIVE, (uint32_t)pxQueue); \
					break; \
			}
			
#undef traceQUEUE_SET_SEND
#define traceQUEUE_SET_SEND( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_QUEUE_SEND, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting + 1);

/* Called when a message failed to be sent to a queue (timeout) */
#undef traceQUEUE_SEND_FAILED
#define traceQUEUE_SEND_FAILED( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
			switch (pxQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					prvTraceStoreEvent2(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_FAILED : PSF_EVENT_QUEUE_SEND_FRONT_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
				case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
					prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_GIVE_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_MUTEX: \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					prvTraceStoreEvent1(PSF_EVENT_MUTEX_GIVE_FAILED, (uint32_t)pxQueue); \
					break; \
			}

/* Called when the task is blocked due to a send operation on a full queue */
#undef traceBLOCKING_ON_QUEUE_SEND
#define traceBLOCKING_ON_QUEUE_SEND( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
			switch (pxQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					prvTraceStoreEvent2(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_BLOCK : PSF_EVENT_QUEUE_SEND_FRONT_BLOCK, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
				case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
					prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_GIVE_BLOCK, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_MUTEX: \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					prvTraceStoreEvent1(PSF_EVENT_MUTEX_GIVE_BLOCK, (uint32_t)pxQueue); \
					break; \
			}

/* Called when a message is sent from interrupt context, e.g., using xQueueSendFromISR */
#undef traceQUEUE_SEND_FROM_ISR
#define traceQUEUE_SEND_FROM_ISR( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
		switch (pxQueue->ucQueueType) \
		{ \
			case queueQUEUE_TYPE_BASE: \
				prvTraceStoreEvent2(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_FROMISR : PSF_EVENT_QUEUE_SEND_FRONT_FROMISR, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting + 1); \
				break; \
			case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
			case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
				prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_GIVE_FROMISR, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting + 1); \
				break; \
		}

/* Called when a message send from interrupt context fails (since the queue was full) */
#undef traceQUEUE_SEND_FROM_ISR_FAILED
#define traceQUEUE_SEND_FROM_ISR_FAILED( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
		switch (pxQueue->ucQueueType) \
		{ \
			case queueQUEUE_TYPE_BASE: \
				prvTraceStoreEvent2(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_FROMISR_FAILED : PSF_EVENT_QUEUE_SEND_FRONT_FROMISR_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
				break; \
			case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
			case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
				prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_GIVE_FROMISR_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
				break; \
		}

/* Called when a message is received from a queue */
#undef traceQUEUE_RECEIVE
#define traceQUEUE_RECEIVE( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
			switch (pxQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					if (isQueueReceiveHookActuallyPeek) \
						prvTraceStoreEvent3(PSF_EVENT_QUEUE_PEEK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting - 1); \
					else\
						prvTraceStoreEvent3(PSF_EVENT_QUEUE_RECEIVE, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting - 1); \
					break; \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
				case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
					if (isQueueReceiveHookActuallyPeek) \
						prvTraceStoreEvent3(PSF_EVENT_SEMAPHORE_PEEK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting - 1); \
					else \
						prvTraceStoreEvent3(PSF_EVENT_SEMAPHORE_TAKE, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting - 1); \
					break; \
				case queueQUEUE_TYPE_MUTEX: \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					if (isQueueReceiveHookActuallyPeek) \
						prvTraceStoreEvent2(PSF_EVENT_MUTEX_PEEK, (uint32_t)pxQueue, xTicksToWait); \
					else \
						prvTraceStoreEvent2(PSF_EVENT_MUTEX_TAKE, (uint32_t)pxQueue, xTicksToWait); \
					break; \
			}

/* Called when a receive operation on a queue fails (timeout) */
#undef traceQUEUE_RECEIVE_FAILED
#define traceQUEUE_RECEIVE_FAILED( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
			switch (pxQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					prvTraceStoreEvent3(isQueueReceiveHookActuallyPeek ? PSF_EVENT_QUEUE_PEEK_FAILED : PSF_EVENT_QUEUE_RECEIVE_FAILED, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
				case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
					prvTraceStoreEvent3(isQueueReceiveHookActuallyPeek ? PSF_EVENT_SEMAPHORE_PEEK_FAILED : PSF_EVENT_SEMAPHORE_TAKE_FAILED, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_MUTEX: \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					prvTraceStoreEvent2(isQueueReceiveHookActuallyPeek ? PSF_EVENT_MUTEX_PEEK_FAILED : PSF_EVENT_MUTEX_TAKE_FAILED, (uint32_t)pxQueue, xTicksToWait); \
					break; \
			}

/* Called when the task is blocked due to a receive operation on an empty queue */
#undef traceBLOCKING_ON_QUEUE_RECEIVE
#define traceBLOCKING_ON_QUEUE_RECEIVE( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
			switch (pxQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					prvTraceStoreEvent3(isQueueReceiveHookActuallyPeek ? PSF_EVENT_QUEUE_PEEK_BLOCK : PSF_EVENT_QUEUE_RECEIVE_BLOCK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
				case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
					prvTraceStoreEvent3(isQueueReceiveHookActuallyPeek ? PSF_EVENT_SEMAPHORE_PEEK_BLOCK : PSF_EVENT_SEMAPHORE_TAKE_BLOCK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_MUTEX: \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					prvTraceStoreEvent2(isQueueReceiveHookActuallyPeek ? PSF_EVENT_MUTEX_PEEK_BLOCK : PSF_EVENT_MUTEX_TAKE_BLOCK, (uint32_t)pxQueue, xTicksToWait); \
					break; \
			}

#if (TRC_CFG_FREERTOS_VERSION > TRC_FREERTOS_VERSION_9_0_1)
/* Called when a peek operation on a queue fails (timeout) */
#undef traceQUEUE_PEEK_FAILED
#define traceQUEUE_PEEK_FAILED( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
			switch (pxQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					prvTraceStoreEvent3(PSF_EVENT_QUEUE_PEEK_FAILED, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
				case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
					prvTraceStoreEvent3(PSF_EVENT_SEMAPHORE_PEEK_FAILED, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_MUTEX: \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					prvTraceStoreEvent2(PSF_EVENT_MUTEX_PEEK_FAILED, (uint32_t)pxQueue, xTicksToWait); \
					break; \
			}

/* Called when the task is blocked due to a peek operation on an empty queue */
#undef traceBLOCKING_ON_QUEUE_PEEK
#define traceBLOCKING_ON_QUEUE_PEEK( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
			switch (pxQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					prvTraceStoreEvent3(PSF_EVENT_QUEUE_PEEK_BLOCK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
				case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
					prvTraceStoreEvent3(PSF_EVENT_SEMAPHORE_PEEK_BLOCK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_MUTEX: \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					prvTraceStoreEvent2(PSF_EVENT_MUTEX_PEEK_BLOCK, (uint32_t)pxQueue, xTicksToWait); \
					break; \
			}

#endif /* (TRC_CFG_FREERTOS_VERSION > TRC_FREERTOS_VERSION_9_0_1) */

/* Called when a message is received in interrupt context, e.g., using xQueueReceiveFromISR */
#undef traceQUEUE_RECEIVE_FROM_ISR
#define traceQUEUE_RECEIVE_FROM_ISR( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
		switch (pxQueue->ucQueueType) \
		{ \
			case queueQUEUE_TYPE_BASE: \
				prvTraceStoreEvent2(PSF_EVENT_QUEUE_RECEIVE_FROMISR, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting - 1); \
				break; \
			case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
			case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
				prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_TAKE_FROMISR, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting - 1); \
				break; \
		}

/* Called when a message receive from interrupt context fails (since the queue was empty) */
#undef traceQUEUE_RECEIVE_FROM_ISR_FAILED
#define traceQUEUE_RECEIVE_FROM_ISR_FAILED( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
		switch (pxQueue->ucQueueType) \
		{ \
			case queueQUEUE_TYPE_BASE: \
				prvTraceStoreEvent2(PSF_EVENT_QUEUE_RECEIVE_FROMISR_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
				break; \
			case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
			case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
				prvTraceStoreEvent2(PSF_EVENT_SEMAPHORE_TAKE_FROMISR_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
				break; \
		}

/* Called on xQueuePeek */
#undef traceQUEUE_PEEK
#define traceQUEUE_PEEK( pxQueue ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(QUEUE, pxQueue) & CurrentFilterMask) \
			switch (pxQueue->ucQueueType) \
			{ \
				case queueQUEUE_TYPE_BASE: \
					prvTraceStoreEvent3(PSF_EVENT_QUEUE_PEEK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
				case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
					prvTraceStoreEvent3(PSF_EVENT_SEMAPHORE_PEEK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
					break; \
				case queueQUEUE_TYPE_MUTEX: \
				case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
					prvTraceStoreEvent1(PSF_EVENT_MUTEX_PEEK, (uint32_t)pxQueue); \
					break; \
			}

/* Called in vTaskPrioritySet */
#undef traceTASK_PRIORITY_SET
#define traceTASK_PRIORITY_SET( pxTask, uxNewPriority ) \
	prvTraceSaveObjectData(pxTask, uxNewPriority); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, pxTask) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_TASK_PRIORITY, (uint32_t)pxTask, uxNewPriority);
	
/* Called in vTaskPriorityInherit, which is called by Mutex operations */
#undef traceTASK_PRIORITY_INHERIT
#define traceTASK_PRIORITY_INHERIT( pxTask, uxNewPriority ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, pxTask) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_TASK_PRIO_INHERIT, (uint32_t)pxTask, uxNewPriority);

/* Called in vTaskPriorityDisinherit, which is called by Mutex operations */
#undef traceTASK_PRIORITY_DISINHERIT
#define traceTASK_PRIORITY_DISINHERIT( pxTask, uxNewPriority ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, pxTask) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_TASK_PRIO_DISINHERIT, (uint32_t)pxTask, uxNewPriority);

/* Called in vTaskResume */
#undef traceTASK_RESUME
#define traceTASK_RESUME( pxTaskToResume ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, pxTaskToResume) & CurrentFilterMask) \
			prvTraceStoreEvent1(PSF_EVENT_TASK_RESUME, (uint32_t)pxTaskToResume);

/* Called in vTaskResumeFromISR */
#undef traceTASK_RESUME_FROM_ISR
#define traceTASK_RESUME_FROM_ISR( pxTaskToResume ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, pxTaskToResume) & CurrentFilterMask) \
		prvTraceStoreEvent1(PSF_EVENT_TASK_RESUME_FROMISR, (uint32_t)pxTaskToResume);

#if (TRC_CFG_INCLUDE_MEMMANG_EVENTS == 1)

extern uint32_t trcHeapCounter;

#undef traceMALLOC
#define traceMALLOC( pvAddress, uiSize ) \
	if (pvAddress != 0) \
	{ \
		trcHeapCounter += uiSize; \
	} \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
	{ \
		if (pvAddress != 0) \
		{ \
			prvTraceStoreEvent2(PSF_EVENT_MALLOC, (uint32_t)pvAddress, uiSize); \
		} \
		else \
		{ \
			prvTraceStoreEvent2(PSF_EVENT_MALLOC_FAILED, (uint32_t)pvAddress, uiSize); \
		} \
	}

#undef traceFREE
#define traceFREE( pvAddress, uiSize ) \
	trcHeapCounter -= uiSize; \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_FREE, (uint32_t)pvAddress, (uint32_t)(0 - uiSize)); /* "0 -" instead of just "-" to get rid of a warning... */

#endif /* (TRC_CFG_INCLUDE_MEMMANG_EVENTS == 1) */

#if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1)

/* Called in timer.c - xTimerCreate */
#undef traceTIMER_CREATE
#define traceTIMER_CREATE(tmr) \
	TRACE_SET_OBJECT_FILTER(TIMER, tmr, CurrentFilterGroup); \
	prvTraceSaveObjectSymbol(tmr, (const char*)tmr->pcTimerName); \
	prvTraceStoreStringEvent(1, PSF_EVENT_OBJ_NAME, (const char*)tmr->pcTimerName, tmr); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TIMER, tmr) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_TIMER_CREATE, (uint32_t)tmr, tmr->xTimerPeriodInTicks);

#undef traceTIMER_CREATE_FAILED
#define traceTIMER_CREATE_FAILED() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent0(PSF_EVENT_TIMER_CREATE_FAILED);

#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X)
#define traceTIMER_COMMAND_SEND_8_0_CASES(tmr) \
				case tmrCOMMAND_RESET: \
					prvTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_RESET : PSF_EVENT_TIMER_RESET_FAILED, (uint32_t)tmr, xOptionalValue); \
					break; \
				case tmrCOMMAND_START_FROM_ISR: \
					prvTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_START_FROMISR : PSF_EVENT_TIMER_START_FROMISR_FAILED, (uint32_t)tmr, xOptionalValue); \
					break; \
				case tmrCOMMAND_RESET_FROM_ISR: \
					prvTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_RESET_FROMISR : PSF_EVENT_TIMER_RESET_FROMISR_FAILED, (uint32_t)tmr, xOptionalValue); \
					break; \
				case tmrCOMMAND_STOP_FROM_ISR: \
					prvTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_STOP_FROMISR : PSF_EVENT_TIMER_STOP_FROMISR_FAILED, (uint32_t)tmr, xOptionalValue); \
					break; \
				case tmrCOMMAND_CHANGE_PERIOD_FROM_ISR: \
					prvTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_CHANGEPERIOD_FROMISR : PSF_EVENT_TIMER_CHANGEPERIOD_FROMISR_FAILED, (uint32_t)tmr, xOptionalValue); \
					break;
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X */
#define traceTIMER_COMMAND_SEND_8_0_CASES(tmr) 
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_8_X_X */

/* Note that xCommandID can never be tmrCOMMAND_EXECUTE_CALLBACK (-1) since the trace macro is not called in that case */
#undef traceTIMER_COMMAND_SEND
#define traceTIMER_COMMAND_SEND(tmr, xCommandID, xOptionalValue, xReturn) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TIMER, tmr) & CurrentFilterMask) \
			switch(xCommandID) \
			{ \
				case tmrCOMMAND_START: \
					prvTraceStoreEvent1((xReturn == pdPASS) ? PSF_EVENT_TIMER_START : PSF_EVENT_TIMER_START_FAILED, (uint32_t)tmr); \
					break; \
				case tmrCOMMAND_STOP: \
					prvTraceStoreEvent1((xReturn == pdPASS) ? PSF_EVENT_TIMER_STOP : PSF_EVENT_TIMER_STOP_FAILED, (uint32_t)tmr); \
					break; \
				case tmrCOMMAND_CHANGE_PERIOD: \
					prvTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_CHANGEPERIOD : PSF_EVENT_TIMER_CHANGEPERIOD_FAILED, (uint32_t)tmr, xOptionalValue); \
					break; \
				case tmrCOMMAND_DELETE: \
					prvTraceStoreEvent1((xReturn == pdPASS) ? PSF_EVENT_TIMER_DELETE : PSF_EVENT_TIMER_DELETE_FAILED, (uint32_t)tmr); \
					break; \
				traceTIMER_COMMAND_SEND_8_0_CASES(tmr) \
			}

#undef traceTIMER_EXPIRED
#define traceTIMER_EXPIRED(tmr) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TIMER, tmr) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_TIMER_EXPIRED, (uint32_t)tmr->pxCallbackFunction, (uint32_t)tmr->pvTimerID);

#endif /* #if (TRC_CFG_INCLUDE_TIMER_EVENTS == 1) */


#if (TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS == 1)

#undef tracePEND_FUNC_CALL
#define tracePEND_FUNC_CALL(func, arg1, arg2, ret) \
	prvTraceStoreEvent1((ret == pdPASS) ? PSF_EVENT_TIMER_PENDFUNCCALL : PSF_EVENT_TIMER_PENDFUNCCALL_FAILED, (uint32_t)func);

#undef tracePEND_FUNC_CALL_FROM_ISR
#define tracePEND_FUNC_CALL_FROM_ISR(func, arg1, arg2, ret) \
	prvTraceStoreEvent1((ret == pdPASS) ? PSF_EVENT_TIMER_PENDFUNCCALL_FROMISR : PSF_EVENT_TIMER_PENDFUNCCALL_FROMISR_FAILED, (uint32_t)func);

#endif /* (TRC_CFG_INCLUDE_PEND_FUNC_CALL_EVENTS == 1) */

#if (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1)

#undef traceEVENT_GROUP_CREATE
#define traceEVENT_GROUP_CREATE(eg) \
	TRACE_SET_OBJECT_FILTER(EVENTGROUP, eg, CurrentFilterGroup); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(EVENTGROUP, eg) & CurrentFilterMask) \
			prvTraceStoreEvent1(PSF_EVENT_EVENTGROUP_CREATE, (uint32_t)eg);

#undef traceEVENT_GROUP_DELETE
#define traceEVENT_GROUP_DELETE(eg) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(EVENTGROUP, eg) & CurrentFilterMask) \
			prvTraceStoreEvent1(PSF_EVENT_EVENTGROUP_DELETE, (uint32_t)eg); \
	prvTraceDeleteSymbol(eg);

#undef traceEVENT_GROUP_CREATE_FAILED
#define traceEVENT_GROUP_CREATE_FAILED() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent0(PSF_EVENT_EVENTGROUP_CREATE_FAILED);

#undef traceEVENT_GROUP_SYNC_BLOCK
#define traceEVENT_GROUP_SYNC_BLOCK(eg, bitsToSet, bitsToWaitFor) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(EVENTGROUP, eg) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_EVENTGROUP_SYNC_BLOCK, (uint32_t)eg, bitsToWaitFor);

#undef traceEVENT_GROUP_SYNC_END
#define traceEVENT_GROUP_SYNC_END(eg, bitsToSet, bitsToWaitFor, wasTimeout) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(EVENTGROUP, eg) & CurrentFilterMask) \
			prvTraceStoreEvent2((wasTimeout != pdTRUE) ? PSF_EVENT_EVENTGROUP_SYNC : PSF_EVENT_EVENTGROUP_SYNC_FAILED, (uint32_t)eg, bitsToWaitFor);

#undef traceEVENT_GROUP_WAIT_BITS_BLOCK
#define traceEVENT_GROUP_WAIT_BITS_BLOCK(eg, bitsToWaitFor) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(EVENTGROUP, eg) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_EVENTGROUP_WAITBITS_BLOCK, (uint32_t)eg, bitsToWaitFor);

#undef traceEVENT_GROUP_WAIT_BITS_END
#define traceEVENT_GROUP_WAIT_BITS_END(eg, bitsToWaitFor, wasTimeout) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(EVENTGROUP, eg) & CurrentFilterMask) \
			prvTraceStoreEvent2((wasTimeout != pdTRUE) ? PSF_EVENT_EVENTGROUP_WAITBITS : PSF_EVENT_EVENTGROUP_WAITBITS_FAILED, (uint32_t)eg, bitsToWaitFor);

#undef traceEVENT_GROUP_CLEAR_BITS
#define traceEVENT_GROUP_CLEAR_BITS(eg, bitsToClear) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(EVENTGROUP, eg) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_EVENTGROUP_CLEARBITS, (uint32_t)eg, bitsToClear);

#undef traceEVENT_GROUP_CLEAR_BITS_FROM_ISR
#define traceEVENT_GROUP_CLEAR_BITS_FROM_ISR(eg, bitsToClear) \
	if (TRACE_GET_OBJECT_FILTER(EVENTGROUP, eg) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_EVENTGROUP_CLEARBITS_FROMISR, (uint32_t)eg, bitsToClear);

#undef traceEVENT_GROUP_SET_BITS
#define traceEVENT_GROUP_SET_BITS(eg, bitsToSet) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(EVENTGROUP, eg) & CurrentFilterMask) \
			prvTraceStoreEvent2(PSF_EVENT_EVENTGROUP_SETBITS, (uint32_t)eg, bitsToSet);

#undef traceEVENT_GROUP_SET_BITS_FROM_ISR
#define traceEVENT_GROUP_SET_BITS_FROM_ISR(eg, bitsToSet) \
	if (TRACE_GET_OBJECT_FILTER(EVENTGROUP, eg) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_EVENTGROUP_SETBITS_FROMISR, (uint32_t)eg, bitsToSet);

#endif /* (TRC_CFG_INCLUDE_EVENT_GROUP_EVENTS == 1) */

#undef traceTASK_NOTIFY_TAKE
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY_TAKE(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask){ \
		if (pxCurrentTCB->ucNotifyState[index] == taskNOTIFICATION_RECEIVED) \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE, (uint32_t)pxCurrentTCB, xTicksToWait); \
		else \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE_FAILED, (uint32_t)pxCurrentTCB, xTicksToWait);}
#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0)
#define traceTASK_NOTIFY_TAKE() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask){ \
		if (pxCurrentTCB->ucNotifyState == taskNOTIFICATION_RECEIVED) \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE, (uint32_t)pxCurrentTCB, xTicksToWait); \
		else \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE_FAILED, (uint32_t)pxCurrentTCB, xTicksToWait);}
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY_TAKE() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask){ \
		if (pxCurrentTCB->eNotifyState == eNotified) \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE, (uint32_t)pxCurrentTCB, xTicksToWait); \
		else \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE_FAILED, (uint32_t)pxCurrentTCB, xTicksToWait);}
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */

#undef traceTASK_NOTIFY_TAKE_BLOCK
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY_TAKE_BLOCK(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE_BLOCK, (uint32_t)pxCurrentTCB, xTicksToWait);
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY_TAKE_BLOCK() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE_BLOCK, (uint32_t)pxCurrentTCB, xTicksToWait);
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */

#undef traceTASK_NOTIFY_WAIT
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY_WAIT(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask){ \
		if (pxCurrentTCB->ucNotifyState[index] == taskNOTIFICATION_RECEIVED) \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT, (uint32_t)pxCurrentTCB, xTicksToWait); \
		else \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT_FAILED, (uint32_t)pxCurrentTCB, xTicksToWait);}
#elif (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_9_0_0)
#define traceTASK_NOTIFY_WAIT() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask){ \
		if (pxCurrentTCB->ucNotifyState == taskNOTIFICATION_RECEIVED) \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT, (uint32_t)pxCurrentTCB, xTicksToWait); \
		else \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT_FAILED, (uint32_t)pxCurrentTCB, xTicksToWait);}
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY_WAIT() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask){ \
		if (pxCurrentTCB->eNotifyState == eNotified) \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT, (uint32_t)pxCurrentTCB, xTicksToWait); \
		else \
			prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT_FAILED, (uint32_t)pxCurrentTCB, xTicksToWait);}
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */

#undef traceTASK_NOTIFY_WAIT_BLOCK
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY_WAIT_BLOCK(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT_BLOCK, (uint32_t)pxCurrentTCB, xTicksToWait);
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY_WAIT_BLOCK() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT_BLOCK, (uint32_t)pxCurrentTCB, xTicksToWait);
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */

#undef traceTASK_NOTIFY
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
			prvTraceStoreEvent1(PSF_EVENT_TASK_NOTIFY, (uint32_t)xTaskToNotify);
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY() \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
			prvTraceStoreEvent1(PSF_EVENT_TASK_NOTIFY, (uint32_t)xTaskToNotify);
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */

#undef traceTASK_NOTIFY_FROM_ISR
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY_FROM_ISR(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreEvent1(PSF_EVENT_TASK_NOTIFY_FROM_ISR, (uint32_t)xTaskToNotify);
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY_FROM_ISR() \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreEvent1(PSF_EVENT_TASK_NOTIFY_FROM_ISR, (uint32_t)xTaskToNotify);
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */
	
#undef traceTASK_NOTIFY_GIVE_FROM_ISR
#if (TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0)
#define traceTASK_NOTIFY_GIVE_FROM_ISR(index) \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreEvent1(PSF_EVENT_TASK_NOTIFY_GIVE_FROM_ISR, (uint32_t)xTaskToNotify);
#else /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */
#define traceTASK_NOTIFY_GIVE_FROM_ISR() \
	if (TRACE_GET_OBJECT_FILTER(TASK, xTaskToNotify) & CurrentFilterMask) \
		prvTraceStoreEvent1(PSF_EVENT_TASK_NOTIFY_GIVE_FROM_ISR, (uint32_t)xTaskToNotify);
#endif /* TRC_CFG_FREERTOS_VERSION >= TRC_FREERTOS_VERSION_10_4_0 */

#undef traceQUEUE_REGISTRY_ADD
#define traceQUEUE_REGISTRY_ADD(object, name) \
	prvTraceSaveObjectSymbol(object, (const char*)name); \
	prvTraceStoreStringEvent(1, PSF_EVENT_OBJ_NAME, name, object);

#if (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1)

#undef traceSTREAM_BUFFER_CREATE
#define traceSTREAM_BUFFER_CREATE( pxStreamBuffer, xIsMessageBuffer ) \
	TRACE_SET_OBJECT_FILTER(STREAMBUFFER, pxStreamBuffer, CurrentFilterGroup); \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, pxStreamBuffer) & CurrentFilterMask) \
			prvTraceStoreEvent2(xIsMessageBuffer == 1 ? PSF_EVENT_MESSAGEBUFFER_CREATE : PSF_EVENT_STREAMBUFFER_CREATE, (uint32_t)pxStreamBuffer, xBufferSizeBytes);

#undef traceSTREAM_BUFFER_CREATE_FAILED
#define traceSTREAM_BUFFER_CREATE_FAILED( xIsMessageBuffer ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		prvTraceStoreEvent2(xIsMessageBuffer == 1 ? PSF_EVENT_MESSAGEBUFFER_CREATE_FAILED : PSF_EVENT_STREAMBUFFER_CREATE_FAILED, 0 , xBufferSizeBytes);

#undef traceSTREAM_BUFFER_CREATE_STATIC_FAILED
#define traceSTREAM_BUFFER_CREATE_STATIC_FAILED( xReturn, xIsMessageBuffer ) \
	traceSTREAM_BUFFER_CREATE_FAILED( xIsMessageBuffer )

#undef traceSTREAM_BUFFER_DELETE
#define traceSTREAM_BUFFER_DELETE( xStreamBuffer ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, pxStreamBuffer) & CurrentFilterMask) \
			prvTraceStoreEvent2(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_DELETE : PSF_EVENT_STREAMBUFFER_DELETE, (uint32_t)xStreamBuffer, prvBytesInBuffer(xStreamBuffer)); \
	prvTraceDeleteSymbol(xStreamBuffer);

#undef traceSTREAM_BUFFER_RESET
#define traceSTREAM_BUFFER_RESET( xStreamBuffer ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, xStreamBuffer) & CurrentFilterMask) \
			prvTraceStoreEvent2(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RESET : PSF_EVENT_STREAMBUFFER_RESET, (uint32_t)xStreamBuffer, 0);

#undef traceSTREAM_BUFFER_SEND
#define traceSTREAM_BUFFER_SEND( xStreamBuffer, xReturn ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, xStreamBuffer) & CurrentFilterMask) \
			prvTraceStoreEvent2(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_SEND : PSF_EVENT_STREAMBUFFER_SEND, (uint32_t)xStreamBuffer, prvBytesInBuffer(xStreamBuffer));

#undef traceBLOCKING_ON_STREAM_BUFFER_SEND
#define traceBLOCKING_ON_STREAM_BUFFER_SEND( xStreamBuffer ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, xStreamBuffer) & CurrentFilterMask) \
			prvTraceStoreEvent1(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_SEND_BLOCK : PSF_EVENT_STREAMBUFFER_SEND_BLOCK, (uint32_t)xStreamBuffer);

#undef traceSTREAM_BUFFER_SEND_FAILED
#define traceSTREAM_BUFFER_SEND_FAILED( xStreamBuffer ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, xStreamBuffer) & CurrentFilterMask) \
			prvTraceStoreEvent1(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_SEND_FAILED : PSF_EVENT_STREAMBUFFER_SEND_FAILED, (uint32_t)xStreamBuffer);

#undef traceSTREAM_BUFFER_RECEIVE
#define traceSTREAM_BUFFER_RECEIVE( xStreamBuffer, xReceivedLength ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, xStreamBuffer) & CurrentFilterMask) \
			prvTraceStoreEvent2(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RECEIVE: PSF_EVENT_STREAMBUFFER_RECEIVE, (uint32_t)xStreamBuffer, prvBytesInBuffer(xStreamBuffer));

#undef traceBLOCKING_ON_STREAM_BUFFER_RECEIVE
#define traceBLOCKING_ON_STREAM_BUFFER_RECEIVE( xStreamBuffer ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, xStreamBuffer) & CurrentFilterMask) \
			prvTraceStoreEvent1(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RECEIVE_BLOCK: PSF_EVENT_STREAMBUFFER_RECEIVE_BLOCK, (uint32_t)xStreamBuffer);

#undef traceSTREAM_BUFFER_RECEIVE_FAILED
#define traceSTREAM_BUFFER_RECEIVE_FAILED( xStreamBuffer ) \
	if (TRACE_GET_OBJECT_FILTER(TASK, TRACE_GET_CURRENT_TASK()) & CurrentFilterMask) \
		if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, xStreamBuffer) & CurrentFilterMask) \
			prvTraceStoreEvent1(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RECEIVE_FAILED: PSF_EVENT_STREAMBUFFER_RECEIVE_FAILED, (uint32_t)xStreamBuffer);

#undef traceSTREAM_BUFFER_SEND_FROM_ISR
#define traceSTREAM_BUFFER_SEND_FROM_ISR( xStreamBuffer, xReturn ) \
	if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, xStreamBuffer) & CurrentFilterMask) \
	{ \
		if ( xReturn > ( size_t ) 0 ) \
		{ \
			prvTraceStoreEvent2(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_SEND_FROM_ISR : PSF_EVENT_STREAMBUFFER_SEND_FROM_ISR, (uint32_t)xStreamBuffer, prvBytesInBuffer(xStreamBuffer)); \
		} \
		else \
		{ \
			prvTraceStoreEvent1(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_SEND_FROM_ISR_FAILED : PSF_EVENT_STREAMBUFFER_SEND_FROM_ISR_FAILED, (uint32_t)xStreamBuffer); \
		} \
	}

#undef traceSTREAM_BUFFER_RECEIVE_FROM_ISR
#define traceSTREAM_BUFFER_RECEIVE_FROM_ISR( xStreamBuffer, xReceivedLength ) \
if (TRACE_GET_OBJECT_FILTER(STREAMBUFFER, xStreamBuffer) & CurrentFilterMask) \
	{ \
		if ( xReceivedLength > ( size_t ) 0 ) \
		{ \
			prvTraceStoreEvent2(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RECEIVE_FROM_ISR : PSF_EVENT_STREAMBUFFER_RECEIVE_FROM_ISR, (uint32_t)xStreamBuffer, prvBytesInBuffer(xStreamBuffer)); \
		} \
		else \
		{ \
			prvTraceStoreEvent1(prvGetStreamBufferType(xStreamBuffer) > 0 ? PSF_EVENT_MESSAGEBUFFER_RECEIVE_FROM_ISR_FAILED : PSF_EVENT_STREAMBUFFER_RECEIVE_FROM_ISR_FAILED, (uint32_t)xStreamBuffer); \
		} \
	}

#endif /* (TRC_CFG_INCLUDE_STREAM_BUFFER_EVENTS == 1) */

#endif /* (TRC_CFG_SCHEDULING_ONLY == 0) */

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */

#else /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
	
/* When recorder is disabled */
#define vTraceSetQueueName(object, name)
#define vTraceSetSemaphoreName(object, name)
#define vTraceSetMutexName(object, name)
#define vTraceSetEventGroupName(object, name)
#define vTraceSetStreamBufferName(object, name)
#define vTraceSetMessageBufferName(object, name)
	
#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */

#ifdef __cplusplus
}
#endif

#endif /* TRC_KERNEL_PORT_H */
