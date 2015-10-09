/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v3.0.2
 * Percepio AB, www.percepio.com
 *
 * trcKernelPort.h
 *
 * The kernel-specific definitions for FreeRTOS.
 *
 * Terms of Use
 * This software (the "Tracealyzer Recorder Library") is the intellectual
 * property of Percepio AB and may not be sold or in other ways commercially
 * redistributed without explicit written permission by Percepio AB.
 *
 * Separate conditions applies for the SEGGER branded source code included.
 *
 * The recorder library is free for use together with Percepio products.
 * You may distribute the recorder library in its original form, but public
 * distribution of modified versions require approval by Percepio AB.
 *
 * Disclaimer
 * The trace tool and recorder library is being delivered to you AS IS and
 * Percepio AB makes no warranty as to its use or performance. Percepio AB does
 * not and cannot warrant the performance or results you may obtain by using the
 * software or documentation. Percepio AB make no warranties, express or
 * implied, as to noninfringement of third party rights, merchantability, or
 * fitness for any particular purpose. In no event will Percepio AB, its
 * technology partners, or distributors be liable to you for any consequential,
 * incidental or special damages, including any lost profits or lost savings,
 * even if a representative of Percepio AB has been advised of the possibility
 * of such damages, or for any claim by any third party. Some jurisdictions do
 * not allow the exclusion or limitation of incidental, consequential or special
 * damages, or the exclusion of implied warranties or limitations on how long an
 * implied warranty may last, so the above limitations may not apply to you.
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2015.
 * www.percepio.com
 ******************************************************************************/


#ifndef TRC_KERNEL_PORT_H
#define TRC_KERNEL_PORT_H

#ifdef __cplusplus
extern “C” {
#endif

#include "FreeRTOS.h"	/* Defines configUSE_TRACE_FACILITY */
#include "trcConfig.h"
#include "trcHardwarePort.h"

extern int uiInEventGroupSetBitsFromISR;

#define USE_TRACEALYZER_RECORDER configUSE_TRACE_FACILITY

#if (USE_TRACEALYZER_RECORDER == 1)

/*******************************************************************************
 * Trace_Init
 *
 * The main initalization routine for the embOS-Trace recorder. Configures RTT,
 * activates the PTRACE instrumentation in embOS and the TzCtrl task.
 * Also sets up the diagnostic User Event channels used by TzCtrl task.
 *
 * Settings used by the trace recorder are found in these header files:
 *  - SEGGER_RTT_Conf.h: settings for SEGGER Real-Time Terminal (RTT) which is
 *    used for the trace streaming.
 *  - trcKernelPort.h: RTT related settings for the trace streaming.
 *  - trcRecorder.h - settings for allocation of internal recorder tables.
 *  - trcHardwarePort.h - hardware-specific configuration (timestamping).
 ******************************************************************************/
void Trace_Init(void);

/*******************************************************************************
 * vTraceOnTraceBegin
 *
 * Called on trace begin.
 ******************************************************************************/
void vTraceOnTraceBegin(void);

/*******************************************************************************
 * vTraceOnTraceEnd
 *
 * Called on trace end.
 ******************************************************************************/
void vTraceOnTraceEnd(void);

#include "trcRecorder.h"

/* Defines that must be set for the recorder to work properly */
#define KERNEL_ID 0x1AA1
#define TRACE_TICK_RATE_HZ configTICK_RATE_HZ /* Defined in "FreeRTOS.h" */
#define TRACE_CPU_CLOCK_HZ configCPU_CLOCK_HZ /* Defined in "FreeRTOSConfig.h" */

#if (TRC_RECORDER_HARDWARE_PORT == TRC_PORT_ARM_Cortex_M)
	
	/* Uses CMSIS API. Must be #included in trcConfig.h. */
	#define TRACE_ALLOC_CRITICAL_SECTION() int __irq_status;
	#define TRACE_ENTER_CRITICAL_SECTION() {__irq_status = __get_PRIMASK(); __set_PRIMASK(1);}
	#define TRACE_EXIT_CRITICAL_SECTION() {__set_PRIMASK(__irq_status);}

#endif

#if ((TRC_RECORDER_HARDWARE_PORT == TRC_PORT_ARM_CORTEX_A9) || (TRC_RECORDER_HARDWARE_PORT == TRC_PORT_Renesas_RX600))
	#define TRACE_ALLOC_CRITICAL_SECTION() int __irq_status;
	#define TRACE_ENTER_CRITICAL_SECTION() {__irq_status = portSET_INTERRUPT_MASK_FROM_ISR();}
	#define TRACE_EXIT_CRITICAL_SECTION() {portCLEAR_INTERRUPT_MASK_FROM_ISR(__irq_status);}
#endif

#ifndef TRACE_ENTER_CRITICAL_SECTION
	#error "This port has no valid definition for critical sections! See http://percepio.com/2014/10/27/how-to-define-critical-sections-for-the-recorder/"
#endif

void* prvTraceGetCurrentTaskHandle(void);
uint32_t prvIsNewTCB(void* pNewTCB);

#define OS_IS_SWITCH_FROM_INT_REQUIRED() 0
#define TRACE_GET_CURRENT_TASK() prvTraceGetCurrentTaskHandle()

/*************************************************************************/
/* KERNEL SPECIFIC OBJECT CONFIGURATION									 */
/*************************************************************************/

/*******************************************************************************
 * The event codes - should match the offline config file.
 *
 * Some sections below are encoded to allow for constructions like:
 *
 * vTraceStoreKernelCall(EVENTGROUP_CREATE + objectclass, ...
 *
 * The object class ID is given by the three LSB bits, in such cases. Since each
 * object class has a separate object property table, the class ID is needed to
 * know what section in the object table to use for getting an object name from
 * an object handle.
 ******************************************************************************/

#define PSF_EVENT_NULL_EVENT								0x00

/* PSF event codes */
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

#define PSF_EVENT_TASK_DELETE								0x20
#define PSF_EVENT_QUEUE_DELETE								0x21
#define PSF_EVENT_SEMAPHORE_DELETE							0x22
#define PSF_EVENT_MUTEX_DELETE								0x23
#define PSF_EVENT_TIMER_DELETE								0x24
#define PSF_EVENT_EVENTGROUP_DELETE							0x25

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
#define PSF_EVENT_SEMAPHORE_PEEK							0x71	/* Will never be used */
#define PSF_EVENT_MUTEX_PEEK								0x72	/* Will never be used */

#define PSF_EVENT_QUEUE_PEEK_FAILED							0x73
#define PSF_EVENT_SEMAPHORE_PEEK_FAILED						0x74	/* Will never be used */
#define PSF_EVENT_MUTEX_PEEK_FAILED							0x75	/* Will never be used */

#define PSF_EVENT_QUEUE_PEEK_BLOCK							0x76
#define PSF_EVENT_SEMAPHORE_PEEK_BLOCK						0x77	/* Will never be used */
#define PSF_EVENT_MUTEX_PEEK_BLOCK							0x78	/* Will never be used */

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

#define TRACE_GET_OS_TICKS() (uiTraceTickCount)

/************************************************************************/
/* KERNEL SPECIFIC DATA AND FUNCTIONS NEEDED TO PROVIDE THE				*/
/* FUNCTIONALITY REQUESTED BY THE TRACE RECORDER						*/
/************************************************************************/

#if (configUSE_TIMERS == 1)
#undef INCLUDE_xTimerGetTimerDaemonTaskHandle
#define INCLUDE_xTimerGetTimerDaemonTaskHandle 1
#endif

/************************************************************************/
/* KERNEL SPECIFIC MACROS USED BY THE TRACE RECORDER					*/
/************************************************************************/

#define TRACE_MALLOC(size) pvPortMalloc(size)

/************************************************************************/
/* KERNEL SPECIFIC WRAPPERS THAT SHOULD BE CALLED BY THE KERNEL		 */
/************************************************************************/

#if (configUSE_TICKLESS_IDLE != 0)

#undef traceLOW_POWER_IDLE_BEGIN
#define traceLOW_POWER_IDLE_BEGIN() \
	{ \
		vTraceStoreEvent0(PSF_EVENT_LOWPOWER_BEGIN); \
	}

#undef traceLOW_POWER_IDLE_END
#define traceLOW_POWER_IDLE_END() \
	{ \
		vTraceStoreEvent0(PSF_EVENT_LOWPOWER_END); \
	}

#endif

/* A macro that will update the tick count when returning from tickless idle */
#undef traceINCREASE_TICK_COUNT
/* Note: This can handle time adjustments of max 2^32 ticks, i.e., 35 seconds at 120 MHz. Thus, tick-less idle periods longer than 2^32 ticks will appear "compressed" on the time line.*/
#define traceINCREASE_TICK_COUNT( xCount ) 

/* Called for each task that becomes ready */
#undef traceMOVED_TASK_TO_READY_STATE
#define traceMOVED_TASK_TO_READY_STATE( pxTCB ) \
	vTraceStoreEvent1(PSF_EVENT_TASK_READY, (uint32_t)pxTCB);

/* Called on each OS tick. Will call uiPortGetTimestamp to make sure it is called at least once every OS tick. */
#undef traceTASK_INCREMENT_TICK
#if (TRC_FREERTOS_VERSION == TRC_FREERTOS_VERSION_7_3_OR_7_4)

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxMissedTicks == 0) { extern uint32_t uiTraceTickCount; uiTraceTickCount++; } \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE) { vTraceStoreEvent1(PSF_EVENT_NEW_TIME, (xTickCount + 1)); }

#else

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxPendedTicks == 0) { extern uint32_t uiTraceTickCount; uiTraceTickCount++; } \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE) { vTraceStoreEvent1(PSF_EVENT_NEW_TIME, (xTickCount + 1)); }

#endif

/* Called on each task-switch */
#undef traceTASK_SWITCHED_IN
#define traceTASK_SWITCHED_IN() \
	if (prvIsNewTCB(pxCurrentTCB)) \
	{ \
		vTraceStoreEvent2(PSF_EVENT_TASK_ACTIVATE, (uint32_t)pxCurrentTCB, pxCurrentTCB->uxPriority); \
	}

/* Called on vTaskSuspend */
#undef traceTASK_SUSPEND
#define traceTASK_SUSPEND( pxTaskToSuspend ) \
	vTraceStoreEvent1(PSF_EVENT_TASK_SUSPEND, (uint32_t)pxTaskToSuspend);

/* Called on vTaskDelay - note the use of FreeRTOS variable xTicksToDelay */
#undef traceTASK_DELAY
#define traceTASK_DELAY() \
	vTraceStoreEvent1(PSF_EVENT_TASK_DELAY, xTicksToDelay);

/* Called on vTaskDelayUntil - note the use of FreeRTOS variable xTimeToWake */
#undef traceTASK_DELAY_UNTIL
#define traceTASK_DELAY_UNTIL() \
	vTraceStoreEvent1(PSF_EVENT_TASK_DELAY_UNTIL, xTimeToWake);

/* Called on vTaskDelete */
#undef traceTASK_DELETE
#define traceTASK_DELETE( pxTaskToDelete ) \
	vTraceStoreEvent2(PSF_EVENT_TASK_DELETE, (uint32_t)pxTaskToDelete, (pxTaskToDelete != NULL) ? (pxTaskToDelete->uxPriority) : 0);

/* Called on vQueueDelete */
#undef traceQUEUE_DELETE
#define traceQUEUE_DELETE( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent2(PSF_EVENT_QUEUE_DELETE, (uint32_t)pxQueue, (pxQueue != NULL) ? (pxQueue->uxMessagesWaiting) : 0); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			vTraceStoreEvent2(PSF_EVENT_MUTEX_DELETE, (uint32_t)pxQueue, (pxQueue != NULL) ? (pxQueue->uxMessagesWaiting) : 0); \
			break; \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
			vTraceStoreEvent2(PSF_EVENT_SEMAPHORE_DELETE, (uint32_t)pxQueue, (pxQueue != NULL) ? (pxQueue->uxMessagesWaiting) : 0); \
			break; \
	}

/* Called on vTaskCreate */
#undef traceTASK_CREATE
#define traceTASK_CREATE(pxNewTCB) \
	if (pxNewTCB != NULL) \
	{ \
		vTraceSaveSymbol(pxNewTCB, (const char*)pcName); \
		vTraceSaveObjectData(pxNewTCB, uxPriority); \
		vTraceStoreStringEvent(1, PSF_EVENT_OBJ_NAME, pcName, pxNewTCB); \
		vTraceStoreEvent2(PSF_EVENT_TASK_CREATE, (uint32_t)pxNewTCB, uxPriority); \
	}

/* Called in vTaskCreate, if it fails (typically if the stack can not be allocated) */
#undef traceTASK_CREATE_FAILED
#define traceTASK_CREATE_FAILED() \
	vTraceStoreEvent0(PSF_EVENT_TASK_CREATE_FAILED);

/* Called in xQueueCreate, and thereby for all other object based on queues, such as semaphores. */
#undef traceQUEUE_CREATE
#define traceQUEUE_CREATE( pxNewQueue )\
	switch (pxNewQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent2(PSF_EVENT_QUEUE_CREATE, (uint32_t)pxNewQueue, pxNewQueue->uxLength); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
			vTraceStoreEvent1(PSF_EVENT_SEMAPHORE_BINARY_CREATE, (uint32_t)pxNewQueue); \
			break; \
	}

/* Called in xQueueCreate, if the queue creation fails */
#undef traceQUEUE_CREATE_FAILED
#define traceQUEUE_CREATE_FAILED( queueType ) \
	switch (queueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent0(PSF_EVENT_QUEUE_CREATE_FAILED); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
			vTraceStoreEvent0(PSF_EVENT_SEMAPHORE_BINARY_CREATE_FAILED); \
			break; \
	}

/* Called in xQueueCreateCountingSemaphore, if the queue creation fails */
#undef traceCREATE_COUNTING_SEMAPHORE
#if TRC_FREERTOS_VERSION == TRC_FREERTOS_VERSION_8_0_OR_LATER
#define traceCREATE_COUNTING_SEMAPHORE() \
	vTraceStoreEvent2(PSF_EVENT_SEMAPHORE_COUNTING_CREATE, (uint32_t)xHandle, ((Queue_t *) xHandle)->uxMessagesWaiting);
#else
#define traceCREATE_COUNTING_SEMAPHORE() \
	vTraceStoreEvent2(PSF_EVENT_SEMAPHORE_COUNTING_CREATE, (uint32_t)pxHandle, pxHandle->uxMessagesWaiting);
#endif

#undef traceCREATE_COUNTING_SEMAPHORE_FAILED
#define traceCREATE_COUNTING_SEMAPHORE_FAILED() \
	vTraceStoreEvent0(PSF_EVENT_SEMAPHORE_COUNTING_CREATE_FAILED);

/* Called in xQueueCreateMutex, and thereby also from xSemaphoreCreateMutex and xSemaphoreCreateRecursiveMutex */
#undef traceCREATE_MUTEX
#define traceCREATE_MUTEX( pxNewQueue ) \
	switch (ucQueueType) \
	{ \
		case queueQUEUE_TYPE_MUTEX: \
			vTraceStoreEvent1(PSF_EVENT_MUTEX_CREATE, (uint32_t)pxNewQueue); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			vTraceStoreEvent1(PSF_EVENT_MUTEX_RECURSIVE_CREATE, (uint32_t)pxNewQueue); \
			break; \
	}

/* Called in xQueueCreateMutex when the operation fails (when memory allocation fails) */
#undef traceCREATE_MUTEX_FAILED
#define traceCREATE_MUTEX_FAILED() \
	switch (ucQueueType) \
	{ \
		case queueQUEUE_TYPE_MUTEX: \
			vTraceStoreEvent0(PSF_EVENT_MUTEX_CREATE_FAILED); \
			break; \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			vTraceStoreEvent0(PSF_EVENT_MUTEX_CREATE_FAILED); \
			break; \
	}

/* Called when a message is sent to a queue */	/* CS IS NEW ! */
#undef traceQUEUE_SEND
#define traceQUEUE_SEND( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent2(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND : PSF_EVENT_QUEUE_SEND_FRONT, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting + 1); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent2(PSF_EVENT_SEMAPHORE_GIVE, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting + 1); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			vTraceStoreEvent1(PSF_EVENT_MUTEX_GIVE, (uint32_t)pxQueue); \
			break; \
	}

/* Called when a message failed to be sent to a queue (timeout) */
#undef traceQUEUE_SEND_FAILED
#define traceQUEUE_SEND_FAILED( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent2(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_FAILED : PSF_EVENT_QUEUE_SEND_FRONT_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent2(PSF_EVENT_SEMAPHORE_GIVE_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			vTraceStoreEvent1(PSF_EVENT_MUTEX_GIVE_FAILED, (uint32_t)pxQueue); \
			break; \
	}

	/*trcKERNEL_HOOKS_KERNEL_SERVICE(SEND, FAILED, UNUSED, pxQueue);*/

/* Called when the task is blocked due to a send operation on a full queue */
#undef traceBLOCKING_ON_QUEUE_SEND
#define traceBLOCKING_ON_QUEUE_SEND( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent2(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_BLOCK : PSF_EVENT_QUEUE_SEND_FRONT_BLOCK, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent2(PSF_EVENT_SEMAPHORE_GIVE_BLOCK, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			vTraceStoreEvent1(PSF_EVENT_MUTEX_GIVE_BLOCK, (uint32_t)pxQueue); \
			break; \
	}

/* Called for Recursive Mutex */
#undef traceGIVE_MUTEX_RECURSIVE
#define traceGIVE_MUTEX_RECURSIVE( pxMutex ) \
	vTraceStoreEvent1(PSF_EVENT_MUTEX_GIVE_RECURSIVE, (uint32_t)pxMutex);

/* Called for Recursive Mutex */
#undef traceGIVE_MUTEX_RECURSIVE_FAILED
#define traceGIVE_MUTEX_RECURSIVE_FAILED( pxMutex ) \
	vTraceStoreEvent1(PSF_EVENT_MUTEX_GIVE_RECURSIVE_FAILED, (uint32_t)pxMutex);

/**************************************************************************/
/* Hack to make sure xQueueGiveFromISR also has a xCopyPosition parameter */
/**************************************************************************/
/* Helpers needed to correctly expand names */
#define TZ__CAT2(a,b) a ## b
#define TZ__CAT(a,b) TZ__CAT2(a, b)

/* Expands name if this header is included... uxQueueType must be a macro that only exists in queue.c or whatever, and it must expand to nothing or to something that's valid in identifiers */
#define xQueueGiveFromISR(a,b) TZ__CAT(xQueueGiveFromISR__, uxQueueType) (a,b)

/* If in queue.c, the "uxQueueType" macro expands to "pcHead". queueSEND_TO_BACK is the value we need to send in */
#define xQueueGiveFromISR__pcHead(__a, __b) MyWrapper(__a, __b, const BaseType_t xCopyPosition); \
BaseType_t xQueueGiveFromISR(__a, __b) { return MyWrapper(xQueue, pxHigherPriorityTaskWoken, queueSEND_TO_BACK); } \
BaseType_t MyWrapper(__a, __b, const BaseType_t xCopyPosition)

/* If not in queue.c, "uxQueueType" isn't expanded */
#define xQueueGiveFromISR__uxQueueType(__a, __b) xQueueGiveFromISR(__a,__b)

/**************************************************************************/
/* End of xQueueGiveFromISR hack                                          */
/**************************************************************************/

/* Called when a message is sent from interrupt context, e.g., using xQueueSendFromISR */
#undef traceQUEUE_SEND_FROM_ISR
#define traceQUEUE_SEND_FROM_ISR( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent2(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_FROMISR : PSF_EVENT_QUEUE_SEND_FRONT_FROMISR, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting + 1); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent2(PSF_EVENT_SEMAPHORE_GIVE_FROMISR, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting + 1); \
			break; \
	}

/* Called when a message send from interrupt context fails (since the queue was full) */
#undef traceQUEUE_SEND_FROM_ISR_FAILED
#define traceQUEUE_SEND_FROM_ISR_FAILED( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent2(xCopyPosition == queueSEND_TO_BACK ? PSF_EVENT_QUEUE_SEND_FROMISR_FAILED : PSF_EVENT_QUEUE_SEND_FRONT_FROMISR_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent2(PSF_EVENT_SEMAPHORE_GIVE_FROMISR_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
			break; \
	}

/* Called when a message is received from a queue */
#undef traceQUEUE_RECEIVE
#define traceQUEUE_RECEIVE( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent3(PSF_EVENT_QUEUE_RECEIVE, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting - 1); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent3(PSF_EVENT_SEMAPHORE_TAKE, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting - 1); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			vTraceStoreEvent2(PSF_EVENT_MUTEX_TAKE, (uint32_t)pxQueue, xTicksToWait); \
			break; \
	}

/* Called when a receive operation on a queue fails (timeout) */
#undef traceQUEUE_RECEIVE_FAILED
#define traceQUEUE_RECEIVE_FAILED( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent3(xJustPeeking == pdFALSE ? PSF_EVENT_QUEUE_RECEIVE_FAILED : PSF_EVENT_QUEUE_PEEK_FAILED, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent3(xJustPeeking == pdFALSE ? PSF_EVENT_SEMAPHORE_TAKE_FAILED : PSF_EVENT_SEMAPHORE_PEEK_FAILED, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			vTraceStoreEvent2(xJustPeeking == pdFALSE ? PSF_EVENT_MUTEX_TAKE_FAILED : PSF_EVENT_MUTEX_PEEK_FAILED, (uint32_t)pxQueue, xTicksToWait); \
			break; \
	}

/* Called when the task is blocked due to a receive operation on an empty queue */
#undef traceBLOCKING_ON_QUEUE_RECEIVE
#define traceBLOCKING_ON_QUEUE_RECEIVE( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent3(xJustPeeking == pdFALSE ? PSF_EVENT_QUEUE_RECEIVE_BLOCK : PSF_EVENT_QUEUE_PEEK_BLOCK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent3(xJustPeeking == pdFALSE ? PSF_EVENT_SEMAPHORE_TAKE_BLOCK : PSF_EVENT_SEMAPHORE_PEEK_BLOCK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			vTraceStoreEvent2(xJustPeeking == pdFALSE ? PSF_EVENT_MUTEX_TAKE_BLOCK : PSF_EVENT_MUTEX_PEEK_BLOCK, (uint32_t)pxQueue, xTicksToWait); \
			break; \
	}
		
#undef traceTAKE_MUTEX_RECURSIVE
#if TRC_FREERTOS_VERSION == TRC_FREERTOS_VERSION_8_0_OR_LATER
#define traceTAKE_MUTEX_RECURSIVE( pxQueue ) \
	vTraceStoreEvent2(PSF_EVENT_MUTEX_TAKE_RECURSIVE, (uint32_t)pxQueue, xTicksToWait);
#else
#define traceTAKE_MUTEX_RECURSIVE( pxQueue ) \
	vTraceStoreEvent2(PSF_EVENT_MUTEX_TAKE_RECURSIVE, (uint32_t)pxQueue, xBlockTime);
#endif

#undef traceTAKE_MUTEX_RECURSIVE_FAILED
#if TRC_FREERTOS_VERSION == TRC_FREERTOS_VERSION_8_0_OR_LATER
#define traceTAKE_MUTEX_RECURSIVE_FAILED( pxQueue ) \
vTraceStoreEvent2(PSF_EVENT_MUTEX_TAKE_RECURSIVE_FAILED, (uint32_t)pxQueue, xTicksToWait);
#else
#define traceTAKE_MUTEX_RECURSIVE_FAILED( pxQueue ) \
vTraceStoreEvent2(PSF_EVENT_MUTEX_TAKE_RECURSIVE_FAILED, (uint32_t)pxQueue, xBlockTime);
#endif

/* Called when a message is received in interrupt context, e.g., using xQueueReceiveFromISR */
#undef traceQUEUE_RECEIVE_FROM_ISR
#define traceQUEUE_RECEIVE_FROM_ISR( pxQueue ) \
switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent2(PSF_EVENT_QUEUE_RECEIVE_FROMISR, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting - 1); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent2(PSF_EVENT_SEMAPHORE_TAKE_FROMISR, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting - 1); \
			break; \
	}

/* Called when a message receive from interrupt context fails (since the queue was empty) */
#undef traceQUEUE_RECEIVE_FROM_ISR_FAILED
#define traceQUEUE_RECEIVE_FROM_ISR_FAILED( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent2(PSF_EVENT_QUEUE_RECEIVE_FROMISR_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent2(PSF_EVENT_SEMAPHORE_TAKE_FROMISR_FAILED, (uint32_t)pxQueue, pxQueue->uxMessagesWaiting); \
			break; \
	}

/* Called on xQueuePeek */
#undef traceQUEUE_PEEK
#define traceQUEUE_PEEK( pxQueue ) \
	switch (pxQueue->ucQueueType) \
	{ \
		case queueQUEUE_TYPE_BASE: \
			vTraceStoreEvent3(PSF_EVENT_QUEUE_PEEK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_BINARY_SEMAPHORE: \
		case queueQUEUE_TYPE_COUNTING_SEMAPHORE: \
			vTraceStoreEvent3(PSF_EVENT_SEMAPHORE_PEEK, (uint32_t)pxQueue, xTicksToWait, pxQueue->uxMessagesWaiting); \
			break; \
		case queueQUEUE_TYPE_MUTEX: \
		case queueQUEUE_TYPE_RECURSIVE_MUTEX: \
			vTraceStoreEvent1(PSF_EVENT_MUTEX_PEEK, (uint32_t)pxQueue); \
			break; \
	}

/* Called in vTaskPrioritySet */
#undef traceTASK_PRIORITY_SET
#define traceTASK_PRIORITY_SET( pxTask, uxNewPriority ) \
	vTraceStoreEvent2(PSF_EVENT_TASK_PRIORITY, (uint32_t)pxTask, uxNewPriority);
	
/* Called in vTaskPriorityInherit, which is called by Mutex operations */
#undef traceTASK_PRIORITY_INHERIT
#define traceTASK_PRIORITY_INHERIT( pxTask, uxNewPriority ) \
	vTraceStoreEvent2(PSF_EVENT_TASK_PRIO_INHERIT, (uint32_t)pxTask, uxNewPriority);

/* Called in vTaskPriorityDisinherit, which is called by Mutex operations */
#undef traceTASK_PRIORITY_DISINHERIT
#define traceTASK_PRIORITY_DISINHERIT( pxTask, uxNewPriority ) \
	vTraceStoreEvent2(PSF_EVENT_TASK_PRIO_DISINHERIT, (uint32_t)pxTask, uxNewPriority);

/* Called in vTaskResume */
#undef traceTASK_RESUME
#define traceTASK_RESUME( pxTaskToResume ) \
	vTraceStoreEvent1(PSF_EVENT_TASK_RESUME, (uint32_t)pxTaskToResume);

/* Called in vTaskResumeFromISR */
#undef traceTASK_RESUME_FROM_ISR
#define traceTASK_RESUME_FROM_ISR( pxTaskToResume ) \
	vTraceStoreEvent1(PSF_EVENT_TASK_RESUME_FROMISR, (uint32_t)pxTaskToResume);

#undef traceMALLOC
#define traceMALLOC( pvAddress, uiSize ) \
	vTraceStoreEvent2(PSF_EVENT_MALLOC, (uint32_t)pvAddress, (int32_t)uiSize);

#undef traceFREE
#define traceFREE( pvAddress, uiSize ) \
	vTraceStoreEvent2(PSF_EVENT_FREE, (uint32_t)pvAddress, (int32_t)(-uiSize));

/* Called in timer.c - xTimerCreate */
#undef traceTIMER_CREATE
#define traceTIMER_CREATE(tmr) \
	vTraceStoreEvent2(PSF_EVENT_TIMER_CREATE, (uint32_t)tmr, tmr->xTimerPeriodInTicks);

#undef traceTIMER_CREATE_FAILED
#define traceTIMER_CREATE_FAILED() \
	vTraceStoreEvent0(PSF_EVENT_TIMER_CREATE_FAILED);

#if TRC_FREERTOS_VERSION == TRC_FREERTOS_VERSION_8_0_OR_LATER
#define traceTIMER_COMMAND_SEND_8_0_CASES(tmr) \
	case tmrCOMMAND_RESET: \
		vTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_RESET : PSF_EVENT_TIMER_RESET_FAILED, (uint32_t)tmr, xOptionalValue); \
		break; \
	case tmrCOMMAND_START_FROM_ISR: \
		vTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_START_FROMISR : PSF_EVENT_TIMER_START_FROMISR_FAILED, (uint32_t)tmr, xOptionalValue); \
		break; \
	case tmrCOMMAND_RESET_FROM_ISR: \
		vTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_RESET_FROMISR : PSF_EVENT_TIMER_RESET_FROMISR_FAILED, (uint32_t)tmr, xOptionalValue); \
		break; \
	case tmrCOMMAND_STOP_FROM_ISR: \
		vTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_STOP_FROMISR : PSF_EVENT_TIMER_STOP_FROMISR_FAILED, (uint32_t)tmr, xOptionalValue); \
		break; \
	case tmrCOMMAND_CHANGE_PERIOD_FROM_ISR: \
		vTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_CHANGEPERIOD_FROMISR : PSF_EVENT_TIMER_CHANGEPERIOD_FROMISR_FAILED, (uint32_t)tmr, xOptionalValue); \
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
			break; \
		case tmrCOMMAND_STOP: \
			break; \
		case tmrCOMMAND_CHANGE_PERIOD: \
			vTraceStoreEvent2((xReturn == pdPASS) ? PSF_EVENT_TIMER_CHANGEPERIOD : PSF_EVENT_TIMER_CHANGEPERIOD_FAILED, (uint32_t)tmr, xOptionalValue); \
			break; \
		case tmrCOMMAND_DELETE: \
			vTraceStoreEvent1((xReturn == pdPASS) ? PSF_EVENT_TIMER_DELETE : PSF_EVENT_TIMER_DELETE_FAILED, (uint32_t)tmr); \
			break; \
		traceTIMER_COMMAND_SEND_8_0_CASES(tmr) \
	}

#undef tracePEND_FUNC_CALL
#define tracePEND_FUNC_CALL(func, arg1, arg2, ret) \
	vTraceStoreEvent1((ret == pdPASS) ? PSF_EVENT_TIMER_PENDFUNCCALL : PSF_EVENT_TIMER_PENDFUNCCALL_FAILED, (uint32_t)func);

#undef tracePEND_FUNC_CALL_FROM_ISR
#define tracePEND_FUNC_CALL_FROM_ISR(func, arg1, arg2, ret) \
	vTraceStoreEvent1((ret == pdPASS) ? PSF_EVENT_TIMER_PENDFUNCCALL_FROMISR : PSF_EVENT_TIMER_PENDFUNCCALL_FROMISR_FAILED, (uint32_t)func);

#undef traceEVENT_GROUP_CREATE
#define traceEVENT_GROUP_CREATE(eg) \
	vTraceStoreEvent1(PSF_EVENT_EVENTGROUP_CREATE, (uint32_t)eg);

#undef traceEVENT_GROUP_DELETE
#define traceEVENT_GROUP_DELETE(eg) \
	vTraceStoreEvent1(PSF_EVENT_EVENTGROUP_DELETE, (uint32_t)eg);

#undef traceEVENT_GROUP_CREATE_FAILED
#define traceEVENT_GROUP_CREATE_FAILED() \
	vTraceStoreEvent0(PSF_EVENT_EVENTGROUP_CREATE_FAILED);

#undef traceEVENT_GROUP_SYNC_BLOCK
#define traceEVENT_GROUP_SYNC_BLOCK(eg, bitsToSet, bitsToWaitFor) \
	vTraceStoreEvent2(PSF_EVENT_EVENTGROUP_SYNC_BLOCK, (uint32_t)eg, bitsToWaitFor);

#undef traceEVENT_GROUP_SYNC_END
#define traceEVENT_GROUP_SYNC_END(eg, bitsToSet, bitsToWaitFor, wasTimeout) \
	vTraceStoreEvent2((wasTimeout != pdTRUE) ? PSF_EVENT_EVENTGROUP_SYNC : PSF_EVENT_EVENTGROUP_SYNC_FAILED, (uint32_t)eg, bitsToWaitFor);

#undef traceEVENT_GROUP_WAIT_BITS_BLOCK
#define traceEVENT_GROUP_WAIT_BITS_BLOCK(eg, bitsToWaitFor) \
	vTraceStoreEvent2(PSF_EVENT_EVENTGROUP_WAITBITS_BLOCK, (uint32_t)eg, bitsToWaitFor);

#undef traceEVENT_GROUP_WAIT_BITS_END
#define traceEVENT_GROUP_WAIT_BITS_END(eg, bitsToWaitFor, wasTimeout) \
	vTraceStoreEvent2((wasTimeout != pdTRUE) ? PSF_EVENT_EVENTGROUP_WAITBITS : PSF_EVENT_EVENTGROUP_WAITBITS_FAILED, (uint32_t)eg, bitsToWaitFor);

#undef traceEVENT_GROUP_CLEAR_BITS
#define traceEVENT_GROUP_CLEAR_BITS(eg, bitsToClear) \
	vTraceStoreEvent2(PSF_EVENT_EVENTGROUP_CLEARBITS, (uint32_t)eg, bitsToClear);

#undef traceEVENT_GROUP_CLEAR_BITS_FROM_ISR
#define traceEVENT_GROUP_CLEAR_BITS_FROM_ISR(eg, bitsToClear) \
	vTraceStoreEvent2(PSF_EVENT_EVENTGROUP_CLEARBITS_FROMISR, (uint32_t)eg, bitsToClear);

#undef traceEVENT_GROUP_SET_BITS
#define traceEVENT_GROUP_SET_BITS(eg, bitsToSet) \
	vTraceStoreEvent2(PSF_EVENT_EVENTGROUP_SETBITS, (uint32_t)eg, bitsToSet);

#undef traceEVENT_GROUP_SET_BITS_FROM_ISR
#define traceEVENT_GROUP_SET_BITS_FROM_ISR(eg, bitsToSet) \
	vTraceStoreEvent2(PSF_EVENT_EVENTGROUP_SETBITS_FROMISR, (uint32_t)eg, bitsToSet);

#undef traceTASK_NOTIFY_TAKE
#define traceTASK_NOTIFY_TAKE() \
	if (pxCurrentTCB->eNotifyState == eNotified) \
		vTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE, (uint32_t)pxCurrentTCB, xTicksToWait); \
	else \
		vTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE_FAILED, (uint32_t)pxCurrentTCB, xTicksToWait);

#undef traceTASK_NOTIFY_TAKE_BLOCK
#define traceTASK_NOTIFY_TAKE_BLOCK() \
	vTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_TAKE_BLOCK, (uint32_t)pxCurrentTCB, xTicksToWait);

#undef traceTASK_NOTIFY_WAIT
#define traceTASK_NOTIFY_WAIT() \
	if (pxCurrentTCB->eNotifyState == eNotified) \
		vTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT, (uint32_t)pxCurrentTCB, xTicksToWait); \
	else \
		vTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT_FAILED, (uint32_t)pxCurrentTCB, xTicksToWait);

#undef traceTASK_NOTIFY_WAIT_BLOCK
#define traceTASK_NOTIFY_WAIT_BLOCK() \
	vTraceStoreEvent2(PSF_EVENT_TASK_NOTIFY_WAIT_BLOCK, (uint32_t)pxCurrentTCB, xTicksToWait);

#undef traceTASK_NOTIFY
#define traceTASK_NOTIFY() \
	vTraceStoreEvent1(PSF_EVENT_TASK_NOTIFY, (uint32_t)xTaskToNotify);

#undef traceTASK_NOTIFY_FROM_ISR
#define traceTASK_NOTIFY_FROM_ISR() \
	vTraceStoreEvent1(PSF_EVENT_TASK_NOTIFY_FROM_ISR, (uint32_t)xTaskToNotify);
	
#undef traceTASK_NOTIFY_GIVE_FROM_ISR
#define traceTASK_NOTIFY_GIVE_FROM_ISR() \
	vTraceStoreEvent1(PSF_EVENT_TASK_NOTIFY_GIVE_FROM_ISR, (uint32_t)xTaskToNotify);

/************************************************************************/
/* KERNEL SPECIFIC MACROS TO NAME OBJECTS, IF NECESSARY				 */
/************************************************************************/
#define vTraceSetQueueName(object, name) \
vTraceStoreKernelObjectName(object, name);

#define vTraceSetSemaphoreName(object, name) \
vTraceStoreKernelObjectName(object, name);

#define vTraceSetMutexName(object, name) \
vTraceStoreKernelObjectName(object, name);

#define vTraceSetEventGroupName(object, name) \
vTraceStoreKernelObjectName(object, name);

#else /*(USE_TRACEALYZER_RECORDER == 1)*/

#define vTraceSetQueueName(object, name)

#define vTraceSetSemaphoreName(object, name)

#define vTraceSetMutexName(object, name)

#define vTraceSetEventGroupName(object, name)

#define Trace_Init() 

#endif /*(USE_TRACEALYZER_RECORDER == 1)*/

#ifdef __cplusplus
}
#endif

#endif /* TRC_KERNEL_PORT_H */
