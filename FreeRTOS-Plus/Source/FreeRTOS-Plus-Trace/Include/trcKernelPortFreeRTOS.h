/*******************************************************************************
 * Tracealyzer v2.7.0 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcKernelPortFreeRTOS.h
 *
 * Kernel-specific functionality for FreeRTOS, used by the recorder library.
 *
 * Terms of Use
 * This software is copyright Percepio AB. The recorder library is free for
 * use together with Percepio products. You may distribute the recorder library
 * in its original form, including modifications in trcHardwarePort.c/.h
 * given that these modification are clearly marked as your own modifications
 * and documented in the initial comment section of these source files.
 * This software is the intellectual property of Percepio AB and may not be
 * sold or in other ways commercially redistributed without explicit written
 * permission by Percepio AB.
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
 * Copyright Percepio AB, 2014.
 * www.percepio.com
 ******************************************************************************/


#ifndef TRCKERNELPORTFREERTOS_H
#define TRCKERNELPORTFREERTOS_H

#include "FreeRTOS.h"	/* Defines configUSE_TRACE_FACILITY */
#include "trcHardwarePort.h"

extern int uiInEventGroupSetBitsFromISR;

#define USE_TRACEALYZER_RECORDER configUSE_TRACE_FACILITY

#if (USE_TRACEALYZER_RECORDER == 1)

/* Defines that must be set for the recorder to work properly */
#define TRACE_KERNEL_VERSION 0x1AA1
#define TRACE_TICK_RATE_HZ configTICK_RATE_HZ /* Defined in "FreeRTOS.h" */
#define TRACE_CPU_CLOCK_HZ configCPU_CLOCK_HZ /* Defined in "FreeRTOSConfig.h" */

#if (SELECTED_PORT == PORT_ARM_CortexM)
	
	#include "board.h" // Uses CMSIS API
	
	#define TRACE_SR_ALLOC_CRITICAL_SECTION() int __irq_status;
	#define TRACE_ENTER_CRITICAL_SECTION() {__irq_status = __get_PRIMASK(); __set_PRIMASK(1);}
	#define TRACE_EXIT_CRITICAL_SECTION() {__set_PRIMASK(__irq_status);}
	
#endif 

#if ((SELECTED_PORT == PORT_ARM_CORTEX_A9) || (SELECTED_PORT == PORT_Renesas_RX600) || (SELECTED_PORT == PORT_MICROCHIP_PIC32MX) || (SELECTED_PORT == PORT_MICROCHIP_PIC32MZ))
	#define TRACE_SR_ALLOC_CRITICAL_SECTION() int __irq_status;
	#define TRACE_ENTER_CRITICAL_SECTION() {__irq_status = portSET_INTERRUPT_MASK_FROM_ISR();}
	#define TRACE_EXIT_CRITICAL_SECTION() {portCLEAR_INTERRUPT_MASK_FROM_ISR(__irq_status);}
#endif

#ifndef TRACE_ENTER_CRITICAL_SECTION
	#error "This port has no valid definition for critical sections! See http://percepio.com/2014/10/27/how-to-define-critical-sections-for-the-recorder/"
#endif

#ifndef TRACE_EXIT_CRITICAL_SECTION
	#error "This port has no valid definition for critical sections! See http://percepio.com/2014/10/27/how-to-define-critical-sections-for-the-recorder/"
#endif

#if (SELECTED_PORT == PORT_ARM_CortexM)
	#define trcCRITICAL_SECTION_BEGIN_ON_CORTEX_M_ONLY trcCRITICAL_SECTION_BEGIN
	#define trcCRITICAL_SECTION_END_ON_CORTEX_M_ONLY trcCRITICAL_SECTION_END
#else
	#define trcCRITICAL_SECTION_BEGIN_ON_CORTEX_M_ONLY() recorder_busy++;
	#define trcCRITICAL_SECTION_END_ON_CORTEX_M_ONLY() recorder_busy--;
#endif

/*************************************************************************/
/* KERNEL SPECIFIC OBJECT CONFIGURATION									 */
/*************************************************************************/
#define TRACE_NCLASSES 7
#define TRACE_CLASS_QUEUE ((traceObjectClass)0)
#define TRACE_CLASS_SEMAPHORE ((traceObjectClass)1)
#define TRACE_CLASS_MUTEX ((traceObjectClass)2)
#define TRACE_CLASS_TASK ((traceObjectClass)3)
#define TRACE_CLASS_ISR ((traceObjectClass)4)
#define TRACE_CLASS_TIMER ((traceObjectClass)5)
#define TRACE_CLASS_EVENTGROUP ((traceObjectClass)6)

#define TRACE_KERNEL_OBJECT_COUNT (NQueue + NSemaphore + NMutex + NTask + NISR + NTimer + NEventGroup)

/* The size of the Object Property Table entries, in bytes, per object */

/* Queue properties (except name):	current number of message in queue */
#define PropertyTableSizeQueue		(NameLenQueue + 1)

/* Semaphore properties (except name): state (signaled = 1, cleared = 0) */
#define PropertyTableSizeSemaphore	(NameLenSemaphore + 1)

/* Mutex properties (except name):	owner (task handle, 0 = free) */
#define PropertyTableSizeMutex		(NameLenMutex + 1)

/* Task properties (except name):	Byte 0: Current priority
									Byte 1: state (if already active)
									Byte 2: legacy, not used
									Byte 3: legacy, not used */
#define PropertyTableSizeTask		(NameLenTask + 4)

/* ISR properties:					Byte 0: priority
									Byte 1: state (if already active) */
#define PropertyTableSizeISR		(NameLenISR + 2)

/* NTimer properties:				Byte 0: state (unused for now) */
#define PropertyTableSizeTimer		(NameLenTimer + 1)

/* NEventGroup properties:			Byte 0-3: state (unused for now)*/
#define PropertyTableSizeEventGroup	(NameLenEventGroup + 4)


/* The layout of the byte array representing the Object Property Table */
#define StartIndexQueue			0
#define StartIndexSemaphore		StartIndexQueue		+ NQueue		* PropertyTableSizeQueue
#define StartIndexMutex			StartIndexSemaphore + NSemaphore	* PropertyTableSizeSemaphore
#define StartIndexTask			StartIndexMutex		+ NMutex		* PropertyTableSizeMutex
#define StartIndexISR			StartIndexTask		+ NTask			* PropertyTableSizeTask
#define StartIndexTimer			StartIndexISR		+ NISR			* PropertyTableSizeISR
#define StartIndexEventGroup	StartIndexTimer		+ NTimer		* PropertyTableSizeTimer

/* Number of bytes used by the object table */
#define TRACE_OBJECT_TABLE_SIZE	StartIndexEventGroup + NEventGroup * PropertyTableSizeEventGroup

#define FREERTOS_VERSION_NOT_SET			0
#define FREERTOS_VERSION_7_3_OR_7_4			1
#define FREERTOS_VERSION_7_5_OR_7_6			2
#define FREERTOS_VERSION_8_0_OR_LATER		3

/* Includes */
#include "trcConfig.h" /* Must be first, even before trcTypes.h */
#include "trcHardwarePort.h"
#include "trcTypes.h"
#include "trcKernelHooks.h"
#include "trcBase.h"
#include "trcKernel.h"
#include "trcUser.h"

#if (INCLUDE_NEW_TIME_EVENTS == 1 && configUSE_TICKLESS_IDLE != 0)
#error "NewTime events can not be used in combination with tickless idle!"
#endif

/* Initialization of the object property table */
void vTraceInitObjectPropertyTable(void);

/* Initialization of the handle mechanism, see e.g, xTraceGetObjectHandle */
void vTraceInitObjectHandleStack(void);

/* Returns the "Not enough handles" error message for the specified object class */
const char* pszTraceGetErrorNotEnoughHandles(traceObjectClass objectclass);

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

#define NULL_EVENT					(0x00) /* Ignored in the analysis*/

/*******************************************************************************
 * EVENTGROUP_DIV
 *
 * Miscellaneous events.
 ******************************************************************************/
#define EVENTGROUP_DIV				(NULL_EVENT + 1)					/*0x01*/
#define DIV_XPS						(EVENTGROUP_DIV + 0)				/*0x01*/
#define DIV_TASK_READY				(EVENTGROUP_DIV + 1)				/*0x02*/
#define DIV_NEW_TIME				(EVENTGROUP_DIV + 2)				/*0x03*/

/*******************************************************************************
 * EVENTGROUP_TS
 *
 * Events for storing task-switches and interrupts. The RESUME events are
 * generated if the task/interrupt is already marked active.
 ******************************************************************************/
#define EVENTGROUP_TS				(EVENTGROUP_DIV + 3)				/*0x04*/
#define TS_ISR_BEGIN				(EVENTGROUP_TS + 0)					/*0x04*/
#define TS_ISR_RESUME				(EVENTGROUP_TS + 1)					/*0x05*/
#define TS_TASK_BEGIN				(EVENTGROUP_TS + 2)					/*0x06*/
#define TS_TASK_RESUME				(EVENTGROUP_TS + 3)					/*0x07*/

/*******************************************************************************
 * EVENTGROUP_OBJCLOSE_NAME
 *
 * About Close Events
 * When an object is evicted from the object property table (object close), two
 * internal events are stored (EVENTGROUP_OBJCLOSE_NAME and
 * EVENTGROUP_OBJCLOSE_PROP), containing the handle-name mapping and object
 * properties valid up to this point.
 ******************************************************************************/
#define EVENTGROUP_OBJCLOSE_NAME	(EVENTGROUP_TS + 4)					/*0x08*/

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
#define EVENTGROUP_OBJCLOSE_PROP	(EVENTGROUP_OBJCLOSE_NAME + 8)		/*0x10*/

/*******************************************************************************
 * EVENTGROUP_CREATE
 *
 * The events in this group are used to log Kernel object creations.
 * The lower three bits in the event code gives the object class, i.e., type of
 * create operation (task, queue, semaphore, etc).
 ******************************************************************************/
#define EVENTGROUP_CREATE_OBJ_SUCCESS	(EVENTGROUP_OBJCLOSE_PROP + 8)	/*0x18*/

/*******************************************************************************
 * EVENTGROUP_SEND
 *
 * The events in this group are used to log Send/Give events on queues,
 * semaphores and mutexes The lower three bits in the event code gives the
 * object class, i.e., what type of object that is operated on (queue, semaphore
 * or mutex).
 ******************************************************************************/
#define EVENTGROUP_SEND_SUCCESS	(EVENTGROUP_CREATE_OBJ_SUCCESS + 8)		/*0x20*/

/*******************************************************************************
 * EVENTGROUP_RECEIVE
 *
 * The events in this group are used to log Receive/Take events on queues,
 * semaphores and mutexes. The lower three bits in the event code gives the
 * object class, i.e., what type of object that is operated on (queue, semaphore
 * or mutex).
 ******************************************************************************/
#define EVENTGROUP_RECEIVE_SUCCESS	(EVENTGROUP_SEND_SUCCESS + 8)		/*0x28*/

/* Send/Give operations, from ISR */
#define EVENTGROUP_SEND_FROM_ISR_SUCCESS \
									(EVENTGROUP_RECEIVE_SUCCESS + 8)	/*0x30*/

/* Receive/Take operations, from ISR */
#define EVENTGROUP_RECEIVE_FROM_ISR_SUCCESS \
							(EVENTGROUP_SEND_FROM_ISR_SUCCESS + 8)		/*0x38*/

/* "Failed" event type versions of above (timeout, failed allocation, etc) */
#define EVENTGROUP_KSE_FAILED \
							(EVENTGROUP_RECEIVE_FROM_ISR_SUCCESS + 8)	/*0x40*/

/* Failed create calls - memory allocation failed */
#define EVENTGROUP_CREATE_OBJ_FAILED	(EVENTGROUP_KSE_FAILED)			/*0x40*/

/* Failed send/give - timeout! */
#define EVENTGROUP_SEND_FAILED		(EVENTGROUP_CREATE_OBJ_FAILED + 8)	/*0x48*/

/* Failed receive/take - timeout! */
#define EVENTGROUP_RECEIVE_FAILED	 (EVENTGROUP_SEND_FAILED + 8)		/*0x50*/

/* Failed non-blocking send/give - queue full */
#define EVENTGROUP_SEND_FROM_ISR_FAILED (EVENTGROUP_RECEIVE_FAILED + 8) /*0x58*/

/* Failed non-blocking receive/take - queue empty */
#define EVENTGROUP_RECEIVE_FROM_ISR_FAILED \
								 (EVENTGROUP_SEND_FROM_ISR_FAILED + 8)	/*0x60*/

/* Events when blocking on receive/take */
#define EVENTGROUP_RECEIVE_BLOCK \
							(EVENTGROUP_RECEIVE_FROM_ISR_FAILED + 8)	/*0x68*/

/* Events when blocking on send/give */
#define EVENTGROUP_SEND_BLOCK	(EVENTGROUP_RECEIVE_BLOCK + 8)			/*0x70*/

/* Events on queue peek (receive) */
#define EVENTGROUP_PEEK_SUCCESS	(EVENTGROUP_SEND_BLOCK + 8)				/*0x78*/

/* Events on object delete (vTaskDelete or vQueueDelete) */
#define EVENTGROUP_DELETE_OBJ_SUCCESS	(EVENTGROUP_PEEK_SUCCESS + 8)	/*0x80*/

/* Other events - object class is implied: TASK */
#define EVENTGROUP_OTHERS	(EVENTGROUP_DELETE_OBJ_SUCCESS + 8)			/*0x88*/
#define TASK_DELAY_UNTIL	(EVENTGROUP_OTHERS + 0)						/*0x88*/
#define TASK_DELAY			(EVENTGROUP_OTHERS + 1)						/*0x89*/
#define TASK_SUSPEND		(EVENTGROUP_OTHERS + 2)						/*0x8A*/
#define TASK_RESUME			(EVENTGROUP_OTHERS + 3)						/*0x8B*/
#define TASK_RESUME_FROM_ISR	(EVENTGROUP_OTHERS + 4)					/*0x8C*/
#define TASK_PRIORITY_SET		(EVENTGROUP_OTHERS + 5)					/*0x8D*/
#define TASK_PRIORITY_INHERIT	(EVENTGROUP_OTHERS + 6)					/*0x8E*/
#define TASK_PRIORITY_DISINHERIT	(EVENTGROUP_OTHERS + 7)				/*0x8F*/

#define EVENTGROUP_MISC_PLACEHOLDER	(EVENTGROUP_OTHERS + 8)				/*0x90*/
#define PEND_FUNC_CALL		(EVENTGROUP_MISC_PLACEHOLDER+0)				/*0x90*/
#define PEND_FUNC_CALL_FROM_ISR (EVENTGROUP_MISC_PLACEHOLDER+1)			/*0x91*/
#define PEND_FUNC_CALL_FAILED (EVENTGROUP_MISC_PLACEHOLDER+2)			/*0x92*/
#define PEND_FUNC_CALL_FROM_ISR_FAILED (EVENTGROUP_MISC_PLACEHOLDER+3)	/*0x93*/
#define MEM_MALLOC_SIZE (EVENTGROUP_MISC_PLACEHOLDER+4)					/*0x94*/
#define MEM_MALLOC_ADDR (EVENTGROUP_MISC_PLACEHOLDER+5)					/*0x95*/
#define MEM_FREE_SIZE (EVENTGROUP_MISC_PLACEHOLDER+6)					/*0x96*/
#define MEM_FREE_ADDR (EVENTGROUP_MISC_PLACEHOLDER+7)					/*0x97*/

/* User events */
#define EVENTGROUP_USEREVENT (EVENTGROUP_MISC_PLACEHOLDER + 8)			/*0x98*/
#define USER_EVENT (EVENTGROUP_USEREVENT + 0)

/* Allow for 0-15 arguments (the number of args is added to event code) */
#define USER_EVENT_LAST (EVENTGROUP_USEREVENT + 15)						/*0xA7*/

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
 * which means a limit of 0xFF (255). The XTS16 is used when the original event
 * has a 16 bit DTS field and thereby can handle values up to 0xFFFF (65535).
 *
 * Using a very high frequency time base can result in many XTS events.
 * Preferably, the time between two OS ticks should fit in 16 bits, i.e.,
 * at most 65535. If your time base has a higher frequency, you can define
 * the TRACE
 ******************************************************************************/

#define EVENTGROUP_SYS (EVENTGROUP_USEREVENT + 16)						/*0xA8*/
#define XTS8 (EVENTGROUP_SYS + 0)										/*0xA8*/
#define XTS16 (EVENTGROUP_SYS + 1)										/*0xA9*/
#define EVENT_BEING_WRITTEN (EVENTGROUP_SYS + 2)						/*0xAA*/
#define RESERVED_DUMMY_CODE (EVENTGROUP_SYS + 3)						/*0xAB*/
#define LOW_POWER_BEGIN (EVENTGROUP_SYS + 4)							/*0xAC*/
#define LOW_POWER_END (EVENTGROUP_SYS + 5)								/*0xAD*/
#define XID (EVENTGROUP_SYS + 6)										/*0xAE*/
#define XTS16L (EVENTGROUP_SYS + 7)										/*0xAF*/

#define EVENTGROUP_TIMER (EVENTGROUP_SYS + 8)							/*0xB0*/
#define TIMER_CREATE (EVENTGROUP_TIMER + 0)								/*0xB0*/
#define TIMER_START (EVENTGROUP_TIMER + 1)								/*0xB1*/
#define TIMER_RST (EVENTGROUP_TIMER + 2)								/*0xB2*/
#define TIMER_STOP (EVENTGROUP_TIMER + 3)								/*0xB3*/
#define TIMER_CHANGE_PERIOD (EVENTGROUP_TIMER + 4)						/*0xB4*/
#define TIMER_DELETE (EVENTGROUP_TIMER + 5)								/*0xB5*/
#define TIMER_START_FROM_ISR (EVENTGROUP_TIMER + 6)						/*0xB6*/
#define TIMER_RESET_FROM_ISR (EVENTGROUP_TIMER + 7)						/*0xB7*/
#define TIMER_STOP_FROM_ISR (EVENTGROUP_TIMER + 8)						/*0xB8*/

#define TIMER_CREATE_FAILED (EVENTGROUP_TIMER + 9)						/*0xB9*/
#define TIMER_START_FAILED (EVENTGROUP_TIMER + 10)						/*0xBA*/
#define TIMER_RESET_FAILED (EVENTGROUP_TIMER + 11)						/*0xBB*/
#define TIMER_STOP_FAILED (EVENTGROUP_TIMER + 12)						/*0xBC*/
#define TIMER_CHANGE_PERIOD_FAILED (EVENTGROUP_TIMER + 13)				/*0xBD*/
#define TIMER_DELETE_FAILED (EVENTGROUP_TIMER + 14)						/*0xBE*/
#define TIMER_START_FROM_ISR_FAILED (EVENTGROUP_TIMER + 15)				/*0xBF*/
#define TIMER_RESET_FROM_ISR_FAILED (EVENTGROUP_TIMER + 16)				/*0xC0*/
#define TIMER_STOP_FROM_ISR_FAILED (EVENTGROUP_TIMER + 17)				/*0xC1*/

#define EVENTGROUP_EG (EVENTGROUP_TIMER + 18)							/*0xC2*/
#define EVENT_GROUP_CREATE (EVENTGROUP_EG + 0)							/*0xC2*/
#define EVENT_GROUP_CREATE_FAILED (EVENTGROUP_EG + 1)					/*0xC3*/
#define EVENT_GROUP_SYNC_BLOCK (EVENTGROUP_EG + 2)						/*0xC4*/
#define EVENT_GROUP_SYNC_END (EVENTGROUP_EG + 3)						/*0xC5*/
#define EVENT_GROUP_WAIT_BITS_BLOCK (EVENTGROUP_EG + 4)					/*0xC6*/
#define EVENT_GROUP_WAIT_BITS_END (EVENTGROUP_EG + 5)					/*0xC7*/
#define EVENT_GROUP_CLEAR_BITS (EVENTGROUP_EG + 6)						/*0xC8*/
#define EVENT_GROUP_CLEAR_BITS_FROM_ISR (EVENTGROUP_EG + 7)				/*0xC9*/
#define EVENT_GROUP_SET_BITS (EVENTGROUP_EG + 8)						/*0xCA*/
#define EVENT_GROUP_DELETE (EVENTGROUP_EG + 9)							/*0xCB*/
#define EVENT_GROUP_SYNC_END_FAILED (EVENTGROUP_EG + 10)				/*0xCC*/
#define EVENT_GROUP_WAIT_BITS_END_FAILED (EVENTGROUP_EG + 11)			/*0xCD*/
#define EVENT_GROUP_SET_BITS_FROM_ISR (EVENTGROUP_EG + 12)				/*0xCE*/
#define EVENT_GROUP_SET_BITS_FROM_ISR_FAILED (EVENTGROUP_EG + 13)		/*0xCF*/

#define TASK_INSTANCE_FINISHED_NEXT_KSE (EVENTGROUP_EG + 14)			/*0xD0*/
#define TASK_INSTANCE_FINISHED_DIRECT (EVENTGROUP_EG + 15)				/*0xD1*/

/************************************************************************/
/* KERNEL SPECIFIC DATA AND FUNCTIONS NEEDED TO PROVIDE THE				*/
/* FUNCTIONALITY REQUESTED BY THE TRACE RECORDER						*/
/************************************************************************/

/******************************************************************************
 * TraceObjectClassTable
 * Translates a FreeRTOS QueueType into trace objects classes (TRACE_CLASS_).
 * This was added since we want to map both types of Mutex and both types of
 * Semaphores on common classes for all Mutexes and all Semaphores respectively.
 *
 * FreeRTOS Queue types
 * #define queueQUEUE_TYPE_BASE					(0U) => TRACE_CLASS_QUEUE
 * #define queueQUEUE_TYPE_MUTEX				(1U) => TRACE_CLASS_MUTEX
 * #define queueQUEUE_TYPE_COUNTING_SEMAPHORE	(2U) => TRACE_CLASS_SEMAPHORE
 * #define queueQUEUE_TYPE_BINARY_SEMAPHORE		(3U) => TRACE_CLASS_SEMAPHORE
 * #define queueQUEUE_TYPE_RECURSIVE_MUTEX		(4U) => TRACE_CLASS_MUTEX
 ******************************************************************************/

extern traceObjectClass TraceObjectClassTable[5];

/* These functions are implemented in the .c file since certain header files
must not be included in this one */
objectHandleType prvTraceGetObjectNumber(void* handle);
unsigned char prvTraceGetObjectType(void* handle);
objectHandleType prvTraceGetTaskNumber(void* handle);
unsigned char prvTraceIsSchedulerActive(void);
unsigned char prvTraceIsSchedulerSuspended(void);
unsigned char prvTraceIsSchedulerStarted(void);
void* prvTraceGetCurrentTaskHandle(void);

#if (configUSE_TIMERS == 1)
#undef INCLUDE_xTimerGetTimerDaemonTaskHandle
#define INCLUDE_xTimerGetTimerDaemonTaskHandle 1
#endif

/************************************************************************/
/* KERNEL SPECIFIC MACROS USED BY THE TRACE RECORDER					*/
/************************************************************************/

#define TRACE_MALLOC(size) pvPortMalloc(size)
#define TRACE_IS_SCHEDULER_ACTIVE() prvTraceIsSchedulerActive()
#define TRACE_IS_SCHEDULER_STARTED() prvTraceIsSchedulerStarted()
#define TRACE_IS_SCHEDULER_SUSPENDED() prvTraceIsSchedulerSuspended()
#define TRACE_GET_CURRENT_TASK() prvTraceGetCurrentTaskHandle()

#define TRACE_GET_TASK_PRIORITY(pxTCB) ((uint8_t)pxTCB->uxPriority)
#define TRACE_GET_TASK_NAME(pxTCB) ((char*)pxTCB->pcTaskName)
#define TRACE_GET_TASK_NUMBER(pxTCB) (prvTraceGetTaskNumber(pxTCB))
#define TRACE_SET_TASK_NUMBER(pxTCB) pxTCB->uxTaskNumber = xTraceGetObjectHandle(TRACE_CLASS_TASK);

#define TRACE_GET_CLASS_TRACE_CLASS(CLASS, kernelClass) TraceObjectClassTable[kernelClass]
#define TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject) TRACE_GET_CLASS_TRACE_CLASS(CLASS, prvTraceGetObjectType(pxObject))

#define TRACE_GET_TIMER_NUMBER(tmr) ( ( objectHandleType ) ((Timer_t*)tmr)->uxTimerNumber )
#define TRACE_SET_TIMER_NUMBER(tmr) ((Timer_t*)tmr)->uxTimerNumber = xTraceGetObjectHandle(TRACE_CLASS_TIMER);
#define TRACE_GET_TIMER_NAME(pxTimer) pxTimer->pcTimerName
#define TRACE_GET_TIMER_PERIOD(pxTimer) pxTimer->xTimerPeriodInTicks

#define TRACE_GET_EVENTGROUP_NUMBER(eg) ( ( objectHandleType ) uxEventGroupGetNumber(eg) )
#define TRACE_SET_EVENTGROUP_NUMBER(eg) ((EventGroup_t*)eg)->uxEventGroupNumber = xTraceGetObjectHandle(TRACE_CLASS_EVENTGROUP);

#define TRACE_GET_OBJECT_NUMBER(CLASS, pxObject) (prvTraceGetObjectNumber(pxObject))

#if (FREERTOS_VERSION < FREERTOS_VERSION_8_0_OR_LATER)
	#define TRACE_SET_OBJECT_NUMBER(CLASS, pxObject) pxObject->ucQueueNumber = xTraceGetObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject));
#else
	#define TRACE_SET_OBJECT_NUMBER(CLASS, pxObject) pxObject->uxQueueNumber = xTraceGetObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject));
#endif

#define TRACE_GET_CLASS_EVENT_CODE(SERVICE, RESULT, CLASS, kernelClass) (uint8_t)(EVENTGROUP_##SERVICE##_##RESULT + TRACE_GET_CLASS_TRACE_CLASS(CLASS, kernelClass))
#define TRACE_GET_OBJECT_EVENT_CODE(SERVICE, RESULT, CLASS, pxObject) (uint8_t)(EVENTGROUP_##SERVICE##_##RESULT + TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject))
#define TRACE_GET_TASK_EVENT_CODE(SERVICE, RESULT, CLASS, pxTCB) (uint8_t)(EVENTGROUP_##SERVICE##_##RESULT + TRACE_CLASS_TASK)

/************************************************************************/
/* KERNEL SPECIFIC WRAPPERS THAT SHOULD BE CALLED BY THE KERNEL		 */
/************************************************************************/

#if (configUSE_TICKLESS_IDLE != 0)

#undef traceLOW_POWER_IDLE_BEGIN
#define traceLOW_POWER_IDLE_BEGIN() \
	{ \
		extern uint32_t trace_disable_timestamp; \
		vTraceStoreLowPower(0); \
		trace_disable_timestamp = 1; \
	}

#undef traceLOW_POWER_IDLE_END
#define traceLOW_POWER_IDLE_END() \
	{ \
		extern uint32_t trace_disable_timestamp; \
		trace_disable_timestamp = 0; \
		vTraceStoreLowPower(1); \
	}

#endif

/* A macro that will update the tick count when returning from tickless idle */
#undef traceINCREASE_TICK_COUNT
/* Note: This can handle time adjustments of max 2^32 ticks, i.e., 35 seconds at 120 MHz. Thus, tick-less idle periods longer than 2^32 ticks will appear "compressed" on the time line.*/
#define traceINCREASE_TICK_COUNT( xCount ) { DWT_CYCLES_ADDED += (xCount * (TRACE_CPU_CLOCK_HZ / TRACE_TICK_RATE_HZ)); }

/* Called for each task that becomes ready */
#undef traceMOVED_TASK_TO_READY_STATE
#define traceMOVED_TASK_TO_READY_STATE( pxTCB ) \
	trcKERNEL_HOOKS_MOVED_TASK_TO_READY_STATE(pxTCB);

/* Called on each OS tick. Will call uiPortGetTimestamp to make sure it is called at least once every OS tick. */
#undef traceTASK_INCREMENT_TICK

#if (FREERTOS_VERSION == FREERTOS_VERSION_7_3_OR_7_4)

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxMissedTicks == 0) { trcKERNEL_HOOKS_INCREMENT_TICK(); } \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE) { trcKERNEL_HOOKS_NEW_TIME(DIV_NEW_TIME, xTickCount + 1); }

#else

#define traceTASK_INCREMENT_TICK( xTickCount ) \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxPendedTicks == 0) { trcKERNEL_HOOKS_INCREMENT_TICK(); } \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE) { trcKERNEL_HOOKS_NEW_TIME(DIV_NEW_TIME, xTickCount + 1); }

#endif

/* Called on each task-switch */
#undef traceTASK_SWITCHED_IN
#define traceTASK_SWITCHED_IN() \
		trcKERNEL_HOOKS_TASK_SWITCH(TRACE_GET_CURRENT_TASK());

/* Called on vTaskSuspend */
#undef traceTASK_SUSPEND
#define traceTASK_SUSPEND( pxTaskToSuspend ) \
	trcKERNEL_HOOKS_TASK_SUSPEND(TASK_SUSPEND, pxTaskToSuspend);

/* Called on vTaskDelay - note the use of FreeRTOS variable xTicksToDelay */
#undef traceTASK_DELAY
#define traceTASK_DELAY() \
	trcKERNEL_HOOKS_TASK_DELAY(TASK_DELAY, pxCurrentTCB, xTicksToDelay); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

/* Called on vTaskDelayUntil - note the use of FreeRTOS variable xTimeToWake */
#undef traceTASK_DELAY_UNTIL
#define traceTASK_DELAY_UNTIL() \
	trcKERNEL_HOOKS_TASK_DELAY(TASK_DELAY_UNTIL, pxCurrentTCB, xTimeToWake); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

#if (INCLUDE_OBJECT_DELETE == 1)
/* Called on vTaskDelete */
#undef traceTASK_DELETE
#define traceTASK_DELETE( pxTaskToDelete ) \
	{ TRACE_SR_ALLOC_CRITICAL_SECTION(); \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_TASK_DELETE(DELETE_OBJ, pxTaskToDelete); \
	TRACE_EXIT_CRITICAL_SECTION(); }
#endif

#if (INCLUDE_OBJECT_DELETE == 1)
/* Called on vQueueDelete */
#undef traceQUEUE_DELETE
#define traceQUEUE_DELETE( pxQueue ) \
	{ TRACE_SR_ALLOC_CRITICAL_SECTION(); \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_OBJECT_DELETE(DELETE_OBJ, UNUSED, pxQueue); \
	TRACE_EXIT_CRITICAL_SECTION(); }
#endif

/* Called on vTaskCreate */
#undef traceTASK_CREATE
#define traceTASK_CREATE(pxNewTCB) \
	if (pxNewTCB != NULL) \
	{ \
		trcKERNEL_HOOKS_TASK_CREATE(CREATE_OBJ, UNUSED, pxNewTCB); \
	}

/* Called in vTaskCreate, if it fails (typically if the stack can not be allocated) */
#undef traceTASK_CREATE_FAILED
#define traceTASK_CREATE_FAILED() \
	trcKERNEL_HOOKS_TASK_CREATE_FAILED(CREATE_OBJ, UNUSED);

/* Called in xQueueCreate, and thereby for all other object based on queues, such as semaphores. */
#undef traceQUEUE_CREATE
#define traceQUEUE_CREATE( pxNewQueue )\
	trcKERNEL_HOOKS_OBJECT_CREATE(CREATE_OBJ, UNUSED, pxNewQueue);

/* Called in xQueueCreate, if the queue creation fails */
#undef traceQUEUE_CREATE_FAILED
#define traceQUEUE_CREATE_FAILED( queueType ) \
	trcKERNEL_HOOKS_OBJECT_CREATE_FAILED(CREATE_OBJ, UNUSED, queueType);

/* Called in xQueueCreateMutex, and thereby also from xSemaphoreCreateMutex and xSemaphoreCreateRecursiveMutex */
#undef traceCREATE_MUTEX
#define traceCREATE_MUTEX( pxNewQueue ) \
	trcKERNEL_HOOKS_OBJECT_CREATE(CREATE_OBJ, UNUSED, pxNewQueue);

/* Called in xQueueCreateMutex when the operation fails (when memory allocation fails) */
#undef traceCREATE_MUTEX_FAILED
#define traceCREATE_MUTEX_FAILED() \
	trcKERNEL_HOOKS_OBJECT_CREATE_FAILED(CREATE_OBJ, UNUSED, queueQUEUE_TYPE_MUTEX);

/* Called when the Mutex can not be given, since not holder */
#undef traceGIVE_MUTEX_RECURSIVE_FAILED
#define traceGIVE_MUTEX_RECURSIVE_FAILED( pxMutex ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(SEND, FAILED, UNUSED, pxMutex);

/* Called when a message is sent to a queue */	/* CS IS NEW ! */
#undef traceQUEUE_SEND
#define traceQUEUE_SEND( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(SEND, SUCCESS, UNUSED, pxQueue); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(UNUSED, pxQueue, TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, pxQueue) == TRACE_CLASS_MUTEX ? (uint8_t)0 : (uint8_t)(pxQueue->uxMessagesWaiting + 1));

/* Called when a message failed to be sent to a queue (timeout) */
#undef traceQUEUE_SEND_FAILED
#define traceQUEUE_SEND_FAILED( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(SEND, FAILED, UNUSED, pxQueue);

/* Called when the task is blocked due to a send operation on a full queue */
#undef traceBLOCKING_ON_QUEUE_SEND
#define traceBLOCKING_ON_QUEUE_SEND( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(SEND, BLOCK, UNUSED, pxQueue);

/* Called when a message is received from a queue */
#undef traceQUEUE_RECEIVE
#define traceQUEUE_RECEIVE( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(RECEIVE, SUCCESS, UNUSED, pxQueue); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(UNUSED, pxQueue, TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, pxQueue) == TRACE_CLASS_MUTEX ? TRACE_GET_TASK_NUMBER(TRACE_GET_CURRENT_TASK()) : (uint8_t)(pxQueue->uxMessagesWaiting - 1));

/* Called when a receive operation on a queue fails (timeout) */
#undef traceQUEUE_RECEIVE_FAILED
#define traceQUEUE_RECEIVE_FAILED( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(RECEIVE, FAILED, UNUSED, pxQueue);

/* Called when the task is blocked due to a receive operation on an empty queue */
#undef traceBLOCKING_ON_QUEUE_RECEIVE
#define traceBLOCKING_ON_QUEUE_RECEIVE( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(RECEIVE, BLOCK, UNUSED, pxQueue); \
	if (TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, pxQueue) != TRACE_CLASS_MUTEX) \
	{trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();}

/* Called on xQueuePeek */
#undef traceQUEUE_PEEK
#define traceQUEUE_PEEK( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(PEEK, SUCCESS, UNUSED, pxQueue);

/* Called when a message is sent from interrupt context, e.g., using xQueueSendFromISR */
#undef traceQUEUE_SEND_FROM_ISR
#define traceQUEUE_SEND_FROM_ISR( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(SEND_FROM_ISR, SUCCESS, UNUSED, pxQueue); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(UNUSED, pxQueue, (uint8_t)(pxQueue->uxMessagesWaiting + 1));

/* Called when a message send from interrupt context fails (since the queue was full) */
#undef traceQUEUE_SEND_FROM_ISR_FAILED
#define traceQUEUE_SEND_FROM_ISR_FAILED( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(SEND_FROM_ISR, FAILED, UNUSED, pxQueue);

/* Called when a message is received in interrupt context, e.g., using xQueueReceiveFromISR */
#undef traceQUEUE_RECEIVE_FROM_ISR
#define traceQUEUE_RECEIVE_FROM_ISR( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(RECEIVE_FROM_ISR, SUCCESS, UNUSED, pxQueue); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(UNUSED, pxQueue, (uint8_t)(pxQueue->uxMessagesWaiting - 1));

/* Called when a message receive from interrupt context fails (since the queue was empty) */
#undef traceQUEUE_RECEIVE_FROM_ISR_FAILED
#define traceQUEUE_RECEIVE_FROM_ISR_FAILED( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(RECEIVE_FROM_ISR, FAILED, UNUSED, pxQueue);

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
	trcKERNEL_HOOKS_TASK_RESUME(TASK_RESUME_FROM_ISR, pxTaskToResume);


#if (FREERTOS_VERSION >= FREERTOS_VERSION_8_0_OR_LATER)

#if (INCLUDE_MEMMANG_EVENTS == 1)

extern void vTraceStoreMemMangEvent(uint32_t ecode, uint32_t address, int32_t size);

#undef traceMALLOC
#define traceMALLOC( pvAddress, uiSize ) {if (pvAddress != 0) vTraceStoreMemMangEvent(MEM_MALLOC_SIZE, ( uint32_t ) pvAddress, (int32_t)uiSize); }

#undef traceFREE
#define traceFREE( pvAddress, uiSize ) {vTraceStoreMemMangEvent(MEM_FREE_SIZE, ( uint32_t ) pvAddress, (int32_t)(-uiSize)); }

#endif

/* Called in timer.c - xTimerCreate */
#undef traceTIMER_CREATE
#define traceTIMER_CREATE(tmr) \
	trcKERNEL_HOOKS_TIMER_CREATE(TIMER_CREATE, tmr);

#undef traceTIMER_CREATE_FAILED
#define traceTIMER_CREATE_FAILED() \
	trcKERNEL_HOOKS_TIMER_EVENT(TIMER_CREATE_FAILED, 0);

/* Note that xCommandID can never be tmrCOMMAND_EXECUTE_CALLBACK (-1) since the trace macro is not called in that case */
#undef traceTIMER_COMMAND_SEND
#define traceTIMER_COMMAND_SEND(tmr, xCommandID, xOptionalValue, xReturn) \
if (xCommandID > tmrCOMMAND_START_DONT_TRACE){\
		if (xCommandID == tmrCOMMAND_CHANGE_PERIOD) vTraceStoreKernelCallWithParam((xReturn == pdPASS) ? TIMER_CHANGE_PERIOD : TIMER_CHANGE_PERIOD_FAILED, TRACE_CLASS_TIMER, TRACE_GET_TIMER_NUMBER(tmr), xOptionalValue);\
		else if ((xCommandID == tmrCOMMAND_DELETE) && (xReturn == pdPASS)){ trcKERNEL_HOOKS_TIMER_DELETE(TIMER_DELETE, tmr); } \
		else {trcKERNEL_HOOKS_TIMER_EVENT(EVENTGROUP_TIMER + xCommandID + ((xReturn == pdPASS)?0:(TIMER_CREATE_FAILED - TIMER_CREATE)), tmr); }\
}

#undef tracePEND_FUNC_CALL
#define tracePEND_FUNC_CALL(func, arg1, arg2, ret) \
if (ret == pdPASS) \
	vTraceStoreKernelCall(PEND_FUNC_CALL, TRACE_CLASS_TASK, uxTaskGetTaskNumber(xTimerGetTimerDaemonTaskHandle()) ); \
else \
	vTraceStoreKernelCall(PEND_FUNC_CALL_FAILED, TRACE_CLASS_TASK, uxTaskGetTaskNumber(xTimerGetTimerDaemonTaskHandle()) );

#undef tracePEND_FUNC_CALL_FROM_ISR
#define tracePEND_FUNC_CALL_FROM_ISR(func, arg1, arg2, ret) \
	if (! uiInEventGroupSetBitsFromISR) vTraceStoreKernelCall(PEND_FUNC_CALL_FROM_ISR, TRACE_CLASS_TASK, uxTaskGetTaskNumber(xTimerGetTimerDaemonTaskHandle()) ); \
	uiInEventGroupSetBitsFromISR = 0;
#endif

#undef traceEVENT_GROUP_CREATE
#define traceEVENT_GROUP_CREATE(eg) \
	TRACE_SET_EVENTGROUP_NUMBER(eg); \
	vTraceStoreKernelCall(EVENT_GROUP_CREATE, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg));

#undef traceEVENT_GROUP_DELETE
#define traceEVENT_GROUP_DELETE(eg) \
	vTraceStoreKernelCall(EVENT_GROUP_DELETE, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg)); \
	vTraceStoreObjectNameOnCloseEvent(TRACE_GET_EVENTGROUP_NUMBER(eg), TRACE_CLASS_EVENTGROUP); \
	vTraceStoreObjectPropertiesOnCloseEvent(TRACE_GET_EVENTGROUP_NUMBER(eg), TRACE_CLASS_EVENTGROUP); \
	vTraceFreeObjectHandle(TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg));

#undef traceEVENT_GROUP_CREATE_FAILED
#define traceEVENT_GROUP_CREATE_FAILED() \
	vTraceStoreKernelCall(EVENT_GROUP_CREATE_FAILED, TRACE_CLASS_EVENTGROUP, 0);

#undef traceEVENT_GROUP_SYNC_BLOCK
#define traceEVENT_GROUP_SYNC_BLOCK(eg, bitsToSet, bitsToWaitFor) \
	vTraceStoreKernelCallWithParam(EVENT_GROUP_SYNC_BLOCK, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg), bitsToWaitFor);

#undef traceEVENT_GROUP_SYNC_END
#define traceEVENT_GROUP_SYNC_END(eg, bitsToSet, bitsToWaitFor, wasTimeout) \
	if (wasTimeout){ vTraceStoreKernelCallWithParam(EVENT_GROUP_SYNC_END_FAILED, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg), bitsToWaitFor);} \
	else{ vTraceStoreKernelCallWithParam(EVENT_GROUP_SYNC_END, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg), bitsToWaitFor); }

#undef traceEVENT_GROUP_WAIT_BITS_BLOCK
#define traceEVENT_GROUP_WAIT_BITS_BLOCK(eg, bitsToWaitFor) \
	vTraceStoreKernelCallWithParam(EVENT_GROUP_WAIT_BITS_BLOCK, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg), bitsToWaitFor); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED();

#undef traceEVENT_GROUP_WAIT_BITS_END
#define traceEVENT_GROUP_WAIT_BITS_END(eg, bitsToWaitFor, wasTimeout) \
	if (wasTimeout){ vTraceStoreKernelCallWithParam(EVENT_GROUP_WAIT_BITS_END_FAILED, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg), bitsToWaitFor); } \
	else{ vTraceStoreKernelCallWithParam(EVENT_GROUP_WAIT_BITS_END, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg), bitsToWaitFor); }

#undef traceEVENT_GROUP_CLEAR_BITS
#define traceEVENT_GROUP_CLEAR_BITS(eg, bitsToClear) \
	if (bitsToClear) vTraceStoreKernelCallWithParam(EVENT_GROUP_CLEAR_BITS, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg), bitsToClear);

#undef traceEVENT_GROUP_CLEAR_BITS_FROM_ISR
#define traceEVENT_GROUP_CLEAR_BITS_FROM_ISR(eg, bitsToClear) \
	if (bitsToClear) vTraceStoreKernelCallWithParam(EVENT_GROUP_CLEAR_BITS_FROM_ISR, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg), bitsToClear);

#undef traceEVENT_GROUP_SET_BITS
#define traceEVENT_GROUP_SET_BITS(eg, bitsToSet) \
	vTraceStoreKernelCallWithParam(EVENT_GROUP_SET_BITS, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg), bitsToSet);

#undef traceEVENT_GROUP_SET_BITS_FROM_ISR
#define traceEVENT_GROUP_SET_BITS_FROM_ISR(eg, bitsToSet) \
	vTraceStoreKernelCallWithParam(EVENT_GROUP_SET_BITS_FROM_ISR, TRACE_CLASS_EVENTGROUP, TRACE_GET_EVENTGROUP_NUMBER(eg), bitsToSet); \
	uiInEventGroupSetBitsFromISR = 1;


/************************************************************************/
/* KERNEL SPECIFIC MACROS TO EXCLUDE OR INCLUDE THINGS IN TRACE			*/
/************************************************************************/

/* Returns the exclude state of the object */
uint8_t uiTraceIsObjectExcluded(traceObjectClass objectclass, objectHandleType handle);

#define TRACE_SET_QUEUE_FLAG_ISEXCLUDED(queueIndex) TRACE_SET_FLAG_ISEXCLUDED(excludedObjects, queueIndex)
#define TRACE_CLEAR_QUEUE_FLAG_ISEXCLUDED(queueIndex) TRACE_CLEAR_FLAG_ISEXCLUDED(excludedObjects, queueIndex)
#define TRACE_GET_QUEUE_FLAG_ISEXCLUDED(queueIndex) TRACE_GET_FLAG_ISEXCLUDED(excludedObjects, queueIndex)

#define TRACE_SET_SEMAPHORE_FLAG_ISEXCLUDED(semaphoreIndex) TRACE_SET_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+semaphoreIndex)
#define TRACE_CLEAR_SEMAPHORE_FLAG_ISEXCLUDED(semaphoreIndex) TRACE_CLEAR_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+semaphoreIndex)
#define TRACE_GET_SEMAPHORE_FLAG_ISEXCLUDED(semaphoreIndex) TRACE_GET_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+semaphoreIndex)

#define TRACE_SET_MUTEX_FLAG_ISEXCLUDED(mutexIndex) TRACE_SET_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+mutexIndex)
#define TRACE_CLEAR_MUTEX_FLAG_ISEXCLUDED(mutexIndex) TRACE_CLEAR_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+mutexIndex)
#define TRACE_GET_MUTEX_FLAG_ISEXCLUDED(mutexIndex) TRACE_GET_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+mutexIndex)

#define TRACE_SET_TASK_FLAG_ISEXCLUDED(taskIndex) TRACE_SET_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+NMutex+1+taskIndex)
#define TRACE_CLEAR_TASK_FLAG_ISEXCLUDED(taskIndex) TRACE_CLEAR_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+NMutex+1+taskIndex)
#define TRACE_GET_TASK_FLAG_ISEXCLUDED(taskIndex) TRACE_GET_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+NMutex+1+taskIndex)

#define TRACE_SET_TIMER_FLAG_ISEXCLUDED(timerIndex) TRACE_SET_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+NMutex+1+NTask+1+timerIndex)
#define TRACE_CLEAR_TIMER_FLAG_ISEXCLUDED(timerIndex) TRACE_CLEAR_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+NMutex+1+NTask+1+timerIndex)
#define TRACE_GET_TIMER_FLAG_ISEXCLUDED(timerIndex) TRACE_GET_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+NMutex+1+NTask+1+timerIndex)

#define TRACE_SET_EVENTGROUP_FLAG_ISEXCLUDED(egIndex) TRACE_SET_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+NMutex+1+NTask+1+NTimer+1+egIndex)
#define TRACE_CLEAR_EVENTGROUP_FLAG_ISEXCLUDED(egIndex) TRACE_CLEAR_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+NMutex+1+NTask+1+NTimer+1+egIndex)
#define TRACE_GET_EVENTGROUP_FLAG_ISEXCLUDED(egIndex) TRACE_GET_FLAG_ISEXCLUDED(excludedObjects, NQueue+1+NSemaphore+1+NMutex+1+NTask+1+NTimer+1+egIndex)


#define TRACE_CLEAR_OBJECT_FLAG_ISEXCLUDED(objectclass, handle) \
switch (objectclass) \
{ \
case TRACE_CLASS_QUEUE: \
	TRACE_CLEAR_QUEUE_FLAG_ISEXCLUDED(handle); \
	break; \
case TRACE_CLASS_SEMAPHORE: \
	TRACE_CLEAR_SEMAPHORE_FLAG_ISEXCLUDED(handle); \
	break; \
case TRACE_CLASS_MUTEX: \
	TRACE_CLEAR_MUTEX_FLAG_ISEXCLUDED(handle); \
	break; \
case TRACE_CLASS_TASK: \
	TRACE_CLEAR_TASK_FLAG_ISEXCLUDED(handle); \
	break; \
case TRACE_CLASS_TIMER: \
	TRACE_CLEAR_TIMER_FLAG_ISEXCLUDED(handle); \
	break; \
case TRACE_CLASS_EVENTGROUP: \
	TRACE_CLEAR_EVENTGROUP_FLAG_ISEXCLUDED(handle); \
	break; \
}

#define TRACE_SET_OBJECT_FLAG_ISEXCLUDED(objectclass, handle) \
switch (objectclass) \
{ \
case TRACE_CLASS_QUEUE: \
	TRACE_SET_QUEUE_FLAG_ISEXCLUDED(handle); \
	break; \
case TRACE_CLASS_SEMAPHORE: \
	TRACE_SET_SEMAPHORE_FLAG_ISEXCLUDED(handle); \
	break; \
case TRACE_CLASS_MUTEX: \
	TRACE_SET_MUTEX_FLAG_ISEXCLUDED(handle); \
	break; \
case TRACE_CLASS_TASK: \
	TRACE_SET_TASK_FLAG_ISEXCLUDED(handle); \
	break; \
case TRACE_CLASS_TIMER: \
	TRACE_SET_TIMER_FLAG_ISEXCLUDED(handle); \
	break; \
case TRACE_CLASS_EVENTGROUP: \
	TRACE_SET_EVENTGROUP_FLAG_ISEXCLUDED(handle); \
	break; \
}

/* Task */
#define vTraceExcludeTaskFromTrace(handle) \
TRACE_SET_TASK_FLAG_ISEXCLUDED(TRACE_GET_TASK_NUMBER(handle));

#define vTraceIncludeTaskInTrace(handle) \
TRACE_CLEAR_TASK_FLAG_ISEXCLUDED(TRACE_GET_TASK_NUMBER(handle));


/* Queue */
#define vTraceExcludeQueueFromTrace(handle) \
TRACE_SET_QUEUE_FLAG_ISEXCLUDED(TRACE_GET_OBJECT_NUMBER(UNUSED, handle));

#define vTraceIncludeQueueInTrace(handle) \
TRACE_CLEAR_QUEUE_FLAG_ISEXCLUDED(TRACE_GET_OBJECT_NUMBER(UNUSED, handle));


/* Semaphore */
#define vTraceExcludeSemaphoreFromTrace(handle) \
TRACE_SET_SEMAPHORE_FLAG_ISEXCLUDED(TRACE_GET_OBJECT_NUMBER(UNUSED, handle));

#define vTraceIncludeSemaphoreInTrace(handle) \
TRACE_CLEAR_QUEUE_FLAG_ISEXCLUDED(TRACE_GET_OBJECT_NUMBER(UNUSED, handle));


/* Mutex */
#define vTraceExcludeMutexFromTrace(handle) \
TRACE_SET_MUTEX_FLAG_ISEXCLUDED(TRACE_GET_OBJECT_NUMBER(UNUSED, handle));

#define vTraceIncludeMutexInTrace(handle) \
TRACE_CLEAR_QUEUE_FLAG_ISEXCLUDED(TRACE_GET_OBJECT_NUMBER(UNUSED, handle));

/* Timer */
#define vTraceExcludeTimerFromTrace(handle) \
TRACE_SET_TIMER_FLAG_ISEXCLUDED(TRACE_GET_TIMER_NUMBER(handle));

#define vTraceIncludeTimerInTrace(handle) \
TRACE_CLEAR_QUEUE_FLAG_ISEXCLUDED(TRACE_GET_TIMER_NUMBER(handle));

/* Event Group */
#define vTraceExcludeEventGroupFromTrace(handle) \
TRACE_SET_EVENTGROUP_FLAG_ISEXCLUDED(TRACE_GET_EVENTGROUP_NUMBER(handle));

#define vTraceIncludeEventGroupInTrace(handle) \
TRACE_CLEAR_EVENTGROUP_FLAG_ISEXCLUDED(TRACE_GET_EVENTGROUP_NUMBER(handle));


/* Kernel Services */
#define vTraceExcludeKernelServiceDelayFromTrace() \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(TASK_DELAY); \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(TASK_DELAY_UNTIL);

#define vTraceIncludeKernelServiceDelayInTrace() \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(TASK_DELAY); \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(TASK_DELAY_UNTIL);

/* HELPER MACROS FOR KERNEL SERVICES FOR OBJECTS */
#define vTraceExcludeKernelServiceSendFromTrace_HELPER(class) \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_SUCCESS + class); \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_BLOCK + class); \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FAILED + class); \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FROM_ISR_SUCCESS + class); \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FROM_ISR_FAILED + class);

#define vTraceIncludeKernelServiceSendInTrace_HELPER(class) \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_SUCCESS + class); \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_BLOCK + class); \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FAILED + class); \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FROM_ISR_SUCCESS + class); \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FROM_ISR_FAILED + class);

#define vTraceExcludeKernelServiceReceiveFromTrace_HELPER(class) \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_SUCCESS + class); \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_BLOCK + class); \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FAILED + class); \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FROM_ISR_SUCCESS + class); \
TRACE_SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FROM_ISR_FAILED + class);

#define vTraceIncludeKernelServiceReceiveInTrace_HELPER(class) \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_SUCCESS + class); \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_BLOCK + class); \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FAILED + class); \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FROM_ISR_SUCCESS + class); \
TRACE_CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FROM_ISR_FAILED + class);

/* EXCLUDE AND INCLUDE FOR QUEUE */
#define vTraceExcludeKernelServiceQueueSendFromTrace() \
vTraceExcludeKernelServiceSendFromTrace_HELPER(TRACE_CLASS_QUEUE);

#define vTraceIncludeKernelServiceQueueSendInTrace() \
vTraceIncludeKernelServiceSendInTrace_HELPER(TRACE_CLASS_QUEUE);

#define vTraceExcludeKernelServiceQueueReceiveFromTrace() \
vTraceExcludeKernelServiceReceiveFromTrace_HELPER(TRACE_CLASS_QUEUE);

#define vTraceIncludeKernelServiceQueueReceiveInTrace() \
vTraceIncludeKernelServiceReceiveInTrace_HELPER(TRACE_CLASS_QUEUE);

/* EXCLUDE AND INCLUDE FOR SEMAPHORE */
#define vTraceExcludeKernelServiceSemaphoreSendFromTrace() \
vTraceExcludeKernelServiceSendFromTrace_HELPER(TRACE_CLASS_SEMAPHORE);

#define vTraceIncludeKernelServicSemaphoreSendInTrace() \
vTraceIncludeKernelServiceSendInTrace_HELPER(TRACE_CLASS_SEMAPHORE);

#define vTraceExcludeKernelServiceSemaphoreReceiveFromTrace() \
vTraceExcludeKernelServiceReceiveFromTrace_HELPER(TRACE_CLASS_SEMAPHORE);

#define vTraceIncludeKernelServiceSemaphoreReceiveInTrace() \
vTraceIncludeKernelServiceReceiveInTrace_HELPER(TRACE_CLASS_SEMAPHORE);

/* EXCLUDE AND INCLUDE FOR MUTEX */
#define vTraceExcludeKernelServiceMutexSendFromTrace() \
vTraceExcludeKernelServiceSendFromTrace_HELPER(TRACE_CLASS_MUTEX);

#define vTraceIncludeKernelServiceMutexSendInTrace() \
vTraceIncludeKernelServiceSendInTrace_HELPER(TRACE_CLASS_MUTEX);

#define vTraceExcludeKernelServiceMutexReceiveFromTrace() \
vTraceExcludeKernelServiceReceiveFromTrace_HELPER(TRACE_CLASS_MUTEX);

#define vTraceIncludeKernelServiceMutexReceiveInTrace() \
vTraceIncludeKernelServiceReceiveInTrace_HELPER(TRACE_CLASS_MUTEX);

/************************************************************************/
/* KERNEL SPECIFIC MACROS TO NAME OBJECTS, IF NECESSARY				 */
/************************************************************************/
#define vTraceSetQueueName(object, name) \
vTraceSetObjectName(TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, object), TRACE_GET_OBJECT_NUMBER(UNUSED, object), name);

#define vTraceSetSemaphoreName(object, name) \
vTraceSetObjectName(TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, object), TRACE_GET_OBJECT_NUMBER(UNUSED, object), name);

#define vTraceSetMutexName(object, name) \
vTraceSetObjectName(TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, object), TRACE_GET_OBJECT_NUMBER(UNUSED, object), name);

#define vTraceSetEventGroupName(object, name) \
vTraceSetObjectName(TRACE_CLASS_EVENTGROUP, (objectHandleType)uxEventGroupGetNumber(object), name);

#undef traceQUEUE_REGISTRY_ADD
#define traceQUEUE_REGISTRY_ADD(object, name) vTraceSetObjectName(TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, object), TRACE_GET_OBJECT_NUMBER(UNUSED, object), name);
#endif

#endif /* TRCKERNELPORTFREERTOS_H_ */








