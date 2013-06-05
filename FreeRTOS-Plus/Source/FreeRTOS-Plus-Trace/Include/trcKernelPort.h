/*******************************************************************************
 * Tracealyzer v2.4.1 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcKernelPort.h
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
 * Copyright Percepio AB, 2013.
 * www.percepio.com
 ******************************************************************************/


#ifndef TRCKERNELPORT_H_
#define TRCKERNELPORT_H_

#include "FreeRTOS.h"	// Defines configUSE_TRACE_FACILITY

#define USE_TRACEALYZER_RECORDER configUSE_TRACE_FACILITY

#if (USE_TRACEALYZER_RECORDER == 1)

/* Defines that must be set for the recorder to work properly */
#define TRACE_KERNEL_VERSION 0x1AA1
#define TRACE_CPU_CLOCK_HZ configCPU_CLOCK_HZ /* Defined in "FreeRTOS.h" */
#define TRACE_PERIPHERAL_CLOCK_HZ configPERIPHERAL_CLOCK_HZ /* Defined in "FreeRTOS.h" */
#define TRACE_TICK_RATE_HZ configTICK_RATE_HZ /* Defined in "FreeRTOS.h" */
#define TRACE_CPU_CLOCKS_PER_TICK configCPU_CLOCKS_PER_TICK /* Defined in "FreeRTOS.h" */

/************************************************************************/
/* KERNEL SPECIFIC OBJECT CONFIGURATION                                 */
/************************************************************************/
#define TRACE_NCLASSES 5
#define TRACE_CLASS_QUEUE ((traceObjectClass)0)
#define TRACE_CLASS_SEMAPHORE ((traceObjectClass)1)
#define TRACE_CLASS_MUTEX ((traceObjectClass)2)
#define TRACE_CLASS_TASK ((traceObjectClass)3)
#define TRACE_CLASS_ISR ((traceObjectClass)4)

#define TRACE_KERNEL_OBJECT_COUNT (NQueue + NSemaphore + NMutex + NTask + NISR)

/* The size of the Object Property Table entries, in bytes, per object */

/* Queue properties (except name):     current number of message in queue */
#define PropertyTableSizeQueue         (NameLenQueue + 1)      

/* Semaphore properties (except name): state (signaled = 1, cleared = 0) */
#define PropertyTableSizeSemaphore     (NameLenSemaphore + 1) 

/* Mutex properties (except name):     owner (task handle, 0 = free) */
#define PropertyTableSizeMutex         (NameLenMutex + 1)         

/* Task properties (except name):      Byte 0: Current priority
                                       Byte 1: state (if already active) 
                                       Byte 2: legacy, not used
                                       Byte 3: legacy, not used */
#define PropertyTableSizeTask         (NameLenTask + 4)

/* ISR properties:                     Byte 0: priority
                                       Byte 1: state (if already active) */
#define PropertyTableSizeISR          (NameLenISR + 2)

/* The layout of the byte array representing the Object Property Table */
#define StartIndexQueue            0
#define StartIndexSemaphore        StartIndexQueue     + NQueue * PropertyTableSizeQueue
#define StartIndexMutex            StartIndexSemaphore + NSemaphore * PropertyTableSizeSemaphore
#define StartIndexTask             StartIndexMutex     + NMutex * PropertyTableSizeMutex
#define StartIndexISR              StartIndexTask      + NTask * PropertyTableSizeTask

/* Number of bytes used by the object table */
#define TRACE_OBJECT_TABLE_SIZE    StartIndexISR       + NISR * PropertyTableSizeISR


/* Includes */
#include "trcTypes.h"
#include "trcConfig.h"
#include "trcHooks.h"
#include "trcHardwarePort.h"
#include "trcBase.h"
#include "trcKernel.h"
#include "trcUser.h"

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
 *  vTraceStoreKernelCall(EVENTGROUP_CREATE + objectclass, ...
 *
 * The object class ID is given by the three LSB bits, in such cases. Since each 
 * object class has a separate object property table, the class ID is needed to 
 * know what section in the object table to use for getting an object name from
 * an object handle. 
 ******************************************************************************/

#define NULL_EVENT                   (0x00)  /* Ignored in the analysis*/

/*******************************************************************************
 * EVENTGROUP_DIV
 *
 * Miscellaneous events.
 ******************************************************************************/
#define EVENTGROUP_DIV               (NULL_EVENT + 1)                   /*0x01*/
#define DIV_XPS                      (EVENTGROUP_DIV + 0)               /*0x01*/
#define DIV_TASK_READY               (EVENTGROUP_DIV + 1)               /*0x02*/
#define DIV_NEW_TIME                 (EVENTGROUP_DIV + 2)               /*0x03*/

/*******************************************************************************
 * EVENTGROUP_TS
 *
 * Events for storing task-switches and interrupts. The RESUME events are 
 * generated if the task/interrupt is already marked active.
 ******************************************************************************/
#define EVENTGROUP_TS                (EVENTGROUP_DIV + 3)               /*0x04*/
#define TS_ISR_BEGIN                 (EVENTGROUP_TS + 0)                /*0x04*/
#define TS_ISR_RESUME                (EVENTGROUP_TS + 1)                /*0x05*/
#define TS_TASK_BEGIN                (EVENTGROUP_TS + 2)                /*0x06*/
#define TS_TASK_RESUME               (EVENTGROUP_TS + 3)                /*0x07*/

/*******************************************************************************
 * EVENTGROUP_OBJCLOSE_NAME
 * 
 * About Close Events
 * When an object is evicted from the object property table (object close), two 
 * internal events are stored (EVENTGROUP_OBJCLOSE_NAME and 
 * EVENTGROUP_OBJCLOSE_PROP), containing the handle-name mapping and object 
 * properties valid up to this point.
 ******************************************************************************/
#define EVENTGROUP_OBJCLOSE_NAME     (EVENTGROUP_TS + 4)                /*0x08*/

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
#define EVENTGROUP_OBJCLOSE_PROP     (EVENTGROUP_OBJCLOSE_NAME + 8)     /*0x10*/

/*******************************************************************************
 * EVENTGROUP_CREATE
 * 
 * The events in this group are used to log Kernel object creations.
 * The lower three bits in the event code gives the object class, i.e., type of
 * create operation (task, queue, semaphore, etc).
 ******************************************************************************/
#define EVENTGROUP_CREATE_SUCCESS    (EVENTGROUP_OBJCLOSE_PROP + 8)             /*0x18*/

/*******************************************************************************
 * EVENTGROUP_SEND
 * 
 * The events in this group are used to log Send/Give events on queues, 
 * semaphores and mutexes The lower three bits in the event code gives the 
 * object class, i.e., what type of object that is operated on (queue, semaphore 
 * or mutex).
 ******************************************************************************/
#define EVENTGROUP_SEND_SUCCESS      (EVENTGROUP_CREATE_SUCCESS + 8)                    /*0x20*/

/*******************************************************************************
 * EVENTGROUP_RECEIVE
 * 
 * The events in this group are used to log Receive/Take events on queues, 
 * semaphores and mutexes. The lower three bits in the event code gives the 
 * object class, i.e., what type of object that is operated on (queue, semaphore
 * or mutex).
 ******************************************************************************/
#define EVENTGROUP_RECEIVE_SUCCESS                       (EVENTGROUP_SEND_SUCCESS + 8)  /*0x28*/

/* Send/Give operations, from ISR */
#define EVENTGROUP_SEND_FROM_ISR_SUCCESS              (EVENTGROUP_RECEIVE_SUCCESS + 8)  /*0x30*/

/* Receive/Take operations, from ISR */
#define EVENTGROUP_RECEIVE_FROM_ISR_SUCCESS     (EVENTGROUP_SEND_FROM_ISR_SUCCESS + 8)  /*0x38*/

/* "Failed" event type versions of above (timeout, failed allocation, etc) */
#define EVENTGROUP_KSE_FAILED         (EVENTGROUP_RECEIVE_FROM_ISR_SUCCESS + 8) /*0x40*/

/* Failed create calls - memory allocation failed */
#define EVENTGROUP_CREATE_FAILED                (EVENTGROUP_KSE_FAILED) /*0x40*/

/* Failed send/give - timeout! */
#define EVENTGROUP_SEND_FAILED           (EVENTGROUP_CREATE_FAILED + 8) /*0x48*/

/* Failed receive/take - timeout! */
#define EVENTGROUP_RECEIVE_FAILED          (EVENTGROUP_SEND_FAILED + 8) /*0x50*/

/* Failed non-blocking send/give - queue full */
#define EVENTGROUP_SEND_FROM_ISR_FAILED (EVENTGROUP_RECEIVE_FAILED + 8) /*0x58*/

/* Failed non-blocking receive/take - queue empty */
#define EVENTGROUP_RECEIVE_FROM_ISR_FAILED \
                                  (EVENTGROUP_SEND_FROM_ISR_FAILED + 8) /*0x60*/

/* Events when blocking on receive/take */
#define EVENTGROUP_RECEIVE_BLOCK \
                               (EVENTGROUP_RECEIVE_FROM_ISR_FAILED + 8) /*0x68*/

/* Events when blocking on send/give */
#define EVENTGROUP_SEND_BLOCK     (EVENTGROUP_RECEIVE_BLOCK + 8)  /*0x70*/

/* Events on queue peek (receive) */
#define EVENTGROUP_PEEK_SUCCESS              (EVENTGROUP_SEND_BLOCK + 8)     /*0x78*/

/* Events on object delete (vTaskDelete or vQueueDelete) */
#define EVENTGROUP_DELETE_SUCCESS            (EVENTGROUP_PEEK_SUCCESS + 8)              /*0x80*/

/* Other events - object class is implied: TASK */
#define EVENTGROUP_OTHERS            (EVENTGROUP_DELETE_SUCCESS + 8)            /*0x88*/
#define TASK_DELAY_UNTIL             (EVENTGROUP_OTHERS + 0)            /*0x88*/
#define TASK_DELAY                   (EVENTGROUP_OTHERS + 1)            /*0x89*/
#define TASK_SUSPEND                 (EVENTGROUP_OTHERS + 2)            /*0x8A*/
#define TASK_RESUME                  (EVENTGROUP_OTHERS + 3)            /*0x8B*/
#define TASK_RESUME_FROM_ISR         (EVENTGROUP_OTHERS + 4)            /*0x8C*/
#define TASK_PRIORITY_SET            (EVENTGROUP_OTHERS + 5)            /*0x8D*/
#define TASK_PRIORITY_INHERIT        (EVENTGROUP_OTHERS + 6)            /*0x8E*/
#define TASK_PRIORITY_DISINHERIT     (EVENTGROUP_OTHERS + 7)            /*0x8F*/

/* Not yet used */
#define EVENTGROUP_FTRACE_PLACEHOLDER    (EVENTGROUP_OTHERS + 8)        /*0x90*/

/* User events */
#define EVENTGROUP_USEREVENT (EVENTGROUP_FTRACE_PLACEHOLDER + 8)        /*0x98*/
#define USER_EVENT (EVENTGROUP_USEREVENT + 0)

/* Allow for 0-15 arguments (the number of args is added to event code) */
#define USER_EVENT_LAST (EVENTGROUP_USEREVENT + 15)                     /*0xA7*/

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

#define EVENTGROUP_SYS (EVENTGROUP_USEREVENT + 16)                      /*0xA8*/
#define XTS8 (EVENTGROUP_SYS + 0)                                       /*0xA8*/
#define XTS16 (EVENTGROUP_SYS + 1)                                      /*0xA9*/

#define EVENT_BEING_WRITTEN (EVENTGROUP_SYS + 2)                        /*0xAA*/

#define RESERVED_DUMMY_CODE (EVENTGROUP_SYS + 3)                        /*0xAB*/



/************************************************************************/
/* KERNEL SPECIFIC DATA AND FUNCTIONS NEEDED TO PROVIDE THE             */
/* FUNCTIONALITY REQUESTED BY THE TRACE RECORDER                        */
/************************************************************************/

/******************************************************************************
 * TraceObjectClassTable
 * Translates a FreeRTOS QueueType into trace objects classes (TRACE_CLASS_).
 * This was added since we want to map both types of Mutex and both types of 
 * Semaphores on common classes for all Mutexes and all Semaphores respectively. 
 * 
 * FreeRTOS Queue types
 * #define queueQUEUE_TYPE_BASE                  (0U) => TRACE_CLASS_QUEUE
 * #define queueQUEUE_TYPE_MUTEX                 (1U) => TRACE_CLASS_MUTEX
 * #define queueQUEUE_TYPE_COUNTING_SEMAPHORE    (2U) => TRACE_CLASS_SEMAPHORE
 * #define queueQUEUE_TYPE_BINARY_SEMAPHORE      (3U) => TRACE_CLASS_SEMAPHORE
 * #define queueQUEUE_TYPE_RECURSIVE_MUTEX       (4U) => TRACE_CLASS_MUTEX 
 ******************************************************************************/

extern traceObjectClass TraceObjectClassTable[5];

/* These functions are implemented in the .c file since certain header files must not be included in this one */
objectHandleType prvTraceGetObjectNumber(void* handle);
unsigned char prvTraceGetObjectType(void* handle);
objectHandleType prvTraceGetTaskNumber(void* handle);
unsigned char prvTraceIsSchedulerActive(void);
unsigned char prvTraceIsSchedulerSuspended(void);
unsigned char prvTraceIsSchedulerStarted(void);
void prvTraceEnterCritical(void);
void prvTraceExitCritical(void);
void* prvTraceGetCurrentTaskHandle(void);


/************************************************************************/
/* KERNEL SPECIFIC MACROS USED BY THE TRACE RECORDER                    */
/************************************************************************/

#define TRACE_MALLOC(size) pvPortMalloc(size)

#define TRACE_ENTER_CRITICAL_SECTION() prvTraceEnterCritical();
#define TRACE_EXIT_CRITICAL_SECTION() prvTraceExitCritical();

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

#define TRACE_GET_OBJECT_NUMBER(CLASS, pxObject) (prvTraceGetObjectNumber(pxObject))
#define TRACE_SET_OBJECT_NUMBER(CLASS, pxObject) pxObject->ucQueueNumber = xTraceGetObjectHandle(TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject));

#define TRACE_GET_CLASS_EVENT_CODE(SERVICE, RESULT, CLASS, kernelClass) (uint8_t)(EVENTGROUP_##SERVICE##_##RESULT + TRACE_GET_CLASS_TRACE_CLASS(CLASS, kernelClass))
#define TRACE_GET_OBJECT_EVENT_CODE(SERVICE, RESULT, CLASS, pxObject) (uint8_t)(EVENTGROUP_##SERVICE##_##RESULT + TRACE_GET_OBJECT_TRACE_CLASS(CLASS, pxObject))
#define TRACE_GET_TASK_EVENT_CODE(SERVICE, RESULT, CLASS, pxTCB) (EVENTGROUP_##SERVICE##_##RESULT + TRACE_CLASS_TASK)



/************************************************************************/
/* KERNEL SPECIFIC WRAPPERS THAT SHOULD BE CALLED BY THE KERNEL         */
/************************************************************************/

/* Called for each task that becomes ready */
#undef traceMOVED_TASK_TO_READY_STATE
#define traceMOVED_TASK_TO_READY_STATE( pxTCB ) \
	trcKERNEL_HOOKS_MOVED_TASK_TO_READY_STATE(pxTCB);

/* Called on each OS tick. Will call uiPortGetTimestamp to make sure it is called at least once every OS tick. */
#undef traceTASK_INCREMENT_TICK
#define traceTASK_INCREMENT_TICK( xTickCount ) \
    if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxPendedTicks == 0) { trcKERNEL_HOOKS_INCREMENT_TICK(); } \
	if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdFALSE) { trcKERNEL_HOOKS_NEW_TIME(DIV_NEW_TIME, xTickCount + 1); }

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
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_TASK_DELAY(TASK_DELAY, pxCurrentTCB, xTicksToDelay); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED(UNUSED,pxCurrentTCB); \
	TRACE_EXIT_CRITICAL_SECTION();

/* Called on vTaskDelayUntil - note the use of FreeRTOS variable xTimeToWake */
#undef traceTASK_DELAY_UNTIL
#define traceTASK_DELAY_UNTIL() \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_TASK_DELAY(TASK_DELAY_UNTIL, pxCurrentTCB, xTimeToWake); \
	trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED(UNUSED,pxCurrentTCB); \
	TRACE_EXIT_CRITICAL_SECTION();

#if (INCLUDE_OBJECT_DELETE == 1)
/* Called on vTaskDelete */
#undef traceTASK_DELETE
#define traceTASK_DELETE( pxTaskToDelete ) \
	trcKERNEL_HOOKS_TASK_DELETE(DELETE, pxTaskToDelete);
#endif

#if (INCLUDE_OBJECT_DELETE == 1)
/* Called on vQueueDelete */
#undef traceQUEUE_DELETE
#define traceQUEUE_DELETE( pxQueue ) \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_OBJECT_DELETE(DELETE, UNUSED, pxQueue); \
	TRACE_EXIT_CRITICAL_SECTION();
#endif

/* Called on vTaskCreate */
#undef traceTASK_CREATE
#define traceTASK_CREATE(pxNewTCB) \
	if (pxNewTCB != NULL) \
	{ \
		trcKERNEL_HOOKS_TASK_CREATE(CREATE, pxNewTCB); \
	}

/* Called in vTaskCreate, if it fails (typically if the stack can not be allocated) */
#undef traceTASK_CREATE_FAILED
#define traceTASK_CREATE_FAILED() \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_TASK_CREATE_FAILED(CREATE); \
	TRACE_EXIT_CRITICAL_SECTION();

/* Called in xQueueCreate, and thereby for all other object based on queues, such as semaphores. */
#undef traceQUEUE_CREATE
#define traceQUEUE_CREATE( pxNewQueue )\
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_OBJECT_CREATE(CREATE, UNUSED, pxNewQueue); \
	TRACE_EXIT_CRITICAL_SECTION();

/* Called in xQueueCreate, if the queue creation fails */
#undef traceQUEUE_CREATE_FAILED
#define traceQUEUE_CREATE_FAILED( queueType ) \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_OBJECT_CREATE_FAILED(CREATE, UNUSED, queueType); \
	TRACE_EXIT_CRITICAL_SECTION();

/* Called in xQueueCreateMutex, and thereby also from xSemaphoreCreateMutex and xSemaphoreCreateRecursiveMutex */
#undef traceCREATE_MUTEX
#define traceCREATE_MUTEX( pxNewQueue ) \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_OBJECT_CREATE(CREATE, UNUSED, pxNewQueue); \
	TRACE_EXIT_CRITICAL_SECTION();

/* Called in xQueueCreateMutex when the operation fails (when memory allocation fails) */
#undef traceCREATE_MUTEX_FAILED
#define traceCREATE_MUTEX_FAILED() \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_OBJECT_CREATE_FAILED(CREATE, UNUSED, queueQUEUE_TYPE_MUTEX); \
	TRACE_EXIT_CRITICAL_SECTION();

/* Called when the Mutex can not be given, since not holder */
#undef traceGIVE_MUTEX_RECURSIVE_FAILED
#define traceGIVE_MUTEX_RECURSIVE_FAILED( pxMutex ) \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_KERNEL_SERVICE(SEND, FAILED, UNUSED, pxMutex); \
	TRACE_EXIT_CRITICAL_SECTION();

/* Called when a message is sent to a queue */
#undef traceQUEUE_SEND
#define traceQUEUE_SEND( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(SEND, SUCCESS, UNUSED, pxQueue); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(UNUSED, pxQueue, TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, pxQueue) == TRACE_CLASS_MUTEX ? (uint8_t)0 : (uint8_t)(pxQueue->uxMessagesWaiting + 1)); /*For mutex, store the new owner rather than queue length */

/* Called when a message failed to be sent to a queue (timeout) */
#undef traceQUEUE_SEND_FAILED
#define traceQUEUE_SEND_FAILED( pxQueue ) \
    TRACE_ENTER_CRITICAL_SECTION();\
    trcKERNEL_HOOKS_KERNEL_SERVICE(SEND, FAILED, UNUSED, pxQueue); \
    TRACE_EXIT_CRITICAL_SECTION();

/* Called when the task is blocked due to a send operation on a full queue */
#undef traceBLOCKING_ON_QUEUE_SEND
#define traceBLOCKING_ON_QUEUE_SEND( pxQueue ) \
	TRACE_ENTER_CRITICAL_SECTION();\
	trcKERNEL_HOOKS_KERNEL_SERVICE(SEND, BLOCK, UNUSED, pxQueue); \
	TRACE_EXIT_CRITICAL_SECTION();

/* Called when a message is received from a queue */
#undef traceQUEUE_RECEIVE
#define traceQUEUE_RECEIVE( pxQueue ) \
	trcKERNEL_HOOKS_KERNEL_SERVICE(RECEIVE, SUCCESS, UNUSED, pxQueue); \
	trcKERNEL_HOOKS_SET_OBJECT_STATE(UNUSED, pxQueue, TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, pxQueue) == TRACE_CLASS_MUTEX ? TRACE_GET_TASK_NUMBER(TRACE_GET_CURRENT_TASK()) : (uint8_t)(pxQueue->uxMessagesWaiting - 1)); /*For mutex, store the new owner rather than queue length */

/* Called when a receive operation on a queue fails (timeout) */
#undef traceQUEUE_RECEIVE_FAILED
#define traceQUEUE_RECEIVE_FAILED( pxQueue ) \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_KERNEL_SERVICE(RECEIVE, FAILED, UNUSED, pxQueue); \
	TRACE_EXIT_CRITICAL_SECTION();

/* Called when the task is blocked due to a receive operation on an empty queue */
#undef traceBLOCKING_ON_QUEUE_RECEIVE
#define traceBLOCKING_ON_QUEUE_RECEIVE( pxQueue ) \
	TRACE_ENTER_CRITICAL_SECTION(); \
	trcKERNEL_HOOKS_KERNEL_SERVICE(RECEIVE, BLOCK, UNUSED, pxQueue); \
	if (TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, pxQueue) != TRACE_CLASS_MUTEX) \
	{ \
		trcKERNEL_HOOKS_SET_TASK_INSTANCE_FINISHED(UNUSED, pxQueue); \
	} \
	TRACE_EXIT_CRITICAL_SECTION();

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


/************************************************************************/
/* KERNEL SPECIFIC MACROS TO EXCLUDE OR INCLUDE THINGS IN TRACE         */
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
/* KERNEL SPECIFIC MACROS TO NAME OBJECTS, IF NECESSARY                 */
/************************************************************************/
#define vTraceSetQueueName(object, name) \
vTraceSetObjectName(TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, object), TRACE_GET_OBJECT_NUMBER(UNUSED, object), name);

#define vTraceSetSemaphoreName(object, name) \
vTraceSetObjectName(TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, object), TRACE_GET_OBJECT_NUMBER(UNUSED, object), name);

#define vTraceSetMutexName(object, name) \
vTraceSetObjectName(TRACE_GET_OBJECT_TRACE_CLASS(UNUSED, object), TRACE_GET_OBJECT_NUMBER(UNUSED, object), name);

#endif

#endif /* TRCKERNELPORT_H_ */