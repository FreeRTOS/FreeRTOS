/*******************************************************************************
 * FreeRTOS+Trace v2.3.0 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcKernel.h
 *
 * Functions used by trcHooks.h, for the FreeRTOS kernel integration.
 *
 * Terms of Use
 * This software is copyright Percepio AB. The recorder library is free for
 * use together with Percepio products. You may distribute the recorder library
 * in its original form, including modifications in trcPort.c and trcPort.h
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
 * FreeRTOS+Trace is available as Free Edition and in two premium editions.
 * You may use the premium features during 30 days for evaluation.
 * Download FreeRTOS+Trace at http://www.percepio.com/products/downloads/
 *
 * Copyright Percepio AB, 2012.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRCKERNEL_H
#define TRCKERNEL_H

#include "trcBase.h"

/* Internal functions */


#if !defined INCLUDE_READY_EVENTS || INCLUDE_READY_EVENTS == 1
void vTraceStoreTaskReady(objectHandleType handle);
#endif

void vTraceStoreTaskswitch(void);

void vTraceStoreKernelCall(uint32_t eventcode, traceObjectClass objectClass, uint32_t byteParam); 

void vTraceStoreKernelCallWithNumericParamOnly(uint32_t evtcode, 
                                               uint16_t param);

void vTraceStoreKernelCallWithParam(uint32_t evtcode, traceObjectClass objectClass, 
                                    uint32_t objectNumber, uint8_t param);

void vTraceSetTaskInstanceFinished(objectHandleType handle);

void vTraceSetPriorityProperty(uint8_t objectclass, uint8_t id, uint8_t value);

uint8_t uiTraceGetPriorityProperty(uint8_t objectclass, uint8_t id);

void vTraceSetObjectState(uint8_t objectclass, uint8_t id, uint8_t value);

uint8_t uiTraceGetObjectState(uint8_t objectclass, uint8_t id);

#if (INCLUDE_OBJECT_DELETE == 1)    

void vTraceStoreObjectNameOnCloseEvent(objectHandleType handle, 
                                       traceObjectClass objectclass);

void vTraceStoreObjectPropertiesOnCloseEvent(objectHandleType handle, 
                                             traceObjectClass objectclass);
#endif

/* Internal constants for task state */
#define TASK_STATE_INSTANCE_NOT_ACTIVE 0
#define TASK_STATE_INSTANCE_ACTIVE 1
#define TASK_STATE_INSTANCE_MARKED_FINISHED 2

extern objectHandleType handle_of_running_task;

/* This defines the mapping between FreeRTOS queue types and our internal 
class IDs */
extern traceObjectClass TraceObjectClassTable[5];

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
 * EVENTGROUP_RE
 *
 * Events that indicate that something is ready to execute.
 ******************************************************************************/
#define EVENTGROUP_RE                (NULL_EVENT + 2)                   /*0x02*/
#define TR_TASK_READY                (EVENTGROUP_RE + 0)                /*0x02*/

/*******************************************************************************
 * EVENTGROUP_TS
 *
 * Events for storing task-switches and interrupts. The RESUME events are 
 * generated if the task/interrupt is already marked active.
 ******************************************************************************/
#define EVENTGROUP_TS                (EVENTGROUP_RE + 2)                /*0x04*/
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
 * EVENTGROUP_OBJCLOSE_PROP), containg the handle-name mapping and object 
 * properties valid up to this point.
 ******************************************************************************/
#define EVENTGROUP_OBJCLOSE_NAME     (EVENTGROUP_TS + 4)                /*0x08*/

/*******************************************************************************
 * EVENTGROUP_OBJCLOSE_PROP
 * 
 * The internal event carrying properties of deleted objects
 * The handle and object class of the closed object is not stored in this event, 
 * but is assumed to be the same as in the preceeding CLOSE event. Thus, these 
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
#define EVENTGROUP_CREATE    (EVENTGROUP_OBJCLOSE_PROP + 8)             /*0x18*/

/*******************************************************************************
 * EVENTGROUP_SEND
 * 
 * The events in this group are used to log Send/Give events on queues, 
 * semaphores and mutexeds The lower three bits in the event code gives the 
 * object class, i.e., what type of object that is operated on (queue, semaphore 
 * or mutex).
 ******************************************************************************/
#define EVENTGROUP_SEND      (EVENTGROUP_CREATE + 8)                    /*0x20*/

/*******************************************************************************
 * EVENTGROUP_RECEIVE
 * 
 * The events in this group are used to log Receive/Take events on queues, 
 * semaphores and mutexes. The lower three bits in the event code gives the 
 * object class, i.e., what type of object that is operated on (queue, semaphore
 * or mutex).
 ******************************************************************************/
#define EVENTGROUP_RECEIVE                       (EVENTGROUP_SEND + 8)  /*0x28*/

/* Send/Give operations, from ISR */
#define EVENTGROUP_SEND_FROM_ISR              (EVENTGROUP_RECEIVE + 8)  /*0x30*/

/* Receive/Take operations, from ISR */
#define EVENTGROUP_RECEIVE_FROM_ISR     (EVENTGROUP_SEND_FROM_ISR + 8)  /*0x38*/

/* "Failed" event type versions of above (timeout, failed allocation, etc) */
#define EVENTGROUP_FAILED_KSE         (EVENTGROUP_RECEIVE_FROM_ISR + 8) /*0x40*/

/* Failed create calls - memory allocation failed */
#define EVENTGROUP_FAILED_CREATE                (EVENTGROUP_FAILED_KSE) /*0x40*/

/* Failed send/give - timeout! */
#define EVENTGROUP_FAILED_SEND           (EVENTGROUP_FAILED_CREATE + 8) /*0x48*/

/* Failed receive/take - timeout! */
#define EVENTGROUP_FAILED_RECEIVE          (EVENTGROUP_FAILED_SEND + 8) /*0x50*/

/* Failed non-blocking send/give - queue full */
#define EVENTGROUP_FAILED_SEND_FROM_ISR (EVENTGROUP_FAILED_RECEIVE + 8) /*0x58*/

/* Failed non-blocking receive/take - queue empty */
#define EVENTGROUP_FAILED_RECEIVE_FROM_ISR \
                                  (EVENTGROUP_FAILED_SEND_FROM_ISR + 8) /*0x60*/

/* Events when blocking on receive/take */
#define EVENTGROUP_BLOCK_ON_RECEIVE \
                               (EVENTGROUP_FAILED_RECEIVE_FROM_ISR + 8) /*0x68*/

/* Events when blocking on send/give */
#define EVENTGROUP_BLOCK_ON_SEND     (EVENTGROUP_BLOCK_ON_RECEIVE + 8)  /*0x70*/

/* Events on queue peek (receive) */
#define EVENTGROUP_PEEK              (EVENTGROUP_BLOCK_ON_SEND + 8)     /*0x78*/

/* Events on object delete (vTaskDelete or vQueueDelete) */
#define EVENTGROUP_DELETE            (EVENTGROUP_PEEK + 8)              /*0x80*/

/* Other events - object class is implied: TASK */
#define EVENTGROUP_OTHERS            (EVENTGROUP_DELETE + 8)            /*0x88*/
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
 * the DTS field of the current event, an XTS event is inserted immidiatly 
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

#endif
