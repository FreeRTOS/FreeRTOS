/*******************************************************************************
 * FreeRTOS+Trace v2.3.0 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcHooks.h
 *
 * The kernel integration hooks for FreeRTOS (v7.1.0 or later). This file should
 * be included in the end of FreeRTOSConfig.h, together with:
 *
 * #define configUSE_TRACE_FACILITY 1
 *
 * NOTE: 
 * For IAR Embedded Workbench for ARM, you need to have a preprocessor condition
 * on the include, to except it from the assembler step which otherwise give
 * compile-time errors.
 *
 * #ifdef __ICCARM__
 *       #include "percepio/Include/trcHooks.h"
 * #endif
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

#ifndef TRCHOOKS_H
#define TRCHOOKS_H

#if (configUSE_TRACE_FACILITY == 1)

    #include "trcUser.h"
	
    #undef INCLUDE_xTaskGetSchedulerState
    #define INCLUDE_xTaskGetSchedulerState 1
	
    #undef INCLUDE_xTaskGetCurrentTaskHandle
    #define INCLUDE_xTaskGetCurrentTaskHandle 1
	
#if !defined INCLUDE_READY_EVENTS || INCLUDE_READY_EVENTS == 1
    /* Called for each task that becomes ready */
    #undef traceMOVED_TASK_TO_READY_STATE
    #define traceMOVED_TASK_TO_READY_STATE( pxTCB ) \
    vTraceStoreTaskReady((unsigned char)pxTCB->uxTaskNumber);
#endif
	
    /* Called on each OS tick. Will call uiPortGetTimestamp to make sure it is called at least once every OS tick. */
    #undef traceTASK_INCREMENT_TICK
    #define traceTASK_INCREMENT_TICK( xTickCount ) \
      if (uxSchedulerSuspended == ( unsigned portBASE_TYPE ) pdTRUE || uxMissedTicks == 0) {extern uint32_t uiTraceTickCount; uiTraceTickCount++; uiTracePortGetTimeStamp(0);}

    /* Called on each task-switch */
    #undef traceTASK_SWITCHED_IN
    #define traceTASK_SWITCHED_IN() \
      vTraceStoreTaskswitch();

    /* Called on vTaskSuspend */
    #undef traceTASK_SUSPEND
    #define traceTASK_SUSPEND( pxTaskToSuspend ) \
      vTraceStoreKernelCall(TASK_SUSPEND, TRACE_CLASS_TASK, pxTaskToSuspend->uxTaskNumber); \
      vTraceSetTaskInstanceFinished((uint8_t)pxTaskToSuspend->uxTaskNumber);

    /* Called on vTaskDelay - note the use of FreeRTOS variable xTicksToDelay */
    #undef traceTASK_DELAY
    #define traceTASK_DELAY() \
      portENTER_CRITICAL(); \
      vTraceStoreKernelCallWithNumericParamOnly(TASK_DELAY, (uint16_t)xTicksToDelay);\
      vTraceSetTaskInstanceFinished((uint8_t)pxCurrentTCB->uxTaskNumber);\
      portEXIT_CRITICAL();

    /* Called on vTaskDelayUntil - note the use of FreeRTOS variable xTimeToWake */
    #undef traceTASK_DELAY_UNTIL
    #define traceTASK_DELAY_UNTIL() \
      portENTER_CRITICAL(); \
      vTraceStoreKernelCallWithNumericParamOnly(TASK_DELAY_UNTIL, (uint16_t)xTimeToWake); \
      vTraceSetTaskInstanceFinished((uint8_t)pxCurrentTCB->uxTaskNumber); \
      portEXIT_CRITICAL();

#ifndef INCLUDE_OBJECT_DELETE
#define INCLUDE_OBJECT_DELETE 1
#endif

#if (INCLUDE_OBJECT_DELETE == 1)
    /* Called on vTaskDelete */
    #undef traceTASK_DELETE
    #define traceTASK_DELETE( pxTaskToDelete ) \
      trcCRITICAL_SECTION_BEGIN(); \
      vTraceStoreKernelCall(EVENTGROUP_DELETE + TRACE_CLASS_TASK, TRACE_CLASS_TASK, pxTaskToDelete->uxTaskNumber); \
      vTraceStoreObjectNameOnCloseEvent((objectHandleType)pxTaskToDelete->uxTaskNumber, TRACE_CLASS_TASK); \
      vTraceStoreObjectPropertiesOnCloseEvent((objectHandleType)pxTaskToDelete->uxTaskNumber, TRACE_CLASS_TASK); \
      vTraceSetPriorityProperty(TRACE_CLASS_TASK, (objectHandleType)pxTaskToDelete->uxTaskNumber, (uint8_t)pxTaskToDelete->uxPriority); \
      vTraceSetObjectState(TRACE_CLASS_TASK, (objectHandleType)pxTaskToDelete->uxTaskNumber, TASK_STATE_INSTANCE_NOT_ACTIVE); \
      vTraceFreeObjectHandle(TRACE_CLASS_TASK, (objectHandleType)pxTaskToDelete->uxTaskNumber); \
      trcCRITICAL_SECTION_END();
#endif

    /* Called on vTaskCreate */
    #undef traceTASK_CREATE
    #define traceTASK_CREATE( pxNewTCB ) \
      if (pxNewTCB != NULL){ \
          pxNewTCB->uxTaskNumber = xTraceGetObjectHandle(TRACE_CLASS_TASK); \
          vTraceSetObjectName(TRACE_CLASS_TASK, (objectHandleType)pxNewTCB->uxTaskNumber, (char*)pxNewTCB->pcTaskName); \
          vTraceSetPriorityProperty(TRACE_CLASS_TASK, (objectHandleType)pxNewTCB->uxTaskNumber, (uint8_t)pxNewTCB->uxPriority); \
          vTraceStoreKernelCall(EVENTGROUP_CREATE + TRACE_CLASS_TASK, TRACE_CLASS_TASK, pxNewTCB->uxTaskNumber);\
      }

    /* Called in vTaskCreate, if it fails (typically if the stack can not be allocated) */
    #undef traceTASK_CREATE_FAILED
    #define traceTASK_CREATE_FAILED() \
      portENTER_CRITICAL();\
      vTraceStoreKernelCall(EVENTGROUP_FAILED_CREATE + TRACE_CLASS_TASK, TRACE_CLASS_TASK, 0); \
      portEXIT_CRITICAL();

    /* Called in xQueueCreate, and thereby for all other object based on queues, such as semaphores. */
    #undef traceQUEUE_CREATE
    #define traceQUEUE_CREATE( pxNewQueue )\
        portENTER_CRITICAL(); \
        pxNewQueue->ucQueueNumber = xTraceGetObjectHandle(TraceObjectClassTable[pxNewQueue->ucQueueType]);\
        vTraceStoreKernelCall(EVENTGROUP_CREATE + TraceObjectClassTable[pxNewQueue->ucQueueType], TraceObjectClassTable[pxNewQueue->ucQueueType], pxNewQueue->ucQueueNumber); \
        vTraceSetObjectState(TraceObjectClassTable[pxNewQueue->ucQueueType], pxNewQueue->ucQueueNumber, 0); \
        portEXIT_CRITICAL();

    /* Called in xQueueCreate, if the queue creation fails */
    #undef traceQUEUE_CREATE_FAILED
    #define traceQUEUE_CREATE_FAILED( queueType ) \
        portENTER_CRITICAL();\
        vTraceStoreKernelCall((uint8_t)(EVENTGROUP_FAILED_CREATE + TraceObjectClassTable[queueType]), TraceObjectClassTable[queueType], 0); \
        portEXIT_CRITICAL();
    
    /* Called in xQueueCreateMutex, and thereby also from xSemaphoreCreateMutex and xSemaphoreCreateRecursiveMutex */
    #undef traceCREATE_MUTEX
    #define traceCREATE_MUTEX( pxNewQueue ) \
      portENTER_CRITICAL();\
      pxNewQueue->ucQueueNumber = xTraceGetObjectHandle(TRACE_CLASS_MUTEX); \
      vTraceStoreKernelCall(EVENTGROUP_CREATE + TraceObjectClassTable[pxNewQueue->ucQueueType], TraceObjectClassTable[pxNewQueue->ucQueueType], pxNewQueue->ucQueueNumber); \
      vTraceSetObjectState(TraceObjectClassTable[pxNewQueue->ucQueueType], pxNewQueue->ucQueueNumber, 0); \
      portEXIT_CRITICAL();

    /* Called in xQueueCreateMutex when the operation fails (when memory allocation fails) */
    #undef traceCREATE_MUTEX_FAILED
    #define traceCREATE_MUTEX_FAILED() \
        portENTER_CRITICAL();\
        vTraceStoreKernelCall(EVENTGROUP_FAILED_CREATE + TRACE_CLASS_MUTEX, TRACE_CLASS_MUTEX, 0);\
        portEXIT_CRITICAL();

    /* Called when the Mutex can not be given, since not holder */
    #undef traceGIVE_MUTEX_RECURSIVE_FAILED
    #define traceGIVE_MUTEX_RECURSIVE_FAILED( pxMutex ) \
        portENTER_CRITICAL();\
        vTraceStoreKernelCall(EVENTGROUP_FAILED_SEND + TRACE_CLASS_MUTEX, TRACE_CLASS_MUTEX, pxMutex->ucQueueNumber); \
        portEXIT_CRITICAL();

    /* Called when a message is sent to a queue */
    #undef traceQUEUE_SEND
    #define traceQUEUE_SEND( pxQueue ) \
      vTraceStoreKernelCall(EVENTGROUP_SEND + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber); \
      if (TraceObjectClassTable[pxQueue->ucQueueType] == TRACE_CLASS_MUTEX){\
          vTraceSetObjectState(TraceObjectClassTable[pxQueue->ucQueueType], (uint8_t)pxQueue->ucQueueNumber, (uint8_t)0); \
      }else{\
          vTraceSetObjectState(TraceObjectClassTable[pxQueue->ucQueueType], (uint8_t)pxQueue->ucQueueNumber, (uint8_t)(pxQueue->uxMessagesWaiting + 1)); \
      }

    /* Called when a message failed to be sent to a queue (timeout) */
    #undef traceQUEUE_SEND_FAILED
    #define traceQUEUE_SEND_FAILED( pxQueue ) \
      portENTER_CRITICAL();\
      vTraceStoreKernelCall(EVENTGROUP_FAILED_SEND + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber); \
      portEXIT_CRITICAL();

    /* Called when the task is blocked due to a send operation on a full queue */
    #undef traceBLOCKING_ON_QUEUE_SEND
    #define traceBLOCKING_ON_QUEUE_SEND( pxQueue ) \
      portENTER_CRITICAL();\
      vTraceStoreKernelCall(EVENTGROUP_BLOCK_ON_SEND + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber); \
      portEXIT_CRITICAL();
                
    /* Called when a message is received from a queue */
    #undef traceQUEUE_RECEIVE
    #define traceQUEUE_RECEIVE( pxQueue ) \
      vTraceStoreKernelCall(EVENTGROUP_RECEIVE + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber); \
      if (TraceObjectClassTable[pxQueue->ucQueueType] == TRACE_CLASS_MUTEX){\
          extern volatile void * volatile pxCurrentTCB; \
          vTraceSetObjectState(TraceObjectClassTable[pxQueue->ucQueueType], (objectHandleType)pxQueue->ucQueueNumber, (objectHandleType)uxTaskGetTaskNumber((xTaskHandle)pxCurrentTCB)); /*For mutex, store the new owner rather than queue length */ \
      }else{\
          vTraceSetObjectState(TraceObjectClassTable[pxQueue->ucQueueType], (objectHandleType)pxQueue->ucQueueNumber, (uint8_t)(pxQueue->uxMessagesWaiting - 1)); \
      }
        
    /* Called when the task is blocked due to a receive operation on an empty queue */
    #undef traceBLOCKING_ON_QUEUE_RECEIVE
    #define traceBLOCKING_ON_QUEUE_RECEIVE( pxQueue ) \
      portENTER_CRITICAL(); \
      vTraceStoreKernelCall(EVENTGROUP_BLOCK_ON_RECEIVE + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber); \
      if (TraceObjectClassTable[pxQueue->ucQueueType] != TRACE_CLASS_MUTEX){\
          extern volatile void * volatile pxCurrentTCB; \
          vTraceSetTaskInstanceFinished((objectHandleType)uxTaskGetTaskNumber((xTaskHandle)pxCurrentTCB)); \
      }\
      portEXIT_CRITICAL();

    /* Called on xQueuePeek */
    #undef traceQUEUE_PEEK
    #define traceQUEUE_PEEK( pxQueue ) \
        vTraceStoreKernelCall(EVENTGROUP_PEEK + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber);

    /* Called when a receive operation on a queue fails (timeout) */
    #undef traceQUEUE_RECEIVE_FAILED
    #define traceQUEUE_RECEIVE_FAILED( pxQueue ) \
      portENTER_CRITICAL(); \
      vTraceStoreKernelCall(EVENTGROUP_FAILED_RECEIVE + TraceObjectClassTable[pxQueue->ucQueueType],  TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber); \
      portEXIT_CRITICAL();
        
    /* Called when a message is sent from interrupt context, e.g., using xQueueSendFromISR */
    #undef traceQUEUE_SEND_FROM_ISR
    #define traceQUEUE_SEND_FROM_ISR( pxQueue ) \
      vTraceStoreKernelCall(EVENTGROUP_SEND_FROM_ISR + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber); \
      vTraceSetObjectState(TraceObjectClassTable[pxQueue->ucQueueType], (objectHandleType)pxQueue->ucQueueNumber, (uint8_t)(pxQueue->uxMessagesWaiting + 1));

    /* Called when a message send from interrupt context fails (since the queue was full) */
    #undef traceQUEUE_SEND_FROM_ISR_FAILED
    #define traceQUEUE_SEND_FROM_ISR_FAILED( pxQueue ) \
      vTraceStoreKernelCall(EVENTGROUP_FAILED_SEND_FROM_ISR + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber);

    /* Called when a message is received in interrupt context, e.g., using xQueueReceiveFromISR */
    #undef traceQUEUE_RECEIVE_FROM_ISR
    #define traceQUEUE_RECEIVE_FROM_ISR( pxQueue ) \
      vTraceStoreKernelCall(EVENTGROUP_RECEIVE_FROM_ISR + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber); \
      vTraceSetObjectState(TraceObjectClassTable[pxQueue->ucQueueType], (objectHandleType)pxQueue->ucQueueNumber, (uint8_t)(pxQueue->uxMessagesWaiting - 1));
    
    /* Called when a message receive from interrupt context fails (since the queue was empty) */
    #undef traceQUEUE_RECEIVE_FROM_ISR_FAILED
    #define traceQUEUE_RECEIVE_FROM_ISR_FAILED( pxQueue ) \
      vTraceStoreKernelCall(EVENTGROUP_FAILED_RECEIVE_FROM_ISR + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber);

#if (INCLUDE_OBJECT_DELETE == 1)
    /* Called on vQueueDelete */
    #undef traceQUEUE_DELETE
    #define traceQUEUE_DELETE( pxQueue ) \
    { \
        portENTER_CRITICAL();\
        vTraceStoreKernelCall(EVENTGROUP_DELETE + TraceObjectClassTable[pxQueue->ucQueueType], TraceObjectClassTable[pxQueue->ucQueueType], pxQueue->ucQueueNumber); \
        vTraceStoreObjectNameOnCloseEvent((objectHandleType)pxQueue->ucQueueNumber, TraceObjectClassTable[pxQueue->ucQueueType]); \
        vTraceStoreObjectPropertiesOnCloseEvent((objectHandleType)pxQueue->ucQueueNumber, TraceObjectClassTable[pxQueue->ucQueueType]); \
        if (TraceObjectClassTable[pxQueue->ucQueueType] == TRACE_CLASS_MUTEX){ \
            vTraceSetObjectState(TraceObjectClassTable[pxQueue->ucQueueType], (objectHandleType)pxQueue->ucQueueNumber, (objectHandleType)uxTaskGetTaskNumber((xTaskHandle)pxQueue->pxMutexHolder)); \
        }else{ \
            vTraceSetObjectState(TraceObjectClassTable[pxQueue->ucQueueType], (objectHandleType)pxQueue->ucQueueNumber, (uint8_t)uxQueueMessagesWaiting(pxQueue)); \
        } \
        vTraceFreeObjectHandle(TraceObjectClassTable[pxQueue->ucQueueType], (objectHandleType)pxQueue->ucQueueNumber); \
        portEXIT_CRITICAL();\
    }
#endif
    
    /* Called in vTaskPrioritySet */
    #undef traceTASK_PRIORITY_SET
    #define traceTASK_PRIORITY_SET( pxTask, uxNewPriority ) \
      vTraceStoreKernelCallWithParam(TASK_PRIORITY_SET, TRACE_CLASS_TASK, pxTask->uxTaskNumber, uiTraceGetPriorityProperty(TRACE_CLASS_TASK, (uint8_t)pxTask->uxTaskNumber));\
      vTraceSetPriorityProperty( TRACE_CLASS_TASK, (uint8_t)pxTask->uxTaskNumber, (uint8_t)uxNewPriority);

    /* Called in vTaskPriorityInherit, which is called by Mutex operations */
    #undef traceTASK_PRIORITY_INHERIT
    #define traceTASK_PRIORITY_INHERIT( pxTask, uxNewPriority ) \
      vTraceStoreKernelCallWithParam(TASK_PRIORITY_INHERIT, TRACE_CLASS_TASK, pxTask->uxTaskNumber, uiTraceGetPriorityProperty(TRACE_CLASS_TASK, (uint8_t)pxTask->uxTaskNumber));\
      vTraceSetPriorityProperty( TRACE_CLASS_TASK, (uint8_t)pxTask->uxTaskNumber, (uint8_t)uxNewPriority );

    /* Called in vTaskPriorityDisinherit, which is called by Mutex operations */
    #undef traceTASK_PRIORITY_DISINHERIT
    #define traceTASK_PRIORITY_DISINHERIT( pxTask, uxNewPriority ) \
      vTraceStoreKernelCallWithParam(TASK_PRIORITY_DISINHERIT, TRACE_CLASS_TASK, pxTask->uxTaskNumber, uiTraceGetPriorityProperty(TRACE_CLASS_TASK, (uint8_t)pxTask->uxTaskNumber));\
      vTraceSetPriorityProperty( TRACE_CLASS_TASK, (uint8_t)pxTask->uxTaskNumber, (uint8_t)uxNewPriority );

    /* Called in vTaskResume */
    #undef traceTASK_RESUME
    #define traceTASK_RESUME( pxTaskToResume ) \
      vTraceStoreKernelCall(TASK_RESUME, TRACE_CLASS_TASK, pxTaskToResume->uxTaskNumber);

    /* Called in vTaskResumeFromISR */
    #undef traceTASK_RESUME_FROM_ISR
    #define traceTASK_RESUME_FROM_ISR( pxTaskToResume )\
      vTraceStoreKernelCall(TASK_RESUME_FROM_ISR, TRACE_CLASS_TASK, pxTaskToResume->uxTaskNumber);

#endif
#endif
