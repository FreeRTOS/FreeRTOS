/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */
#ifndef GLOBAL_VARS_H
#define GLOBAL_VARS_H

#include "task.h"

#include <stdbool.h>

/* Indicates that the task is an Idle task. */
#define taskATTRIBUTE_IS_IDLE                   ( UBaseType_t ) ( 1UL << 0UL )

/*
 * Macros used by vListTask to indicate which state a task is in.
 */
#define tskRUNNING_CHAR                         ( 'X' )
#define tskBLOCKED_CHAR                         ( 'B' )
#define tskREADY_CHAR                           ( 'R' )
#define tskDELETED_CHAR                         ( 'D' )
#define tskSUSPENDED_CHAR                       ( 'S' )

/* Values that can be assigned to the ucNotifyState member of the TCB. */
#define taskNOT_WAITING_NOTIFICATION            ( ( uint8_t ) 0 )   /* Must be zero as it is the initialised value. */
#define taskWAITING_NOTIFICATION                ( ( uint8_t ) 1 )
#define taskNOTIFICATION_RECEIVED               ( ( uint8_t ) 2 )

/* Indicates that the task is not actively running on any core. */
#define taskTASK_NOT_RUNNING                    ( TaskRunning_t ) ( -1 )

/* Indicates that the task is actively running but scheduled to yield. */
#define taskTASK_YIELDING                       ( TaskRunning_t ) ( -2 )

#if ( configUSE_16_BIT_TICKS == 1 )
    #define taskEVENT_LIST_ITEM_VALUE_IN_USE    0x8000U
#else
    #define taskEVENT_LIST_ITEM_VALUE_IN_USE    0x80000000UL
#endif

typedef BaseType_t TaskRunning_t;

/*
 * Task control block.  A task control block (TCB) is allocated for each task,
 * and stores task state information, including a pointer to the task's context
 * (the task's run time environment, including register values)
 */
typedef struct tskTaskControlBlock       /* The old naming convention is used to prevent breaking kernel aware debuggers. */
{
    volatile StackType_t * pxTopOfStack; /**< Points to the location of the last item placed on the tasks stack.  THIS MUST BE THE FIRST MEMBER OF THE TCB STRUCT. */

    #if ( portUSING_MPU_WRAPPERS == 1 )
        xMPU_SETTINGS xMPUSettings; /**< The MPU settings are defined as part of the port layer.  THIS MUST BE THE SECOND MEMBER OF THE TCB STRUCT. */
    #endif

    #if ( configUSE_CORE_AFFINITY == 1 ) && ( configNUMBER_OF_CORES > 1 )
        UBaseType_t uxCoreAffinityMask; /**< Used to link the task to certain cores.  UBaseType_t must have greater than or equal to the number of bits as configNUMBER_OF_CORES. */
    #endif

    ListItem_t xStateListItem;                  /**< The list that the state list item of a task is reference from denotes the state of that task (Ready, Blocked, Suspended ). */
    ListItem_t xEventListItem;                  /**< Used to reference a task from an event list. */
    UBaseType_t uxPriority;                     /**< The priority of the task.  0 is the lowest priority. */
    StackType_t * pxStack;                      /**< Points to the start of the stack. */
    #if ( configNUMBER_OF_CORES > 1 )
        volatile BaseType_t xTaskRunState;      /**< Used to identify the core the task is running on, if the task is running. Otherwise, identifies the task's state - not running or yielding. */
        UBaseType_t uxTaskAttributes;           /**< Task's attributes - currently used to identify the idle tasks. */
    #endif
    char pcTaskName[ configMAX_TASK_NAME_LEN ]; /**< Descriptive name given to the task when created.  Facilitates debugging only. */

    #if ( configUSE_TASK_PREEMPTION_DISABLE == 1 )
        UBaseType_t uxPreemptionDisable; /**< Used to prevent the task from being preempted. */
    #endif

    #if ( configUSE_TASK_PREEMPTION_DISABLE == 1 )
        UBaseType_t uxDeferredStateChange; /**< Used to indicate if the task's state change is deferred. */
    #endif

    #if ( ( portSTACK_GROWTH > 0 ) || ( configRECORD_STACK_HIGH_ADDRESS == 1 ) )
        StackType_t * pxEndOfStack; /**< Points to the highest valid address for the stack. */
    #endif

    #if ( portCRITICAL_NESTING_IN_TCB == 1 )
        UBaseType_t uxCriticalNesting; /**< Holds the critical section nesting depth for ports that do not maintain their own count in the port layer. */
    #endif

    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxTCBNumber;  /**< Stores a number that increments each time a TCB is created.  It allows debuggers to determine when a task has been deleted and then recreated. */
        UBaseType_t uxTaskNumber; /**< Stores a number specifically for use by third party trace code. */
    #endif

    #if ( configUSE_MUTEXES == 1 )
        UBaseType_t uxBasePriority; /**< The priority last assigned to the task - used by the priority inheritance mechanism. */
        UBaseType_t uxMutexesHeld;
    #endif

    #if ( configUSE_APPLICATION_TASK_TAG == 1 )
        TaskHookFunction_t pxTaskTag;
    #endif

    #if ( configNUM_THREAD_LOCAL_STORAGE_POINTERS > 0 )
        void * pvThreadLocalStoragePointers[ configNUM_THREAD_LOCAL_STORAGE_POINTERS ];
    #endif

    #if ( configGENERATE_RUN_TIME_STATS == 1 )
        configRUN_TIME_COUNTER_TYPE ulRunTimeCounter; /**< Stores the amount of time the task has spent in the Running state. */
    #endif

    #if ( configUSE_C_RUNTIME_TLS_SUPPORT == 1 )
        configTLS_BLOCK_TYPE xTLSBlock; /**< Memory block used as Thread Local Storage (TLS) Block for the task. */
    #endif

    #if ( configUSE_TASK_NOTIFICATIONS == 1 )
        volatile uint32_t ulNotifiedValue[ configTASK_NOTIFICATION_ARRAY_ENTRIES ];
        volatile uint8_t ucNotifyState[ configTASK_NOTIFICATION_ARRAY_ENTRIES ];
    #endif

    /* See the comments in FreeRTOS.h with the definition of
     * tskSTATIC_AND_DYNAMIC_ALLOCATION_POSSIBLE. */
    #if ( tskSTATIC_AND_DYNAMIC_ALLOCATION_POSSIBLE != 0 )
        uint8_t ucStaticallyAllocated; /**< Set to pdTRUE if the task is a statically allocated to ensure no attempt is made to free the memory. */
    #endif

    #if ( INCLUDE_xTaskAbortDelay == 1 )
        uint8_t ucDelayAborted;
    #endif

    #if ( configUSE_POSIX_ERRNO == 1 )
        int iTaskErrno;
    #endif
} tskTCB;

/* The old tskTCB name is maintained above then typedefed to the new TCB_t name
 * below to enable the use of older kernel aware debuggers. */
typedef tskTCB TCB_t;


typedef struct QueuePointers
{
    int8_t * pcTail;     /**< Points to the byte at the end of the queue storage area.  Once more byte is allocated than necessary to store the queue items, this is used as a marker. */
    int8_t * pcReadFrom; /**< Points to the last place that a queued item was read from when the structure is used as a queue. */
} QueuePointers_t;

typedef struct SemaphoreData
{
    TaskHandle_t xMutexHolder;        /**< The handle of the task that holds the mutex. */
    UBaseType_t uxRecursiveCallCount; /**< Maintains a count of the number of times a recursive mutex has been recursively 'taken' when the structure is used as a mutex. */
} SemaphoreData_t;

typedef struct QueueDefinition /* The old naming convention is used to prevent breaking kernel aware debuggers. */
{
    int8_t * pcHead;           /**< Points to the beginning of the queue storage area. */
    int8_t * pcWriteTo;        /**< Points to the free next place in the storage area. */

    union
    {
        QueuePointers_t xQueue;     /**< Data required exclusively when this structure is used as a queue. */
        SemaphoreData_t xSemaphore; /**< Data required exclusively when this structure is used as a semaphore. */
    } u;

    List_t xTasksWaitingToSend;             /**< List of tasks that are blocked waiting to post onto this queue.  Stored in priority order. */
    List_t xTasksWaitingToReceive;          /**< List of tasks that are blocked waiting to read from this queue.  Stored in priority order. */

    volatile UBaseType_t uxMessagesWaiting; /**< The number of items currently in the queue. */
    UBaseType_t uxLength;                   /**< The length of the queue defined as the number of items it will hold, not the number of bytes. */
    UBaseType_t uxItemSize;                 /**< The size of each items that the queue will hold. */

    volatile int8_t cRxLock;                /**< Stores the number of items received from the queue (removed from the queue) while the queue was locked.  Set to queueUNLOCKED when the queue is not locked. */
    volatile int8_t cTxLock;                /**< Stores the number of items transmitted to the queue (added to the queue) while the queue was locked.  Set to queueUNLOCKED when the queue is not locked. */

    #if ( ( configSUPPORT_STATIC_ALLOCATION == 1 ) && ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) )
        uint8_t ucStaticallyAllocated; /**< Set to pdTRUE if the memory used by the queue was statically allocated to ensure no attempt is made to free the memory. */
    #endif

    #if ( configUSE_QUEUE_SETS == 1 )
        struct QueueDefinition * pxQueueSetContainer;
    #endif

    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxQueueNumber;
        uint8_t ucQueueType;
    #endif

    #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) )
        portSPINLOCK_TYPE xTaskSpinlock;
        portSPINLOCK_TYPE xISRSpinlock;
    #endif /* #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) ) */
} xQUEUE;

/* The old xQUEUE name is maintained above then typedefed to the new Queue_t
 * name below to enable the use of older kernel aware debuggers. */
typedef xQUEUE Queue_t;

/* Structure that hold state information on the buffer. */
typedef struct StreamBufferDef_t
{
    volatile size_t xTail;                       /* Index to the next item to read within the buffer. */
    volatile size_t xHead;                       /* Index to the next item to write within the buffer. */
    size_t xLength;                              /* The length of the buffer pointed to by pucBuffer. */
    size_t xTriggerLevelBytes;                   /* The number of bytes that must be in the stream buffer before a task that is waiting for data is unblocked. */
    volatile TaskHandle_t xTaskWaitingToReceive; /* Holds the handle of a task waiting for data, or NULL if no tasks are waiting. */
    volatile TaskHandle_t xTaskWaitingToSend;    /* Holds the handle of a task waiting to send data to a message buffer that is full. */
    uint8_t * pucBuffer;                         /* Points to the buffer itself - that is - the RAM that stores the data passed through the buffer. */
    uint8_t ucFlags;

    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxStreamBufferNumber; /* Used for tracing purposes. */
    #endif

    #if ( configUSE_SB_COMPLETED_CALLBACK == 1 )
        StreamBufferCallbackFunction_t pxSendCompletedCallback;    /* Optional callback called on send complete. sbSEND_COMPLETED is called if this is NULL. */
        StreamBufferCallbackFunction_t pxReceiveCompletedCallback; /* Optional callback called on receive complete.  sbRECEIVE_COMPLETED is called if this is NULL. */
    #endif
    UBaseType_t uxNotificationIndex;                               /* The index we are using for notification, by default tskDEFAULT_INDEX_TO_NOTIFY. */
    #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) )
        portSPINLOCK_TYPE xTaskSpinlock;
        portSPINLOCK_TYPE xISRSpinlock;
    #endif /* #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) ) */
} StreamBuffer_t;


#endif /* ifndef GLOBAL_VARS_H */
