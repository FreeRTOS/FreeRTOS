/*
 * IoT Common V1.0.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 */

/**
 * @file iot_taskpool_internal.h
 * @brief Internal header of task pool library. This header should not be included in
 * typical application code.
 */

#ifndef IOT_TASKPOOL_INTERNAL_H_
#define IOT_TASKPOOL_INTERNAL_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Task pool include. */
#include "iot_error.h"
#include "iot_taskpool_freertos.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "semphr.h"
#include "timers.h"

/* Configure logs for TASKPOOL functions. */
#ifdef IOT_LOG_LEVEL_TASKPOOL
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_TASKPOOL
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "TASKPOOL" )
#include "iot_logging_setup.h"

/* ---------------------------------------------------------------------------------------------- */

/**
 * @brief The task pool data structure keeps track of the internal state and the signals for the dispatcher threads.
 * The task pool is a thread safe data structure.
 *
 * @warning This is a system-level data type that should not be modified or used directly in any application.
 * @warning This is a system-level data type that can and will change across different versions of the platform, with no regards for backward compatibility.
 *
 */
typedef struct _taskPool
{
    IotDeQueue_t dispatchQueue;               /**< @brief The queue for the jobs waiting to be executed. */
    IotListDouble_t timerEventsList;          /**< @brief The timeouts queue for all deferred jobs waiting to be executed. */
    SemaphoreHandle_t dispatchSignal;         /**< @brief The synchronization object on which threads are waiting for incoming jobs. */
    StaticSemaphore_t dispatchSignalBuffer;   /**< @brief The semaphore buffer. */
    SemaphoreHandle_t xTimerEventMutex;       /**< @brief The mutex for guarding the Timer Event Queue. */
    StaticSemaphore_t xTimerEventMutexBuffer; /**< @brief The buffer for statically allocating the mutex. */
    TimerHandle_t timer;                      /**< @brief The timer for deferred jobs. */
    StaticTimer_t timerBuffer;                /**< @brief The timer buffer. */
    bool running;                             /**< @brief A flag to track whether the task pool is operational or should shut down. */
} _taskPool_t;

/**
 * @brief Represents an operation that is subject to a timer.
 *
 * These events are queued per MQTT connection. They are sorted by their
 * expiration time.
 */
typedef struct _taskPoolTimerEvent
{
    IotLink_t link;            /**< @brief List link member. */
    TickType_t expirationTime; /**< @brief When this event should be processed. */
} _taskPoolTimerEvent_t;

/**
 * @brief The job data structure keeps track of the user callback and context, as well as the status of the job.
 *
 * @warning This is a system-level data type that should not be modified or used directly in any application.
 * @warning This is a system-level data type that can and will change across different versions of the platform, with no regards for backward compatibility.
 *
 */
typedef struct _taskPoolJob
{
    IotLink_t link;                    /**< @brief The link to insert the job in the dispatch queue. */
    IotTaskPoolRoutine_t userCallback; /**< @brief The user provided callback. */
    void * pUserContext;               /**< @brief The user provided context. */
    IotTaskPoolJobStatus_t status;     /**< @brief The status for the job. */
    _taskPoolTimerEvent_t timer;       /**< @brief The timer for scheduling this job deferred. */
} _taskPoolJob_t;


#endif /* ifndef IOT_TASKPOOL_INTERNAL_H_ */
