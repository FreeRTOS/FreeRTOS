/*******************************************************************************
 * FreeRTOS+Trace v2.3.0 Recorder Library
 * Percepio AB, www.percepio.com
 *
 * trcUser.c
 *
 * The public API of the trace recorder library.
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

#include <string.h>
#include <stdarg.h>

#include "trcUser.h"
#include "task.h"
#include "semphr.h"

#if (configUSE_TRACE_FACILITY == 1)

extern uint8_t inExcludedTask;
extern uint8_t nISRactive;
extern uint8_t handle_of_last_logged_task;
extern uint32_t dts_min;
extern uint32_t hwtc_count_max_after_tick;
extern uint32_t hwtc_count_sum_after_tick;
extern uint32_t hwtc_count_sum_after_tick_counter;
extern unsigned char ucQueueGetQueueType(void*);
extern unsigned char ucQueueGetQueueNumber(void*);
extern char* traceErrorMessage;
static void vTraceMonitorTask(void);
static void prvTraceExcludeOrIncludeKernelServiceFromTrace(traceKernelService, uint8_t);
    
/*******************************************************************************
 * vTraceMonitorTask
 *
 * A task which periodically reports the recorder status to the console.
 * This is included depending on USE_TRACE_PROGRESS_MONITOR_TASK.
 ******************************************************************************/
static void vTraceMonitorTask(void)
{    
    portTickType xNextWakeTime;
    char localsprintbuffer[90];
    char* err = NULL;    
    char* lastErr = NULL;      
    #define STATE_INIT 0
    #define STATE_STARTED 1
    #define STATE_STOPPED 2    
    int state = STATE_INIT;
    
    vTraceConsoleMessage("\n\r[FreeRTOS+Trace] Monitor task started...\n\r");

    /* Initialise xNextWakeTime - this only needs to be done once. */
    xNextWakeTime = xTaskGetTickCount();

    for (;;)
    {
        lastErr = err;        
        err = xTraceGetLastError();
        if (err != lastErr)
        {
            sprintf(localsprintbuffer, "\n\r[FreeRTOS+Trace] Error: %s\n\r", err);
            vTraceConsoleMessage(localsprintbuffer); 
        }
        
        if (state == STATE_STOPPED || state == STATE_INIT) 
        {
            if (RecorderDataPtr->recorderActive == 1)
            {
                state = STATE_STARTED;
                vTraceConsoleMessage("\n\r[FreeRTOS+Trace] Recorder started.\n\r");                                       
            }
            else
            {
                if (state == STATE_INIT)
                {
                    
                    vTraceConsoleMessage("\n\r[FreeRTOS+Trace] Recorder not started.\n\r");
                    state = STATE_STOPPED;
                }
            }
        }
        
        if (state == STATE_STARTED)
        {
            if (RecorderDataPtr->frequency > 0)
            {
                sprintf(localsprintbuffer, 
                    "\n\r[FreeRTOS+Trace] Event count: %d, Duration: %d ms. [%d ticks]\n\r", 
                    (int)RecorderDataPtr->numEvents, 
                    (int)(RecorderDataPtr->absTimeLastEventSecond*1000 + (RecorderDataPtr->absTimeLastEvent*1000)/ RecorderDataPtr->frequency), (int)xTaskGetTickCount());
                vTraceConsoleMessage(localsprintbuffer);
            }

            if (RecorderDataPtr->recorderActive == 0)
            {
                state = STATE_STOPPED;
                vTraceConsoleMessage("\n\r[FreeRTOS+Trace] Recorder stopped.\n\r");                                       
                vTracePortEnd();
            }
                

        }

    /* Place this task in the blocked state until it is time to run again. */
        vTaskDelayUntil( &xNextWakeTime, TRACE_PROGRESS_MONITOR_TASK_PERIOD);
        
    }
}

/*******************************************************************************
 * vTraceClear
 *
 * Resets the recorder. Only necessary if a restart is desired - this is not 
 * needed in the startup initialization.
 ******************************************************************************/
void vTraceClear(void)
{
    trcCRITICAL_SECTION_BEGIN();
    
    RecorderDataPtr->absTimeLastEvent = 0;
    RecorderDataPtr->nextFreeIndex = 0;
    RecorderDataPtr->numEvents = 0;
    RecorderDataPtr->bufferIsFull = 0;

    trcCRITICAL_SECTION_END();
    
}

/*******************************************************************************
 * vTraceStartStatusMonitor
 *
 * This starts a task to monitor the state of½ the recorder. 
 * This task periodically prints a line to the console window, which shows the 
 * number of events recorded and the latest timestamp. This task
 * calls vTracePortEnd when the recorder has been stopped, where custom
 * actions can be added, e.g., to store the trace to a file
 * if a file system is available on the device.
 ******************************************************************************/
void vTraceStartStatusMonitor(void)
{    
    vTraceConsoleMessage("\n\r[FreeRTOS+Trace] Starting Trace Status Monitor...\n\r");
    (void)xTaskCreate( (pdTASK_CODE)vTraceMonitorTask, (const signed char*)"TraceMon", TRACE_PROGRESS_MONITOR_TASK_STACKSIZE, NULL, TRACE_PROGRESS_MONITOR_TASK_PRIORITY, NULL );
}

/*******************************************************************************
 * uiTraceStart
 *
 * Starts the recorder. The recorder will not be started if an error has been
 * indicated using vTraceError, e.g. if any of the Nx constants in trcConfig.h 
 * has a too small value (NTASK, NQUEUE, etc).
 * 
 * Returns 1 if the recorder was started successfully.
 * Returns 0 if the recorder start was prevented due to a previous internal 
 * error. In that case, check vTraceGetLastError to get the error message.
 * Any error message is also presented when opening a trace file in 
 * FreeRTOS+Trace v2.2.2 or later.
 ******************************************************************************/

uint32_t uiTraceStart(void)
{        
    if (traceErrorMessage == NULL)
    {
        trcCRITICAL_SECTION_BEGIN();
        RecorderDataPtr->recorderActive = 1;
        vTraceStoreTaskswitch(); /* Register the currently running task */
        trcCRITICAL_SECTION_END();
    }

    return RecorderDataPtr->recorderActive;
}

/*******************************************************************************
 * vTraceStart 
 *
 * Starts the recorder. The recorder will not be started if an error has been
 * indicated using vTraceError, e.g. if any of the Nx constants in trcConfig.h 
 * has a too small value (NTASK, NQUEUE, etc).
 * 
 * This function is obsolete, but has been saved for backwards compatibility. 
 * We recommend using uiTraceStart instead.
 ******************************************************************************/
void vTraceStart(void)
{        
    (void)uiTraceStart();
}

/*******************************************************************************
 * vTraceStop
 *
 * Stops the recorder. The recording can be resumed by calling vTraceStart.
 * This does not reset the recorder. Use vTraceClear is that is desired.
 ******************************************************************************/
void vTraceStop(void)
{
    RecorderDataPtr->recorderActive = 0;
}

/*******************************************************************************
 * xTraceGetLastError
 *
 * Gives the last error message, if any. NULL if no error message is stored.
 * The message is cleared on read.
 * Any error message is also presented when opening a trace file in 
 * FreeRTOS+Trace v2.2.2 or later.
 ******************************************************************************/
char* xTraceGetLastError(void)
{   
    return traceErrorMessage;
}

/*******************************************************************************
 * vTraceGetTraceBuffer
 * 
 * Returns a pointer to the recorder data structure. Use this together with 
 * uiTraceGetTraceBufferSize if you wish to implement an own store/upload 
 * solution, e.g., in case a debugger connection is not available for uploading 
 * the data.
 ******************************************************************************/
void* vTraceGetTraceBuffer(void)
{
    return RecorderDataPtr;
}

/*******************************************************************************
 * uiTraceGetTraceBufferSize
 * 
 * Gets the size of the recorder data structure. For use together with 
 * vTraceGetTraceBuffer if you wish to implement an own store/upload solution, 
 * e.g., in case a debugger connection is not available for uploading the data.
 ******************************************************************************/
uint32_t uiTraceGetTraceBufferSize(void)
{
    return sizeof(RecorderDataType);
}

/*******************************************************************************
 * prvTraceExcludeOrIncludeKernelServiceFromTrace
 * 
 * Includes or excludes all events that is related to the kernel service.
 ******************************************************************************/
static void prvTraceExcludeOrIncludeKernelServiceFromTrace(traceKernelService kernelService, uint8_t flag)
{
    switch(kernelService)
    {
    case TRACE_KERNEL_SERVICE_TASK_CREATE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_CREATE + TRACE_CLASS_TASK);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_CREATE + TRACE_CLASS_TASK);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_CREATE + TRACE_CLASS_TASK);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_CREATE + TRACE_CLASS_TASK);
        }
        break;
    case TRACE_KERNEL_SERVICE_TASK_DELETE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_DELETE + TRACE_CLASS_TASK);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_DELETE + TRACE_CLASS_TASK);
        }
        break;
    case TRACE_KERNEL_SERVICE_TASK_DELAY:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(TASK_DELAY);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(TASK_DELAY_UNTIL);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(TASK_DELAY);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(TASK_DELAY_UNTIL);
        }
        break;
    case TRACE_KERNEL_SERVICE_PRIORITY_SET:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(TASK_PRIORITY_SET);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(TASK_PRIORITY_SET);
        }
        break;
    case TRACE_KERNEL_SERVICE_TASK_SUSPEND:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(TASK_SUSPEND);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(TASK_SUSPEND);
        }
        break;
    case TRACE_KERNEL_SERVICE_TASK_RESUME:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(TASK_RESUME);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(TASK_RESUME_FROM_ISR);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(TASK_RESUME);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(TASK_RESUME_FROM_ISR);
        }
        break;
    case TRACE_KERNEL_SERVICE_QUEUE_CREATE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_CREATE + TRACE_CLASS_QUEUE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_CREATE + TRACE_CLASS_QUEUE);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_CREATE + TRACE_CLASS_QUEUE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_CREATE + TRACE_CLASS_QUEUE);
        }
        break;
    case TRACE_KERNEL_SERVICE_QUEUE_DELETE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_DELETE + TRACE_CLASS_QUEUE);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_DELETE + TRACE_CLASS_QUEUE);
        }
        break;
    case TRACE_KERNEL_SERVICE_QUEUE_SEND:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND + TRACE_CLASS_QUEUE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND + TRACE_CLASS_QUEUE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_SEND + TRACE_CLASS_QUEUE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FROM_ISR + TRACE_CLASS_QUEUE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND_FROM_ISR + TRACE_CLASS_QUEUE);
            
            
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND + TRACE_CLASS_QUEUE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND + TRACE_CLASS_QUEUE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_SEND + TRACE_CLASS_QUEUE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FROM_ISR + TRACE_CLASS_QUEUE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND_FROM_ISR + TRACE_CLASS_QUEUE);
        }
        break;
    case TRACE_KERNEL_SERVICE_QUEUE_RECEIVE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE + TRACE_CLASS_QUEUE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE + TRACE_CLASS_QUEUE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_RECEIVE + TRACE_CLASS_QUEUE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FROM_ISR + TRACE_CLASS_QUEUE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE_FROM_ISR + TRACE_CLASS_QUEUE);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE + TRACE_CLASS_QUEUE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE + TRACE_CLASS_QUEUE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_RECEIVE + TRACE_CLASS_QUEUE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FROM_ISR + TRACE_CLASS_QUEUE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE_FROM_ISR + TRACE_CLASS_QUEUE);
        }
        break;
    case TRACE_KERNEL_SERVICE_QUEUE_PEEK:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_PEEK + TRACE_CLASS_QUEUE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_PEEK + TRACE_CLASS_SEMAPHORE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_PEEK + TRACE_CLASS_MUTEX);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_PEEK + TRACE_CLASS_QUEUE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_PEEK + TRACE_CLASS_SEMAPHORE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_PEEK + TRACE_CLASS_MUTEX);
        }
        break;
    case TRACE_KERNEL_SERVICE_MUTEX_CREATE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_CREATE + TRACE_CLASS_MUTEX);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_CREATE + TRACE_CLASS_MUTEX);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_CREATE + TRACE_CLASS_MUTEX);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_CREATE + TRACE_CLASS_MUTEX);
        }
        break;
    case TRACE_KERNEL_SERVICE_MUTEX_DELETE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_DELETE + TRACE_CLASS_MUTEX);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_DELETE + TRACE_CLASS_MUTEX);
        }
        break;
    case TRACE_KERNEL_SERVICE_MUTEX_GIVE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND + TRACE_CLASS_MUTEX);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND + TRACE_CLASS_MUTEX);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_SEND + TRACE_CLASS_MUTEX);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FROM_ISR + TRACE_CLASS_MUTEX);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND_FROM_ISR + TRACE_CLASS_MUTEX);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND + TRACE_CLASS_MUTEX);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND + TRACE_CLASS_MUTEX);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_SEND + TRACE_CLASS_MUTEX);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FROM_ISR + TRACE_CLASS_MUTEX);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND_FROM_ISR + TRACE_CLASS_MUTEX);
        }
        break;
    case TRACE_KERNEL_SERVICE_MUTEX_TAKE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE + TRACE_CLASS_MUTEX);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE + TRACE_CLASS_MUTEX);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_RECEIVE + TRACE_CLASS_MUTEX);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FROM_ISR + TRACE_CLASS_MUTEX);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE_FROM_ISR + TRACE_CLASS_MUTEX);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE + TRACE_CLASS_MUTEX);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE + TRACE_CLASS_MUTEX);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_RECEIVE + TRACE_CLASS_MUTEX);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FROM_ISR + TRACE_CLASS_MUTEX);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE_FROM_ISR + TRACE_CLASS_MUTEX);
        }
        break;
    case TRACE_KERNEL_SERVICE_SEMAPHORE_CREATE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_CREATE + TRACE_CLASS_SEMAPHORE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_CREATE + TRACE_CLASS_SEMAPHORE);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_CREATE + TRACE_CLASS_SEMAPHORE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_CREATE + TRACE_CLASS_SEMAPHORE);
        }
        break;
    case TRACE_KERNEL_SERVICE_SEMAPHORE_DELETE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_DELETE + TRACE_CLASS_SEMAPHORE);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_DELETE + TRACE_CLASS_SEMAPHORE);
        }
        break;
    case TRACE_KERNEL_SERVICE_SEMAPHORE_GIVE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND + TRACE_CLASS_SEMAPHORE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND + TRACE_CLASS_SEMAPHORE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_SEND + TRACE_CLASS_SEMAPHORE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FROM_ISR + TRACE_CLASS_SEMAPHORE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND_FROM_ISR + TRACE_CLASS_SEMAPHORE);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND + TRACE_CLASS_SEMAPHORE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND + TRACE_CLASS_SEMAPHORE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_SEND + TRACE_CLASS_SEMAPHORE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_SEND_FROM_ISR + TRACE_CLASS_SEMAPHORE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_SEND_FROM_ISR + TRACE_CLASS_SEMAPHORE);
        }
        break;
    case TRACE_KERNEL_SERVICE_SEMAPHORE_TAKE:
        if (flag)
        {
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE + TRACE_CLASS_SEMAPHORE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE + TRACE_CLASS_SEMAPHORE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_RECEIVE + TRACE_CLASS_SEMAPHORE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FROM_ISR + TRACE_CLASS_SEMAPHORE);
            SET_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE_FROM_ISR + TRACE_CLASS_SEMAPHORE);
        }
        else
        {
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE + TRACE_CLASS_SEMAPHORE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE + TRACE_CLASS_SEMAPHORE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_BLOCK_ON_RECEIVE + TRACE_CLASS_SEMAPHORE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_RECEIVE_FROM_ISR + TRACE_CLASS_SEMAPHORE);
            CLEAR_EVENT_CODE_FLAG_ISEXCLUDED(EVENTGROUP_FAILED_RECEIVE_FROM_ISR + TRACE_CLASS_SEMAPHORE);
        }
        break;
    }
}

/******************************************************************************
 * vTraceExclude______FromTrace
 *
 * Excludes a task or object from the trace.
 * This can be useful if some irrelevant task is very frequent and is "eating
 * up the buffer". This should be called after the task has been created, but 
 * before starting the FreeRTOS scheduler.
 *****************************************************************************/
void vTraceExcludeQueueFromTrace(void* handle)
{
    SET_QUEUE_FLAG_ISEXCLUDED(ucQueueGetQueueNumber(handle));
}

void vTraceExcludeSemaphoreFromTrace(void* handle)
{
    SET_SEMAPHORE_FLAG_ISEXCLUDED(ucQueueGetQueueNumber(handle));
}

void vTraceExcludeMutexFromTrace(void* handle)
{
    SET_MUTEX_FLAG_ISEXCLUDED(ucQueueGetQueueNumber(handle));
}

void vTraceExcludeTaskFromTrace(void* handle)
{
    SET_TASK_FLAG_ISEXCLUDED(uxTaskGetTaskNumber(handle));
}

void vTraceExcludeKernelServiceFromTrace(traceKernelService kernelService)
{
    prvTraceExcludeOrIncludeKernelServiceFromTrace(kernelService, 1);
}

/******************************************************************************
 * vTraceInclude______InTrace
 *
 * Includes a task, object or kernel service in the trace. This is only
 * necessary if the task or object has been previously exluded.
 *****************************************************************************/
void vTraceIncludeQueueInTrace(void* handle)
{
    CLEAR_QUEUE_FLAG_ISEXCLUDED(ucQueueGetQueueNumber(handle));
}

void vTraceIncludeSemaphoreInTrace(void* handle)
{
    CLEAR_SEMAPHORE_FLAG_ISEXCLUDED(ucQueueGetQueueNumber(handle));
}

void vTraceIncludeMutexInTrace(void* handle)
{
    CLEAR_MUTEX_FLAG_ISEXCLUDED(ucQueueGetQueueNumber(handle));
}

void vTraceIncludeTaskInTrace(void* handle)
{
    CLEAR_TASK_FLAG_ISEXCLUDED(uxTaskGetTaskNumber(handle));
}

void vTraceIncludeKernelServiceInTrace(traceKernelService kernelService)
{
    prvTraceExcludeOrIncludeKernelServiceFromTrace(kernelService, 0);
}

/*******************************************************************************
 * vTraceSetQueueName
 *
 * Assigns a name to a FreeRTOS Queue, Semaphore or Mutex. This function should
 * be called right after creation of the queue/mutex/semaphore. If not using 
 * this function, the queues/mutexes/semaphores will be presented by their
 * numeric handle only.
 *
 * Example:
 *     actuatorQ = xQueueCreate(3, sizeof(QueueMessage));
 *     vTraceSetQueueName(actuatorQ, "ActuatorQueue");
 ******************************************************************************/
void vTraceSetQueueName(void* queue, const char* name)
{
    int t = ucQueueGetQueueType(queue);    
    vTraceSetObjectName(TraceObjectClassTable[t], 
                        (objectHandleType)ucQueueGetQueueNumber(queue), name);
}


/******************************************************************************
 * vTraceTaskInstanceIsFinished
 * 
 * This defines an explicit Instance Finish Event for the current task. It tells 
 * the recorder that the current instance of this task is finished at the next 
 * kernel call of the task, e.g., a taskDelay or a queue receive. This function 
 * should be called right before the api function call considered to be the end 
 * of the current task instance, i.e., the Instance Finish Event.
 *****************************************************************************/
void vTraceTaskInstanceIsFinished()
{
    if (handle_of_last_logged_task)
    {
        SET_TASK_FLAG_MARKIFE(handle_of_last_logged_task);    
    }
}

/*******************************************************************************
 * vvTraceTaskSkipDefaultInstanceFinishedEvents
 *
 * This is useful if there are implicit Instance Finish Events, such as 
 * vTaskDelayUntil or xQueueReceive, in a task where an explicit Instance Finish 
 * Event has been defined. This function tells the recorder that only the 
 * explicitly defined functions, using vTraceTaskInstanceIsFinished, should be
 * treated as Instance Finish Events for this task. The implicit Instance Finish 
 * Events are thus disregarded for the calling task.
 ******************************************************************************/
void vTraceTaskSkipDefaultInstanceFinishedEvents()
{    
    if (handle_of_last_logged_task)
    {
        PROPERTY_TASK_IFE_SERVICECODE(handle_of_last_logged_task) = 
          RESERVED_DUMMY_CODE;
    }
}

/*******************************************************************************
 * Interrupt recording functions 
 ******************************************************************************/

#if (INCLUDE_ISR_TRACING == 1)

#define MAX_ISR_NESTING 16
static uint8_t isrstack[MAX_ISR_NESTING];

/*******************************************************************************
 * vTraceSetISRProperties
 * 
 * Registers an Interrupt Service Routine in the recorder library, This must be
 * called before using vTraceStoreISRBegin to store ISR events. This is 
 * typically called in the startup of the system, before the scheduler is 
 * started.
 *
 * Example:
 *     #define ID_ISR_TIMER1 1       // lowest valid ID is 1
 *     #define PRIO_OF_ISR_TIMER1 3  // the hardware priority of the interrupt
 *     ...
 *     vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *     ...
 *     void ISR_handler()
 *     {
 *         vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *         ...
 *         vTraceStoreISREnd();
 *     }
 *
 * NOTE: To safely record ISRs, you need to make sure that all traced 
 * interrupts actually are disabled by trcCRITICAL_SECTION_BEGIN(), which 
 * typically is mapped to portENTER_CRITICAL(), which uses the macro 
 * portDISABLE_INTERRUPTS. However, in some ports of FreeRTOS and depending on 
 * FreeRTOS configuration, this does not disable high priority interrupts!
 * If an ISR calls vTraceStoreISRBegin while the recorder is busy, it will
 * stop the recording and give an error message.
 ******************************************************************************/
void vTraceSetISRProperties(objectHandleType handle, const char* name, char priority)
{
    vTraceSetObjectName(TRACE_CLASS_ISR, handle, name);
    vTraceSetPriorityProperty(TRACE_CLASS_ISR, handle, priority);
}

/*******************************************************************************
 * vTraceStoreISRBegin
 * 
 * Registers the beginning of an Interrupt Service Routine.
 *
 * Example:
 *     #define ID_ISR_TIMER1 1       // lowest valid ID is 1
 *     #define PRIO_OF_ISR_TIMER1 3  // the hardware priority of the interrupt
 *     ...
 *     vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *     ...
 *     void ISR_handler()
 *     {
 *         vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *         ...
 *         vTraceStoreISREnd();
 *     }
 *
 * NOTE: You need to make sure that any traced interrupts actually are 
 * disabled by trcCRITICAL_SECTION_BEGIN(), i.e., taskENTER_CRITICAL() which
 * uses portDISABLE_INTERRUPTS(). 
 * In some ports of FreeRTOS, this does not disable high-priority interrupts,
 * i.e., with priorities above configMAX_SYSCALL_INTERRUPT_PRIORITY.
 * If an invalid call to vTraceStoreISRBegin is detected (i.e., that preempted
 * a critical section of the recorder) this will generate a recorder error 
 * using vTraceError.
 ******************************************************************************/
void vTraceStoreISRBegin(objectHandleType handle)
{
    uint16_t dts4;
    TSEvent* ts = NULL;

    if (recorder_busy)
    {
      vTraceError("Illegal call to vTraceStoreISRBegin/End");
      return;
    }
    if (RecorderDataPtr->recorderActive && handle_of_last_logged_task)
    {    
        trcCRITICAL_SECTION_BEGIN();
        dts4 = (uint16_t)prvTraceGetDTS(0xFFFF);

        if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */    
        {    

            if (nISRactive < MAX_ISR_NESTING)
            {    
                isrstack[nISRactive] = handle;
                nISRactive++;            
                ts = (TSEvent*)xTraceNextFreeEventBufferSlot();
                if (ts != NULL)
                {
                    ts->type = TS_ISR_BEGIN;
                    ts->dts = dts4;
                    ts->objHandle = handle;
                    prvTraceUpdateCounters();                
                }
            }
            else
            {            
                /* This should not occur unless something is very wrong */            
                vTraceError("Too many nested interrupts!");
            }        
        }
        trcCRITICAL_SECTION_END();        
    }
}


#if (SELECTED_PORT == PORT_ARM_CortexM)

int tailchain_irq_pending(void);

/*******************************************************************************
 * tailchain_irq_pending
 *
 * For Cortex-M chips only. Returns 1 if an interrupt is pending, by checking 
 * the 8 NVIC IRQ pend registers at 0xE000E200 to 0xE000E21C. Returns 0 if no 
 * interrupt is pending. This is used to predict tailchaining of ISRs.
 ******************************************************************************/
int tailchain_irq_pending(void)
{
  uint32_t* pend_reg = ((uint32_t*)0xE000E200);
  int i;

  for (i=0; i<8; i++)
  {
    if (pend_reg[i] != 0)
    {
      return 1;
    }
  }
  return 0;  
}

#endif

/*******************************************************************************
 * vTraceStoreISREnd
 * 
 * Registers the end of an Interrupt Service Routine. 
 *
 * Example:
 *     #define ID_ISR_TIMER1 1       // lowest valid ID is 1
 *     #define PRIO_OF_ISR_TIMER1 3  // the hardware priority of the interrupt
 *     ...
 *     vTraceSetISRProperties(ID_ISR_TIMER1, "ISRTimer1", PRIO_OF_ISR_TIMER1);
 *     ...
 *     void ISR_handler()
 *     {
 *         vTraceStoreISRBegin(ID_OF_ISR_TIMER1);
 *         ...
 *         vTraceStoreISREnd();
 *     }
 *
 * NOTE: You need to make sure that any traced interrupts actually are 
 * disabled by trcCRITICAL_SECTION_BEGIN(), i.e., taskENTER_CRITICAL() which
 * uses portDISABLE_INTERRUPTS(). 
 * In some ports of FreeRTOS, this does not disable high-priority interrupts,
 * i.e., with priorities above configMAX_SYSCALL_INTERRUPT_PRIORITY.
 * If an invalid call to vTraceStoreISREnd is detected (i.e., that preempted
 * a critical section of the recorder) this will generate a recorder error 
 * using vTraceError.
 ******************************************************************************/
void vTraceStoreISREnd(void)
{
    TSEvent* ts;
    uint16_t dts5;

    if (recorder_busy)
    {
      vTraceError("Illegal call to vTraceStoreISRBegin/End");
      return;
    }
    
    if (RecorderDataPtr->recorderActive && handle_of_last_logged_task)
    {
        #if (SELECTED_PORT == PORT_ARM_CortexM)
        if (tailchain_irq_pending() > 0)
        {
            nISRactive--; /* If an IRQ strikes exactly here, the resulting 
            ISR tailchaining is not detected. The trace instead shows a very 
            short fragment of the earlier preempted task/ISR, and then the new
            ISR begins. */
            return;
        }
        #endif
      
        trcCRITICAL_SECTION_BEGIN();
        dts5 = (uint16_t)prvTraceGetDTS(0xFFFF);

        if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */    
        {    
            ts = (TSEvent*)xTraceNextFreeEventBufferSlot();
            if (ts != NULL)
            {
                if (nISRactive > 1)
                {
                    /* return to another isr */
                    ts->type = TS_ISR_RESUME;
                    ts->objHandle = isrstack[nISRactive];
                }
                else
                {
                    /* return to task */
                    ts->type = TS_TASK_RESUME;
                    ts->objHandle = handle_of_last_logged_task;
                }
                ts->dts = dts5;
                nISRactive--;
                prvTraceUpdateCounters();
            }
        }
        trcCRITICAL_SECTION_END();        
    }
}

#else

/* ISR tracing is turned off */
void vTraceIncreaseISRActive(void)
{
    if (RecorderDataPtr->recorderActive && handle_of_last_logged_task)
        nISRactive++;
}

void vTraceDecreaseISRActive(objectHandleType handle)
{
    if (RecorderDataPtr->recorderActive && handle_of_last_logged_task)
        nISRactive--;
}
#endif


/*******************************************************************************
 * User Event functions
 ******************************************************************************/

#if (INCLUDE_USER_EVENTS == 1)

 /******************************************************************************
 * vTraceUserEvent
 *
 * Basic user event (Standard and Professional Edition only)
 * 
 * Generates a User Event with a text label. The label is created/looked up
 * in the symbol table using xTraceOpenLabel.
 ******************************************************************************/
void vTraceUserEvent(traceLabel eventLabel)
{
    UserEvent* ue;
    uint8_t dts1;

    if (RecorderDataPtr->recorderActive && (! inExcludedTask || nISRactive ) && handle_of_last_logged_task)
    {
        trcCRITICAL_SECTION_BEGIN();

        dts1 = (uint8_t)prvTraceGetDTS(0xFF);

        if (RecorderDataPtr->recorderActive) /* Need to repeat this check! */    
        {       
            ue = (UserEvent*) xTraceNextFreeEventBufferSlot();
            if (ue != NULL)
            {
                ue->dts = dts1;
                ue->type = USER_EVENT;
                ue->payload = eventLabel;
                prvTraceUpdateCounters();
            }
        }
        trcCRITICAL_SECTION_END();        
    }
}

/*** Locally used in vTracePrintF ***/

/* one word (32 bit) is required for the USER_EVENT entry, 8 words 
(8*32 bit = 32 byte) available for argument data */
#define MAX_ARG_SIZE (4+32)    

static uint8_t writeInt8(void * buffer, uint8_t i, uint8_t value);
static uint8_t writeInt16(void * buffer, uint8_t i, uint16_t value);
static uint8_t writeInt32(void * buffer, uint8_t i, uint32_t value);

#if (INCLUDE_FLOAT_SUPPORT)
static uint8_t writeFloat(void * buffer, uint8_t i, float value);
static uint8_t writeDouble(void * buffer, uint8_t i, double value);
#endif

/*** Locally used in vTracePrintF ***/
static uint8_t writeInt8(void * buffer, uint8_t i, uint8_t value)
{    
    
    if (i >= MAX_ARG_SIZE)
    {
        return 255;
    }

    ((uint8_t*)buffer)[i] = value;

	if (i + 1 > MAX_ARG_SIZE)
	{
		return 255;
	}

    return i + 1;
}

/*** Locally used in vTracePrintF ***/
static uint8_t writeInt16(void * buffer, uint8_t i, uint16_t value)
{	
    /* Align to multiple of 2 */
    while ((i % 2) != 0)
    {
		if (i >= MAX_ARG_SIZE)
		{
			return 255;
		}
		        
        ((uint8_t*)buffer)[i] = 0;
        i++;        
    }
    
    if (i + 2 > MAX_ARG_SIZE)
    {
        return 255;
    }

    ((uint16_t*)buffer)[i/2] = value;

    return i + 2;
}

/*** Locally used in vTracePrintF ***/
static uint8_t writeInt32(void * buffer, uint8_t i, uint32_t value)
{
    
    /* A 32 bit value should begin at an even 4-byte address */
    while ((i % 4) != 0)
    {
		if (i >= MAX_ARG_SIZE)
		{
			return 255;
		}
		
        ((uint8_t*)buffer)[i] = 0;
        i++;
    }
    
    if (i + 4 > MAX_ARG_SIZE)
    {
        return 255;
    }        

    ((uint32_t*)buffer)[i/4] = value;

    return i + 4;
}

#if (INCLUDE_FLOAT_SUPPORT)

/*** Locally used in vTracePrintF ***/
static uint8_t writeFloat(void * buffer, uint8_t i, float value)
{
    /* A 32 bit value should begin at an even 4-byte address */
    while ((i % 4) != 0)
    {
		if (i >= MAX_ARG_SIZE)
		{
			return 255;
		}

        ((uint8_t*)buffer)[i] = 0;
        i++;
    }

    if (i + 4 > MAX_ARG_SIZE)
    {
        return 255;
    }        

    ((float*)buffer)[i/4] = value;
    
    return i + 4;
}

/*** Locally used in vTracePrintF ***/
static uint8_t writeDouble(void * buffer, uint8_t i, double value)
{
    uint32_t * dest = buffer;
    uint32_t * src = (void*)&value;
    /* The double is written as two 32 bit values, and should begin at an even 
    4-byte address (to avoid having to align with 8 byte) */
    while (i % 4 != 0)
    {
		if (i >= MAX_ARG_SIZE)
		{
			return 255;
		}

        ((uint8_t*)buffer)[i] = 0;
        i++;        
    }
    
    if (i + 8 > MAX_ARG_SIZE)
    {
        return 255;
    }       
    
    dest[i/4+0] = src[0];
    dest[i/4+1] = src[1];
    
    return i + 8;
}

#endif

 /******************************************************************************
 * vTracePrintF 
 * 
 * Advanced user events (Professional Edition only)
 *
 * Generates User Event with formatted text and data, similar to a "printf".
 * It is very fast compared to a normal "printf" since this function only 
 * stores the arguments. The actual formatting is done
 * on the host PC when the trace is displayed in the viewer tool. 
 *
 * User Event labels are created using xTraceOpenLabel.
 * Example:
 *
 *     traceLabel adc_uechannel = xTraceOpenLabel("ADC User Events");
 *     ...
 *     vTracePrint(adc_uechannel, 
 *                 "ADC channel %d: %lf volts", 
 *                 ch, (double)adc_reading/(double)scale);
 *
 * This can be combined into one line, if desired, but this is slower:
 *
 *     vTracePrint(xTraceOpenLabel("ADC User Events"), 
 *                 "ADC channel %d: %lf volts", 
 *                 ch, (double)adc_reading/(double)scale);
 *
 * Calling xTraceOpenLabel multiple times will not create duplicate entries, but
 * it is of course faster to just do it once, and then keep the handle for later 
 * use. If you don´t have any data arguments, only a text label/string, it is 
 * better to use vTraceUserEvent - it is faster.
 *
 * Format specifiers supported:
 *  %d - 32 bit signed integer
 *  %u - 32 bit unsigned integer
 *  %f - 32 bit float
 *  %s - string (is copied to the recorder symbol table)
 *  %hd - 16 bit signed integer
 *  %hu - 16 bit unsigned integer
 *  %bd - 8 bit signed integer
 *  %bu - 8 bit unsigned integer
 *  %lf - double-precision float
 * 
 * Up to 15 data arguments are allowed, with a total size of maximum 32 byte.
 * In case this is exceeded, the user event is changed into an error message.
 * 
 * The data is stored in trace buffer, and is packed to allow storing multiple 
 * smaller data entries in the same 4-byte record, e.g., four 8-bit values.
 * A string requires two bytes, as the symbol table is limited to 64K. Storing a 
 * double (%lf) uses two records, so this is quite costly. Use float (%f) unless
 * the higher precision is really necessary.
 ******************************************************************************/
void vTracePrintF(traceLabel eventLabel, const char* formatStr, ...)
{
    UserEvent* ue1;
    va_list vl;
    uint8_t argCounter = 0;
    uint8_t i = 0;
    uint8_t nofEventEntries = 0;
    uint16_t formatStrIndex = 0;    

    /**************************************************************************
    * The array tempDataBuffer is a local buffer used in a two-phase commit of 
    * the event data, since a vTracePrintF may span over multiple slots in the 
    * buffer.
    * This buffer can be made larger, of course, but remember the risk for 
    * stack overflow. Note: This should be a LOCAL buffer, must not be made 
    * global. That would cause data corruption when two calls to vTracePrintF
    * from different tasks overlaps (interrupts are only disabled in a small 
    * part of this function, otherwise enabled)
    ***************************************************************************/
		
    uint32_t tempDataBuffer[(3 + MAX_ARG_SIZE) / 4];   
	
	
    if ((inExcludedTask == 0) &&
        (nISRactive == 0) &&
        (RecorderDataPtr->recorderActive == 1) &&
        (handle_of_last_logged_task > 0))
    {        
        /* First, write the "primary" user event entry in the local buffer, but 
        let the event type be "EVENT_BEING_WRITTEN" for now...*/

        ue1 = (UserEvent*)(&tempDataBuffer[0]);         
        ue1->type = EVENT_BEING_WRITTEN;      /* Update this as the last step */
        
        i = 4;
        formatStrIndex = 0;
        va_start(vl, formatStr);          /* Begin reading the arguments list */

        while (formatStr[formatStrIndex] != '\0')
        {
            if (formatStr[formatStrIndex] == '%')
            {
                argCounter++;

                if (argCounter > 15)
                {
                    vTraceError("vTracePrintF - Too many arguments, max 15 allowed!");
                    va_end(vl);                    
                    formatStr = "[vTracePrintF error] Too many arguments, max 15 allowed!";
                    i = 4;
                    break;            
                }

/*******************************************************************************
 * These below code writes raw data (primitive datatypes) in the event buffer, 
 * instead of the normal event structs (where byte 0 is event type).
 * These data entries must never be interpreted as real event data, as the type
 * field would be misleading since used for payload data. 
 * 
 * The correctness of this encoding depends on two mechanisms:
 * 
 * 1. An initial USER_EVENT, which type code tells the number of 32-bit data 
 * entires that follows. (code - USER_EVENT = number of data entries). 
 * Note that a data entry corresponds to the slots that normally corresponds to 
 * one (1) event, i.e., 32 bits. vTracePrintF may encode several pieces of data 
 * in one data entry, e.g., two 16-bit values or four 8-bit values, one 16-bit
 * value followes by two 8-bit values, etc.
 *
 * 2. A two-phase commit procedure, where the USER_EVENT and data entries are 
 * written to a local buffer at first, and when all checks are OK then copied to
 * the main event buffer using a fast memcpy. The event code is finalized as the
 * very last step. Before that that step, the event code indicates an unfinished
 * event, which causes it to be ignored and stop the loading of the file (since 
 * an unfinished event is the last event in the trace).
*******************************************************************************/
                formatStrIndex++;
                switch (formatStr[formatStrIndex])
                {
                case 'd':    i = writeInt32((uint8_t*)tempDataBuffer, 
                                                i, 
                                                (uint32_t)va_arg(vl, uint32_t)); 
                             break;
                case 'u':    i = writeInt32((uint8_t*)tempDataBuffer, 
                                                i, 
                                                (uint32_t)va_arg(vl, uint32_t)); 
                             break;
                case 's':    i = writeInt16((uint8_t*)tempDataBuffer, 
                                                i, 
                                                (uint16_t)xTraceOpenLabel((char*)va_arg(vl, char*))); 
                             break;

#if (INCLUDE_FLOAT_SUPPORT)
                             /* Yes, "double" as type also in the float 
                             case. This since "float" is promoted into "double" 
                             by the va_arg stuff. */
                case 'f':    i = writeFloat((uint8_t*)tempDataBuffer, 
                                                i, 
                                                (float)va_arg(vl, double)); 
                             break;    
#else
/* No support for floats, but attempt to store a float user event
avoid a possible crash due to float reference. Instead store the 
data on uint_32 format (will not be displayed anyway). This is just
to keep va_arg and i consistent. */

                case 'f':    i = writeInt32((uint8_t*)tempDataBuffer,
                                                i, 
                                                (uint32_t)va_arg(vl, double)); 
#endif
                case 'l':
                    formatStrIndex++;
                    switch (formatStr[formatStrIndex])
                    {
#if (INCLUDE_FLOAT_SUPPORT)
                    case 'f':     i = writeDouble((uint8_t*)tempDataBuffer, 
                                                      i, 
                                                      (double)va_arg(vl, double)); 
                                  break;
#else
/* No support for floats, but attempt to store a float user event
avoid a possible crash due to float reference. Instead store the 
data on uint_32 format (will not be displayed anyway). This is just
to keep va_arg and i consistent. */
                    case 'f':    i = writeInt32((uint8_t*)tempDataBuffer, /* In this case, the value will not be shown anyway */
                                                    i, 
                                                    (uint32_t)va_arg(vl, double)); 
                                 i = writeInt32((uint8_t*)tempDataBuffer, /* Do it twice, to write in total 8 bytes */
                                                    i, 
                                                    (uint32_t)va_arg(vl, double)); 
#endif

                    }
                    break;
                case 'h':
                    formatStrIndex++;
                    switch (formatStr[formatStrIndex])
                    {
                    case 'd':    i = writeInt16((uint8_t*)tempDataBuffer, 
                                                    i, 
                                                    (uint16_t)va_arg(vl, uint32_t)); 
                                 break;
                    case 'u':    i = writeInt16((uint8_t*)tempDataBuffer, 
                                                    i, 
                                                    (uint16_t)va_arg(vl, uint32_t)); 
                                 break;
                    }
                    break;
                case 'b':
                    formatStrIndex++;
                    switch (formatStr[formatStrIndex])
                    {
                    case 'd':    i = writeInt8((uint8_t*)tempDataBuffer, 
                                                   i, 
                                                   (uint8_t)va_arg(vl, uint32_t)); 
                                 break;
                    case 'u':    i = writeInt8((uint8_t*)tempDataBuffer, 
                                                   i, 
                                                   (uint8_t)va_arg(vl, uint32_t)); 
                                 break;
                    }
                    break;
                }
            }                                    
            formatStrIndex++;    
            if (i == 255)
            {
                va_end(vl);
                //vTraceError("vTracePrintF - Too large arguments, max 32 byte allowed!");
                formatStr = "[vTracePrintF error] Too large arguments, max 32 byte allowed!";
                i = 4;
                break;
            }
        }

        va_end(vl);
		
        /* Store the format string, with a reference to the channel symbol */
        ue1->payload = prvTraceOpenSymbol(formatStr, eventLabel);     

        trcCRITICAL_SECTION_BEGIN();  

        ue1->dts = (uint8_t)prvTraceGetDTS(0xFF);
        if (! RecorderDataPtr->recorderActive)
        {

            /* Abort, since an XTS event (created by prvTraceGetDTS) filled the 
            buffer, and the recorder stopped since not circular buffer. */
            trcCRITICAL_SECTION_END();
        
            return;
        }
            
        nofEventEntries = (i+3)/4;

        /* If the data does not fit in the remaining main buffer, wrap around to 
        0 if allowed, otherwise stop the recorder and quit). */
        if (RecorderDataPtr->nextFreeIndex + nofEventEntries > RecorderDataPtr->maxEvents)
        {
#if (RECORDER_STORE_MODE == STORE_MODE_RING_BUFFER)
            (void)memset(& RecorderDataPtr->eventData[RecorderDataPtr->nextFreeIndex * 4], 
                   0, 
                   (RecorderDataPtr->maxEvents - RecorderDataPtr->nextFreeIndex)*4);
            RecorderDataPtr->nextFreeIndex = 0;
            RecorderDataPtr->bufferIsFull = 1;
#else
            /* Abort and stop recorder, since the event data will not fit in the
            buffer and not circular buffer in this case... */
            trcCRITICAL_SECTION_END();
            vTraceStop();

            
            return;
#endif
        }
    
#if (RECORDER_STORE_MODE == STORE_MODE_RING_BUFFER)
        /* Check that the buffer to be overwritten does not contain any user 
        events that would be partially overwritten. If so, they must be "killed"
        by replacing the user event and following data with NULL events (i.e., 
        using a memset to zero).*/
        prvCheckDataToBeOverwrittenForMultiEntryUserEvents(nofEventEntries);
#endif
        /* Copy the local buffer to the main buffer */
        (void)memcpy(& RecorderDataPtr->eventData[RecorderDataPtr->nextFreeIndex * 4], 
               tempDataBuffer, 
               i);

        /* Update the event type, i.e., number of data entries following the 
        main USER_EVENT entry (Note: important that this is after the memcpy, 
        but within the critical section!)*/
        RecorderDataPtr->eventData[RecorderDataPtr->nextFreeIndex * 4] = 
          (uint8_t) USER_EVENT + nofEventEntries - 1;    
        
        /* Update the main buffer event index (already checked that it fits in 
        the buffer, so no need to check for wrapping)*/
        
        RecorderDataPtr->nextFreeIndex += nofEventEntries;
        RecorderDataPtr->numEvents += nofEventEntries;
        
        if (RecorderDataPtr->nextFreeIndex >= EVENT_BUFFER_SIZE)
        {
        
#if (RECORDER_STORE_MODE == STORE_MODE_RING_BUFFER)
            RecorderDataPtr->nextFreeIndex = 0;
            RecorderDataPtr->bufferIsFull = 1;
#else
            vTraceStop();
#endif
        }

        trcCRITICAL_SECTION_END();
    }    
}
    
/*******************************************************************************
 * xTraceOpenLabel
 * 
 * Creates user event labels for user event channels or for individual events.
 * User events can be used to log application events and data for display in
 * the visualization tool. A user event is identified by a label, i.e., a string,
 * which is stored in the recorder's symbol table.
 * When logging a user event, a numeric handle (reference) to this string is
 * used to identify the event. This is obtained by calling 
 * 
 *     xTraceOpenLabel()
 *
 * which adds the string to the symbol table (if not already present)
 * and returns the corresponding handle.
 *
 * This can be used in two ways:
 *
 * 1. The handle is looked up every time, when storing the user event.
 *
 * Example:
 *     vTraceUserEvent(xTraceOpenLabel("MyUserEvent"));
 *
 * 2. The label is registered just once, with the handle stored in an
 *  application variable - much like using a file handle.
 *
 * Example:
 *     myEventHandle = xTraceOpenLabel("MyUserEvent");
 *     ...
 *     vTraceUserEvent(myEventHandle);
 *
 * The second option is faster since no lookup is required on each event, and 
 * therefore recommended for user events that are frequently
 * executed and/or located in time-critical code. The lookup operation is
 * however fairly fast due to the design of the symbol table.
 ******************************************************************************/
traceLabel xTraceOpenLabel(const char* label)
{
    return prvTraceOpenSymbol(label, 0);
}
#endif
#endif

