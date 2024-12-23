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

/******************************************************************************
 * NOTE: Windows will not be running the FreeRTOS demo threads continuously, so
 * do not expect to get real time behaviour from the FreeRTOS Windows port, or
 * this demo application.  Also, the timing information in the FreeRTOS+Trace
 * logs have no meaningful units.  See the documentation page for the Windows
 * port for further information:
 * https://www.FreeRTOS.org/FreeRTOS-Windows-Simulator-Emulator-for-Visual-Studio-and-Eclipse-MingW.html
 *
 * NOTE 2:  This project provides two demo applications.  A simple blinky style
 * project, and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting in main.c is used to select
 * between the two.  See the notes on using mainCREATE_SIMPLE_BLINKY_DEMO_ONLY
 * in main.c.  This file implements the simply blinky version.  Console output
 * is used in place of the normal LED toggling.
 *
 * NOTE 3:  This file only contains the source code that is specific to the
 * basic demo.  Generic functions, such FreeRTOS hook functions, are defined
 * in main.c.
 ******************************************************************************
 *
 * main_blinky() creates one queue, one software timer, and two tasks.  It then
 * starts the scheduler.
 *
 * The Queue Send Task:
 * The queue send task is implemented by the prvQueueSendTask() function in
 * this file.  It uses vTaskDelayUntil() to create a periodic task that sends
 * the value 100 to the queue every 200 milliseconds (please read the notes
 * above regarding the accuracy of timing under Windows).
 *
 * The Queue Send Software Timer:
 * The timer is a one-shot timer that is reset by a key press.  The timer's
 * period is set to two seconds - if the timer expires then its callback
 * function writes the value 200 to the queue.  The callback function is
 * implemented by prvQueueSendTimerCallback() within this file.
 *
 * The Queue Receive Task:
 * The queue receive task is implemented by the prvQueueReceiveTask() function
 * in this file.  prvQueueReceiveTask() waits for data to arrive on the queue.
 * When data is received, the task checks the value of the data, then outputs a
 * message to indicate if the data came from the queue send task or the queue
 * send software timer.
 *
 * Expected Behaviour:
 * - The queue send task writes to the queue every 200ms, so every 200ms the
 *   queue receive task will output a message indicating that data was received
 *   on the queue from the queue send task.
 * - The queue send software timer has a period of two seconds, and is reset
 *   each time a key is pressed.  So if two seconds expire without a key being
 *   pressed then the queue receive task will output a message indicating that
 *   data was received on the queue from the queue send software timer.
 *
 * NOTE:  Console input and output relies on Windows system calls, which can
 * interfere with the execution of the FreeRTOS Windows port.  This demo only
 * uses Windows system call occasionally.  Heavier use of Windows system calls
 * can crash the port.
 */

/* Standard includes. */
#include <stdio.h>
#include <conio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"
#include "event_groups.h"

/* Priorities at which the tasks are created. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY    ( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_SEND_TASK_PRIORITY       ( tskIDLE_PRIORITY + 1 )

/* The rate at which data is sent to the queue.  The times are converted from
 * milliseconds to ticks using the pdMS_TO_TICKS() macro. */
#define mainTASK_SEND_FREQUENCY_MS         pdMS_TO_TICKS( 200UL )
#define mainTIMER_SEND_FREQUENCY_MS        pdMS_TO_TICKS( 2000UL )

/* The number of items the queue can hold at once. */
#define mainQUEUE_LENGTH                   ( 2 )

/* The values sent to the queue receive task from the queue send task and the
 * queue send software timer respectively. */
#define mainVALUE_SENT_FROM_TASK           ( 100UL )
#define mainVALUE_SENT_FROM_TIMER          ( 200UL )

/* This demo allows for users to perform actions with the keyboard. */
#define mainNO_KEY_PRESS_VALUE             ( -1 )
#define mainRESET_TIMER_KEY                ( 'r' )
#define mainINTERRUPT_NUMBER 4
/*-----------------------------------------------------------*/

/*
 * The tasks as described in the comments at the top of this file.
 */
static void prvQueueReceiveTask( void * pvParameters );
static void prvQueueSendTask( void * pvParameters );
static void prvHanlderTask(void* pvParameters);
static void prvGenInterruptTask(void* pvParameters);
static uint32_t ulExampleInterruptHandler(void);
static void DeferredHandler(void* pvParameter1, uint32_t ulParameter2);
static void prvPrintTask(void* pvParameters);
static void prvResurMutexTask(void *pvParameters);
static void prvReadEventGroupTask(void *pvParameters);
static void prvGroupSyncTask(void *pvParameters);
/*
 * The callback function executed when the software timer expires.
 */
static void prvQueueSendTimerCallback( TimerHandle_t xTimerHandle );

/*-----------------------------------------------------------*/

/* The queue used by both tasks. */
static QueueHandle_t xQueue = NULL;
static QueueHandle_t xIntQueue = NULL;
static QueueHandle_t xStrQueue = NULL;

/* A software timer that is started from the tick hook. */
static TimerHandle_t xTimer = NULL;

static SemaphoreHandle_t xBinary, xCounting, xMutex, xRecursiveMutex;
static EventGroupHandle_t xGroup;
static TaskHandle_t xTaskHandler;

static enum {
    MinDemoType,
    BinarySemaphore = 1,
    CountingSemaphore,
    CentralizedDefer,
    ISRSendData,
    Mutex,
    RecursiveMutex,
    EventGroup,
    GroupSync,
    TaskNotify,
    TaskNotifyNoClear,
    MaxDemoType
} DemoType;

static char *pStrDemoName[] = {
    "MinDemoType",
    "BinarySemaphore",
    "CountingSemaphore",
    "CentralizedDefer",
    "ISRSendData",
    "Mutex",
    "RecursiveMutex",
    "EventGroup",
    "GroupSync",
    "TaskNotify(ClearOnExit==TRUE)",
    "TaskNotify(ClearOnExit==FALSE)"
    "MaxDemoType"
};
/*-----------------------------------------------------------*/

/*** SEE THE COMMENTS AT THE TOP OF THIS FILE ***/
void main_blinky( void )
{
    const TickType_t xTimerPeriod = mainTIMER_SEND_FREQUENCY_MS;

    printf( "\r\nStarting the blinky demo. Press \'%c\' to reset the software timer used in this demo.\r\n\r\n", mainRESET_TIMER_KEY );

    /* Create the queue. */
    xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( uint32_t ) );
    // Create an integer queue of 5 items
    xIntQueue = xQueueCreate(5, sizeof(uint32_t));
    xStrQueue = xQueueCreate(5, sizeof(char *));
    // Create binary semaphore
    xBinary = xSemaphoreCreateBinary();
    // Create counting semaphore
    xCounting = xSemaphoreCreateCounting(5, 0);
    // Create Mutex
    xMutex = xSemaphoreCreateMutex();
    // Create Recursive Mutex
    xRecursiveMutex = xSemaphoreCreateRecursiveMutex();
    // Create eventgroup
    xGroup = xEventGroupCreate();
    DemoType = ISRSendData;

    if( xQueue != NULL )
    {
        /* Start the two tasks as described in the comments at the top of this
         * file. */
        //xTaskCreate( prvQueueReceiveTask,             /* The function that implements the task. */
        //             "Rx",                            /* The text name assigned to the task - for debug only as it is not used by the kernel. */
        //             configMINIMAL_STACK_SIZE,        /* The size of the stack to allocate to the task. */
        //             NULL,                            /* The parameter passed to the task - not used in this simple case. */
        //             mainQUEUE_RECEIVE_TASK_PRIORITY, /* The priority assigned to the task. */
        //             NULL );                          /* The task handle is not required, so NULL is passed. */

        //xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_SEND_TASK_PRIORITY, NULL );
        printf("Choose Demo Type: \n");
        for (int i = BinarySemaphore; i < MaxDemoType; i++)
        {
            printf("  [%d]  %s\n", i, pStrDemoName[i]);
        }
        scanf("%d", &DemoType); 
        printf("DemoType = %d\n", DemoType);
        // prvGenInterruptTask generates an interrupt every 500ms to trigger ulExampleInterruptHandler.
        // ulExampleInterruptHandler gives xBinary which allows prvHanlderTask to switch from delay list to ready list.
        // prvHanlderTask takes care of deferred interrupt handling.
        if (DemoType == Mutex) {
            printf("Default xMutex = %lld, xBinary = %lld\n", uxSemaphoreGetCount(xMutex), uxSemaphoreGetCount(xBinary));
            xTaskCreate(prvPrintTask, "prvPrintTask", configMINIMAL_STACK_SIZE, "Task1", 1, NULL);
            xTaskCreate(prvPrintTask, "prvPrintTask", configMINIMAL_STACK_SIZE, "Task2", 1, NULL);
        } else if (DemoType == RecursiveMutex) {
            xTaskCreate(prvResurMutexTask, "prvResurMutexTask", configMINIMAL_STACK_SIZE, "prvResurMutexTask", 2, NULL);
        } else if (DemoType == GroupSync) {
            xTaskCreate(prvGroupSyncTask, "Task 1", configMINIMAL_STACK_SIZE, 1, 1, NULL);
            xTaskCreate(prvGroupSyncTask, "Task 2", configMINIMAL_STACK_SIZE, 2, 1, NULL);
            xTaskCreate(prvGroupSyncTask, "Task 3", configMINIMAL_STACK_SIZE, 4, 1, NULL);
        } else {
            xTaskCreate(prvHanlderTask, "prvHanlderTask", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandler);
            xTaskCreate(prvGenInterruptTask, "prvGenInterruptTask", configMINIMAL_STACK_SIZE, NULL, 1, NULL);
            xTaskCreate(prvReadEventGroupTask, "prvReadEventGroupTask", configMINIMAL_STACK_SIZE, NULL, 1, NULL);
            vPortSetInterruptHandler(mainINTERRUPT_NUMBER, (void*)ulExampleInterruptHandler);
        }
        /* Create the software timer, but don't start it yet. */
        xTimer = xTimerCreate( "Timer",                     /* The text name assigned to the software timer - for debug only as it is not used by the kernel. */
                               xTimerPeriod,                /* The period of the software timer in ticks. */
                               pdTRUE,                      /* xAutoReload is set to pdTRUE, so this timer goes off periodically with a period of xTimerPeriod ticks. */
                               NULL,                        /* The timer's ID is not used. */
                               prvQueueSendTimerCallback ); /* The function executed when the timer expires. */

        //xTimerStart( xTimer, 0 );                           /* The scheduler has not started so use a block time of 0. */

        /* Start the tasks and timer running. */
        vTaskStartScheduler();
    }

    /* If all is well, the scheduler will now be running, and the following
     * line will never be reached.  If the following line does execute, then
     * there was insufficient FreeRTOS heap memory available for the idle and/or
     * timer tasks	to be created.  See the memory management section on the
     * FreeRTOS web site for more details. */
    for( ; ; )
    {
    }
}
/*-----------------------------------------------------------*/
// There are 3 tasks. Each task set one bit in event group
static void prvGroupSyncTask(void *pvParameters) {
    EventBits_t BitsToSet;

    BitsToSet = (EventBits_t)pvParameters;
    for (;;) {
        vTaskDelay(pdMS_TO_TICKS(rand() % 500UL));
        printf("%s start group sync, BitsToSet %llx\n", pcTaskGetTaskName(NULL), BitsToSet);
        // Get the current xGroup->uxEventBits and save to uxOriginalBitValue. 
        // Set BitsToSet to xGroup->uxEventBits.
        // If uxOriginalBitValue | BitsToSet == TargetBits (0x7), clear TargetBits in xGroup->uxEventBits and return.
        // Else move task to delayed list and yield.
        // If task runs again, it means either the required bits were set or the block time expired.
        // If timeout, clear TargetBits in xGroup->uxEventBits and return.
        xEventGroupSync(xGroup, BitsToSet, 0x7, portMAX_DELAY);
        printf("%s end group sync\n", pcTaskGetTaskName(NULL));
    }
}
static void prvResurMutexTask(void *pvParameters)
{
    for (;;)
    {
        printf("xRecursiveMutex = %lld\n", uxSemaphoreGetCount(xRecursiveMutex));
        if (xSemaphoreTakeRecursive(xRecursiveMutex, portMAX_DELAY) == pdTRUE)
        {
            printf("Take xRecursiveMutex Successfully\n");
            // If we use xSemaphoreTake here, xSemaphoreTake will enters blocked state to wait for xRecursiveMutex.
            // This is a deadlock.
            xSemaphoreTakeRecursive(xRecursiveMutex, portMAX_DELAY);
            printf("   2nd take xRecursiveMutex = %lld\n", uxSemaphoreGetCount(xRecursiveMutex));
            xSemaphoreGiveRecursive(xRecursiveMutex);
            printf("   Release xRecursiveMutex = %lld\n", uxSemaphoreGetCount(xRecursiveMutex));
            xSemaphoreGiveRecursive(xRecursiveMutex);
            printf("   2nd Release xRecursiveMutex = %lld\n", uxSemaphoreGetCount(xRecursiveMutex));
        }
        vTaskDelay(pdMS_TO_TICKS(50UL));
    }
}

static void prvPrintTask(void *pvParameters)
{
    char *pStr;
    TickType_t xTimeAtWhichMutexWasTaken;
    pStr = (char *)pvParameters;
    for (;;)
    {
        printf("[%s], xSemaphoreTake is started = %lld\n", pStr, uxSemaphoreGetCount(xMutex));
        xSemaphoreTake(xMutex, portMAX_DELAY);
        {
            xTimeAtWhichMutexWasTaken = xTaskGetTickCount();
            printf("[%s], xSemaphoreTake is completed = %lld and go to blocked status\n", pStr, uxSemaphoreGetCount(xMutex));
            vTaskDelay(pdMS_TO_TICKS(100UL));
        }
        printf("[%s], xSemaphoreGive is started and Release xMutex = %lld\n", pStr, uxSemaphoreGetCount(xMutex));
        xSemaphoreGive(xMutex);
        printf("[%s], xSemaphoreGive is completed\n", pStr);
        if (xTaskGetTickCount() != xTimeAtWhichMutexWasTaken)
        {
            printf("[%s], taskYIELD is started\n", pStr);
            taskYIELD();
            printf("[%s], taskYIELD is completed\n", pStr);
        }
    }
}

static uint32_t ulExampleInterruptHandler(void)
{
    static uint32_t value = 1;
    int temp;
    static char *pStr[] = { "String 0", "String 1", "String 2", "String 3", "String 4" };
    static const char *pcString = "Bit Setting ISR - About to set bit 2.";
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    /* The xHigherPriorityTaskWoken parameter must be initialized to
    pdFALSE as it will get set to pdTRUE inside the interrupt safe
    API function if a context switch is required. */
    xHigherPriorityTaskWoken = pdFALSE;
    /* 'Give' the semaphore to unblock the task, passing in the address of
    xHigherPriorityTaskWoken as the interrupt safe API function's
    pxHigherPriorityTaskWoken parameter. */
    switch (DemoType)
    {
        case BinarySemaphore:
            printf("[ulExampleInterruptHandler]  Give (Send) semaphore +++\n");
            xSemaphoreGiveFromISR(xBinary, &xHigherPriorityTaskWoken);
            printf("[ulExampleInterruptHandler]  Give (Send) semaphore xHigherPriorityTaskWoken %lld ---\n", xHigherPriorityTaskWoken);
            break;
        case CountingSemaphore:
            // Generate 3 events
            printf("[ulExampleInterruptHandler]  Give (Send) semaphore +++\n");
            xSemaphoreGiveFromISR(xCounting, &xHigherPriorityTaskWoken);
            xSemaphoreGiveFromISR(xCounting, &xHigherPriorityTaskWoken);
            xSemaphoreGiveFromISR(xCounting, &xHigherPriorityTaskWoken);
            printf("[ulExampleInterruptHandler]  Give (Send) semaphore xHigherPriorityTaskWoken %lld ---\n", xHigherPriorityTaskWoken);
            break;
        case CentralizedDefer:
            // Send DeferredHandler to timer daemon task to run
            xTimerPendFunctionCallFromISR(DeferredHandler, NULL, value, &xHigherPriorityTaskWoken);
            value++;
            printf("[ulExampleInterruptHandler]  Send tmrCOMMAND_EXECUTE_CALLBACK to timer daemon\n");
            break;
        case ISRSendData:
            // Receive all items from xIntQueue
            while (xQueueReceiveFromISR(xIntQueue, &temp, &xHigherPriorityTaskWoken) != pdFAIL)
            {
                xQueueSendFromISR(xStrQueue, &pStr[temp], &xHigherPriorityTaskWoken);
                printf("[ulExampleInterruptHandler] Send String \"%s\"\n", pStr[temp]);
            }
            break;
        case EventGroup:
            // Send DeferredHandler to timer daemon task to take care of event group
            printf("Send DeferredHandler to Timer Daemon\n");
            xTimerPendFunctionCallFromISR(DeferredHandler, (void *)pcString, 0, &xHigherPriorityTaskWoken);
            // Set bit 2 to event group
            printf("Send vEventGroupSetBitsCallback to Timer Daemon\n");
            xEventGroupSetBitsFromISR(xGroup, 1UL << 2UL, &xHigherPriorityTaskWoken);
            break;
        case TaskNotifyNoClear:
            vTaskNotifyGiveFromISR(xTaskHandler, &xHigherPriorityTaskWoken);
            vTaskNotifyGiveFromISR(xTaskHandler, &xHigherPriorityTaskWoken);
        case TaskNotify:
            vTaskNotifyGiveFromISR(xTaskHandler, &xHigherPriorityTaskWoken);
            printf("vTaskNotifyGiveFromISR\n");
            break;
        default:
            break;
    }
    // For real HW platform, vTaskSwitchContext is performed. 
    // For x86 simulator, kernel thread will suspend current task and run another task in ready list.
    portYIELD_FROM_ISR(xHigherPriorityTaskWoken);
}

static void prvReadEventGroupTask(void *pvParameters)
{
    EventBits_t xEventGroupValue;

    for (;;)
    {

        xEventGroupValue = xEventGroupWaitBits(xGroup, 0x7, pdTRUE, pdFALSE, portMAX_DELAY);
        if (xEventGroupValue & 0x1)
            printf("Bit Reading Task - Event bit 0 is set\n");
        if (xEventGroupValue & 0x2)
            printf("Bit Reading Task - Event bit 1 is set\n");
        if (xEventGroupValue & 0x4)
            printf("Bit Reading Task - Event bit 2 is set\n");
    }
}

static void DeferredHandler(void *pvParameter1, uint32_t ulParameter2)
{
    switch (DemoType) {
        case EventGroup:
            printf("%s\n", (char *)pvParameter1);
            break;
        default:
            printf("  Timer daemon runs DeferredHandler ulParameter2 %u\n", ulParameter2);
            break;
    }
}

// Handle deferred interrupt
static void prvHanlderTask(void* pvParameters)
{
    char *pStr;
    uint32_t ulEventsToProcess;

    for (;;)
    {
        switch (DemoType)
        {
            case BinarySemaphore:
                printf("[prvHanlderTask] xBinary = %lld\n", uxSemaphoreGetCount(xBinary));
                xSemaphoreTake(xBinary, portMAX_DELAY);
                printf("[prvHanlderTask] Deferred Interrupt Handling\n");
                break;
            case CountingSemaphore:
                printf("[prvHanlderTask] xCounting = %lld\n", uxSemaphoreGetCount(xCounting));
                xSemaphoreTake(xCounting, portMAX_DELAY);
                printf("[prvHanlderTask] Deferred Interrupt Handling\n");
                break;
            case ISRSendData:
                while (xQueueReceive(xStrQueue, &pStr, pdMS_TO_TICKS(100UL)) == pdTRUE)
                {
                    printf("[prvHanlderTask] Receive string \"%s\"\n", pStr);
                }
                break;
            case EventGroup:
                vTaskDelay(pdMS_TO_TICKS(200UL));
                printf("Bit Setting Task - set bit 0 is started\n");
                xEventGroupSetBits(xGroup, 1UL << 0UL);
                printf("Bit Setting Task - set bit 0 is completed\n");
                vTaskDelay(pdMS_TO_TICKS(200UL));
                printf("Bit Setting Task - set bit 1 is started\n");
                xEventGroupSetBits(xGroup, 1UL << 1UL);
                printf("Bit Setting Task - set bit 1 is completed\n");
                break;
            case TaskNotify:
                ulEventsToProcess = ulTaskNotifyTake(pdTRUE, pdMS_TO_TICKS(500UL + 100UL));
                printf("ulEventsToProcess = %x\n", ulEventsToProcess);
                break;
            case TaskNotifyNoClear:
                ulEventsToProcess = ulTaskNotifyTake(pdFALSE, pdMS_TO_TICKS(500UL + 100UL));
                printf("ulEventsToProcess = %x\n", ulEventsToProcess);
                break;
            default:
                break;
        }
    }
}

static void prvGenInterruptTask(void* pvParameters)
{
    int i;

    for (;;)
    {
        vTaskDelay(pdMS_TO_TICKS(500UL));
        switch (DemoType)
        {
            case ISRSendData:
                // Send 5 items to xIntQueue
                for (i = 0; i < 5; i++)
                    xQueueSend(xIntQueue, &i, 0);
                printf("[prvGenInterruptTask] Send 5 items to xIntQueue\n");
            case BinarySemaphore:
            case CountingSemaphore:
            case CentralizedDefer:
            case EventGroup:
            case TaskNotify:
            case TaskNotifyNoClear:
                printf("[prvGenInterruptTask] Generate Interrupt +++\n");
                vPortGenerateSimulatedInterrupt(mainINTERRUPT_NUMBER);
                printf("[prvGenInterruptTask] Generate Interrupt ---\n");
                break;
            default:
                break;
        }
    }
}

static void prvQueueSendTask( void * pvParameters )
{
    TickType_t xNextWakeTime;
    const TickType_t xBlockTime = mainTASK_SEND_FREQUENCY_MS;
    const uint32_t ulValueToSend = mainVALUE_SENT_FROM_TASK;

    /* Prevent the compiler warning about the unused parameter. */
    ( void ) pvParameters;

    /* Initialise xNextWakeTime - this only needs to be done once. */
    xNextWakeTime = xTaskGetTickCount();

    for( ; ; )
    {
        /* Place this task in the blocked state until it is time to run again.
         *  The block time is specified in ticks, pdMS_TO_TICKS() was used to
         *  convert a time specified in milliseconds into a time specified in ticks.
         *  While in the Blocked state this task will not consume any CPU time. */
        vTaskDelayUntil( &xNextWakeTime, xBlockTime );

        /* Send to the queue - causing the queue receive task to unblock and
         * write to the console.  0 is used as the block time so the send operation
         * will not block - it shouldn't need to block as the queue should always
         * have at least one space at this point in the code. */
        xQueueSend( xQueue, &ulValueToSend, 0U );
    }
}
/*-----------------------------------------------------------*/

static void prvQueueSendTimerCallback( TimerHandle_t xTimerHandle )
{
    const uint32_t ulValueToSend = mainVALUE_SENT_FROM_TIMER;

    /* This is the software timer callback function.  The software timer has a
     * period of two seconds and is reset each time a key is pressed.  This
     * callback function will execute if the timer expires, which will only happen
     * if a key is not pressed for two seconds. */

    /* Avoid compiler warnings resulting from the unused parameter. */
    ( void ) xTimerHandle;

    /* Send to the queue - causing the queue receive task to unblock and
     * write out a message.  This function is called from the timer/daemon task, so
     * must not block.  Hence the block time is set to 0. */
    xQueueSend( xQueue, &ulValueToSend, 0U );
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void * pvParameters )
{
    uint32_t ulReceivedValue;

    /* Prevent the compiler warning about the unused parameter. */
    ( void ) pvParameters;

    for( ; ; )
    {
        /* Wait until something arrives in the queue - this task will block
         * indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
         * FreeRTOSConfig.h.  It will not use any CPU time while it is in the
         * Blocked state. */
        xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

        /* Enter critical section to use printf. Not doing this could potentially cause
         * a deadlock if the FreeRTOS simulator switches contexts and another task
         * tries to call printf - it should be noted that use of printf within
         * the FreeRTOS simulator is unsafe, but used here for simplicity. */
        taskENTER_CRITICAL();
        {
            /*  To get here something must have been received from the queue, but
             * is it an expected value?  Normally calling printf() from a task is not
             * a good idea.  Here there is lots of stack space and only one task is
             * using console IO so it is ok.  However, note the comments at the top of
             * this file about the risks of making Windows system calls (such as
             * console output) from a FreeRTOS task. */
            if( ulReceivedValue == mainVALUE_SENT_FROM_TASK )
            {
                printf( "Message received from task - idle time %llu%%\r\n", ulTaskGetIdleRunTimePercent() );
            }
            else if( ulReceivedValue == mainVALUE_SENT_FROM_TIMER )
            {
                printf( "Message received from software timer\r\n" );
            }
            else
            {
                printf( "Unexpected message\r\n" );
            }
        }
        taskEXIT_CRITICAL();
    }
}
/*-----------------------------------------------------------*/

/* Called from prvKeyboardInterruptSimulatorTask(), which is defined in main.c. */
void vBlinkyKeyboardInterruptHandler( int xKeyPressed )
{
    /* Handle keyboard input. */
    switch( xKeyPressed )
    {
        case mainRESET_TIMER_KEY:

            if( xTimer != NULL )
            {
                /* Critical section around printf to prevent a deadlock
                 * on context switch. */
                taskENTER_CRITICAL();
                {
                    printf( "\r\nResetting software timer.\r\n\r\n" );
                }
                taskEXIT_CRITICAL();

                /* Reset the software timer. */
                xTimerReset( xTimer, portMAX_DELAY );
            }

            break;

        default:
            break;
    }
}
