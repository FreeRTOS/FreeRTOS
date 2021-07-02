/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */
#include "queue.h"    /* RTOS queue related API prototypes. */
#include "timers.h"   /* Software timer related API prototypes. */
#include "semphr.h"   /* Semaphore related API prototypes. */
#include <stdio.h>
#include "pico/stdlib.h"
#include "pico/multicore.h"

#ifndef mainRUN_FREE_RTOS_ON_CORE
#define mainRUN_FREE_RTOS_ON_CORE 0
#endif

/* Priorities at which the tasks are created.  The event semaphore task is
given the maximum priority of ( configMAX_PRIORITIES - 1 ) to ensure it runs as
soon as the semaphore is given. */
#define mainSDK_MUTEX_USE_TASK_PRIORITY     ( tskIDLE_PRIORITY + 3 )
#define mainSDK_SEMAPHORE_USE_TASK_PRIORITY ( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_RECEIVE_TASK_PRIORITY     ( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_SEND_TASK_PRIORITY        ( tskIDLE_PRIORITY + 1 )
#define mainEVENT_SEMAPHORE_TASK_PRIORITY   ( configMAX_PRIORITIES - 1 )

/* The rate at which data is sent to the queue, specified in milliseconds, and
converted to ticks using the pdMS_TO_TICKS() macro. */
#define mainQUEUE_SEND_PERIOD_MS            pdMS_TO_TICKS( 200 )

/* The period of the example software timer, specified in milliseconds, and
converted to ticks using the pdMS_TO_TICKS() macro. */
#define mainSOFTWARE_TIMER_PERIOD_MS        pdMS_TO_TICKS( 1000 )

/* The number of items the queue can hold.  This is 1 as the receive task
has a higher priority than the send task, so will remove items as they are added,
meaning the send task should always find the queue empty. */
#define mainQUEUE_LENGTH                    ( 1 )

/*-----------------------------------------------------------*/

/*
 * Implement this function for any hardware specific clock configuration
 * that was not already performed before main() was called.
 */
static void prvSetupHardware( void );

/*
 * The queue send and receive tasks as described in the comments at the top of
 * this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*
 * The callback function assigned to the example software timer as described at
 * the top of this file.
 */
static void vExampleTimerCallback( TimerHandle_t xTimer );

/*
 * The event semaphore task as described at the top of this file.
 */
static void prvEventSemaphoreTask( void *pvParameters );

/**
 * A task that uses an SDK mutex
 */
static void prvSDKMutexUseTask( void *pvParameters );

/**
 * A task that uses an SDK semaphore
 */
static void prvSDKSemaphoreUseTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used by the queue send and queue receive tasks. */
static QueueHandle_t xQueue = NULL;

/* The semaphore (in this case binary) that is used by the FreeRTOS tick hook
 * function and the event semaphore task.
 */
static SemaphoreHandle_t xEventSemaphore = NULL;

/* The counters used by the various examples.  The usage is described in the
 * comments at the top of this file.
 */
static volatile uint32_t ulCountOfTimerCallbackExecutions = 0;
static volatile uint32_t ulCountOfItemsSentOnQueue = 0;
static volatile uint32_t ulCountOfItemsReceivedOnQueue = 0;
static volatile uint32_t ulCountOfReceivedSemaphores = 0;
static volatile uint32_t ulCountOfSDKMutexEnters = 0;
static volatile uint32_t ulCountOfSDKSemaphoreAcquires = 0;

/*-----------------------------------------------------------*/

#include "pico/mutex.h"
#include "pico/sem.h"

#if configNUM_CORES > 1
#error Require only one core configured for FreeRTOS
#endif

auto_init_mutex(xSDKMutex);
static semaphore_t xSDKSemaphore;

static void prvNonRTOSWorker() {
    printf("Core %d: Doing regular SDK stuff\n", get_core_num());
    uint32_t counter;
    while (true) {
        mutex_enter_blocking(&xSDKMutex);
        printf("Core %d: Acquire SDK mutex\n", get_core_num());
        absolute_time_t end_time = make_timeout_time_ms(750);
        while (!time_reached(end_time)) {
            counter++;
            printf("Core %d: Busy work with mutex %d\n", get_core_num(), counter);
            busy_wait_us(137384);
        }
        printf("Core %d: Release SDK mutex\n", get_core_num());
        mutex_exit(&xSDKMutex);
        printf("Core %d: Starting SDK sleep\n", get_core_num());
        sleep_ms(1200);
        printf("Core %d: Finish SDK sleep; release SDK semaphore\n", get_core_num());
        sem_release(&xSDKSemaphore);
    }
}

static void prvLaunchRTOS() {
    printf("Core %d: Launching FreeRTOS scheduler\n", get_core_num());
    /* Start the tasks and timer running. */
    vTaskStartScheduler();
    /* should never reach here */
    panic_unsupported();
}

static void prvCore1Entry() {
#if ( mainRUN_FREE_RTOS_ON_CORE == 1 )
    prvLaunchRTOS();
#else
    prvNonRTOSWorker();
#endif
}

int main(void) {
    TimerHandle_t xExampleSoftwareTimer = NULL;

    /* Configure the system ready to run the demo.  The clock configuration
    can be done here if it was not done before main() was called. */
    prvSetupHardware();

    /* Create the queue used by the queue send and queue receive tasks. */
    xQueue = xQueueCreate(     /* The number of items the queue can hold. */
            mainQUEUE_LENGTH,
    /* The size of each item the queue holds. */
            sizeof(uint32_t));


    /* Create the semaphore used by the FreeRTOS tick hook function and the
    event semaphore task.  NOTE: A semaphore is used for example purposes,
    using a direct to task notification will be faster! */
    xEventSemaphore = xSemaphoreCreateBinary();


    /* Create the queue receive task as described in the comments at the top
    of this file. */
    xTaskCreate(     /* The function that implements the task. */
            prvQueueReceiveTask,
            /* Text name for the task, just to help debugging. */
            "Rx",
            /* The size (in words) of the stack that should be created
            for the task. */
            configMINIMAL_STACK_SIZE,
            /* A parameter that can be passed into the task.  Not used
            in this simple demo. */
            NULL,
            /* The priority to assign to the task.  tskIDLE_PRIORITY
            (which is 0) is the lowest priority.  configMAX_PRIORITIES - 1
            is the highest priority. */
            mainQUEUE_RECEIVE_TASK_PRIORITY,
            /* Used to obtain a handle to the created task.  Not used in
            this simple demo, so set to NULL. */
            NULL);


    /* Create the queue send task in exactly the same way.  Again, this is
    described in the comments at the top of the file. */
    xTaskCreate(prvQueueSendTask,
                "TX",
                configMINIMAL_STACK_SIZE,
                NULL,
                mainQUEUE_SEND_TASK_PRIORITY,
                NULL);


    /* Create the task that is synchronised with an interrupt using the
    xEventSemaphore semaphore. */
    xTaskCreate(prvEventSemaphoreTask,
                "Sem",
                configMINIMAL_STACK_SIZE,
                NULL,
                mainEVENT_SEMAPHORE_TASK_PRIORITY,
                NULL);


    /* Create the task that uses SDK mutexes */
    xTaskCreate(prvSDKMutexUseTask,
                "SDK Mutex Use",
                configMINIMAL_STACK_SIZE,
                NULL,
                mainSDK_MUTEX_USE_TASK_PRIORITY,
                NULL);

    sem_init(&xSDKSemaphore, 0, 1);

    /* Create the task that uses SDK mutexes */
    xTaskCreate(prvSDKSemaphoreUseTask,
                "SDK Seamphore Use",
                configMINIMAL_STACK_SIZE,
                NULL,
                mainSDK_SEMAPHORE_USE_TASK_PRIORITY,
                NULL);

    /* Create the software timer as described in the comments at the top of
    this file. */
    xExampleSoftwareTimer = xTimerCreate(     /* A text name, purely to help
                                            debugging. */
            (const char *) "LEDTimer",
            /* The timer period, in this case
            1000ms (1s). */
            mainSOFTWARE_TIMER_PERIOD_MS,
            /* This is a periodic timer, so
            xAutoReload is set to pdTRUE. */
            pdTRUE,
            /* The ID is not used, so can be set
            to anything. */
            (void *) 0,
            /* The callback function that switches
            the LED off. */
            vExampleTimerCallback
    );

    /* Start the created timer.  A block time of zero is used as the timer
    command queue cannot possibly be full here (this is the first timer to
    be created, and it is not yet running). */
    xTimerStart(xExampleSoftwareTimer, 0);

    multicore_launch_core1(prvCore1Entry);
#if ( mainRUN_FREE_RTOS_ON_CORE == 0 )
    prvLaunchRTOS();
#else
    prvNonRTOSWorker();
#endif
}
/*-----------------------------------------------------------*/

static void vExampleTimerCallback( TimerHandle_t xTimer )
{
    /* The timer has expired.  Count the number of times this happens.  The
    timer that calls this function is an auto re-load timer, so it will
    execute periodically. */
    ulCountOfTimerCallbackExecutions++;
}
/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
    TickType_t xNextWakeTime;
    const uint32_t ulValueToSend = 100UL;

    /* Initialise xNextWakeTime - this only needs to be done once. */
    xNextWakeTime = xTaskGetTickCount();

    for( ;; )
    {
        /* Place this task in the blocked state until it is time to run again.
        The block time is specified in ticks, the constant used converts ticks
        to ms.  The task will not consume any CPU time while it is in the
        Blocked state. */
        vTaskDelayUntil( &xNextWakeTime, mainQUEUE_SEND_PERIOD_MS );

        /* Send to the queue - causing the queue receive task to unblock and
        increment its counter.  0 is used as the block time so the sending
        operation will not block - it shouldn't need to block as the queue
        should always be empty at this point in the code. */
        ulCountOfItemsSentOnQueue++;
        printf("Core %d - Thread '%s': Queue send %d\n", get_core_num(), pcTaskGetName(xTaskGetCurrentTaskHandle()), ulCountOfItemsSentOnQueue);
        xQueueSend( xQueue, &ulValueToSend, 0 );
    }
}
/*-----------------------------------------------------------*/


static void prvQueueReceiveTask( void *pvParameters )
{
    uint32_t ulReceivedValue;

    for( ;; )
    {
        /* Wait until something arrives in the queue - this task will block
        indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
        FreeRTOSConfig.h. */
        xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );
        /*  To get here something must have been received from the queue, but
        is it the expected value?  If it is, increment the counter. */
        if( ulReceivedValue == 100UL )
        {
            /* Count the number of items that have been received correctly. */
            ulCountOfItemsReceivedOnQueue++;
            printf("Core %d - Thread '%s': Queue receive %d\n", get_core_num(), pcTaskGetName(xTaskGetCurrentTaskHandle()), ulCountOfItemsReceivedOnQueue);
        }
    }
}
/*-----------------------------------------------------------*/

static void prvEventSemaphoreTask( void *pvParameters )
{
    for( ;; )
    {
        /* Block until the semaphore is 'given'.  NOTE:
        A semaphore is used for example purposes.  In a real application it might
        be preferable to use a direct to task notification, which will be faster
        and use less RAM. */
        xSemaphoreTake( xEventSemaphore, portMAX_DELAY );

        /* Count the number of times the semaphore is received. */
        ulCountOfReceivedSemaphores++;
        printf("Core %d - Thread '%s': Semaphore taken %d\n", get_core_num(), pcTaskGetName(xTaskGetCurrentTaskHandle()), ulCountOfReceivedSemaphores);
    }
}
/*-----------------------------------------------------------*/

static void prvSDKMutexUseTask( void *pvParameters )
{
    for( ;; )
    {
        mutex_enter_blocking(&xSDKMutex);
        ulCountOfSDKMutexEnters++;
        printf("Core %d - Thread '%s': SDK Mutex Entered, sleeping for a while %d\n", get_core_num(), pcTaskGetName(xTaskGetCurrentTaskHandle()), ulCountOfSDKMutexEnters);
        vTaskDelay(3000);
        printf("Core %d - Thread '%s': Sleep finished; SDK Mutex releasing %d\n", get_core_num(), pcTaskGetName(xTaskGetCurrentTaskHandle()), ulCountOfSDKMutexEnters);
        mutex_exit(&xSDKMutex);
    }
}
/*-----------------------------------------------------------*/

static void prvSDKSemaphoreUseTask( void *pvParameters )
{
    for( ;; )
    {
        absolute_time_t t = get_absolute_time();
        if (sem_acquire_timeout_us(&xSDKSemaphore, 250500)) {
            ulCountOfSDKSemaphoreAcquires++;
            printf("Core %d - Thread '%s': SDK Sem acquired %d\n", get_core_num(), pcTaskGetName(xTaskGetCurrentTaskHandle()), ulCountOfSDKMutexEnters);
        } else {
            printf("Core %d - Thread '%s': SDK Sem wait timeout (ok) after %d us\n", get_core_num(), pcTaskGetName(xTaskGetCurrentTaskHandle()),
                   (int)absolute_time_diff_us(t, get_absolute_time()));
        }
    }
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    static uint32_t ulCount = 0;

    /* The RTOS tick hook function is enabled by setting configUSE_TICK_HOOK to
    1 in FreeRTOSConfig.h.

    "Give" the semaphore on every 500th tick interrupt. */
    ulCount++;
    if( ulCount >= 50UL )
    {
        /* This function is called from an interrupt context (the RTOS tick
        interrupt),    so only ISR safe API functions can be used (those that end
        in "FromISR()".

        xHigherPriorityTaskWoken was initialised to pdFALSE, and will be set to
        pdTRUE by xSemaphoreGiveFromISR() if giving the semaphore unblocked a
        task that has equal or higher priority than the interrupted task.
        NOTE: A semaphore is used for example purposes.  In a real application it
        might be preferable to use a direct to task notification,
        which will be faster and use less RAM. */
        gpio_xor_mask(1u << PICO_DEFAULT_LED_PIN);
        xSemaphoreGiveFromISR( xEventSemaphore, &xHigherPriorityTaskWoken );
        ulCount = 0UL;
    }

    /* If xHigherPriorityTaskWoken is pdTRUE then a context switch should
    normally be performed before leaving the interrupt (because during the
    execution of the interrupt a task of equal or higher priority than the
    running task was unblocked).  The syntax required to context switch from
    an interrupt is port dependent, so check the documentation of the port you
    are using.

    In this case, the function is running in the context of the tick interrupt,
    which will automatically check for the higher priority task to run anyway,
    so no further action is required. */
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
    /* The malloc failed hook is enabled by setting
    configUSE_MALLOC_FAILED_HOOK to 1 in FreeRTOSConfig.h.

    Called if a call to pvPortMalloc() fails because there is insufficient
    free memory available in the FreeRTOS heap.  pvPortMalloc() is called
    internally by FreeRTOS API functions that create tasks, queues, software
    timers, and semaphores.  The size of the FreeRTOS heap is set by the
    configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
    panic("malloc failed");
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t xTask, char *pcTaskName )
{
    ( void ) pcTaskName;
    ( void ) xTask;

    /* Run time stack overflow checking is performed if
    configconfigCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
    function is called if a stack overflow is detected.  pxCurrentTCB can be
    inspected in the debugger if the task name passed into this function is
    corrupt. */
    for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
    volatile size_t xFreeStackSpace;

    /* The idle task hook is enabled by setting configUSE_IDLE_HOOK to 1 in
    FreeRTOSConfig.h.

    This function is called on each cycle of the idle task.  In this case it
    does nothing useful, other than report the amount of FreeRTOS heap that
    remains unallocated. */
    xFreeStackSpace = xPortGetFreeHeapSize();

    if( xFreeStackSpace > 100 )
    {
        /* By now, the kernel has allocated everything it is going to, so
        if there is a lot of heap remaining unallocated then
        the value of configTOTAL_HEAP_SIZE in FreeRTOSConfig.h can be
        reduced accordingly. */
    }
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
    /* Want to be able to printf */
    stdio_init_all();
    /* And flash LED */
    gpio_init(PICO_DEFAULT_LED_PIN);
    gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
}