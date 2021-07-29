/******************************************************************************
 *
 * main_tickless() creates one queue, and two tasks.  It then starts the
 * scheduler.
 * 
 *    Two tasks are created, an Rx task and a Tx task.  A queue is created to
 *    pass a message from the Tx task to the Rx task.
 *
 *  + The Rx task blocks on a queue to wait for data, blipping an LED each time
 *    data is received (turning it on and then off again) before returning to
 *    block on the queue once more.
 *
 *  + The Tx task repeatedly blocks on an attempt to obtain a semaphore, and
 *    unblocks if either the semaphore is received or its block time expires.
 *    After leaving the blocked state the Tx task uses the queue to send a
 *    value to the Rx task, which in turn causes the Rx task to exit the
 *    Blocked state and blip the LED.  The rate at which the LED is seen to blip
 *    is therefore dependent on the block time
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#if ( mainSELECTED_APPLICATION == TICKLESS_DEMO )
#include "task.h"
#include "semphr.h"
#include "partest.h"

/* Priorities at which the tasks are created. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY     ( tskIDLE_PRIORITY + 1 )
#define mainQUEUE_SEND_TASK_PRIORITY        ( tskIDLE_PRIORITY + 2 )


/* LED that is toggled. */
#define mainCHECK_TASK_LED                  ( 5 )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added, meaning the send task should always find
the queue empty. */
#define mainQUEUE_LENGTH                    ( 1 )

/* The value that is sent from the Tx task to the Rx task on the queue. */
#define mainQUEUED_VALUE                    ( 100UL )

/* The length of time the LED will remain on for. */
#define mainLED_TOGGLE_DELAY                ( 30 )

/* Holds the block time used by the Tx task. */
TickType_t xSendBlockTime = ( 500UL );

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK                      ( 0 )

/*-----------------------------------------------------------*/

/* The tasks as described in the comments at the top of this file. */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used by both tasks. */
static QueueHandle_t xQueue = NULL;
/* The semaphore on which the Tx task blocks. */
static SemaphoreHandle_t xTxSemaphore = NULL;

void main_tickless( void )
{
    
    /* Create the semaphore as described at the top of this file. */
    xTxSemaphore = xSemaphoreCreateBinary();
    configASSERT( xTxSemaphore );

    /* Create the queue as described at the top of this file. */
    xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );
    configASSERT( xQueue );

    /* Start the two tasks as described at the top of this file. */
    xTaskCreate( prvQueueReceiveTask, "Rx", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_RECEIVE_TASK_PRIORITY, NULL );
    xTaskCreate( prvQueueSendTask, "Tx", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_SEND_TASK_PRIORITY, NULL );

    /* Start the scheduler running running. */
    vTaskStartScheduler();

    /* If all is well the next line of code will not be reached as the
    scheduler will be running.  If the next line is reached then it is likely
    there was insufficient FreeRTOS heap available for the idle task and/or
    timer task to be created.  See http://www.freertos.org/a00111.html. */
    for( ;; );
}

void init_tickless( void )
{

    vParTestInitialise();
}

static void prvQueueSendTask( void *pvParameters )
{
const unsigned long ulValueToSend = mainQUEUED_VALUE;

    /* Remove compiler warning about unused parameter. */
    ( void ) pvParameters;

    for( ;; )
    {
        /* Enter the Blocked state to wait for the semaphore.  The task will
        leave the Blocked state if either the semaphore is received or
        xSendBlockTime ticks pass without the semaphore being received. */
        xSemaphoreTake( xTxSemaphore, xSendBlockTime );

        /* Send to the queue - causing the Tx task to flash its LED. */
        xQueueSend( xQueue, &ulValueToSend, mainDONT_BLOCK );
    }
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
unsigned long ulReceivedValue;

/* Remove compiler warning about unused parameter. */
    ( void ) pvParameters;

    for( ;; )
    {
        /* Wait until something arrives in the queue. */
        xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

        /*  To get here something must have arrived, but is it the expected
        value?  If it is, turn the LED on for a short while. */
        if( ulReceivedValue == mainQUEUED_VALUE )
        {
            /* LED on */
            vParTestSetLED( mainCHECK_TASK_LED, 0 );

            /* Delay */
            vTaskDelay( mainLED_TOGGLE_DELAY );

            /* LED off */
            vParTestToggleLED( mainCHECK_TASK_LED);
        }
    }
}
/*-----------------------------------------------------------*/

#endif /* mainSELECTED_APPLICATION == TICKLESS_DEMO */