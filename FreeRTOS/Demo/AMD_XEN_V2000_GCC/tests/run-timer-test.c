#include "FreeRTOS.h"
#include "FreeRTOS_CLI.h"
#include "stdint.h"
#include "string.h"
#include "stdio.h"
#include "cli.h"
#include "task.h"
#include "integer.h"
#include "timers.h"
#include "register_tests.h"

#define mainTIMER_SEND_FREQUENCY_MS      pdMS_TO_TICKS( 1000UL )
#define tmrDONT_BLOCK                    ( ( TickType_t ) 0 )
#define NUM_TEST_TIMERS                  5
static uint32_t timer_callback_count=0;
static void prvQueueSendTimerCallback1( TimerHandle_t xTimerHandle )
{
    portENTER_CRITICAL();
    timer_callback_count ++;
    portEXIT_CRITICAL();
}
static BaseType_t prvRuntimerDemo( char * pcWriteBuffer,
                                  size_t xWriteBufferLen,
                                  const char * pcCommandString )
{
    memset(pcWriteBuffer, 0x00, xWriteBufferLen );
    TimerHandle_t xAutoReloadTimers[ NUM_TEST_TIMERS ];
    TickType_t xTimer;
    int failed_setup = 0;
    timer_callback_count=0;
    const TickType_t xTimerPeriod = mainTIMER_SEND_FREQUENCY_MS;
    for( xTimer = 0; xTimer < NUM_TEST_TIMERS; xTimer++ )
    {
        xAutoReloadTimers[ xTimer ] = xTimerCreate( "Timer",
                               xTimerPeriod,
                               pdTRUE,
                               NULL,
                               prvQueueSendTimerCallback1 );

        if( xAutoReloadTimers[ xTimer ] != NULL )
        {
             xTimerStart( xAutoReloadTimers[ xTimer ], 0) ;
        }
    }
    vTaskDelay(xTimerPeriod+10);
    uint8_t ucTimer;
    uint32_t active_timer_count_before_stop=0;
    uint32_t active_timer_count_after_stop=0;
    /* Count active timers and stop them */
    for( ucTimer = 0; ucTimer < NUM_TEST_TIMERS; ucTimer++ )
    {
        if (xAutoReloadTimers[ ucTimer ] != NULL) {
             if( xTimerIsTimerActive( xAutoReloadTimers[ ucTimer ] ) == pdTRUE )
             {
                 active_timer_count_before_stop++;
             }
             xTimerStop( xAutoReloadTimers[ ucTimer ], tmrDONT_BLOCK );
        }
    }
    vTaskDelay(pdMS_TO_TICKS(1000));
    /* Check if any timers are still active */
    for( ucTimer = 0; ucTimer < NUM_TEST_TIMERS; ucTimer++ )
    {
        if( xTimerIsTimerActive( xAutoReloadTimers[ ucTimer ] ) == pdTRUE )
        {
            active_timer_count_after_stop++;
        }
    }
    uint32_t result = 1;
    if (active_timer_count_before_stop != NUM_TEST_TIMERS){
         result = 0;
    }
    if (timer_callback_count != NUM_TEST_TIMERS){
         result = 0;
    }
    if (active_timer_count_after_stop != 0){
         result = 0;
    }
    if (result){
        snprintf(pcWriteBuffer, xWriteBufferLen, "PASS: run-timer-test");
    }
    else{
        snprintf(pcWriteBuffer, xWriteBufferLen, "FAIL: run-timer-test");
    }
    return 0;
}

static const CLI_Command_Definition_t run_timer_test =
{
    "run-timer-test",
    "\r\nrun-timer-test:\r\n Run timer Test\r\n\r\n",
    prvRuntimerDemo, /* The function to run. */
    0
};

void register_timer_demo(void) {
    FreeRTOS_CLIRegisterCommand( &run_timer_test );
}


