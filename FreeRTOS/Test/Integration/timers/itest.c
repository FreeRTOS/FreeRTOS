
#include "FreeRTOS.h"
#include "timers.h"

#include "unity.h"
#include "unity_fixture.h"

TEST_GROUP( Timers );

TEST_SETUP( Timers )
{}

TEST_TEAR_DOWN( Timers )
{}

TEST_GROUP_RUNNER( Timers )
{
    RUN_TEST_CASE( Timers, TimerHappyPath );
}


void prvCallBack_TimerTest( TimerHandle_t xTimer )
{

}

TimerHandle_t prvCreateTimer()
{

}

TEST( Timers, TimerHappyPath )
{
    TimerHandle_t xTimer_Handle = NULL;
    TickType_t xTimerPeriod = pdMS_TO_TICKS( 1 * 1000 );
    UBaseType_t ulID = 0;
    static StaticTimer_t xTimer_Memory;

    xTimer_Handle = xTimerCreateStatic( "static-timer",
                                       portMAX_DELAY,
                                       pdFALSE,
                                       &ulID,
                                       prvCallBack_TimerTest,
                                       &xTimer_Memory
                                       );

    TEST_ASSERT( xTimer_Handle != NULL );
}

/**
 * @brief Attempts to mangle list [IoTClock_TimerCreate, IotClock_
 * 
 */
TEST( Timers, TimerAttemptMangle )
{
    /* IotClock_TimerCreate */
    TimerHandle_t xTimer_Handle = NULL;
    TickType_t xTimerPeriod = pdMS_TO_TICKS( 1 * 1000 );
    UBaseType_t ulID = 0;
    static StaticTimer_t xTimer_Memory;

    xTimer_Handle = xTimerCreateStatic( "static-timer",
                                       portMAX_DELAY,
                                       pdFALSE,
                                       &ulID,
                                       prvCallBack_TimerTest,
                                       &xTimer_Memory
                                       );

    /* IotClock_TimerArm */
    xTimerChangePeriod( xTimer_Handle, 2 * xTimerPeriod, portMAX_DELAY );

    /* IotClock_TimerDestroy */
    if( xTimerIsTimerActive( xTimer_Handle ))
    {
        xTimerStop( xTimer_Handle, portMAX_DELAY );

        while( xTimerIsTimerActive( xTimer_Handle ) == pdTRUE )
        {
            vTaskDelay(1);
        }
    }

    /* IotClock_TimerCreate */
    xTimer_Handle = xTimerCreateStatic( "static-timer",
                                    portMAX_DELAY,
                                    pdFALSE,
                                    &ulID,
                                    prvCallBack_TimerTest,
                                    &xTimer_Memory
                                    );

    TEST_ASSERT( xTimer_Handle != NULL );
}