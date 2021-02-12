#include "FreeRTOS.h"
#include "timers.h"
#include "task.h"

#include "unity.h"
#include "unity_fixture.h"

#ifndef CONFIG_TEST_STACK_SIZE
    #define CONFIG_TEST_STACK_SIZE 0x1000
#endif

#ifndef CONFIG_TEST_PRIORITY
    #define CONFIG_TEST_PRIORITY tskIDLE_PRIORITY + 1
#endif

void prvTestTask()
{
    /* Configure profiling */
    #if ( projCOVERAGE_TEST != 1 )
        //vTraceEnable( TRC_START );
        //uiTraceStart();
    #endif

    /* Run test suite then report result */
    UNITY_BEGIN();
    RUN_TEST_GROUP( Timers );
    UNITY_END();

    while(1);
    vTaskDelete( NULL );
}

void main(void) 
{
    configPRINTF(("Starting...\n"));
    TaskHandle_t xTask_Test = NULL;
    xTaskCreate( prvTestTask,
                 "Test",
                 CONFIG_TEST_STACK_SIZE,
                 NULL,
                 CONFIG_TEST_PRIORITY,
                 &xTask_Test );

    vTaskStartScheduler();
}

void vAssertCalled( const char * pcFile, unsigned long ulLine )
{
    configPRINTF(( "Assert @ %s:%d\n" , pcFile, ulLine ));
    while(1);
}

void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                     StackType_t ** ppxTimerTaskStackBuffer,
                                     uint32_t * pulTimerTaskStackSize )
{
    static StaticTask_t xTimerTaskTCB;
    static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];
    *ppxTimerTaskTCBBuffer = &xTimerTaskTCB;
    *ppxTimerTaskStackBuffer = uxTimerTaskStack;
    *pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}

void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    uint32_t * pulIdleTaskStackSize )
{
    static StaticTask_t xIdleTaskTCB;
    static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];
    *ppxIdleTaskTCBBuffer = &xIdleTaskTCB;
    *ppxIdleTaskStackBuffer = uxIdleTaskStack;
    *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}

void vApplicationDaemonTaskStartupHook( void )
{}

void vApplicationTickHook( void )
{}


void vApplicationMallocFailedHook( void )
{
    configPRINTF( ( "ERROR: Malloc failed to allocate memory\n" ) );
    configASSERT( 1 );
    while(1);
}

void vApplicationIdleHook( void )
{}