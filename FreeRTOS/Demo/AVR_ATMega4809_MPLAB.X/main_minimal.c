#include <avr/eeprom.h>

#include "FreeRTOS.h"
#include "task.h"
#include "croutine.h"
#include "PollQ.h"
#include "integer.h"
#include "serial.h"
#include "comtest.h"
#include "crflash.h"
#include "partest.h"
#include "regtest.h"

/* Priority definitions for most of the tasks in the demo application.  Some
tasks just use the idle priority. */
#define mainCOM_TEST_PRIORITY       ( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY     ( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY     ( tskIDLE_PRIORITY + 3 )

/* Baud rate used by the serial port tasks. */
#define mainCOM_TEST_BAUD_RATE      ( ( unsigned long ) 9600 )

/* LED used by the serial port tasks.  This is toggled on each character Tx,
and mainCOM_TEST_LED + 1 is toggles on each character Rx. */
#define mainCOM_TEST_LED            ( 6 )

/* LED that is toggled by the check task.  The check task periodically checks
that all the other tasks are operating without error.  If no errors are found
the LED is toggled.  If an error is found at any time the LED is never toggles
again. */
#define mainCHECK_TASK_LED          ( 5 )

/* The period between executions of the check task. */
#define mainCHECK_PERIOD            ( ( TickType_t ) 1000 / portTICK_PERIOD_MS )

/* An address in the EEPROM used to count resets.  This is used to check that
the demo application is not unexpectedly resetting. */
#define mainRESET_COUNT_ADDRESS     ( 0x1400 )

/* The number of coroutines to create. */
#define mainNUM_FLASH_COROUTINES    ( 3 )

/*
 * The task function for the "Check" task.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Checks the unique counts of other tasks to ensure they are still operational.
 * Flashes an LED if everything is okay.
 */
static void prvCheckOtherTasksAreStillRunning( void );

/*
 * Called on boot to increment a count stored in the EEPROM.  This is used to
 * ensure the CPU does not reset unexpectedly.
 */
static void prvIncrementResetCount( void );

void main_minimal( void )
{
    prvIncrementResetCount();

    /* Create the standard demo tasks. */
    vStartIntegerMathTasks( tskIDLE_PRIORITY );
    vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
    vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
    vStartRegTestTasks();
    
    /* Create the tasks defined within this file. */
    xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

    /* Create the co-routines that flash the LED's. */
    vStartFlashCoRoutines( mainNUM_FLASH_COROUTINES );
    
    /* In this port, to use preemptive scheduler define configUSE_PREEMPTION
    as 1 in portmacro.h.  To use the cooperative scheduler define
    configUSE_PREEMPTION as 0. */
    vTaskStartScheduler();
}

void init_minimal( void )
{
    /* Configure UART pins: PB0 Rx, PB1 Tx */
    PORTB.DIR &= ~PIN1_bm;
    PORTB.DIR |= PIN0_bm;
    
    vParTestInitialise();
}

static void vErrorChecks( void *pvParameters )
{
static volatile unsigned long ulDummyVariable = 3UL;

    /* The parameters are not used. */
    ( void ) pvParameters;

    /* Cycle for ever, delaying then checking all the other tasks are still
    operating without error. */
    for( ;; )
    {
        vTaskDelay( mainCHECK_PERIOD );

        /* Perform a bit of 32bit maths to ensure the registers used by the
        integer tasks get some exercise.  The result here is not important -
        see the demo application documentation for more info. */
        ulDummyVariable *= 3;
        
        prvCheckOtherTasksAreStillRunning();
    }
}
/*-----------------------------------------------------------*/

static void prvCheckOtherTasksAreStillRunning( void )
{
static portBASE_TYPE xErrorHasOccurred = pdFALSE;

    if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
    {
        xErrorHasOccurred = pdTRUE;
    }

    if( xAreComTestTasksStillRunning() != pdTRUE )
    {
        xErrorHasOccurred = pdTRUE;
    }

    if( xArePollingQueuesStillRunning() != pdTRUE )
    {
        xErrorHasOccurred = pdTRUE;
    }

    if( xAreRegTestTasksStillRunning() != pdTRUE )
    {
        xErrorHasOccurred = pdTRUE;
    }
    
    if( xErrorHasOccurred == pdFALSE )
    {
        /* Toggle the LED if everything is okay so we know if an error occurs even if not
        using console IO. */
        vParTestToggleLED( mainCHECK_TASK_LED );
    }
}
/*-----------------------------------------------------------*/

static void prvIncrementResetCount( void )
{
unsigned char ucResetCount;

    eeprom_read_block( &ucResetCount, ( void * ) mainRESET_COUNT_ADDRESS, sizeof( ucResetCount ) );
    ucResetCount++;
    eeprom_write_byte( ( void * ) mainRESET_COUNT_ADDRESS, ucResetCount );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
    vCoRoutineSchedule();
}
