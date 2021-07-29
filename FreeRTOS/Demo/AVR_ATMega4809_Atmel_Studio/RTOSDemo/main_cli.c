/*
    (c) 2018 Microchip Technology Inc. and its subsidiaries. 
    
    Subject to your compliance with these terms, you may use Microchip software and any 
    derivatives exclusively with Microchip products. It is your responsibility to comply with third party 
    license terms applicable to your use of third party software (including open source software) that 
    may accompany Microchip software.
    
    THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS". NO WARRANTIES, WHETHER 
    EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE, INCLUDING ANY 
    IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY, AND FITNESS 
    FOR A PARTICULAR PURPOSE.
    
    IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE, 
    INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND 
    WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP 
    HAS BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE. TO 
    THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL 
    CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT 
    OF FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS 
    SOFTWARE.
*/

#include <avr/io.h>
#include "porthardware.h"
/* Scheduler include files. */
#include "FreeRTOS.h"
#if (mainSELECTED_APPLICATION == CLI_DEMO)
#include "serial.h"
#include "UARTCommandConsole.h"
#include "PollQ.h"
#include "task.h"
#include "partest.h"
#include "serial/usart.h"

/* Priority definitions for most of the tasks in the demo application.  Some
tasks just use the idle priority. */
#define mainCOM_TEST_PRIORITY       ( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY     ( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY     ( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY       ( tskIDLE_PRIORITY + 1UL )

/* Baud rate used by the CLI demo. */
#define mainCOM_CLI_BAUD_RATE       ( ( unsigned long ) 230400 )

/* The period between executions of the check task. */
#define mainCHECK_PERIOD            ( ( TickType_t ) 1000 / portTICK_PERIOD_MS )

/* LED that is toggled by the check task.  The check task periodically checks
that all the other tasks are operating without error.  If no errors are found
the LED is toggled.  If an error is found at any time the LED is never toggles
again. */
#define mainCHECK_TASK_LED          ( 5 )

/* The check task, as described at the top of this file. */
static void prvCheckTask( void *pvParameters );

void main_cli( void )
{
    /* Create the task that performs the 'check' functionality, as described at
    the top of this file. */
    
    vUARTCommandConsoleStart( ( configMINIMAL_STACK_SIZE * 3 ), tskIDLE_PRIORITY );    
    vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
    
    /* Create the tasks defined within this file. */
    xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );
    
    vTaskStartScheduler();
    
    /* If all is well, the scheduler will now be running, and the following
    line will never be reached.  If the following line does execute, then
    there was either insufficient FreeRTOS heap memory available for the idle
    and/or timer tasks to be created, or vTaskStartScheduler() was called from
    User mode.  See the memory management section on the FreeRTOS web site for
    more details on the FreeRTOS heap http://www.freertos.org/a00111.html.  The
    mode from which main() is called is set in the C start up code and must be
    a privileged mode (not user mode). */
    for( ;; );
}
/*-----------------------------------------------------------*/

void init_cli( void )
{
    USART_cfg_t cfg;
    USART_initConfigs(&cfg);

    cfg.BAUD = (uint16_t)USART_BAUD_RATE(mainCOM_CLI_BAUD_RATE);
    cfg.CTRLA = 1 << USART_RXCIE_bp;
    cfg.CTRLB = 1 << USART_RXEN_bp | 1 << USART_TXEN_bp;
    cfg.CTRLC = 0x03;

    USART_setConfigs(cfg);

    vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
TickType_t xLastExecutionTime;
unsigned long ulErrorFound = pdFALSE;

    /* Just to stop compiler warnings. */
    ( void ) pvParameters;

    /* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
    works correctly. */
    xLastExecutionTime = xTaskGetTickCount();

    /* Cycle for ever, delaying then checking all the other tasks are still
    operating without error.  The onboard LED is toggled on each iteration 
    unless an error occurred. */
    for( ;; )
    {
        /* Delay until it is time to execute again. */
        vTaskDelayUntil( &xLastExecutionTime, mainCHECK_PERIOD );

        /* Check all the demo tasks (other than the flash tasks) to ensure
        that they are all still running, and that none have detected an error. */
        if( xArePollingQueuesStillRunning() != pdTRUE )
        {
           ulErrorFound |= 1UL << 0UL;
        }
        
        if( ulErrorFound == pdFALSE )
        {
            /* Toggle the LED if everything is okay so we know if an error occurs even if not
            using console IO. */

            /* Toggle LED on pin PC6. */
            vParTestToggleLED( mainCHECK_TASK_LED );
        }
    }
}
/*-----------------------------------------------------------*/

void vMainConfigureTimerForRunTimeStats( void )
{
    /* Used by the optional run-time stats gathering functionality. */
}
/*-----------------------------------------------------------*/

uint32_t ulMainGetRunTimeCounterValue( void )
{
uint32_t ulSysTickCounts, ulTickCount, ulReturn;

    /* How many clocks have passed since it was last reloaded? */
     ulSysTickCounts = TICK_TMR_READ();

    /* How many times has Tick Counter overflowed? */
    ulTickCount = xTaskGetTickCountFromISR();
    /* This is called from the context switch, so will be called from a
    critical section.  xTaskGetTickCountFromISR() contains its own critical
    section, and the ISR safe critical sections are not designed to nest,
    so reset the critical section. */

    /* Is there a SysTick interrupt pending? */
    if( TICK_INT_READY() != 0UL )
    {
        /* There is a SysTick interrupt pending, so the SysTick has overflowed
        but the tick count not yet incremented. */
        ulTickCount++;
        ulSysTickCounts = TICK_TMR_READ();
    }

    ulReturn = ( ulTickCount * ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) );

    ulReturn += ulSysTickCounts;

    return ulReturn;
}

#endif /* mainSELECTED_APPLICATION == CLI_DEMO */
