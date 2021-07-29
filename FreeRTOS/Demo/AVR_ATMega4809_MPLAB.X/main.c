/*
(C) 2020 Microchip Technology Inc. and its subsidiaries.

Subject to your compliance with these terms, you may use Microchip software and
any derivatives exclusively with Microchip products. It is your responsibility
to comply with third party license terms applicable to your use of third party
software (including open source software) that may accompany Microchip software.

THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".  NO WARRANTIES, WHETHER EXPRESS,
IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE, INCLUDING ANY IMPLIED WARRANTIES
OF NON-INFRINGEMENT, MERCHANTABILITY, AND FITNESS FOR A PARTICULAR PURPOSE.
IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND WHATSOEVER
RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS BEEN ADVISED OF
THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.  TO THE FULLEST EXTENT ALLOWED
BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL CLAIMS IN ANY WAY RELATED TO THIS
SOFTWARE WILL NOT EXCEED THE AMOUNT OF FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY
TO MICROCHIP FOR THIS SOFTWARE.
*/

#include <avr/io.h>
#include "FreeRTOS.h"
#include "clk_config.h"

FUSES = 
{
    .APPEND = 0,
    .BODCFG = ACTIVE_DIS_gc | LVL_BODLEVEL0_gc | SAMPFREQ_1KHZ_gc | SLEEP_DIS_gc,
    .BOOTEND = 0,
    .OSCCFG = FREQSEL_20MHZ_gc,
    .SYSCFG0 = CRCSRC_NOCRC_gc | RSTPINCFG_GPIO_gc,
    .SYSCFG1 = SUT_64MS_gc,
    .WDTCFG = PERIOD_OFF_gc | WINDOW_OFF_gc,
};

/* Configure the hardware as necessary to run this demo. */
static void prvSetupHardware( void );

#if ( mainSELECTED_APPLICATION == BLINKY_DEMO )
extern void main_blinky( void );
extern void init_blinky( void );
#elif ( mainSELECTED_APPLICATION == MINIMAL_DEMO )
extern void main_minimal( void );
extern void init_minimal( void );
#elif ( mainSELECTED_APPLICATION == FULL_DEMO)
extern void main_full( void );
extern void init_full( void );
#elif ( mainSELECTED_APPLICATION == CLI_DEMO )
extern void main_cli( void );
extern void init_cli( void );
#elif ( mainSELECTED_APPLICATION == TICKLESS_DEMO )
extern void main_tickless( void );
extern void init_tickless( void );
#elif ( mainSELECTED_APPLICATION == TRACE_DEMO )
extern void main_trace( void );
extern void init_trace( void );
#else
#error Invalid mainSELECTED_APPLICATION setting. See the comments at the top of this file and above the mainSELECTED_APPLICATION definition.
#endif

int main( void )
{
    prvSetupHardware();

#if ( mainSELECTED_APPLICATION == BLINKY_DEMO )
    main_blinky();
#elif ( mainSELECTED_APPLICATION == MINIMAL_DEMO )
    main_minimal();
#elif ( mainSELECTED_APPLICATION == FULL_DEMO )
    main_full();
#elif ( mainSELECTED_APPLICATION == CLI_DEMO )
    main_cli();
#elif ( mainSELECTED_APPLICATION == TICKLESS_DEMO )
    main_tickless();
#elif ( mainSELECTED_APPLICATION == TRACE_DEMO )
    vTraceEnable(TRC_INIT);
    //vTraceEnable(TRC_START);
    main_trace();
#endif

    return 0;
}

static void prvSetupHardware( void )
{
    /* Ensure no interrupts execute while the scheduler is in an inconsistent
    state.  Interrupts are automatically enabled when the scheduler is
    started. */
    portDISABLE_INTERRUPTS();

    CLK_init();

#if ( mainSELECTED_APPLICATION == BLINKY_DEMO )
    init_blinky();
#elif ( mainSELECTED_APPLICATION == MINIMAL_DEMO )
    init_minimal();
#elif ( mainSELECTED_APPLICATION == FULL_DEMO )
    init_full();
#elif ( mainSELECTED_APPLICATION == CLI_DEMO )
    init_cli();
#elif ( mainSELECTED_APPLICATION == TICKLESS_DEMO )
    init_tickless();
#elif ( mainSELECTED_APPLICATION == TRACE_DEMO )
    init_trace();
#endif
}

/* vApplicationStackOverflowHook is called when a stack overflow occurs.
This is usefull in application development, for debugging.  To use this
hook, uncomment it, and set configCHECK_FOR_STACK_OVERFLOW to 1 in
"FreeRTOSConfig.h" header file. */

// #include "task.h"
// void vApplicationStackOverflowHook(TaskHandle_t pxTask, char *pcTaskName )
// {
//     for( ;; );
// }

/* vApplicationMallocFailedHook is called when memorry allocation fails.
This is usefull in application development, for debugging.  To use this
hook, uncomment it, and set configUSE_MALLOC_FAILED_HOOK to 1 in
"FreeRTOSConfig.h" header file. */

// void vApplicationMallocFailedHook( void )
// {
//     for( ;; );
// }
