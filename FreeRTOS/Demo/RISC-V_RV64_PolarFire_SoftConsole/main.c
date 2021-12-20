/*
 * FreeRTOS V202111.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/******************************************************************************
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined in this file) is used to
 * select between the two.  The simply blinky demo is implemented and described
 * in main_blinky.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and standard FreeRTOS hook functions.
 *
 * When running on the PolarFire SoC hardware:
 * When executing correctly the yellow LED will toggle every three seconds.  If
 * the yellow LED toggles every 500ms then one of the self-monitoring test tasks
 * discovered a potential issue.  If the red led toggles rapidly then a hardware
 * exception occurred.
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 */

/* FreeRTOS kernel includes. */
#include <FreeRTOS.h>
#include <task.h>

/* PolarFire HAL includes. */
#include "mpfs_hal/mss_hal.h"
#include "drivers/mss/mss_gpio/mss_gpio.h"
#include "drivers/mss/mss_mmuart/mss_uart.h"

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY  0

/*-----------------------------------------------------------*/

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
#if ( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
    extern void main_blinky( void );
#else
    extern void main_full( void );
#endif /* #if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 */

/*
 * Prototypes for the standard FreeRTOS callback/hook functions implemented
 * within this file.  See https://www.freertos.org/a00016.html
 */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/*
 * Setup the hardware to run this demo.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

/* Main function for the HART0(E51 processor). Application code running on
 * HART0 is placed here. */
void e51( void )
{
    prvSetupHardware();

    /* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
     * of this file. */
    #if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
    {
        main_blinky();
    }
    #else
    {
        main_full();
    }
    #endif
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
    /* Configure UART0. */
    SYSREG->SUBBLK_CLOCK_CR |= SUBBLK_CLOCK_CR_MMUART0_MASK;
    SYSREG->SOFT_RESET_CR   &= ~SOFT_RESET_CR_MMUART0_MASK;
    MSS_UART_init( &( g_mss_uart0_lo ),
                   MSS_UART_115200_BAUD,
                   MSS_UART_DATA_8_BITS | MSS_UART_NO_PARITY | MSS_UART_ONE_STOP_BIT );

    /* Configure the LED. */
    mss_config_clk_rst( MSS_PERIPH_GPIO2, ( uint8_t )MPFS_HAL_FIRST_HART, PERIPHERAL_ON );
    MSS_GPIO_config( GPIO2_LO, MSS_GPIO_16, MSS_GPIO_OUTPUT_MODE ); /* Red Led (LED1). */
    MSS_GPIO_config( GPIO2_LO, MSS_GPIO_18, MSS_GPIO_OUTPUT_MODE ); /* Yellow Led (LED3). */
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
    /* vApplicationMallocFailedHook() will only be called if
     * configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
     * function that will get called if a call to pvPortMalloc() fails.
     * pvPortMalloc() is called internally by the kernel whenever a task, queue,
     * timer or semaphore is created.  It is also called by various parts of the
     * demo application.  If heap_1.c or heap_2.c are used, then the size of the
     * heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
     * FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
     * to query the size of free heap space that remains (although it does not
     * provide information on how the remaining heap might be fragmented). */
    taskDISABLE_INTERRUPTS();
    for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
    /* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
     * to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
     * task.  It is essential that code added to this hook function never attempts
     * to block in any way (for example, call xQueueReceive() with a block time
     * specified, or call vTaskDelay()).  If the application makes use of the
     * vTaskDelete() API function (as this demo application does) then it is also
     * important that vApplicationIdleHook() is permitted to return to its calling
     * function, because it is the responsibility of the idle task to clean up
     * memory allocated by the kernel to any task that has since been deleted. */
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
    ( void ) pcTaskName;
    ( void ) pxTask;

    /* Run time stack overflow checking is performed if
     * configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
     * function is called if a stack overflow is detected. */
    taskDISABLE_INTERRUPTS();
    for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
    /* The tests in the full demo expect some interaction with interrupts. */
    #if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY != 1 )
    {
        extern void vFullDemoTickHook( void );
        vFullDemoTickHook();
    }
    #endif
}
/*-----------------------------------------------------------*/

void vToggleLED( void )
{
static volatile uint8_t value = 0u;

    value = ( value == 0u ) ? 1u : 0u;
    MSS_GPIO_set_output( GPIO2_LO, MSS_GPIO_18, value );
}
/*-----------------------------------------------------------*/

void vAssertCalled( void )
{
volatile uint32_t ul;
const uint32_t ulNullLoopDelay = 0x1ffffUL;
static volatile uint8_t value = 0u;

    taskDISABLE_INTERRUPTS();

    /* Flash the red LED to indicate that assert was hit - interrupts are off
     * here to prevent any further tick interrupts or context switches, so the
     * delay is implemented as a crude loop instead of a peripheral timer. */
    for( ;; )
    {
        for( ul = 0; ul < ulNullLoopDelay; ul++ )
        {
            __asm volatile( "nop" );
        }

        value = ( value == 0u ) ? 1u : 0u;
        MSS_GPIO_set_output( GPIO2_LO, MSS_GPIO_16, value );
    }
}
/*-----------------------------------------------------------*/
