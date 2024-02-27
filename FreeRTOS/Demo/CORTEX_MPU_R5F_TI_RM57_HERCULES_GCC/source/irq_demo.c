/*
 * FreeRTOS V202212.00
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOSConfig.h"
#include "FreeRTOS.h"
#include "task.h"
#include "portmacro.h"

/* HalCoGen includes. */
#include "sci.h"

/* Demo include */
#include "demo_tasks.h"

#if( mainDEMO_TYPE & IRQ_DEMO )

/** @brief TCB used by the IRQ Test Task */
PRIVILEGED_DATA static StaticTask_t xIRQTestTaskTCB;

/** @brief MPU Region Aligned Stack used by the IRQ Test Task */

PRIVILEGED_DATA static StackType_t uxIRQTestTaskStack[ configMINIMAL_STACK_SIZE ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x4UL ) ) );

    /** @brief Parameters that are passed into the IRQ test task solely for
     * the purpose of ensuring parameters are passed into tasks correctly. */
    #define irqTASK_PARAMETER ( 0xFEEDBEEFUL )

/** @brief Statically allocated task handle for the IRQ Test task. */
PRIVILEGED_DATA static TaskHandle_t xIRQTaskHandle;

PRIVILEGED_DATA volatile static uint32_t ulIntNestTestVal;
/* ----------------------------------------------------------------------------------- */

/** @brief Entry point for the Unprivileged IRQ Test Task.
 * @param pvParameters A test value to ensure the task's arguments are correctly set.
 * @note This task raises Software Interrupts (SWI) in the form of IRQs using the
 * Vectored Interrupt Manager (VIM) built into the RM57 by Texas Instrument (TI).
 * It does this through use of the Software Interrupt Registers (SSIRs).
 * More information about these can be found in the following document:
 * https://www.ti.com/document-viewer/RM57L843/datasheet#system_information_and_electrical_specifications/SPNS1607150
 */
static void prvIRQTestTask( void * pvParameters )
{
    /* Ensure that the correct parameter was passed to the task */
    configASSERT( ( uint32_t ) pvParameters == irqTASK_PARAMETER );
    volatile uint32_t * xSoftwareInterruptRegister;
    volatile TickType_t ulLoopCount;
    volatile TickType_t xPreIRQTickCount;
    for( ;; )
    {
        /* Disable IRQs to raise a Software Based IRQ */
        // portDISABLE_INTERRUPTS();
        sci_print( "IRQ Test Task Starting IRQ Nesting Test!\r\n" );
        ulIntNestTestVal = 0xFFFFUL;

        /* Get the tick count before raising the SWI */
        xPreIRQTickCount = xTaskGetTickCount();

        /* Trigger an IRQ by writing to the SSI Register with a data value */
        xSoftwareInterruptRegister = portSSI_INT_REG_FOUR;
        *xSoftwareInterruptRegister = portSSI_FOUR_KEY | 0x44UL;

        /* When using a debugger IRQs can be paused/delayed.
         * This loop exists to keep the compiler from optimizing it out
         * while also giving the debugger time to trigger the IRQ. */
        ulLoopCount = xPreIRQTickCount;
        while( ( ulLoopCount + xPreIRQTickCount ) < ( xPreIRQTickCount + 0x20UL ) )
        {
            if( 0xFFFFUL != ulIntNestTestVal )
            {
                ulLoopCount++;
            }
            else
            {
                ulLoopCount = 0xFFFF0000UL;
            }
        }

        if( 0x4UL == ulIntNestTestVal )
        {
            sci_print( "IRQ Test Task reported correct unwinding!\r\n" );
            vToggleLED( 0x1 );
        }
        else
        {
            sci_print( "IRQ Test Task did not receive the correct nesting value!\r\n" );
            configASSERT( 0x0 );
        }

        sci_print( "IRQ Test Task sleeping before next loop!\r\n\r\n" );
        /* Sleep for odd number of seconds to schedule at different real-times */
        vTaskDelay( pdMS_TO_TICKS( 3150UL ) );
    }
}

/* ----------------------------------------------------------------------------------- */

void vIRQDemoHandler( void ) /* PRIVILEGED_FUNCTION */
{
    sci_print( "\tSWI Based IRQ was raised!\r\n" );
    volatile uint32_t ulSSIRegisterValue;
    volatile uint32_t ulSSIIntFlagValue;
    volatile uint32_t * xSoftwareInterruptRegister;
    /* The 4 different SWI Registers use a bitfield to mark that they where raised */
    {
        /* Determine what channel raised the IRQ without clearing the interrupt */
        ulSSIIntFlagValue = portSSI_INTFLAG_REG;
        if( 0x1UL & ulSSIIntFlagValue )
        {
            xSoftwareInterruptRegister = portSSI_INT_REG_ONE;
            ulSSIRegisterValue = *xSoftwareInterruptRegister;
            if( ulSSIRegisterValue & 0x11UL )
            {
                ulIntNestTestVal++;
                sci_print( "\t\tSWI Channel #1 Raised with Data Value 0x11, clearing the "
                           "IRQs...\r\n" );
                /* Read to mark this IRQ as cleared */
                /* Mark the Nested Channel 1 IRQ as cleared */
                ulSSIIntFlagValue = portSSI_VEC_REG;
                configASSERT( 0x1101UL == ulSSIIntFlagValue );

                /* Mark the Nested Channel 2 IRQ as cleared */
                ulSSIIntFlagValue = portSSI_VEC_REG;
                configASSERT( 0x2202UL == ulSSIIntFlagValue );

                /* Mark the Nested Channel 3 IRQ as cleared */
                ulSSIIntFlagValue = portSSI_VEC_REG;
                configASSERT( 0x3303UL == ulSSIIntFlagValue );

                /* Mark the Nested Channel 4 IRQ as cleared */
                ulSSIIntFlagValue = portSSI_VEC_REG;
                configASSERT( 0x4404UL == ulSSIIntFlagValue );

                /* Should be no other IRQs raised, mask out the data */
                ulSSIIntFlagValue = ( portSSI_VEC_REG ) & 0XFFUL;
                configASSERT( 0x0UL == ulSSIIntFlagValue );
            }
        }

        else if( 0x2UL & ulSSIIntFlagValue )
        {
            xSoftwareInterruptRegister = portSSI_INT_REG_TWO;
            ulSSIRegisterValue = *xSoftwareInterruptRegister;
            if( ulSSIRegisterValue & 0x22UL )
            {
                ulIntNestTestVal++;
                sci_print( "\t\tSWI Channel #2 triggering nested Channel #1 IRQ!\r\n" );
                xSoftwareInterruptRegister = portSSI_INT_REG_ONE;
                *xSoftwareInterruptRegister = portSSI_ONE_KEY | 0x11UL;
                __asm volatile( "CPSIE I" );
            }
        }

        else if( 0x4UL & ulSSIIntFlagValue )
        {
            xSoftwareInterruptRegister = portSSI_INT_REG_THREE;
            ulSSIRegisterValue = *xSoftwareInterruptRegister;
            if( ulSSIRegisterValue & 0x33UL )
            {
                ulIntNestTestVal++;
                sci_print( "\t\tSWI Channel #3 triggering nested Channel #2 IRQ!\r\n" );
                xSoftwareInterruptRegister = portSSI_INT_REG_TWO;
                *xSoftwareInterruptRegister = portSSI_TWO_KEY | 0x22UL;
                __asm volatile( "CPSIE I" );
            }
        }

        else /* if( 0x8UL & ulSSIIntFlagValue ) */
        {
            xSoftwareInterruptRegister = portSSI_INT_REG_FOUR;
            ulSSIRegisterValue = *xSoftwareInterruptRegister;
            if( ulSSIRegisterValue & 0x44UL )
            {
                ulIntNestTestVal = 0x1UL;
                sci_print( "\t\tSWI Channel #4 triggering nested Channel #3 IRQ!\r\n" );
                xSoftwareInterruptRegister = portSSI_INT_REG_THREE;
                *xSoftwareInterruptRegister = portSSI_THREE_KEY | 0x33UL;
                __asm volatile( "CPSIE I" );
            }
        }
    }
}

/* ----------------------------------------------------------------------------------- */

BaseType_t xCreateIRQTestTask( void )
{
    /* Declaration when these variable are exported from linker scripts. */
    extern uint32_t __SRAM_segment_start__[];
    extern uint32_t __SRAM_segment_end__[];
    extern uint32_t __peripherals_start__[];
    extern uint32_t __peripherals_end__[];

    uint32_t ulPeriphRegionStart = ( uint32_t ) __peripherals_start__;
    uint32_t ulPeriphRegionSize = ( uint32_t ) __peripherals_end__ - ulPeriphRegionStart;
    uint32_t ulPeriphRegionAttr = portMPU_REGION_PRIV_RW_USER_RW_NOEXEC | portMPU_REGION_DEVICE_SHAREABLE;

    uint32_t ulSRAMBaseAddress = ( uint32_t ) __SRAM_segment_start__;
    uint32_t ulSRAMRegionSize = ( uint32_t ) __SRAM_segment_end__ - ulSRAMBaseAddress;
    uint32_t ulSRAMRegionAttr = portMPU_REGION_PRIV_RW_USER_RW_NOEXEC
                              | portMPU_REGION_NORMAL_OIWTNOWA_SHARED;

    BaseType_t xReturn = pdFAIL;
    /* Create the register check tasks, as described at the top of this file. */
    TaskParameters_t  xIRQTestTaskParameters = {
        /* The function that implements the task. */
        .pvTaskCode = prvIRQTestTask,
        /* The name of the task. */
        .pcName = "IRQTestTask",
        /* Size of stack to allocate for the task - in words not bytes!. */
        .usStackDepth = configMINIMAL_STACK_SIZE,
        /* Parameter passed into the task. */
        .pvParameters = ( void * ) irqTASK_PARAMETER,
        /* Priority of the task. */
        .uxPriority = ( configTIMER_TASK_PRIORITY + 0x2UL ) | portPRIVILEGE_BIT,
        .puxStackBuffer = uxIRQTestTaskStack,
        .pxTaskBuffer = &xIRQTestTaskTCB,
        .xRegions = {
                    /* MPU Region 0 */
                    { ( void * ) ulSRAMBaseAddress, ulSRAMRegionSize, ulSRAMRegionAttr },
                    /* MPU Region 1 */
                    { 0, 0, 0 },
                    /* MPU Region 2 */
                    { 0, 0, 0 },
                    /* MPU Region 3 */
                    { 0, 0, 0 },
                    /* MPU Region 4 */
                    { 0, 0, 0 },
                    /* MPU Region 5 */
                    { 0, 0, 0 },
                    /* MPU Region 6 */
                    { 0, 0, 0 },
    #if( configTOTAL_MPU_REGIONS == 16 )
                        /* MPU Region 7 */
                        { 0, 0, 0 },
                        /* MPU Region 8 */
                        { 0, 0, 0 },
                        /* MPU Region 9 */
                        { 0, 0, 0 },
                        /* MPU Region 10 */
                        { 0, 0, 0 },
    #endif
                    /* Last Configurable MPU Region */
                    { ( void * ) ulPeriphRegionStart, ulPeriphRegionSize, ulPeriphRegionAttr },
        }
    };

    /* Create the first register test task as a privileged task */
    xReturn = xTaskCreateRestrictedStatic( &( xIRQTestTaskParameters ),
                                           &( xIRQTaskHandle ) );
    if( pdPASS == xReturn )
    {
        sci_print( "Created the IRQ Test Task\r\n" );
    }
    else
    {
        sci_print( "Failed to create the IRQ Test Task\r\n" );
    }

    ulIntNestTestVal = 0xFEEDBEEFUL;
    return xReturn;
}
#endif /* ( mainDEMO_TYPE & IRQ_DEMO ) */
