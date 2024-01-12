/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
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

#if ( mainDEMO_TYPE & IRQ_DEMO )

/** @brief TCB used by the Notification Test Task */
PRIVILEGED_DATA static StaticTask_t xNotificationTestTaskTCB;

/** @brief MPU Region Aligned Stack used by the Notification Test Task */

PRIVILEGED_DATA static StackType_t uxNotificationTestTaskStack[ demoIRQ_STACK_SIZE ]
    __attribute__( ( aligned( demoIRQ_STACK_SIZE * 0x4UL ) ) );

/** @brief Parameters that are passed into the IRQ test task solely for
 * the purpose of ensuring parameters are passed into tasks correctly. */
#define irqTASK_PARAMETER ( 0xFEEDBEEFUL )

/** @brief Value sent from the IRQ Handler to the Task */
#define irqNOTIFICATION_VALUE  0x1234UL

extern PRIVILEGED_DATA volatile uint32_t ulPortYieldRequired;
/** @brief Statically allocated task handle for the Notification Test task. */
PRIVILEGED_DATA static TaskHandle_t xIRQTaskHandle;

PRIVILEGED_DATA volatile static uint32_t ulIntNestTestVal;
/* ----------------------------------------------------------------------------------- */

static void prvNotifyCheck(BaseType_t ulRetVal)
{
    if( pdPASS == ulRetVal )
    {
        sci_print("Sent a notification!\r\n");
    }
    else
    {
        sci_print("Notification did not return pdPASS.\r\n");
        configASSERT( 0x0 );
    }
}

/** @brief Entry point for the Unprivileged Notification Test Task.
 * @param pvParameters A test value to ensure the task's arguments are correctly set.
 * @note This task raises Software Interrupts (SWI) in the form of IRQs using the
 * Vectored Interrupt Manager (VIM) built into the RM46 by Texas Instrument (TI).
 * It does this through use of the Software Interrupt Registers (SSIRs).
 * More information about these can be found in the following documents:
 * SWI Info Section 6.15: https://www.ti.com/lit/ds/symlink/rm46l852.pdf?ts=1704878833799
 * VIM Info: https://www.ti.com/lit/pdf/spna218
 */
static void prvNotificationTestTask( void * pvParameters )
{
    BaseType_t xReturned;
    uint32_t ulNotificationValue;

    /* Ensure that the correct parameter was passed to the task */
    configASSERT( ( uint32_t ) pvParameters == irqTASK_PARAMETER );
    for( ;; )
    {
        /* Clear the notification value each loop */
        ulNotificationValue = 0x0UL;

        /* The task should not yet have a notification pending. */
        xReturned = xTaskNotifyWait( 0x0UL, 0x0UL, &ulNotificationValue, 0x0UL );
        configASSERT( pdFAIL == xReturned );
        configASSERT( 0x0UL == ulNotificationValue );

        /* Tell the task to notify itself twice */
        xReturned = xTaskNotifyGive( xTaskGetCurrentTaskHandle() );
        prvNotifyCheck(xReturned);

        xReturned = xTaskNotifyGive( xTaskGetCurrentTaskHandle() );
        prvNotifyCheck(xReturned);

        /* Perform a non-blocking notification read, should see two "gives" */
        ulNotificationValue = ulTaskNotifyTake( pdTRUE, 0x0 );

        /* Two notifications have been sent to this task by itself */
        configASSERT( 0x2UL == ulNotificationValue );
        sci_print("IRQ Task correctly sent itself two notifications!\r\n");

        /* Now make the task send itself a notification with a value */
        xReturned = xTaskNotify( xTaskGetCurrentTaskHandle(), irqNOTIFICATION_VALUE, eSetValueWithOverwrite );
        prvNotifyCheck(xReturned);

        /* Clear ulNotificationValue before using it */
        ulNotificationValue = 0x0UL;
        /* Receive the value sent using xTaskNotify */
        xReturned = xTaskNotifyWait( 0, 0, &ulNotificationValue, ( TickType_t ) 0x50UL );
        prvNotifyCheck(xReturned);
        configASSERT( ulNotificationValue == irqNOTIFICATION_VALUE );

        /* Disable IRQs to raise a Software Based IRQ */
        //portDISABLE_INTERRUPTS();
        sci_print("Notification Test Task Starting IRQ Nesting Test!\r\n");
        ulIntNestTestVal = 0xFFFFUL;
        /* Trigger an IRQ by writing to the SSI Register with a data value */
        volatile uint32_t * xSoftwareInterruptRegister = portSSI_INT_REG_FOUR;
        *xSoftwareInterruptRegister = portSSI_FOUR_KEY | 0x44UL;

        /* When using a debugger IRQs can be paused/delayed.
         * Lazy loop to wait for it to trigger. */
        volatile uint32_t ulLoopCount = 0x0;
        while( ulLoopCount++ < 0x20)
        {
            if( ulIntNestTestVal >= 0x10UL )
            {
                ulIntNestTestVal = xTaskGetTickCount();
            }
            else
            {
                ulLoopCount = 0x30;
            }
        }

        if(0x0UL == ulIntNestTestVal)
        {
            sci_print("Notification Test Did not get the expected value!\r\n");
        }
        else
        {
            sci_print("Notification Test Got the expected value!\r\n");
        }
        #if 0
            /* While inside of this call the Kernel will enable interrupts, causing
             * the pending IRQ from above to be triggered. */
            xReturned = xTaskNotifyWait( 0, 0, &ulNotificationValue, 0x50 );
            prvNotifyCheck(xReturned);
            if( irqNOTIFICATION_VALUE != ulNotificationValue )
            {
                sci_print("Notification Test Did not get the expected value!\r\n");
            }
            else
            {
                sci_print("Notification Test Got the expected value!\r\n");
            }

            xTaskNotify( xTaskGetCurrentTaskHandle(), ulNotificationValue, eSetValueWithOverwrite );
            xReturned = xTaskNotifyStateClear( NULL );

            /* First time a notification was pending. */
            configASSERT( xReturned == pdTRUE );
            xReturned = xTaskNotifyStateClear( NULL );

            /* Second time the notification was already clear. */
            configASSERT( xReturned == pdFALSE );
        #endif
    }
}

/* ----------------------------------------------------------------------------------- */

void vIRQDemoHandler( void ) /* PRIVILEGED_FUNCTION */
{
    //sci_print("SWI IRQ Raised\r\n");
    //volatile uint32_t * xSSIIntRegBase = portSSI_INT_REG_BASE;
    volatile uint32_t ulSSIRegisterValue;
    //volatile uint32_t ulSSIVecValue;
    volatile uint32_t ulSSIIntFlagValue;
    volatile uint32_t * xSoftwareInterruptRegister;
    /* The 4 different SWI Registers use a bitfield to mark that they where raised */
    /* do */
    {
        /* Determine what channel raised the IRQ without clearing the interrupt */
        ulSSIIntFlagValue = portSSI_INTFLAG_REG;
        if( 0x1UL & ulSSIIntFlagValue )
        {
            sci_print("\tSoftware Interrupt Channel One Raised!\r\n");
            xSoftwareInterruptRegister = portSSI_INT_REG_ONE;
            /* Mark this interrupt channel as read and acknowledged */
            ulSSIRegisterValue = *xSoftwareInterruptRegister;
            if( ulSSIRegisterValue & 0x11UL )
            {
                ulIntNestTestVal++;
                sci_print("\tSWI Channel #1 Raised with Data Value 0x11, unwinding nested stack!\r\n");
            }
            ulSSIIntFlagValue ^= 0x1UL;
            xTaskGenericNotifyFromISR( xIRQTaskHandle,
                            ( UBaseType_t ) 0x0UL,
                            irqNOTIFICATION_VALUE,
                            eSetValueWithOverwrite,
                            NULL,
                            ( BaseType_t * ) &ulPortYieldRequired );
        }

        else if( 0x2UL & ulSSIIntFlagValue )
        {
            sci_print("\tSoftware Interrupt Channel Two Raised!\r\n");

            xSoftwareInterruptRegister = portSSI_INT_REG_TWO;
            ulSSIRegisterValue = *xSoftwareInterruptRegister;
            if( ulSSIRegisterValue & 0x22UL )
            {
                ulIntNestTestVal++;
                sci_print("\tSWI Channel #2 Raised with Data Value 0x22!\r\n");
                xSoftwareInterruptRegister = portSSI_INT_REG_ONE;
                *xSoftwareInterruptRegister = portSSI_ONE_KEY | 0x11UL;
                //__asm volatile("CPSIE I");

            }

            ulSSIIntFlagValue ^= 0x2UL;
        }

        else if( 0x4UL & ulSSIIntFlagValue )
        {
            sci_print("\tSoftware Interrupt Channel Three Raised!\r\n");

            xSoftwareInterruptRegister = portSSI_INT_REG_THREE;
            ulSSIRegisterValue = *xSoftwareInterruptRegister;
            if( ulSSIRegisterValue & 0x33UL )
            {
                ulIntNestTestVal++;
                sci_print("\tSWI Channel #3 Raised with Data Value 0x33!\r\n");
                xSoftwareInterruptRegister = portSSI_INT_REG_TWO;
                *xSoftwareInterruptRegister = portSSI_TWO_KEY | 0x22UL;
                //__asm volatile("CPSIE I");

            }
            ulSSIIntFlagValue ^= 0x4UL;
        }

        else /* if( 0x8UL & ulSSIIntFlagValue ) */
        {
            sci_print("\tSoftware Interrupt Channel Four Raised!\r\n");

            xSoftwareInterruptRegister = portSSI_INT_REG_FOUR;
            ulSSIRegisterValue = *xSoftwareInterruptRegister;
            if( ulSSIRegisterValue & 0x44UL )
            {
                ulIntNestTestVal = 0x1UL;
                sci_print("\tSWI Channel #4 Raised with Data Value 0x44!\r\n");
                // xSoftwareInterruptRegister = portSSI_INT_REG_THREE;
                // *xSoftwareInterruptRegister = portSSI_THREE_KEY | 0x33UL;
                //__asm volatile("CPSIE I");
#if 0
                xTaskGenericNotifyFromISR( xIRQTaskHandle,
                                ( UBaseType_t ) 0x0UL,
                                irqNOTIFICATION_VALUE,
                                eSetValueWithOverwrite,
                                NULL,
                                ( BaseType_t * ) &ulPortYieldRequired );
#endif
            }
            ulSSIIntFlagValue ^= 0x8UL;
        }

        /* Read the SSI Vec reg to clear corresponding bits and flags
         * For more info refer to
         * TODO: FInd the right doc
         * Joshua said it was page 184
         *  */
        ulSSIIntFlagValue = portSSI_VEC_REG;

    }
    /* while( 0x0UL != ulSSIIntFlagValue); */

}

/* ----------------------------------------------------------------------------------- */

BaseType_t xCreateNotificationTestTask( void )
{
    /* Declaration when these variable are exported from linker scripts. */
    extern uint32_t __SRAM_segment_start__[];
    // extern uint32_t __SRAM_segment_end__[];
    uint32_t ulSRAMBaseAddress = ( uint32_t ) __SRAM_segment_start__;
    uint32_t ulSRAMRegionSize = portMPU_SIZE_128KB | portMPU_REGION_ENABLE;

    uint32_t ulWriteMemoryPermissions = portMPU_PRIV_RW_USER_RW_NOEXEC |
                                        portMPU_NORMAL_OIWTNOWA_SHARED;

    BaseType_t xReturn = pdFAIL;
    /* Create the register check tasks, as described at the top of this file. */
    TaskParameters_t  xNotificationTestTaskParameters = {
        /* The function that implements the task. */
        .pvTaskCode = prvNotificationTestTask,
        /* The name of the task. */
        .pcName = "NotificationTestTask",
        /* Size of stack to allocate for the task - in words not bytes!. */
        .usStackDepth = demoIRQ_STACK_SIZE,
        /* Parameter passed into the task. */
        .pvParameters = ( void * ) irqTASK_PARAMETER,
        /* Priority of the task. */
        .uxPriority = ( configTIMER_TASK_PRIORITY + 0x2UL ) | portPRIVILEGE_BIT,
        .puxStackBuffer = uxNotificationTestTaskStack,
        .pxTaskBuffer = &xNotificationTestTaskTCB,
        .xRegions = {
                    /* MPU Region 0 */
                    { ( void * ) ulSRAMBaseAddress, ulSRAMRegionSize, ulWriteMemoryPermissions },
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
#if( configTOTAL_MPU_REGIONS == 16 )
                        /* MPU Region 6 */
                        { 0, 0, 0 },
                        /* MPU Region 7 */
                        { 0, 0, 0 },
                        /* MPU Region 8 */
                        { 0, 0, 0 },
                        /* MPU Region 9 */
                        { 0, 0, 0 },
#endif
        }
    };

    /* Create the first register test task as a privileged task */
    xReturn = xTaskCreateRestrictedStatic( &( xNotificationTestTaskParameters ), &( xIRQTaskHandle ) );
    if( pdPASS == xReturn )
    {
        sci_print( "Created the Notification Test Task\r\n" );
    }
    else
    {
        sci_print( "Failed to create the Notification Test Task\r\n" );
    }

    ulIntNestTestVal = 0xFEEDBEEFUL;
    return xReturn;
}
#endif /* ( mainDEMO_TYPE & IRQ_DEMO ) */
