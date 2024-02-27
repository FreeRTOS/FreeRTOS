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

/* ------------------------------------------------------------------------- */
/**
 * @file main.c
 * @brief File implementing RM46L852 specific functions
 */

/* FreeRTOS includes. */
#include "FreeRTOSConfig.h"
#include "FreeRTOS.h"
#include "portmacro.h"
#include "task.h"
#include "timers.h"

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>

/* HalCoGen includes. */
#include "system.h"
#include "gio.h"
#include "het.h"
#include "reg_vim.h"
#include "sci.h"
#include "sys_vim.h"
#include "system.h"

/* Demo Tasks include */
#include "demo_tasks.h"

/* ----------------------- Microcontroller Registers ----------------------- */

/** @brief Configure the hardware to start the scheduler timer. */
PRIVILEGED_FUNCTION void vMainSetupTimerInterrupt( void );

/** @brief Set up necessary hardware registers */
PRIVILEGED_FUNCTION static void prvSetupHardware( void );

/** @brief Landing point function for any failed configASSERT() check.
 * @param pcFuncName The function that raised the assert.
 * @param ulLine The line that the assert was called from.
 * @note Unprivileged tasks shall pre-fetch abort if their assert fails. */
FREERTOS_SYSTEM_CALL void vAssertCalled( const char * pcFileName, uint32_t ulLine );

PRIVILEGED_FUNCTION void vApplicationIRQHandler( void );
/* --------------------- Static Task Memory Allocation --------------------- */

/** @brief Statically declared TCB Used by the Idle Task */
PRIVILEGED_DATA static StaticTask_t xTimerTaskTCB;

/** @brief Statically declared MPU aligned stack used by the timer task */
PRIVILEGED_DATA static StackType_t uxTimerTaskStack[ configMINIMAL_STACK_SIZE ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x4U ) ) );

/** @brief Statically declared TCB Used by the Idle Task */
PRIVILEGED_DATA static StaticTask_t xIdleTaskTCB;

/** @brief Statically declared MPU aligned stack used by the idle task */
PRIVILEGED_DATA static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ]
    __attribute__( ( aligned( configMINIMAL_STACK_SIZE * 0x4U ) ) );

/** @brief Simple variable to show how the idle tick hook can be used */
PRIVILEGED_DATA static volatile TickType_t ulIdleTickHookCount = 0x0;

extern PRIVILEGED_DATA volatile uint32_t ulPortYieldRequired;

/* ------------------------------------------------------------------------- */

int main( void )
{
    UBaseType_t xReturn = pdPASS;
    ulIdleTickHookCount = 0x0;
    prvSetupHardware();

    sci_print( "\r\n---------------------------- Create FreeRTOS Tasks"
               "----------------------------\r\n\r\n" );

#if( mainDEMO_TYPE & REGISTER_DEMO )
    {
        if( pdPASS == xReturn )
        {
            sci_print( "Creating the Register test tasks\r\n" );
            xReturn = xCreateRegisterTestTasks();
        }
    }
#endif /* ( mainDEMO_TYPE & REGISTER_DEMO ) */

#if( mainDEMO_TYPE & QUEUE_DEMO )
    {
        if( pdPASS == xReturn )
        {
            sci_print( "Creating the Queue Demo Tasks\r\n" );
            xReturn = xCreateQueueTasks();
        }
    }
#endif /* ( mainDEMO_TYPE & QUEUE_DEMO ) */

#if( mainDEMO_TYPE & MPU_DEMO )
    {
        if( pdPASS == xReturn )
        {
            sci_print( "Creating the MPU Demo Tasks\r\n" );
            xReturn = xCreateMPUTasks();
        }
    }
#endif

#if( mainDEMO_TYPE & IRQ_DEMO )
    {
        if( pdPASS == xReturn )
        {
            sci_print( "Creating the IRQ Demo Tasks\r\n" );
            xReturn = xCreateIRQTestTask();
        }
    }
#endif /* ( mainDEMO_TYPE & IRQ_DEMO ) */

#if( mainDEMO_TYPE & NOTIFICATION_DEMO )
    {
        if( pdPASS == xReturn )
        {
            sci_print( "Creating the Notification Demo Tasks\r\n" );
            xReturn = xCreateNotificationTestTask();
        }
    }
#endif /* ( mainDEMO_TYPE & NOTIFICATION_DEMO ) */

    if( pdPASS == xReturn )
    {
        sci_print( "\r\n--------------------------- Start of FreeRTOS Demos"
                   "---------------------------\r\n\r\n" );
        vTaskStartScheduler();
    }
    else
    {
        sci_print( "Failed to create the Demo Tasks\r\n" );
        configASSERT( pdFAIL );
    }

    /* If all is well, the scheduler will now be running, and the following
     * line will never be reached. If the following line does execute, then
     * there was an error when creating the necessary FreeRTOS objects. */
    configASSERT( 0x0 );
    return 0;
}
/*---------------------------------------------------------------------------*/

static void prvSetupHardware( void )
{
    systemInit();
    gioInit();
    hetInit();
    sciInit();

    /* Setup gioPORTB for when using the RM46 Launchpad */
    gioPORTB->DIR |= ( 0x01 << 1 ); /*configure GIOB[1] as output */
    gioPORTB->DIR |= ( 0x01 << 2 ); /*configure GIOB[3] as output */

    /* Configure HET as master, pull functionality, and switch on. */
    hetREG1->GCR = 0x01000001;
    hetREG1->PULDIS = 0x00000000;

    /* Configure pins connected to LEDs NHET[0,2,4,5,25,16,17,18,20,27,29,31]
     * as output. */
    hetREG1->DIR = 0xAA178035;
    hetREG1->DOUT = 0x0;

    /* Enable notifications for the SCI register */
    /* Use a BAUD rate of 115200, 1 stop bit, and None Parity */
    sciEnableNotification( scilinREG, SCI_RX_INT );
}

/*---------------------------------------------------------------------------*/

void vToggleLED( uint32_t ulLEDNum )
{
    uint32_t ulLEDVal;
    uint32_t ulGIOVal;

    if( 0x0 == ulLEDNum )
    {
        /* RM46 TMDX Dev Kit LED1 use NHET[0], Launchpad LED2 uses GIOB[1] */
        ulLEDVal = 1UL << 0UL;
        ulGIOVal = 1UL << 1UL;
    }
    else
    {
        /* RM46 TMDX Dev Kit LED2 use NHET[5], Launchpad LED3 uses GIOB[2] */
        ulLEDVal = 1UL << 5UL;
        ulGIOVal = 1UL << 2UL;
    }

    if( ( hetREG1->DOUT & ulLEDVal ) == 0 )
    {
        hetREG1->DOUT |= ulLEDVal;
        gioPORTB->DOUT |= ulGIOVal;
    }
    else
    {
        hetREG1->DOUT &= ~ulLEDVal;
        gioPORTB->DOUT &= ~ulGIOVal;
    }
}

/*---------------------------------------------------------------------------*/

void vMainSetupTimerInterrupt( void )
{
    /* Disable timer 0. */
    portRTI_GCTRL_REG &= 0xFFFFFFFEUL;

    /* Use the internal counter. */
    portRTI_TBCTRL_REG = 0x00000000U;

    /* COMPSEL0 will use the RTIFRC0 counter. */
    portRTI_COMPCTRL_REG = 0x00000000U;

    /* Initialise the counter and the prescale counter registers. */
    portRTI_CNT0_UC0_REG = 0x00000000U;
    portRTI_CNT0_FRC0_REG = 0x00000000U;

    /* Set Prescalar for RTI clock. */
    portRTI_CNT0_CPUC0_REG = 0x00000001U;
    portRTI_CNT0_COMP0_REG = ( configCPU_CLOCK_HZ / 2 ) / configTICK_RATE_HZ;
    portRTI_CNT0_UDCP0_REG = ( configCPU_CLOCK_HZ / 2 ) / configTICK_RATE_HZ;

    /* Clear interrupts. */
    portRTI_INTFLAG_REG = 0x0007000FU;
    portRTI_CLEARINTENA_REG = 0x00070F0FU;

    /* Enable the compare 0 interrupt. */
    portRTI_SETINTENA_REG = 0x00000001U;
    portRTI_GCTRL_REG |= 0x00000001U;
}

/*---------------------------------------------------------------------------*/

void vApplicationIdleHook( void )
{
    /* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
     * to 1 in FreeRTOSConfig.h. It will be called on each iteration of the
     * idle task. It is essential that code added to this hook function never
     * attempts to block in any way (for example, call xQueueReceive() with a
     * block time specified, or call vTaskDelay()). If application tasks make
     * use of the vTaskDelete() API function to delete themselves then it is
     * also important that vApplicationIdleHook() is permitted to return to its
     * calling function, because it is the responsibility of the idle task to
     * clean up memory allocated by the kernel to any task that has since
     * deleted itself. */
    ulIdleTickHookCount++;
    if( ( TickType_t ) 0xF00000 == ulIdleTickHookCount )
    {
        sci_print( "vApplicationIdleHook has run 0xF0 0000 times!\r\n" );
    }

    else if( ( TickType_t ) 0xFFFFFFFF == ulIdleTickHookCount )
    {
        sci_print( "vApplicationIdleHook has run 0xFFFFFFFF times! "
                   "Setting it to 0x0!\r\n" );
        ulIdleTickHookCount = 0x0;
    }
}

/*---------------------------------------------------------------------------*/

void vAssertCalled( const char * pcFuncName, uint32_t ulLine ) /* FREERTOS_SYSTEM_CALL */
{
    volatile uint32_t ulSetToNonZeroInDebuggerToContinue = 0;

    /* Called if an assertion passed to configASSERT() fails. See
     * http://www.freertos.org/a00110.html#configASSERT for more information. */
    volatile const char * callingFunc = pcFuncName;
    volatile uint32_t callingLine = ulLine;

    /* These variables can be inspected in a debugger. */
    if( callingFunc != ( char * ) callingLine )
    {
        __asm volatile( "NOP" );
    }

    /* NOTE: Unprivileged tasks cannot enter critical sections on the ARM_CRx_MPU port.
     * Meaning unprivileged tasks will cause a pre-fetch abort if they fail an assert. */
    taskENTER_CRITICAL();
    {
        if( callingFunc != ( char * ) callingLine )
        {
            __asm volatile( "NOP" );
        }

        /* You can step out of this function to debug the assertion by using
         * the debugger to set ulSetToNonZeroInDebuggerToContinue to a non-zero
         * value. */
        while( ulSetToNonZeroInDebuggerToContinue == 0 )
        {
            __asm volatile( "NOP" );
            __asm volatile( "NOP" );
        }
    }
    taskEXIT_CRITICAL();
}

/*---------------------------------------------------------------------------*/

/** @brief Default IRQ Handler used in the ARM_Cortex_RX ports.
 * @note This Handler is directly tied to the Texas Instrument's Hercules
 * Vectored Interrupt Manager (VIM). For more information about what
 * this is and how it operates please refer to their document:
 * https://www.ti.com/lit/pdf/spna218
 */
void vApplicationIRQHandler( void )
{
    /* Load the IRQ Channel Number and Function PTR from the VIM */
    volatile uint32_t ulIRQChannelIndex = portVIM_IRQ_INDEX;
    volatile ISRFunction_t xIRQFncPtr = portVIM_IRQ_VEC_REG;

    /* Setup Bit Mask Clear Values */
    volatile uint32_t ulPendingIRQMask;

    volatile uint32_t ulPendISRReg0 = vimREG->REQMASKCLR0;
    volatile uint32_t ulPendISRReg1 = vimREG->REQMASKCLR1;
    volatile uint32_t ulPendISRReg2 = vimREG->REQMASKCLR2;
    volatile uint32_t ulPendISRReg3 = vimREG->REQMASKCLR3;

    if( NULL == xIRQFncPtr )
    {
        sci_print( "Received a NULL Function Pointer from the IRQ VIM\r\n" );
        configASSERT( pdFALSE );
    }
    else
    {
        if( 0U != ulIRQChannelIndex )
        {
            ulIRQChannelIndex--;
        }

        if( ulIRQChannelIndex <= 31U )
        {
            ulPendingIRQMask = 0xFFFFFFFFU << ulIRQChannelIndex;
            vimREG->REQMASKCLR0 = ulPendingIRQMask;
            vimREG->REQMASKCLR1 = 0xFFFFFFFFU;
            vimREG->REQMASKCLR2 = 0xFFFFFFFFU;
            vimREG->REQMASKCLR3 = 0xFFFFFFFFU;
        }
        else if( ulIRQChannelIndex <= 63U )
        {
            ulPendingIRQMask = 0xFFFFFFFFU << ( ulIRQChannelIndex - 32U );
            vimREG->REQMASKCLR1 = ulPendingIRQMask;
            vimREG->REQMASKCLR2 = 0xFFFFFFFFU;
            vimREG->REQMASKCLR3 = 0xFFFFFFFFU;
        }
        else if( ulIRQChannelIndex <= 95U )
        {
            ulPendingIRQMask = 0xFFFFFFFFU << ( ulIRQChannelIndex - 64U );
            vimREG->REQMASKCLR2 = ulPendingIRQMask;
            vimREG->REQMASKCLR3 = 0xFFFFFFFFU;
        }
        else
        {
            ulPendingIRQMask = 0xFFFFFFFFU << ( ulIRQChannelIndex - 96U );
            vimREG->REQMASKCLR3 = ulPendingIRQMask;
        }
    }
    /*
     * Channel 0 is the ESM handler, treat this as a special case.
     * phantomInterrupt()
     * Keep interrupts disabled, this function does not return
     */

    if( 0UL == ulIRQChannelIndex )
    {
        sci_print( "Phantom interrupt?\r\n" );
        configASSERT( pdFALSE );
        ( *xIRQFncPtr )();
    }
    else if( ( phantomInterrupt == xIRQFncPtr ) )
    {
        sci_print( "IRQ With no registered function in sys_vim.c has been raised\r\n" );
        configASSERT( pdFALSE );
    }
    else
    {
        /* Information about the mapping of Interrupts in the VIM to their
         * causes can be found in the RM48L852 Data Sheet:
         * https://www.ti.com/lit/ds/symlink/rm46l852.pdf?ts=1704878833799 */
        /* An IRQ Raised by Channel Two of the VIM is RTI Compare Interrupt 0. */
        if( 2UL == ulIRQChannelIndex )
        {
            /* This is the System Tick Timer Interrupt */
            ulPortYieldRequired = xTaskIncrementTick();
            /* Acknowledge the System Tick Timer Interrupt */
            portRTI_INTFLAG_REG = 0x1UL;
        }
        /* An IRQ Raised by Channel 21 of the VIM is a Software Interrupt (SSI). */
        else if( 21UL == ulIRQChannelIndex )
        {
#if( mainDEMO_TYPE & IRQ_DEMO )
            /* This is an interrupt raised by Software */
            vIRQDemoHandler();
#else
            sci_print( "SWI of unknown cause was raised!\r\n" );
            configASSERT( 0x0 );
#endif

            /* Register read is needed to mark the end of the IRQ */
            volatile uint32_t ulEndOfIntRegVal = *portEND_OF_INTERRUPT_REG;
            *portEND_OF_INTERRUPT_REG = ulEndOfIntRegVal;
        }
        else
        {
            sci_print( "Unmapped IRQ Channel Number Raised\r\n" );
        }
    }

    vimREG->REQMASKSET0 = ulPendISRReg0;
    vimREG->REQMASKSET1 = ulPendISRReg1;
    vimREG->REQMASKSET2 = ulPendISRReg2;
    vimREG->REQMASKSET3 = ulPendISRReg3;
}
/*---------------------------------------------------------------------------*/

void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    uint32_t * pulIdleTaskStackSize )
{
    /* Pass out a pointer to the StaticTask_t structure in which the Idle
     * task's state will be stored. */
    *ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

    /* Pass out the array that will be used as the Idle task's stack. */
    *ppxIdleTaskStackBuffer = uxIdleTaskStack;

    /* Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
     * Note that, as the array is necessarily of type StackType_t,
     * configMINIMAL_STACK_SIZE is specified in words, not bytes. */
    *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}
/*---------------------------------------------------------------------------*/

void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                     StackType_t ** ppxTimerTaskStackBuffer,
                                     uint32_t * pulTimerTaskStackSize )
{
    /* Pass out a pointer to the StaticTask_t structure in which the Timer
     * task's state will be stored. */
    *ppxTimerTaskTCBBuffer = &xTimerTaskTCB;

    /* Pass out the array that will be used as the Timer task's stack. */
    *ppxTimerTaskStackBuffer = uxTimerTaskStack;

    /* Pass out the size of the array pointed to by *ppxTimerTaskStackBuffer.
     * Note that, as the array is necessarily of type StackType_t,
     * configMINIMAL_STACK_SIZE is specified in words, not bytes. */
    *pulTimerTaskStackSize = configMINIMAL_STACK_SIZE;
}
/*---------------------------------------------------------------------------*/
