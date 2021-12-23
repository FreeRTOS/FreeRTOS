/*
 * FreeRTOS V202112.00
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/*
 * This demo demonstrates the best practice of deferring majority of the
 * interrupt processing work from IRQ handlers to an unprivileged task. IRQ
 * handlers execute in privileged mode and therefore, have access to all the
 * memories. Keeping the IRQ handlers small and deferring most of the work to
 * unprivileged task provides better security.
 *
 * This demo creates a queue, known as interrupt queue. IRQ handlers post
 * requests to this queue which are later served by an unprivileged interrupt
 * handler task.
 *
 *                   +-------------------------+
 *        +--------->+    Interrupt Queue      +------------+
 *        |          +-------------------------+            |
 *        |                                                 | Fetch and Serve
 *   Post |                                                 |
 *        |                                                 v
 *        |                                          +------+--------+
 * +------+--------+                                 |               |
 * |  IRQ Handler  |                                 |               |
 * |  (Privileged) |                                 |   Interrupt   |
 * +---------------+                                 |    Handler    |
 *                                                   |     Task      |
 *                                                   | (Unprivileged)|
 *                                                   |               |
 *                                                   |               |
 *                                                   +---------------+
 *
 * This demo show-cases the following 2 demos:
 * 1. LED Demo -  The LED demo creates a task which periodically toggles the on
 *                board RGB LED. Whenever user presses the USER button, the
 *                user button pressed IRQ handler changes the color of the LED.
 *                The user button pressed IRQ handler posts a request to the
 *                interrupt queue and task of changing the LED color is deferred
 *                to the unprivileged handler.
 * 2. UART Demo - The UART demo creates a task which prints a command menu on
 *                the serial console and then waits for the user input. Whenever
 *                user enters any input on the serial console to run a command,
 *                the UART received IRQ handler handles it and prints the
 *                appropriate response on the serial console. The UART received
 *                IRQ handler posts a request to the interrupt queue and task of
 *                handling the command and providing the response is deferred
 *                to the unprivileged handler.
 */

/* FreeRTOS kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* BSP includes. */
#include "board.h"
#include "clock_config.h"
#include "fsl_debug_console.h"
#include "fsl_device_registers.h"
#include "fsl_inputmux.h"
#include "fsl_power.h"
#include "fsl_pint.h"
#include "fsl_usart.h"
#include "pin_mux.h"

/* Demo includes. */
#include "led_demo.h"
#include "uart_demo.h"
#include "interrupt_handler_task.h"

/**
 * @brief Length of the interrupt queue.
 */
#define USER_IRQ_QUEUE_LEN          8
#define USER_IRQ_QUEUE_BUF_SIZE     ( sizeof( UserIrqRequest_t ) * USER_IRQ_QUEUE_LEN )

/**
 * @brief UART_MEM_START to (UART_MEM_START + UART_MEM_LEN) cover the range
 * used by USART_WriteBlocking().
 */
#define UART_MEM_START              ( USART0 )
#define UART_MEM_LEN                ( 3648 )

/**
 * @brief GPIO_MEM_START to (GPIO_MEM_START + GPIO_MEM_LEN) covers the range
 * used for setting and clearing GPIO pins.
 */
#define GPIO_MEM_START              ( 0x4008E200u )
#define GPIO_MEM_LEN                ( 256 )

/**
 * @brief Handle and storage for the interrupt queue shared between IRQ handlers
 * and the interrupt handler task.
 */
static QueueHandle_t xUserIrqQueueHandle;
static StaticQueue_t xStaticQueue;
static uint8_t ucQueueBuffer[ USER_IRQ_QUEUE_BUF_SIZE ];
/*-----------------------------------------------------------*/

/**
 * @brief Initialize hardware.
 */
static void prvInitializeHardware( void );

/**
 * @brief Initialize user button pressed interrupt.
 */
static void prvInitializeUserButtonInterrupt( void );

/**
 * @brief Initialize UART received interrupt.
 */
static void prvInitializeUartReceivedInterrupt( void );

/**
 * @brief Handler for pin interrupt when USER button is pressed.
 *
 * The handler enqueues a user IRQ request for the IRQ to be further processed
 * in the unprivileged interrupt handler.
 */
static void userButtonPressedHandler( pint_pin_int_t xInterruptType, uint32_t ulMatchStatus );

/**
 * @brief Handler for UART interrupt when UART data is received.
 *
 * The handler enqueues a user IRQ request for the IRQ to be further processed
 * in the unprivileged interrupt handler.
 */
void FLEXCOMM0_IRQHandler( void );

/**
 * @brief Create the demo tasks.
 */
static void prvCreateDemoTasks( void );
/*-----------------------------------------------------------*/

static void prvInitializeHardware( void )
{
    /* Set BOD VBAT level to 1.65V. */
    POWER_SetBodVbatLevel( kPOWER_BodVbatLevel1650mv, kPOWER_BodHystLevel50mv, false );

    /* Attach main clock divide to FLEXCOMM0 (debug console). */
    CLOCK_AttachClk( BOARD_DEBUG_UART_CLK_ATTACH );

    /* Board initialization. */
    BOARD_InitBootPins();
    BOARD_InitBootClocks();
    BOARD_InitDebugConsole();
}
/*-----------------------------------------------------------*/

static void prvInitializeUserButtonInterrupt( void )
{
    /* Connect trigger sources to PINT. */
    INPUTMUX_Init( INPUTMUX );
    INPUTMUX_AttachSignal( INPUTMUX, kPINT_PinInt0, kINPUTMUX_GpioPort1Pin9ToPintsel );

    /* Turnoff clock to inputmux to save power. Clock is only needed to make changes. */
    INPUTMUX_Deinit( INPUTMUX );

    /* Initialize PINT. */
    PINT_Init( PINT );

    /* Setup Pin Interrupt 0 for rising edge. */
    PINT_PinInterruptConfig( PINT, kPINT_PinInt0, kPINT_PinIntEnableRiseEdge, userButtonPressedHandler );

    /* Enable callback for PINT0 by Index. */
    PINT_EnableCallbackByIndex( PINT, kPINT_PinInt0 );
}
/*-----------------------------------------------------------*/

static void prvInitializeUartReceivedInterrupt( void )
{
    usart_config_t config;
    USART_GetDefaultConfig( &( config ) );
    config.enableTx = true;
    config.enableRx = true;
    USART_Init( USART0, &( config ), CLOCK_GetFlexCommClkFreq( 0U ) );

    /* Enable RX interrupt. */
    USART_EnableInterrupts( USART0, kUSART_RxLevelInterruptEnable | kUSART_RxErrorInterruptEnable );
    EnableIRQ( FLEXCOMM0_IRQn );
}
/*-----------------------------------------------------------*/

static void userButtonPressedHandler( pint_pin_int_t xInterruptType, uint32_t ulMatchStatus )
{
    UserIrqRequest_t xIrqRequest;
    BaseType_t xHigherPriorityTaskWoken;

    /* Silence warnings about unused variables. */
    ( void ) xInterruptType;
    ( void ) ulMatchStatus;

    /* We have not woken a task at the start of the ISR. */
    xHigherPriorityTaskWoken = pdFALSE;

    /* Enqueue a request to user IRQ queue to be processed in the unprivileged
     * interrupt handler. */
    xIrqRequest.xHandlerFunction = vButtonPressedIRQHandler;
    xIrqRequest.ulData = 0; /* Not used. */
    xQueueSendFromISR( xUserIrqQueueHandle, &( xIrqRequest ), &( xHigherPriorityTaskWoken ) );

    /* Posting the above request might have unblocked the interrupt handler task.
     * Make sure to return to the interrupt handler task in case it was not already
     * running. */
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

/* Override weak definition of FLEXCOMM0_IRQHandler */
void FLEXCOMM0_IRQHandler(void)
{
    UserIrqRequest_t xIrqRequest;
    BaseType_t xHigherPriorityTaskWoken;

    /* We have not woken a task at the start of the ISR. */
    xHigherPriorityTaskWoken = pdFALSE;

    /* If new data arrived. */
    if( ( kUSART_RxFifoNotEmptyFlag | kUSART_RxError ) & USART_GetStatusFlags( USART0 ) )
    {
        /* Enqueue a request to user IRQ queue to be processed in the unprivileged
         * interrupt handler. */
        xIrqRequest.xHandlerFunction = vUartDataReceivedIRQHandler;
        xIrqRequest.ulData = ( uint32_t ) USART_ReadByte( USART0 );
        xQueueSendFromISR( xUserIrqQueueHandle, &( xIrqRequest ), &( xHigherPriorityTaskWoken ) );
    }

    /* Posting the above request might have unblocked the interrupt handler task.
     * Make sure to return to the interrupt handler task in case it was not already
     * running. */
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvCreateDemoTasks( void )
{
    static StackType_t xInterruptHandlerTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
    static StackType_t xLedDemoTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
    static StackType_t xUartDemoTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );

    extern TaskHandle_t xUartDemoTaskHandle;
    extern uint32_t __user_irq_shared_memory_start__[];
    extern uint32_t __user_irq_shared_memory_end__[];
    uint32_t ulSharedMemoryLength = ( uint32_t )__user_irq_shared_memory_end__ - ( uint32_t )__user_irq_shared_memory_start__ + 1;

    /* The interrupt handler task needs access to UART memory region too as we
     * write the response to UART from the interrupt handler in the UART demo. */
    TaskParameters_t xInterruptHandlerTaskParameters =
    {
        .pvTaskCode     = vInterruptHandlerTask,
        .pcName         = "InterruptHandlerTask",
        .usStackDepth   = configMINIMAL_STACK_SIZE,
        .pvParameters   = xUserIrqQueueHandle,
        .uxPriority     = configMAX_PRIORITIES - 1, /* Run the interrupt handler task at the highest priority. */
        .puxStackBuffer = xInterruptHandlerTaskStack,
        .xRegions       =
        {
            { __user_irq_shared_memory_start__, ulSharedMemoryLength, tskMPU_REGION_READ_WRITE | tskMPU_REGION_EXECUTE_NEVER },
            { ( void * ) UART_MEM_START,        UART_MEM_LEN,         tskMPU_REGION_READ_WRITE | tskMPU_REGION_EXECUTE_NEVER },
            { 0,                                0,                    0                                                      },
        }
    };
    TaskParameters_t xLedDemoTaskParameters =
    {
        .pvTaskCode     = vLedDemoTask,
        .pcName         = "LedDemoTask",
        .usStackDepth   = configMINIMAL_STACK_SIZE,
        .pvParameters   = NULL,
        .uxPriority     = tskIDLE_PRIORITY,
        .puxStackBuffer = xLedDemoTaskStack,
        .xRegions       =
        {
            { __user_irq_shared_memory_start__, ulSharedMemoryLength, tskMPU_REGION_READ_WRITE | tskMPU_REGION_EXECUTE_NEVER },
            { ( void * ) GPIO_MEM_START,        GPIO_MEM_LEN,         tskMPU_REGION_READ_WRITE | tskMPU_REGION_EXECUTE_NEVER },
            { 0,                                0,                    0                                                      },
        }
    };
    TaskParameters_t xUartDemoTaskParameters =
    {
        .pvTaskCode     = vUartDemoTask,
        .pcName         = "UartDemoTask",
        .usStackDepth   = configMINIMAL_STACK_SIZE,
        .pvParameters   = NULL,
        .uxPriority     = tskIDLE_PRIORITY,
        .puxStackBuffer = xUartDemoTaskStack,
        .xRegions       =
        {
            { __user_irq_shared_memory_start__, ulSharedMemoryLength, tskMPU_REGION_READ_WRITE | tskMPU_REGION_EXECUTE_NEVER },
            { ( void * ) UART_MEM_START,        UART_MEM_LEN,         tskMPU_REGION_READ_WRITE | tskMPU_REGION_EXECUTE_NEVER },
            { 0,                                0,                    0                                                      },
        }
    };

    xTaskCreateRestricted( &( xInterruptHandlerTaskParameters ), NULL );
    xTaskCreateRestricted( &( xLedDemoTaskParameters ), NULL );
    xTaskCreateRestricted( &( xUartDemoTaskParameters ), &( xUartDemoTaskHandle ) );
}
/*-----------------------------------------------------------*/

/**
 * @brief Entry point.
 */
int main( void )
{
    /* Initialize board hardware. */
    prvInitializeHardware();

    /* Create the interrupt queue for deferring work from ISRs to the
     * unprivileged interrupt handler task. */
    xUserIrqQueueHandle = xQueueCreateStatic( USER_IRQ_QUEUE_LEN,
                                              sizeof( UserIrqRequest_t ),
                                              ucQueueBuffer,
                                              &( xStaticQueue ) );

    prvCreateDemoTasks();
    prvInitializeUserButtonInterrupt();
    prvInitializeUartReceivedInterrupt();

    vTaskStartScheduler();

    /* Should never reach here. */
    for( ; ; );
}
/*-----------------------------------------------------------*/

/* Stack overflow hook. */
void vApplicationStackOverflowHook( TaskHandle_t xTask, char *pcTaskName )
{
    /* Force an assert. */
    configASSERT( pcTaskName == 0 );
}
/*-----------------------------------------------------------*/

/* configUSE_STATIC_ALLOCATION is set to 1, so the application must provide an
 * implementation of vApplicationGetIdleTaskMemory() to provide the memory that
 * is used by the Idle task. */
void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    uint32_t * pulIdleTaskStackSize )
{
    /* If the buffers to be provided to the Idle task are declared inside this
     * function then they must be declared static - otherwise they will be
     * allocated on the stack and so not exists after this function exits. */
    static StaticTask_t xIdleTaskTCB;
    static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );

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
/*-----------------------------------------------------------*/

/* configUSE_STATIC_ALLOCATION and configUSE_TIMERS are both set to 1, so the
 * application must provide an implementation of vApplicationGetTimerTaskMemory()
 * to provide the memory that is used by the Timer service task. */
void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                     StackType_t ** ppxTimerTaskStackBuffer,
                                     uint32_t * pulTimerTaskStackSize )
{
    /* If the buffers to be provided to the Timer task are declared inside this
     * function then they must be declared static - otherwise they will be
     * allocated on the stack and so not exists after this function exits. */
    static StaticTask_t xTimerTaskTCB;
    static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ] __attribute__( ( aligned( 32 ) ) );

    /* Pass out a pointer to the StaticTask_t structure in which the Timer
     * task's state will be stored. */
    *ppxTimerTaskTCBBuffer = &xTimerTaskTCB;

    /* Pass out the array that will be used as the Timer task's stack. */
    *ppxTimerTaskStackBuffer = uxTimerTaskStack;

    /* Pass out the size of the array pointed to by *ppxTimerTaskStackBuffer.
     * Note that, as the array is necessarily of type StackType_t,
     * configTIMER_TASK_STACK_DEPTH is specified in words, not bytes. */
    *pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}
/*-----------------------------------------------------------*/
