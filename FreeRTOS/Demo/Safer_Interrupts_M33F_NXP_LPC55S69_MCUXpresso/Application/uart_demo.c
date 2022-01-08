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

/* Standard includes. */
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

#include "board.h"
#include "fsl_usart.h"

/* Demo interface include. */
#include "uart_demo.h"

/**
 * @brief The command menu presented to the user.
 */
#define UART_COMMAND_MENU           "\r\nChoose one of the following:\r\n" \
                                    "1. Get current tick count.\r\n"       \
                                    "2. Get number of tasks.\r\n"
#define UART_COMMAND_MENU_LEN       ( sizeof( UART_COMMAND_MENU ) - 1 )

/**
 * @brief Prompt for the user input.
 */
#define UART_PROMPT_STR             "> "
#define UART_PROMPT_STR_LEN         ( sizeof( UART_PROMPT_STR ) - 1 )

/**
 * @brief Valid commands entered by the user.
 */
#define GET_TICK_COUNT_COMMAND      49 /* ASCII code for char '1'. */
#define GET_NUM_TASKS_COMMAND       50 /* ASCII code for char '2'. */

/**
 * @brief Length of the buffer used for the response.
 */
#define UART_RESPONSE_BUF_LEN      ( 32 )
/*-----------------------------------------------------------*/

/* The following needs to be placed in the shared memory as it is accessed in
 * the UART received IRQ handler which is unprivileged. */
TaskHandle_t xUartDemoTaskHandle __attribute__( ( section( "user_irq_shared_memory" ) ) );
/*-----------------------------------------------------------*/

void vUartDemoTask( void * pvParams )
{
    /* Silence compiler warnings about unused variables. */
    ( void ) pvParams;

    for( ;; )
    {
        USART_WriteBlocking( USART0, UART_COMMAND_MENU, UART_COMMAND_MENU_LEN );
        USART_WriteBlocking( USART0, UART_PROMPT_STR, UART_PROMPT_STR_LEN );

        ulTaskNotifyTake( pdFALSE, portMAX_DELAY );
    }
}
/*-----------------------------------------------------------*/

void vUartDataReceivedIRQHandler( uint32_t ulData )
{
    char response[ UART_RESPONSE_BUF_LEN ];

    if( ulData == GET_TICK_COUNT_COMMAND )
    {
        TickType_t xTickCount = xTaskGetTickCount();
        snprintf( response, sizeof( response ), "%c\r\nTick Count: %u\r\n", ( char ) ulData, xTickCount );
    }
    else if( ulData == GET_NUM_TASKS_COMMAND )
    {
        UBaseType_t xTaskCount = uxTaskGetNumberOfTasks();
        snprintf( response, sizeof( response ), "%c\r\nTask Count: %u\r\n", ( char ) ulData, xTaskCount );
    }
    else
    {
        snprintf( response, sizeof( response ), "\r\nInvalid command: %c.\r\n", ( char ) ulData );
    }

    /* Print the response and unblock the UART demo task. */
    USART_WriteBlocking( USART0, response, strlen( response ) );
    xTaskNotifyGive( xUartDemoTaskHandle );
}
/*-----------------------------------------------------------*/
