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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo program includes. */
#include "serial.h"

/* Renesas includes. */
#include "platform.h"
#include "r_dtc_rx_if.h"
#include "r_sci_rx_if.h"
#include "r_byteq_if.h"

/* Eval board specific definitions. */
#include "demo_specific_io.h"

/* Characters received from the UART are stored in this queue, ready to be
received by the application.  ***NOTE*** Using a queue in this way is very
convenient, but also very inefficient.  It can be used here because characters
will only arrive slowly.  In a higher bandwidth system a circular RAM buffer or
DMA should be used in place of this queue. */
static QueueHandle_t xRxQueue = NULL;

/* When a task calls vSerialPutString() its handle is stored in xSendingTask,
before being placed into the Blocked state (so does not use any CPU time) to
wait for the transmission to end.  The task handle is then used from the UART
transmit end interrupt to remove the task from the Blocked state. */
static TaskHandle_t xSendingTask = NULL;

/* Callback function which is called from Renesas API's interrupt service routine. */
void vSerialSciCallback( void *pvArgs )
{
sci_cb_args_t *pxArgs = (sci_cb_args_t *)pvArgs;

    /* Renesas API has a built-in queue but we will ignore it.  If the queue is not
    full, a received character is passed with SCI_EVT_RX_CHAR event.  If the queue 
    is full, a received character is passed with SCI_EVT_RXBUF_OVFL event. */
    if( SCI_EVT_RX_CHAR == pxArgs->event || SCI_EVT_RXBUF_OVFL == pxArgs->event )
    {
        BaseType_t xHigherPriorityTaskWoken = pdFALSE;

        configASSERT( xRxQueue );

        /* Characters received from the UART are stored in this queue, ready to be
        received by the application.  ***NOTE*** Using a queue in this way is very
        convenient, but also very inefficient.  It can be used here because
        characters will only arrive slowly.  In a higher bandwidth system a circular
        RAM buffer or DMA should be used in place of this queue. */
        xQueueSendFromISR( xRxQueue, &pxArgs->byte, &xHigherPriorityTaskWoken );

        /* See http://www.freertos.org/xQueueOverwriteFromISR.html for information
        on the semantics of this ISR. */
        portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
    }
    /* Renesas API notifies the completion of transmission by SCI_EVT_TEI event. */
    else if( SCI_EVT_TEI == pxArgs->event )
    {
        BaseType_t xHigherPriorityTaskWoken = pdFALSE;

        if( xSendingTask != NULL )
        {
            /* A task is waiting for the end of the Tx, unblock it now.
            http://www.freertos.org/vTaskNotifyGiveFromISR.html */
            vTaskNotifyGiveFromISR( xSendingTask, &xHigherPriorityTaskWoken );
            xSendingTask = NULL;

            portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
        }
    }
}

/* Function required in order to link UARTCommandConsole.c - which is used by
multiple different demo application. */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
    ( void ) ulWantedBaud;
    ( void ) uxQueueLength;

    /* Characters received from the UART are stored in this queue, ready to be
    received by the application.  ***NOTE*** Using a queue in this way is very
    convenient, but also very inefficient.  It can be used here because
    characters will only arrive slowly.  In a higher bandwidth system a circular
    RAM buffer or DMA should be used in place of this queue. */
    xRxQueue = xQueueCreate( uxQueueLength, sizeof( char ) );
    configASSERT( xRxQueue );

    /* Set interrupt priority. (Other UART settings had been initialized in the
    src/smc_gen/general/r_cg_hardware_setup.c.) */
    uint8_t ucInterruptPriority = configMAX_SYSCALL_INTERRUPT_PRIORITY - 1;
    R_SCI_Control( xSerialSciHandle, SCI_CMD_SET_RXI_PRIORITY, ( void * ) &ucInterruptPriority );
    R_SCI_Control( xSerialSciHandle, SCI_CMD_SET_TXI_PRIORITY, ( void * ) &ucInterruptPriority );

    /* Only one UART is supported, so it doesn't matter what is returned
    here. */
    return 0;
}

/* Function required in order to link UARTCommandConsole.c - which is used by
multiple different demo application. */
void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
const TickType_t xMaxBlockTime = pdMS_TO_TICKS( 5000 );

    /* Only one port is supported. */
    ( void ) pxPort;

    /* Don't send the string unless the previous string has been sent. */
    if( ( xSendingTask == NULL ) && ( usStringLength > 0 ) )
    {
        /* Ensure the calling task's notification state is not already
        pending. */
        xTaskNotifyStateClear( NULL );

        /* Store the handle of the transmitting task.  This is used to unblock
        the task when the transmission has completed. */
        xSendingTask = xTaskGetCurrentTaskHandle();

        /* Send the string using the Renesas API with a workaround. */
        if( usStringLength > 1 )
        {
            /* Set up Data Transfer Control. */
            dtc_cmd_arg_t xSerialTxDtcArg;
            dtc_transfer_data_cfg_t xSerialTxDtcConfig;

            xSerialTxDtcArg.act_src                   = U_DTC_UART_CLI_TX_ACT;
            xSerialTxDtcConfig.transfer_mode          = DTC_TRANSFER_MODE_NORMAL;
            xSerialTxDtcConfig.data_size              = DTC_DATA_SIZE_BYTE;
            xSerialTxDtcConfig.src_addr_mode          = DTC_SRC_ADDR_INCR;
            xSerialTxDtcConfig.dest_addr_mode         = DTC_DES_ADDR_FIXED;
            xSerialTxDtcConfig.response_interrupt     = DTC_INTERRUPT_AFTER_ALL_COMPLETE;
            xSerialTxDtcConfig.repeat_block_side      = DTC_REPEAT_BLOCK_SOURCE;
            xSerialTxDtcConfig.chain_transfer_enable  = DTC_CHAIN_TRANSFER_DISABLE;
            xSerialTxDtcConfig.chain_transfer_mode    = (dtc_chain_transfer_mode_t)0;
            xSerialTxDtcConfig.source_addr            = ( uint32_t ) pcString;
            xSerialTxDtcConfig.dest_addr              = ( uint32_t ) &U_DTC_UART_CLI_TX_DR;
            xSerialTxDtcConfig.transfer_count         = ( uint32_t ) usStringLength - 1;
            xSerialTxDtcArg.chain_transfer_nr         = 0;
            xSerialTxDtcArg.p_transfer_data           = &xSerialTxDtcInfo;
            xSerialTxDtcArg.p_data_cfg                = &xSerialTxDtcConfig;

            R_DTC_Create( xSerialTxDtcArg.act_src, &xSerialTxDtcInfo, &xSerialTxDtcConfig, 0 );
            R_DTC_Control( DTC_CMD_ACT_SRC_ENABLE, NULL, &xSerialTxDtcArg );
            R_SCI_Send( xSerialSciHandle, ( uint8_t * ) (pcString + usStringLength - 1), 1 );
        }
        else
        {
            R_SCI_Send( xSerialSciHandle, ( uint8_t * ) pcString, 1 );
        }

        /* Wait in the Blocked state (so not using any CPU time) until the
        transmission has completed. */
        ulTaskNotifyTake( pdTRUE, xMaxBlockTime );

        /* A breakpoint can be set here for debugging. */
        nop();
    }
}

/* Function required in order to link UARTCommandConsole.c - which is used by
multiple different demo application. */
signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
    /* Only one UART is supported. */
    ( void ) pxPort;

    /* Return a received character, if any are available.  Otherwise block to
    wait for a character. */
    return xQueueReceive( xRxQueue, pcRxedChar, xBlockTime );
}

/* Function required in order to link UARTCommandConsole.c - which is used by
multiple different demo application. */
signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
    /* Just mapped to vSerialPutString() so the block time is not used. */
    ( void ) xBlockTime;

    vSerialPutString( pxPort, &cOutChar, sizeof( cOutChar ) );
    return pdPASS;
}
