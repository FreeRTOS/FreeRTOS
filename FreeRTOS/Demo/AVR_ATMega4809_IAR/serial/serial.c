/*
 * FreeRTOS V202012.00
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


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER FOR IAR AVR PORT. */

#include <stdlib.h>
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"
#include "serial.h"

#define USART_BAUD_RATE(BAUD_RATE) ((float)(configCPU_CLOCK_HZ * 64 / (16 * (float)BAUD_RATE)) + 0.5)
 
static QueueHandle_t xRxedChars;
static QueueHandle_t xCharsForTx;

#define vInterruptOn() USART3.CTRLA |= (1 << USART_DREIE_bp)

#define vInterruptOff() USART3.CTRLA &= ~(1 << USART_DREIE_bp)

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
    portENTER_CRITICAL();
    {
        /* Create the queues used by the com test task. */
        xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
        xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

        USART3.BAUD = (uint16_t)USART_BAUD_RATE(ulWantedBaud); /* set baud rate register */

        USART3.CTRLA = 1 << USART_LBME_bp       /* Loop-back Mode Enable: enabled */
                     | USART_RS485_OFF_gc       /* RS485 Mode disabled */
                     | 1 << USART_RXCIE_bp;     /* Receive Complete Interrupt Enable: enabled */

        USART3.CTRLB = 1 << USART_RXEN_bp       /* Reciever enable: enabled */
                     | USART_RXMODE_NORMAL_gc   /* Normal mode */
                     | 1 << USART_TXEN_bp;      /* Transmitter Enable: enabled */
    }
    
    portEXIT_CRITICAL();
    
    /* Unlike other ports, this serial code does not allow for more than one
    com port.  We therefore don't return a pointer to a port structure and can
    instead just return NULL. */
    return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
    /* Get the next character from the buffer.  Return false if no characters
    are available, or arrive before xBlockTime expires. */
    if( xQueueReceive( xRxedChars, pcRxedChar, xBlockTime ) )
    {
        return pdTRUE;
    }
    else
    {
        return pdFALSE;
    }
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
    /* Return false if after the block time there is no room on the Tx queue. */
    if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
    {
        return pdFAIL;
    }
    
    vInterruptOn();
    
    return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
    /* Turn off the interrupts.  We may also want to delete the queues and/or
    re-install the original ISR. */

    portENTER_CRITICAL();
    {
        vInterruptOff();
        USART3.CTRLB &= ~(1 << USART_RXEN_bp);
    }
    portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

__interrupt void USART3_RXC_handler(void)
{
signed char ucChar, xHigherPriorityTaskWoken = pdFALSE;

    /* Get the character and post it on the queue of Rxed characters.
    If the post causes a task to wake force a context switch as the woken task
    may have a higher priority than the task we have interrupted. */
    ucChar = USART3.RXDATAL;

    xQueueSendFromISR( xRxedChars, &ucChar, &xHigherPriorityTaskWoken );

    if( xHigherPriorityTaskWoken != pdFALSE )
    {
        portYIELD_FROM_ISR();
    }
        
}

__interrupt void USART3_DRE_handler(void)
{
signed char cChar, cTaskWoken = pdFALSE;

    if( xQueueReceiveFromISR( xCharsForTx, &cChar, &cTaskWoken ) == pdTRUE )
    {
        /* Send the next character queued for Tx. */
        USART3.TXDATAL = cChar;
    }
    else
    {
        /* Queue empty, nothing to send. */
        vInterruptOff();
    }
}
