/*
 * FreeRTOS Kernel V10.3.1
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
#include <avr/interrupt.h>
#include "usart.h"

#define RX_BUFFER_SIZE 128
#define TX_BUFFER_SIZE 128

static uint8_t rxbuf[RX_BUFFER_SIZE];
static uint8_t txbuf[TX_BUFFER_SIZE];

xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
    portENTER_CRITICAL();
    {
        USART_initialize(rxbuf, RX_BUFFER_SIZE, txbuf, TX_BUFFER_SIZE, ulWantedBaud);
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
    volatile TickType_t currentTick;
    
    currentTick = xTaskGetTickCount();
    
    while(((xTaskGetTickCount() - currentTick) < xBlockTime) && !(USART_isRxReady()))
    {
        vTaskDelay(1);
    };

    if (USART_isRxReady())
    {
        *pcRxedChar = USART_read();
        return pdTRUE;
    }
    return pdFALSE;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
    volatile TickType_t currentTick;
    
    currentTick = xTaskGetTickCount();
    
    while(((xTaskGetTickCount() - currentTick) < xBlockTime) && !(USART_isTxReady()))
    {
        vTaskDelay(1);
    };
    if (USART_isTxReady())
    {
        USART_write( cOutChar);
        return pdTRUE;
    }
    /* Return false if after the block time there is no room on the Tx buffer. */
    return pdFALSE;
}
/*-----------------------------------------------------------*/

void vSerialPutString(xComPortHandle pxPort, const signed char * const pcBuffer, unsigned short xBufferLength )
{
    size_t cByteToSend;
    
    for( cByteToSend = 0; cByteToSend < xBufferLength; cByteToSend++ )
    {
        xSerialPutChar(pxPort, pcBuffer[cByteToSend], portMAX_DELAY);
    }
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
    /* Turn off the interrupts.  We may also want to delete the queues and/or
    re-install the original ISR. */

    portENTER_CRITICAL();
    {      
        USART_close();
    }
    portEXIT_CRITICAL();
}
