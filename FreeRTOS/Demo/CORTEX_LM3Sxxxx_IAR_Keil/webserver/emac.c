/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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
#include "semphr.h"
#include "task.h"

/* Demo includes. */
#include "emac.h"

/* uIP includes. */
#include "uip.h"

/* Hardware library includes. */
#include "hw_types.h"
#include "hw_memmap.h"
#include "hw_ints.h"
#include "hw_ethernet.h"
#include "ethernet.h"
#include "interrupt.h"

#define emacNUM_RX_BUFFERS		5
#define emacFRAM_SIZE_BYTES 	2
#define macNEGOTIATE_DELAY 		2000
#define macWAIT_SEND_TIME		( 10 )

/* The task that handles the MAC peripheral.  This is created at a high
priority and is effectively a deferred interrupt handler.  The peripheral
handling is deferred to a task to prevent the entire FIFO having to be read
from within an ISR. */
void vMACHandleTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The semaphore used to wake the uIP task when data arrives. */
SemaphoreHandle_t xEMACSemaphore = NULL;

/* The semaphore used to wake the interrupt handler task.  The peripheral
is processed at the task level to prevent the need to read the entire FIFO from
within the ISR itself. */
SemaphoreHandle_t xMACInterruptSemaphore = NULL;

/* The buffer used by the uIP stack.  In this case the pointer is used to
point to one of the Rx buffers. */
unsigned char *uip_buf;

/* Buffers into which Rx data is placed. */
static union
{
	unsigned long ulJustForAlignment;
	unsigned char ucRxBuffers[ emacNUM_RX_BUFFERS ][ UIP_BUFSIZE + ( 4 * emacFRAM_SIZE_BYTES ) ];
} uxRxBuffers;

/* The length of the data within each of the Rx buffers. */
static unsigned long ulRxLength[ emacNUM_RX_BUFFERS ];

/* Used to keep a track of the number of bytes to transmit. */
static unsigned long ulNextTxSpace;

/*-----------------------------------------------------------*/

portBASE_TYPE vInitEMAC( void )
{
unsigned long ulTemp;
portBASE_TYPE xReturn;

	/* Ensure all interrupts are disabled. */
	EthernetIntDisable( ETH_BASE, ( ETH_INT_PHY | ETH_INT_MDIO | ETH_INT_RXER | ETH_INT_RXOF | ETH_INT_TX | ETH_INT_TXER | ETH_INT_RX));

	/* Clear any interrupts that were already pending. */
    ulTemp = EthernetIntStatus( ETH_BASE, pdFALSE );
    EthernetIntClear( ETH_BASE, ulTemp );

	/* Initialise the MAC and connect. */
    EthernetInit( ETH_BASE );
    EthernetConfigSet( ETH_BASE, ( ETH_CFG_TX_DPLXEN | ETH_CFG_TX_CRCEN | ETH_CFG_TX_PADEN ) );
    EthernetEnable( ETH_BASE );

	/* Mark each Rx buffer as empty. */
	for( ulTemp = 0; ulTemp < emacNUM_RX_BUFFERS; ulTemp++ )
	{
		ulRxLength[ ulTemp ] = 0;
	}

	/* Create the queue and task used to defer the MAC processing to the
	task level. */
	vSemaphoreCreateBinary( xMACInterruptSemaphore );
	xSemaphoreTake( xMACInterruptSemaphore, 0 );
	xReturn = xTaskCreate( vMACHandleTask, "MAC", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, NULL );
	vTaskDelay( macNEGOTIATE_DELAY );

	/* We are only interested in Rx interrupts. */
	IntPrioritySet( INT_ETH, configKERNEL_INTERRUPT_PRIORITY );
    IntEnable( INT_ETH );
    EthernetIntEnable(ETH_BASE, ETH_INT_RX);

	return xReturn;
}
/*-----------------------------------------------------------*/

unsigned int uiGetEMACRxData( unsigned char *ucBuffer )
{
static unsigned long ulNextRxBuffer = 0;
unsigned int iLen;

	iLen = ulRxLength[ ulNextRxBuffer ];

	if( iLen != 0 )
	{
		/* Leave room for the size at the start of the buffer. */
		uip_buf = &( uxRxBuffers.ucRxBuffers[ ulNextRxBuffer ][ 2 ] );

		ulRxLength[ ulNextRxBuffer ] = 0;

		ulNextRxBuffer++;
		if( ulNextRxBuffer >= emacNUM_RX_BUFFERS )
		{
			ulNextRxBuffer = 0;
		}
	}

    return iLen;
}
/*-----------------------------------------------------------*/

void vInitialiseSend( void )
{
	/* Set the index to the first byte to send - skipping over the size
	bytes. */
	ulNextTxSpace = 2;
}
/*-----------------------------------------------------------*/

void vIncrementTxLength( unsigned long ulLength )
{
	ulNextTxSpace += ulLength;
}
/*-----------------------------------------------------------*/

void vSendBufferToMAC( void )
{
unsigned long *pulSource;
unsigned short * pus;
unsigned long ulNextWord;

	/* Locate the data to be send. */
	pus = ( unsigned short * ) uip_buf;

	/* Add in the size of the data. */
	pus--;
	*pus = ulNextTxSpace;

	/* Wait for data to be sent if there is no space immediately. */
    while( !EthernetSpaceAvail( ETH_BASE ) )
    {
		vTaskDelay( macWAIT_SEND_TIME );
    }

	pulSource = ( unsigned long * ) pus;

	for( ulNextWord = 0; ulNextWord < ulNextTxSpace; ulNextWord += sizeof( unsigned long ) )
	{
       	HWREG(ETH_BASE + MAC_O_DATA) = *pulSource;
		pulSource++;
	}

	/* Go. */
    HWREG( ETH_BASE + MAC_O_TR ) = MAC_TR_NEWTX;
}
/*-----------------------------------------------------------*/

void vEMAC_ISR( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
unsigned long ulTemp;

	/* Clear the interrupt. */
	ulTemp = EthernetIntStatus( ETH_BASE, pdFALSE );
	EthernetIntClear( ETH_BASE, ulTemp );

	/* Was it an Rx interrupt? */
	if( ulTemp & ETH_INT_RX )
	{
		xSemaphoreGiveFromISR( xMACInterruptSemaphore, &xHigherPriorityTaskWoken );
		EthernetIntDisable( ETH_BASE, ETH_INT_RX );
	}

    /* Switch to the uIP task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void vMACHandleTask( void *pvParameters )
{
unsigned long i, ulInt;
unsigned long ulLength;
unsigned long *pulBuffer;
static unsigned long ulNextRxBuffer = 0;

	for( ;; )
	{
		/* Wait for something to do. */
		xSemaphoreTake( xMACInterruptSemaphore, portMAX_DELAY );

		while( ( ulInt = ( EthernetIntStatus( ETH_BASE, pdFALSE ) & ETH_INT_RX ) ) != 0 )
		{
			ulLength = HWREG( ETH_BASE + MAC_O_DATA );

			/* Leave room at the start of the buffer for the size. */
			pulBuffer = ( unsigned long * ) &( uxRxBuffers.ucRxBuffers[ ulNextRxBuffer ][ 2 ] );
			*pulBuffer = ( ulLength >> 16 );

			/* Get the size of the data. */
			pulBuffer = ( unsigned long * ) &( uxRxBuffers.ucRxBuffers[ ulNextRxBuffer ][ 4 ] );
			ulLength &= 0xFFFF;

			if( ulLength > 4 )
			{
				ulLength -= 4;

				if( ulLength >= UIP_BUFSIZE )
				{
					/* The data won't fit in our buffer.  Ensure we don't
					try to write into the buffer. */
					ulLength = 0;
				}

				/* Read out the data into our buffer. */
				for( i = 0; i < ulLength; i += sizeof( unsigned long ) )
				{
					*pulBuffer = HWREG( ETH_BASE + MAC_O_DATA );
					pulBuffer++;
				}

				/* Store the length of the data into the separate array. */
				ulRxLength[ ulNextRxBuffer ] = ulLength;

				/* Use the next buffer the next time through. */
				ulNextRxBuffer++;
				if( ulNextRxBuffer >= emacNUM_RX_BUFFERS )
				{
					ulNextRxBuffer = 0;
				}

				/* Ensure the uIP task is not blocked as data has arrived. */
				xSemaphoreGive( xEMACSemaphore );
			}
		}

		EthernetIntEnable( ETH_BASE, ETH_INT_RX );

		( void ) ulInt;
	}
}

