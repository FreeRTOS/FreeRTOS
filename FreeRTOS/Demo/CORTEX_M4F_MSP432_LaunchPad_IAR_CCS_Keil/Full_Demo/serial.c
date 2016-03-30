/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
	BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER.

	Note1:  This driver is used specifically to provide an interface to the
	FreeRTOS+CLI command interpreter.  It is *not* intended to be a generic
	serial port driver.  Nor is it intended to be used as an example of an
	efficient implementation.  In particular, a queue is used to buffer
	received characters, which is fine in this case as key presses arrive
	slowly, but a DMA and/or RAM buffer should be used in place of the queue in
	applications that expect higher throughput.

	Note2:  This driver does not attempt to handle UART errors.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo application includes. */
#include "serial.h"

/*-----------------------------------------------------------*/

/*
 * The UART interrupt handler.
 */
void vUART_Handler( void );

/*-----------------------------------------------------------*/

/* The queue into which received key presses are placed.  NOTE THE COMMENTS AT
THE TOP OF THIS FILE REGARDING THE USE OF QUEUES FOR THIS PURPOSE. */
static QueueHandle_t xRxQueue = NULL;

/* Variables used in the Tx interrupt to send a string. */
static volatile const signed char *pcStringStart = NULL, *pcStringEnd = NULL;
static volatile TaskHandle_t xTransmittingTask = NULL;

static EUSCI_A_Type * const pxUARTA0 = ( EUSCI_A_Type * ) EUSCI_A0_BASE;

/* UART Configuration for 19200 baud.  Value generated using the tool provided
on the following page:
http://software-dl.ti.com/msp430/msp430_public_sw/mcu/msp430/MSP430BaudRateConverter/index.html
 */
const eUSCI_UART_Config xUARTConfig =
{
	EUSCI_A_UART_CLOCKSOURCE_SMCLK,	/* SMCLK Clock Source. */
	156,							/* BRDIV */
	4,								/* UCxBRF */
	0,								/* UCxBRS */
	EUSCI_A_UART_NO_PARITY,			/* No Parity. */
	EUSCI_A_UART_LSB_FIRST,			/* MSB First. */
	EUSCI_A_UART_ONE_STOP_BIT,		/* One stop bit. */
	EUSCI_A_UART_MODE,				/* UART mode. */
	EUSCI_A_UART_OVERSAMPLING_BAUDRATE_GENERATION /* Low Frequency Mode. */
};

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned long uxQueueLength )
{
	/* Create the queue used to hold received characters.  NOTE THE COMMENTS AT
	THE TOP OF THIS FILE REGARDING THE USE OF QUEUES FOR THIS PURPSOE. */
	xRxQueue = xQueueCreate( uxQueueLength, sizeof( char ) );
	configASSERT( xRxQueue );

	/* Use the library functions to initialise and enable the UART. */
	MAP_UART_initModule( EUSCI_A0_BASE, &xUARTConfig );
	MAP_UART_enableModule( EUSCI_A0_BASE );
	MAP_UART_clearInterruptFlag( EUSCI_A0_BASE, EUSCI_A_UART_RECEIVE_INTERRUPT | EUSCI_A_UART_TRANSMIT_INTERRUPT );
	MAP_UART_enableInterrupt( EUSCI_A0_BASE, EUSCI_A_UART_RECEIVE_INTERRUPT );

	/* The interrupt handler uses the FreeRTOS API function so its priority must
	be at or below the configured maximum system call interrupt priority.
	configKERNEL_INTERRUPT_PRIORITY is the priority used by the RTOS tick and
	(should) always be set to the minimum priority. */
	MAP_Interrupt_setPriority( INT_EUSCIA0, configKERNEL_INTERRUPT_PRIORITY );
	MAP_Interrupt_enableInterrupt( INT_EUSCIA0 );

	/* Only one UART is supported so the handle is not used. */
	return ( xComPortHandle ) 0;
}
/*-----------------------------------------------------------*/

BaseType_t xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
BaseType_t xReturn;

	/* Only a single port is supported. */
	( void ) pxPort;

	/* Obtain a received character from the queue - entering the Blocked state
	(so not consuming any processing time) to wait for a character if one is not
	already available. */
	xReturn = xQueueReceive( xRxQueue, pcRxedChar, xBlockTime );
	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
const TickType_t xMaxWaitTime = pdMS_TO_TICKS( 20UL * ( uint32_t ) usStringLength );

	/* Only a single port is supported. */
	( void ) pxPort;

	/* Note there is no mutual exclusion at the driver level.  If more than one
	task is using the serial port then mutual exclusion should be provided where
	this function is called. */

	/* Ensure notifications are not already waiting. */
	( void ) ulTaskNotifyTake( pdTRUE, 0 );

	/* Remember which task is sending the byte. */
	xTransmittingTask = xTaskGetCurrentTaskHandle();

	/* Mark the start and end of the data being sent. */
	pcStringStart = pcString;
	pcStringEnd = pcStringStart + usStringLength;

	/* Start to send the first byte. */
	pxUARTA0->TXBUF = ( uint_fast8_t ) *pcString;

	/* Enable the interrupt then wait for the byte to be sent.  The interrupt
	will be disabled again in the ISR. */
	MAP_UART_enableInterrupt( EUSCI_A0_BASE, EUSCI_A_UART_TRANSMIT_INTERRUPT );
	ulTaskNotifyTake( pdTRUE, xMaxWaitTime );
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
const TickType_t xMaxWaitTime = pdMS_TO_TICKS( 20UL );

	/* Only a single port is supported. */
	( void ) pxPort;

	/* Note there is no mutual exclusion at the driver level.  If more than one
	task is using the serial port then mutual exclusion should be provided where
	this function is called. */

	/* Ensure notifications are not already waiting. */
	( void ) ulTaskNotifyTake( pdTRUE, 0 );

	/* Remember which task is sending the byte. */
	xTransmittingTask = xTaskGetCurrentTaskHandle();

	/* Mark the start and end of the data being sent - in this case just a
	single byte. */
	pcStringStart = &cOutChar;
	pcStringEnd = pcStringStart + sizeof( cOutChar );

	/* Start to send the byte. */
	pxUARTA0->TXBUF = ( uint_fast8_t ) cOutChar;

	/* Enable the interrupt then wait for the byte to be sent.  The interrupt
	will be disabled again in the ISR. */
	MAP_UART_enableInterrupt( EUSCI_A0_BASE, EUSCI_A_UART_TRANSMIT_INTERRUPT );
	ulTaskNotifyTake( pdTRUE, xMaxWaitTime );

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose(xComPortHandle xPort)
{
	/* Not supported as not required by the demo application. */
	( void ) xPort;
}
/*-----------------------------------------------------------*/

void vUART_Handler( void )
{
uint8_t ucChar;
BaseType_t xHigherPriorityTaskWoken = pdFALSE;
uint_fast8_t xInterruptStatus;

	xInterruptStatus = MAP_UART_getEnabledInterruptStatus( EUSCI_A0_BASE );

	if( ( xInterruptStatus & EUSCI_A_UART_RECEIVE_INTERRUPT_FLAG ) != 0x00 )
	{
		/* Obtain the character. */
		ucChar = MAP_UART_receiveData( EUSCI_A0_BASE );

		/* Send the character to the queue.  Note the comments at the top of this
		file with regards to the inefficiency of this method for anything other than
		very low bandwidth communications.

		If writing to the queue unblocks a task, and the unblocked task	has a
		priority above the currently running task (the task that this interrupt
		interrupted), then xHigherPriorityTaskWoken will be set	to pdTRUE inside the
		xQueueSendFromISR() function.  xHigherPriorityTaskWoken is then passed to
		portYIELD_FROM_ISR() at	the end of this interrupt handler to request a
		context switch so the interrupt returns directly to the (higher priority)
		unblocked task. */
		xQueueSendFromISR( xRxQueue, &ucChar, &xHigherPriorityTaskWoken );
	}

	if( ( xInterruptStatus & EUSCI_A_UART_TRANSMIT_INTERRUPT_FLAG ) != 0x00 )
	{
		/* Are there more characters to transmit? */
		pcStringStart++;
		if( ( uint32_t ) pcStringStart < ( uint32_t ) pcStringEnd )
		{
			/* This is probably quite a heavy wait function just for writing to
			the Tx register.  An optimised design would probably replace this
			with a simple register write. */
			pxUARTA0->TXBUF = ( uint_fast8_t ) *pcStringStart;
		}
		else
		{
			/* No more characters to send.  Disable the interrupt and notify the
			task, if the task is waiting. */
			MAP_UART_disableInterrupt( EUSCI_A0_BASE, EUSCI_A_UART_TRANSMIT_INTERRUPT );
			if( xTransmittingTask != NULL )
			{
				vTaskNotifyGiveFromISR( xTransmittingTask, &xHigherPriorityTaskWoken );
				xTransmittingTask = NULL;
			}
		}
	}


	/* portYIELD_FROM_ISR() will request a context switch if executing this
	interrupt handler caused a task to leave the blocked state, and the task
	that left the blocked state has a higher priority than the currently running
	task (the task this interrupt interrupted).  See the comment above the calls
	to xSemaphoreGiveFromISR() and xQueueSendFromISR() within this function. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}





