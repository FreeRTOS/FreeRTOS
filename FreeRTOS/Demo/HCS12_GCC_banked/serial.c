/*
	serial.c  for using FreeRTOS
	Copyright (C) 2005  Robotronics Inc.
*/


/* BASIC INTERRUPT DRIVEN SERIAL PORT DRIVER for port 1.

   GCC demo modifications by Jeff Smith, Robotronics Inc. 2005
*/

#include "cpu.h"
#include <sys/sio.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"

/* Demo application include files. */
#include "sci.h"
#include "serial.h"

/* The queues used to communicate between the task code and the interrupt
service routines. */
static QueueHandle_t xRxedChars; 
static QueueHandle_t xCharsForTx; 

/* Interrupt identification bits. */
#define serOVERRUN_INTERRUPT		( '\x08' )
#define serRX_INTERRUPT				( 0x20 )
#define serTX_INTERRUPT				( 0x80 )

/*-----------------------------------------------------------*/


/*
 * Initialise port for interrupt driven communications.
 */
xComPortHandle xSerialPortInitMinimal( unsigned long ulWantedBaud, unsigned portBASE_TYPE uxQueueLength )
{
	/* Hardware setup is performed by the Processor Expert generated code.  
	This function just creates the queues used to communicate between the 
	interrupt code and the task code - then sets the required baud rate. */

	xRxedChars = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );
	xCharsForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( signed char ) );

	SCI_SetBaudRateMode( ( char ) ulWantedBaud );

	return NULL;
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
	/* Get the next character from the buffer queue.  Return false if no characters
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
	/* Place the character in the queue of characters to be transmitted. */
	if( xQueueSend( xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	/* Turn on the Tx interrupt so the ISR will remove the character from the
	queue and send it.   This does not need to be in a critical section as
	if the interrupt has already removed the character the next interrupt
	will simply turn off the Tx interrupt again. */
	SCICR2 |= 0x80;				// TIE

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{	
	/* Not supported. */
	//( void ) xPort;
}
/*-----------------------------------------------------------*/


/* 
 * Interrupt service routine for the serial port.  Must be in non-banked
 * memory. 
 */

void ATTR_INT ATTR_NEAR vCOM_ISR( void );

void vCOM_ISR( void )
{
volatile unsigned char ucByte, ucStatus;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* What caused the interrupt? */
	ucStatus = SCISR1;
	
	if( ucStatus & serOVERRUN_INTERRUPT )
	{
		/* The interrupt was caused by an overrun.  Clear the error by reading
		the data register. */
		ucByte = SCIDRL;
	}
	else
	if( ucStatus & serRX_INTERRUPT )
	{
		/* The interrupt was caused by a character being received.
		Read the received byte. */
		ucByte = SCIDRL;

		/* Post the character onto the queue of received characters - noting
		whether or not this wakes a task. */
		xQueueSendFromISR( xRxedChars, ( void * ) &ucByte, &xHigherPriorityTaskWoken );
	}
	
	if( ( ucStatus & serTX_INTERRUPT ) && ( SCICR2 & 0x80 ) )
	{	
		/* The interrupt was caused by a character being transmitted. */
		if( xQueueReceiveFromISR( xCharsForTx, ( void * ) &ucByte, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			/* Clear the SCRF bit. */
			SCIDRL = ucByte;
		}
		else
		{
			/* Disable transmit interrupt */
			SCICR2 &= ~0x80;			// TIE
		}
	}

	if( xHigherPriorityTaskWoken )
	{
		portYIELD();
	}
}

