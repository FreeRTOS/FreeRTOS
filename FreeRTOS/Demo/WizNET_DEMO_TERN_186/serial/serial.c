/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/


#include <stdlib.h>
#include <embedded.h>
#include "FreeRTOS.h"
#include "portasm.h"
#include "queue.h"
#include "task.h"
#include "semphr.h"

#define serMAX_PORTS			( ( unsigned short ) 2 )

#define serPORT_0_INT_REG		( 0xff44 )
#define serPORT_0_BAUD_REG		( 0xff88 )
#define serPORT_0_RX_REG		( 0xff86 )
#define serPORT_0_TX_REG		( 0xff84 )
#define serPORT_0_STATUS_REG	( 0xff82 )
#define serPORT_0_CTRL_REG		( 0xff80 )
#define serPORT_0_IRQ			( 0x14 )

#define serPORT_1_INT_REG		( 0xff42 )
#define serPORT_1_BAUD_REG		( 0xff18 )
#define serPORT_1_RX_REG		( 0xff16 )
#define serPORT_1_TX_REG		( 0xff14 )
#define serPORT_1_STATUS_REG	( 0xff12 )
#define serPORT_1_CTRL_REG		( 0xff10 )
#define serPORT_1_IRQ			( 0x11 )

#define serTX_EMPTY				( ( unsigned short ) 0x40 )
#define serRX_READY				( ( unsigned short ) 0x80 )

#define serRESET_PIC( usEOI_TYPE )	portOUTPUT_WORD( ( unsigned short ) 0xff22, usEOI_TYPE )
#define serTX_HOLD_EMPTY_INT		( ( unsigned short ) 0x100 )

#define serENABLE_INTERRUPTS		( ( unsigned short ) 0x80 )
#define serMODE						( ( unsigned short ) 0x01 )
#define serENABLE_TX_MACHINES		( ( unsigned short ) 0x40 )
#define serENABLE_RX_MACHINES		( ( unsigned short ) 0x20 )
#define serINTERRUPT_MASK			( ( unsigned short ) 0x08 )
#define serCLEAR_ALL_STATUS_BITS	( ( unsigned short ) 0x00 )
#define serINTERRUPT_PRIORITY		( ( unsigned short ) 0x01 ) /*< Just below the scheduler priority. */

#define serDONT_BLOCK				( ( TickType_t ) 0 )

typedef enum
{ 
	serCOM1 = 0, 
	serCOM2, 
	serCOM3, 
	serCOM4, 
	serCOM5, 
	serCOM6, 
	serCOM7, 
	serCOM8 
} eCOMPort;

typedef enum 
{ 
	serNO_PARITY, 
	serODD_PARITY, 
	serEVEN_PARITY, 
	serMARK_PARITY, 
	serSPACE_PARITY 
} eParity;

typedef enum 
{ 
	serSTOP_1, 
	serSTOP_2 
} eStopBits;

typedef enum 
{
	serBITS_5,
	serBITS_6,
	serBITS_7,
	serBITS_8
} eDataBits;

typedef enum
{
	ser50 = 0,
	ser75,
	ser110,
	ser134,
	ser150,
	ser200,
	ser300,
	ser600,
	ser1200,
	ser1800,
	ser2400,
	ser4800,
	ser9600,
	ser19200,
	ser38400,
	ser57600,
	ser115200
} eBaud;

typedef struct xCOM_PORT
{
	/* Hardware parameters for this port. */
	short sTxInterruptOn;
	unsigned short usIntReg;
	unsigned short usBaudReg;
	unsigned short usRxReg;
	unsigned short usTxReg;
	unsigned short usStatusReg;
	unsigned short usCtrlReg;

	unsigned short usIRQVector;

	/* Queues used for communications with com test task. */
	QueueHandle_t xRxedChars; 
	QueueHandle_t xCharsForTx;

	/* This semaphore does nothing useful except test a feature of the
	scheduler. */
	SemaphoreHandle_t xTestSem;

} xComPort;

static xComPort xPorts[ serMAX_PORTS ] = 
{
	{ pdFALSE, serPORT_0_INT_REG, serPORT_0_BAUD_REG, serPORT_0_RX_REG, serPORT_0_TX_REG, serPORT_0_STATUS_REG, serPORT_0_CTRL_REG, serPORT_0_IRQ, NULL, NULL, NULL },
	{ pdFALSE, serPORT_1_INT_REG, serPORT_1_BAUD_REG, serPORT_1_RX_REG, serPORT_1_TX_REG, serPORT_1_STATUS_REG, serPORT_1_CTRL_REG, serPORT_1_IRQ, NULL, NULL, NULL }
};

typedef xComPort * xComPortHandle;

/**
 * Lookup the baud rate from the enum.
 */
static unsigned long prvBaud( eBaud eWantedBaud ); 

/* These prototypes are repeated here so we don't have to include the serial header.  This allows
the xComPortHandle structure details to be private to this file. */
xComPortHandle xSerialPortInit( eCOMPort ePort, eBaud eWantedBaud, eParity eWantedParity, eDataBits eWantedDataBits, eStopBits eWantedStopBits, unsigned portBASE_TYPE uxBufferLength );
portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, char *pcRxedChar, TickType_t xBlockTime );
portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, char cOutChar, TickType_t xBlockTime );
void vSerialClose( xComPortHandle xPort );
short sSerialWaitForSemaphore( xComPortHandle xPort );
/*-----------------------------------------------------------*/

static short xComPortISR( xComPort * const pxPort );

#define vInterruptOn( pxPort, usInterrupt )										\
{																				\
unsigned short usIn;														\
																				\
	portENTER_CRITICAL();														\
	{																			\
		if( pxPort->sTxInterruptOn == pdFALSE )									\
		{																		\
			usIn = portINPUT_WORD( pxPort->usCtrlReg );							\
			portOUTPUT_WORD( pxPort->usCtrlReg, usIn | usInterrupt );			\
																				\
			pxPort->sTxInterruptOn = pdTRUE;									\
		}																		\
	}																			\
	portEXIT_CRITICAL();														\
}																				
/*-----------------------------------------------------------*/

#define vInterruptOff( pxPort, usInterrupt )									\
{																				\
	unsigned short usIn = portINPUT_WORD( pxPort->usCtrlReg );				\
	if( usIn & usInterrupt )													\
	{																			\
		portOUTPUT_WORD( pxPort->usCtrlReg, usIn & ~usInterrupt);				\
		pxPort->sTxInterruptOn = pdFALSE;										\
	}																			\
}
/*-----------------------------------------------------------*/


/* Define an interrupt handler for each port */
#define COM_IRQ_WRAPPER(N)										\
	static void __interrupt COM_IRQ##N##_WRAPPER( void )		\
	{															\
        if( xComPortISR( &( xPorts[##N##] ) ) )                 \
        {                                                       \
			portEND_SWITCHING_ISR();                            \
		}                                                       \
	}

  

COM_IRQ_WRAPPER( 0 )
COM_IRQ_WRAPPER( 1 )

static pxISR xISRs[ serMAX_PORTS ] = 
{
	COM_IRQ0_WRAPPER, 
	COM_IRQ1_WRAPPER
};

/*-----------------------------------------------------------*/

static unsigned long prvBaud( eBaud eWantedBaud )
{
	switch( eWantedBaud )
    {
		case ser50			:	return 50UL;
		case ser75			:	return 75UL;
		case ser110			:	return 110UL;
		case ser134			:	return 134UL;
		case ser150			:	return 150UL;
		case ser200			:	return 200UL;
		case ser300			:	return 300UL;
		case ser600			:	return 600UL;
		case ser1200		:	return 1200UL;
		case ser1800		:	return 1800UL;
		case ser2400		:	return 2400UL;
		case ser4800		:	return 4800UL;
		case ser19200		:	return 19200UL;
		case ser38400		:	return 38400UL;
		case ser57600		:	return 57600UL;
		case ser115200		:	return 115200UL;
		default				:	return 9600UL;
    }
}

/*-----------------------------------------------------------*/

xComPortHandle xSerialPortInit( eCOMPort ePort, eBaud eWantedBaud, eParity eWantedParity, eDataBits eWantedDataBits, eStopBits eWantedStopBits, unsigned portBASE_TYPE uxBufferLength )
{
unsigned short usPort;
xComPortHandle pxPort = NULL;
unsigned long ulBaudDiv;

	/* BAUDDIV = ( Microprocessor Clock / Baud Rate ) / 16 */
    ulBaudDiv = ( configCPU_CLOCK_HZ / prvBaud( eWantedBaud ) ) / 16UL;

	/* Only n, 8, 1 is supported so these parameters are not required for this
	port. */
	( void ) eWantedParity;
	( void ) eWantedDataBits;
    ( void ) eWantedStopBits;

	/* Currently only n,8,1 is supported. */

	usPort = ( unsigned short ) ePort;
	
	if( usPort < serMAX_PORTS )
	{
		pxPort = &( xPorts[ usPort ] );

		portENTER_CRITICAL();
		{
			unsigned short usInWord;

			/* Create the queues used by the com test task. */
			pxPort->xRxedChars = xQueueCreate( uxBufferLength, ( unsigned portBASE_TYPE ) sizeof( char ) );
			pxPort->xCharsForTx = xQueueCreate( uxBufferLength, ( unsigned portBASE_TYPE ) sizeof( char ) );

			/* Create the test semaphore.  This does nothing useful except test a feature of the scheduler. */
			vSemaphoreCreateBinary( pxPort->xTestSem );

			/* There is no ISR here already to restore later. */
			setvect( ( short ) pxPort->usIRQVector, xISRs[ usPort ] );

			usInWord = portINPUT_WORD( pxPort->usIntReg );
			usInWord &= ~serINTERRUPT_MASK;
			usInWord |= serINTERRUPT_PRIORITY;
			portOUTPUT_WORD( pxPort->usIntReg, usInWord );

			portOUTPUT_WORD( pxPort->usBaudReg, ( unsigned short ) ulBaudDiv );
			portOUTPUT_WORD( pxPort->usCtrlReg, serENABLE_INTERRUPTS | serMODE | serENABLE_TX_MACHINES | serENABLE_RX_MACHINES );

			portOUTPUT_WORD( pxPort->usStatusReg, serCLEAR_ALL_STATUS_BITS );
		}
		portEXIT_CRITICAL();
	}

	return pxPort;
} /*lint !e715 Some parameters are not used as only a subset of the serial port functionality is currently implemented. */
/*-----------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const char * const pcString, unsigned short usStringLength )
{
unsigned short usByte;
char *pcNextChar;

	pcNextChar = ( char * ) pcString;

	for( usByte = 0; usByte < usStringLength; usByte++ )
	{
		xQueueSend( pxPort->xCharsForTx, pcNextChar, serDONT_BLOCK );
		pcNextChar++;
	}

	vInterruptOn( pxPort, serTX_HOLD_EMPTY_INT );
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, char *pcRxedChar, TickType_t xBlockTime )
{
	/* Get the next character from the buffer, note that this routine is only 
	called having checked that the is (at least) one to get */
	if( xQueueReceive( pxPort->xRxedChars, pcRxedChar, xBlockTime ) )
	{
		return pdTRUE;
	}
	else
	{
		return pdFALSE;
	}
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, char cOutChar, TickType_t xBlockTime )
{
	if( xQueueSend( pxPort->xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	vInterruptOn( pxPort, serTX_HOLD_EMPTY_INT );

	return pdPASS;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialWaitForSemaphore( xComPortHandle xPort )
{
const TickType_t xBlockTime = ( TickType_t ) 0xffff;

	/* This function does nothing interesting, but test the 
	semaphore from ISR mechanism. */
	return xSemaphoreTake( xPort->xTestSem, xBlockTime );
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
unsigned short usOutput;

	/* Turn off the interrupts.  We may also want to delete the queues and/or
	re-install the original ISR. */

	portENTER_CRITICAL();
	{
		usOutput = portINPUT_WORD( xPort->usCtrlReg );

		usOutput &= ~serENABLE_INTERRUPTS;
		usOutput &= ~serENABLE_TX_MACHINES;
		usOutput &= ~serENABLE_RX_MACHINES;
		portOUTPUT_WORD( xPort->usCtrlReg, usOutput );

		usOutput = portINPUT_WORD( xPort->usIntReg );
		usOutput |= serINTERRUPT_MASK;
		portOUTPUT_WORD( xPort->usIntReg, usOutput );
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/
unsigned short usStatus;
static portBASE_TYPE xComPortISR( xComPort * const pxPort )
{
unsigned short usStatusRegister;
char cChar;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* NOTE:  THIS IS NOT AN EFFICIENT ISR AS IT IS DESIGNED SOLELY TO TEST
	THE SCHEDULER FUNCTIONALITY.  REAL APPLICATIONS SHOULD NOT USE THIS
	FUNCTION. */

	usStatusRegister = portINPUT_WORD( pxPort->usStatusReg );

	if( usStatusRegister & serRX_READY )
	{
		cChar = ( char ) portINPUT_WORD( pxPort->usRxReg );
		xQueueSendFromISR( pxPort->xRxedChars, &cChar, &xHigherPriorityTaskWoken );

		/* Also release the semaphore - this does nothing interesting and is just a test. */
		xSemaphoreGiveFromISR( pxPort->xTestSem, &xHigherPriorityTaskWoken );
	}
	else if( pxPort->sTxInterruptOn && ( usStatusRegister & serTX_EMPTY ) )
	{
		if( xQueueReceiveFromISR( pxPort->xCharsForTx, &cChar, &xHigherPriorityTaskWoken ) == pdTRUE )
		{
			portOUTPUT_WORD( pxPort->usTxReg, ( unsigned short ) cChar );
		}
		else
		{
			/* Queue empty, nothing to send */
			vInterruptOff( pxPort, serTX_HOLD_EMPTY_INT );
		}
	}

    serRESET_PIC( pxPort->usIRQVector );

	/* If posting to the queue woke a task that was blocked on the queue we may
	want to switch to the woken task - depending on its priority relative to
	the task interrupted by this ISR. */
	return xHigherPriorityTaskWoken;
}





