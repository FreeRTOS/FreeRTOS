/*
	This serial port driver is borrowed heavily from DZComm.  I have
	simplified it by removing a lot of the functionality (hardware 
	flow control, etc.).  For more details and the full version see
	http://dzcomm.sourceforge.net


	FreeRTOS.org V4.8.0 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	***************************************************************************
	*																		  *
	* SAVE TIME AND MONEY!  Why not get us to quote to get FreeRTOS.org		  *
	* running on your hardware - or even write all or part of your application*
	* for you?  See http://www.OpenRTOS.com for details.					  *
	*																		  *
	***************************************************************************
	***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

/*
Changes from V1.00:
	
	+ Call to the more efficient portSWITCH_CONTEXT() replaces the call to 
	  taskYIELD() in the ISR.

Changes from V1.2.0:

	+ Added vSerialPutString().

Changes from V1.2.3

	+ The function xPortInitMinimal() has been renamed to 
	  xSerialPortInitMinimal() and the function xPortInit() has been renamed
	  to xSerialPortInit().

Changes From V2.0.0

	+ Use portTickType in place of unsigned pdLONG for delay periods.
	+ cQueueReieveFromISR() used in place of xQueueReceive() in ISR.
*/


#include <stdlib.h>
#include <dos.h>
#include "FreeRTOS.h"
#include "queue.h"
#include "task.h"
#include "semphr.h"
#include "portasm.h"

#define serMAX_IRQs						( 16 )
#define serTRANSMIT_HOLD_EMPTY_INT		( 0x02 )
#define serCOM1_STANDARD_IRQ			( ( unsigned portCHAR ) 4 )
#define serCOM2_STANDARD_IRQ			( ( unsigned portCHAR ) 3 )


#define	serIMR_8259_0					( ( unsigned portCHAR ) 0x21 )
#define	serIMR_8259_1					( ( unsigned portCHAR ) 0xa1 )
#define	serISR_8259_0					( ( unsigned portCHAR ) 0x20 )
#define	serISR_8259_1					( ( unsigned portCHAR ) 0xa0 )
#define	serALL_COMS_INTERRUPTS			( ( unsigned portCHAR ) 0x0f )
#define	serALL_MODEM_CTRL_INTERRUPTS	( ( unsigned portCHAR ) 0x0f )

#define serTRANSMIT_HOLD_OFFSET					( 0 )
#define serRECEIVE_DATA_OFFSET					( 0 )
#define serBAUD_RATE_DIVISOR_LOW_OFFSET			( 0 )
#define serBAUD_RATE_DIVISOR_HIGH_OFFSET		( 1 )
#define serINTERRUPT_ENABLE_OFFSET				( 1 )
#define serINTERRUPT_ID_OFFSET					( 2 )
#define serFIFO_CTRL_OFFSET						( 2 )
#define serLINE_CTRL_OFFSET						( 3 )
#define serMODEM_CTRL_OFFSET					( 4 )
#define serLINE_STATUS_OFFSET					( 5 )
#define serMODEM_STATUS_OFFSET					( 6 )
#define serSCR_OFFSET							( 7 )

#define serMAX_BAUD			( ( unsigned portLONG ) 115200UL )

#define serNO_INTERRUPTS	( 0x00 )

#define vInterruptOn( pxPort, ucInterrupt )										\
{																				\
	unsigned portCHAR ucIn = portINPUT_BYTE( pxPort->usInterruptEnableReg );	\
	if( !( ucIn & ucInterrupt ) )												\
	{																			\
		portOUTPUT_BYTE( pxPort->usInterruptEnableReg, ucIn | ucInterrupt );	\
	}																			\
}																				
/*-----------------------------------------------------------*/

#define vInterruptOff( pxPort, ucInterrupt )									\
{																				\
	unsigned portCHAR ucIn = portINPUT_BYTE( pxPort->usInterruptEnableReg );	\
	if( ucIn & ucInterrupt )													\
	{																			\
		portOUTPUT_BYTE( pxPort->usInterruptEnableReg, ucIn & ~ucInterrupt);	\
	}																			\
}
/*-----------------------------------------------------------*/

typedef enum
{ 
	serCOM1, 
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
	ser50,		
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

/* This *MUST* match the order in the eBaud definition. */
unsigned portLONG ulBaudFromEnum[] = 
{ 
	( unsigned portLONG ) 50, 
	( unsigned portLONG ) 75, 
	( unsigned portLONG ) 110, 
	( unsigned portLONG ) 134, 
	( unsigned portLONG ) 150,	
	( unsigned portLONG ) 200, 
	( unsigned portLONG ) 300, 
	( unsigned portLONG ) 600, 
	( unsigned portLONG ) 1200, 
	( unsigned portLONG ) 1800, 
	( unsigned portLONG ) 2400,   
	( unsigned portLONG ) 4800,   
	( unsigned portLONG ) 9600,  
	( unsigned portLONG ) 19200,  
	( unsigned portLONG ) 38400UL,
	( unsigned portLONG ) 57600UL,
	( unsigned portLONG ) 115200UL
};

typedef struct xCOM_PORT
{ 
	unsigned portSHORT sPort;   /* comm port address eg. 0x3f8    */
	unsigned portCHAR ucIRQ;    /* comm IRQ eg. 3                 */

	/* Next two fields used for setting up the IRQ routine and
	* (un)masking the interrupt in certain circumstances.
	*/
	unsigned portSHORT usIRQVector;
	unsigned portCHAR ucInterruptEnableMast;

	/* Read/Write buffers. */
	xQueueHandle xRxedChars; 
	xQueueHandle xCharsForTx;

	/* This lot are set up to minimise CPU time where accessing the comm
	* port's registers.
	*/
	unsigned portSHORT usTransmitHoldReg; 
	unsigned portSHORT usReceiveDataRegister;
	unsigned portSHORT usBaudRateDivisorLow; 
	unsigned portSHORT usBaudRateDivisorHigh;
	unsigned portSHORT usInterruptEnableReg;
	unsigned portSHORT usInterruptIDReg;
	unsigned portSHORT usFIFOCtrlReg;
	unsigned portSHORT usLineCtrlReg;
	unsigned portSHORT usModemCtrlReg;
	unsigned portSHORT usLineStatusReg;
	unsigned portSHORT usModemStatusReg;
	unsigned portSHORT usSCRReg;
	unsigned portSHORT us8259InterruptServiceReg;
	unsigned portSHORT us8259InterruptMaskReg;

	/* This semaphore does nothing useful except test a feature of the
	scheduler. */
	xSemaphoreHandle xTestSem;

} xComPort;

typedef xComPort *xComPortHandle;

/* A xComPort structure can be associated with each IRQ.  Initially none
are create/installed. */
xComPort *xPortStatus[ serMAX_IRQs ] = { NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL };

/*-----------------------------------------------------------*/

/* These prototypes are repeated here so we don't have to include the serial header.  This allows
the xComPortHandle structure details to be private to this file. */
xComPortHandle xSerialPortInit( eCOMPort ePort, eBaud eWantedBaud, eParity eWantedParity, eDataBits eWantedDataBits, eStopBits eWantedStopBits, unsigned portBASE_TYPE uxBufferLength );
portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, portCHAR *pcRxedChar, portTickType xBlockTime );
portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, portCHAR cOutChar, portTickType xBlockTime );
portBASE_TYPE xSerialWaitForSemaphore( xComPortHandle xPort );

static void prvSetupPortHardware( xComPort *pxPort, eCOMPort ePort, eBaud eWantedBaud, eParity eWantedParity, eDataBits eWantedDataBits, eStopBits eWantedStopBits );
static portSHORT sComPortISR( const xComPort * const pxPort );

/*-----------------------------------------------------------*/

/* Define an interrupt handler for each slot in the xPortStatus array. */

#define COM_IRQ_WRAPPER(N)										\
	static void __interrupt COM_IRQ##N##_WRAPPER( void )		\
	{															\
		portDISABLE_INTERRUPTS();								\
		if( sComPortISR( xPortStatus[##N##] ) )					\
		{														\
			portSWITCH_CONTEXT();								\
		}														\
	} 

COM_IRQ_WRAPPER( 0 )
COM_IRQ_WRAPPER( 1 )
COM_IRQ_WRAPPER( 2 )
COM_IRQ_WRAPPER( 3 )
COM_IRQ_WRAPPER( 4 )
COM_IRQ_WRAPPER( 5 )
COM_IRQ_WRAPPER( 6 )
COM_IRQ_WRAPPER( 7 )
COM_IRQ_WRAPPER( 8 )
COM_IRQ_WRAPPER( 9 )
COM_IRQ_WRAPPER( 10 )
COM_IRQ_WRAPPER( 11 )
COM_IRQ_WRAPPER( 12 )
COM_IRQ_WRAPPER( 13 )
COM_IRQ_WRAPPER( 14 )
COM_IRQ_WRAPPER( 15 )

static pxISR xISRs[ serMAX_IRQs ] = 
{
	COM_IRQ0_WRAPPER, 
	COM_IRQ1_WRAPPER, 
	COM_IRQ2_WRAPPER, 
	COM_IRQ3_WRAPPER, 
	COM_IRQ4_WRAPPER, 
	COM_IRQ5_WRAPPER, 
	COM_IRQ6_WRAPPER, 
	COM_IRQ7_WRAPPER, 
	COM_IRQ8_WRAPPER, 
	COM_IRQ9_WRAPPER, 
	COM_IRQ10_WRAPPER, 
	COM_IRQ11_WRAPPER, 
	COM_IRQ12_WRAPPER, 
	COM_IRQ13_WRAPPER, 
	COM_IRQ14_WRAPPER,
	COM_IRQ15_WRAPPER
};

static pxISR xOldISRs[ serMAX_IRQs ] = { NULL };

/*-----------------------------------------------------------*/


xComPortHandle xSerialPortInit( eCOMPort ePort, eBaud eWantedBaud, eParity eWantedParity, eDataBits eWantedDataBits, eStopBits eWantedStopBits, unsigned portBASE_TYPE uxBufferLength )
{
xComPort *pxPort;

	/* Create a structure to handle this port. */
	pxPort = ( xComPort * ) pvPortMalloc( sizeof( xComPort ) );
	
	if( pxPort != NULL )
	{
		/* Create the queues used by the comtest task. */
		pxPort->xRxedChars = xQueueCreate( uxBufferLength, ( unsigned portBASE_TYPE ) sizeof( portCHAR ) );
		pxPort->xCharsForTx = xQueueCreate( uxBufferLength, ( unsigned portBASE_TYPE ) sizeof( portCHAR ) );

		/* Create the test semaphore.  This does nothing useful except test a feature of the scheduler. */
		vSemaphoreCreateBinary( pxPort->xTestSem );

		prvSetupPortHardware( pxPort, ePort, eWantedBaud, eWantedParity, eWantedDataBits, eWantedStopBits );

		return pxPort;
	}

	return NULL;
}
/*-----------------------------------------------------------*/

static void prvSetupPortHardware( xComPort *pxPort, eCOMPort ePort, eBaud eWantedBaud, eParity eWantedParity, eDataBits eWantedDataBits, eStopBits eWantedStopBits )
{
portSHORT sIn;
unsigned portLONG ulDivisor;
unsigned portCHAR ucDivisorLow;
unsigned portCHAR ucDivisorHigh;
unsigned portCHAR ucCommParam;

	/* IRQ numbers - standard */
	if( ( ePort == serCOM1 ) || ( ePort == serCOM3 ) || ( ePort == serCOM5 ) || ( ePort == serCOM7 ) )
	{
		pxPort->ucIRQ = serCOM1_STANDARD_IRQ;
		pxPort->sPort = 0x3f8;
	}
	else
	{
		pxPort->ucIRQ = serCOM2_STANDARD_IRQ;
		pxPort->sPort = 0x2f8;
	}

	/* Set up variables in port making it easy to see which sIn/o address is which */
	pxPort->usTransmitHoldReg = pxPort->sPort + serTRANSMIT_HOLD_OFFSET;
	pxPort->usReceiveDataRegister = pxPort->sPort + serRECEIVE_DATA_OFFSET;
	pxPort->usBaudRateDivisorLow = pxPort->sPort + serBAUD_RATE_DIVISOR_LOW_OFFSET;
	pxPort->usBaudRateDivisorHigh = pxPort->sPort + serBAUD_RATE_DIVISOR_HIGH_OFFSET;
	pxPort->usInterruptEnableReg = pxPort->sPort + serINTERRUPT_ENABLE_OFFSET;
	pxPort->usInterruptIDReg = pxPort->sPort + serINTERRUPT_ID_OFFSET;
	pxPort->usFIFOCtrlReg = pxPort->sPort + serFIFO_CTRL_OFFSET;
	pxPort->usLineCtrlReg = pxPort->sPort + serLINE_CTRL_OFFSET;
	pxPort->usModemCtrlReg = pxPort->sPort + serMODEM_CTRL_OFFSET;
	pxPort->usLineStatusReg = pxPort->sPort + serLINE_STATUS_OFFSET;
	pxPort->usModemStatusReg = pxPort->sPort + serMODEM_STATUS_OFFSET;
	pxPort->usSCRReg = pxPort->sPort + serSCR_OFFSET;

	/* Set communication parameters. */
	ulDivisor = serMAX_BAUD / ulBaudFromEnum[ eWantedBaud ];
	ucDivisorLow = ( unsigned portCHAR ) ulDivisor & ( unsigned portCHAR ) 0xff;
	ucDivisorHigh = ( unsigned portCHAR ) ( ( ( unsigned portSHORT ) ulDivisor >> 8 ) & 0xff );
	
	switch( eWantedParity )
	{	
		case serNO_PARITY:		ucCommParam = 0x00;
								break;
		case serODD_PARITY:		ucCommParam = 0x08;
								break;
		case serEVEN_PARITY:	ucCommParam = 0x18;
								break;
		case serMARK_PARITY:	ucCommParam = 0x28;
								break;
		case serSPACE_PARITY:	ucCommParam = 0x38;
								break;
		default:				ucCommParam = 0x00;
								break;
	}

	switch ( eWantedDataBits )
	{
		case serBITS_5:	ucCommParam |= 0x00;
						break;
		case serBITS_6:	ucCommParam |= 0x01;
						break;
		case serBITS_7:	ucCommParam |= 0x02;
						break;
		case serBITS_8:	ucCommParam |= 0x03;
						break;
		default:		ucCommParam |= 0x03;
						break;
	}

	if( eWantedStopBits == serSTOP_2 ) 
	{
		ucCommParam |= 0x04;
	}

	/* Reset UART into known state - Thanks to Bradley Town */
	portOUTPUT_BYTE( pxPort->usLineCtrlReg, 0x00 );			/* Access usTransmitHoldReg/RBR/usInterruptEnableReg */
	portOUTPUT_BYTE( pxPort->usInterruptEnableReg, 0x00 );	/* Disable interrupts from UART */
	portOUTPUT_BYTE( pxPort->usModemCtrlReg, 0x04 );		/* Enable some multi-port cards */

	/* Code based on stuff from SVAsync lib. Clear UART Status and data registers
	setting up FIFO if possible */
	sIn = portINPUT_BYTE( pxPort->usSCRReg );
	portOUTPUT_BYTE( pxPort->usSCRReg, 0x55 );

	if( portINPUT_BYTE( pxPort->usSCRReg ) == 0x55 )
	{
		/* The chip is better than an 8250 */
		portOUTPUT_BYTE( pxPort->usSCRReg, sIn );	/* Set usSCRReg back to what it was before */
		portINPUT_BYTE( pxPort->usSCRReg);			/* Give slow motherboards a chance */

		/* Try and start the FIFO. It appears that some chips need a two call 
		protocol, but those that don't seem to work even if you do start it twice. 
		The first call is simply to start it, the second starts it and sets an 8 
		byte FIFO trigger level. */
		portOUTPUT_BYTE( pxPort->usFIFOCtrlReg, 0x01 );
		portINPUT_BYTE( pxPort->usFIFOCtrlReg );			/* Give slow motherboards a chance to catch up */
		portOUTPUT_BYTE( pxPort->usFIFOCtrlReg, 0x87 );

		/* Check that the FIFO initialised */
		if( ( portINPUT_BYTE( pxPort->usInterruptIDReg ) & 0xc0 ) != 0xc0 )
		{
			/* It didn't so we assume it isn't there but disable it to be on the 
			safe side. */
			portOUTPUT_BYTE( pxPort->usInterruptIDReg, 0xfe );
		}
	}

	/* End of (modified) SVAsync code.  
	Set interrupt parameters calculating mask for 8259 controller's 
	IMR and number of interrupt handler for given irq level	 */
	if (pxPort->ucIRQ <= 7)
	{	
		/* if 0<=irq<=7 first IMR address used */
		pxPort->ucInterruptEnableMast = ~(0x01 << pxPort->ucIRQ);
		pxPort->usIRQVector = pxPort->ucIRQ + 8;
		pxPort->us8259InterruptMaskReg = serIMR_8259_0;
		pxPort->us8259InterruptServiceReg = serISR_8259_0;
	}
	else
	{
		pxPort->ucInterruptEnableMast = ~( 0x01 << ( pxPort->ucIRQ % 8 ) );
		pxPort->usIRQVector = 0x70 + ( pxPort->ucIRQ - 8) ;
		pxPort->us8259InterruptMaskReg = serIMR_8259_1;
		pxPort->us8259InterruptServiceReg = serISR_8259_1;
	}

	/* Set Port Toggle to usBaudRateDivisorLow/usBaudRateDivisorHigh registers 
	to set baud rate */
	portOUTPUT_BYTE( pxPort->usLineCtrlReg, ucCommParam | 0x80 );
	portOUTPUT_BYTE( pxPort->usBaudRateDivisorLow, ucDivisorLow );
	portOUTPUT_BYTE( pxPort->usBaudRateDivisorHigh, ucDivisorHigh );

	/* reset usLineCtrlReg and Port Toggleout */
	portOUTPUT_BYTE( pxPort->usLineCtrlReg, ucCommParam & 0x7F );

	portENTER_CRITICAL();

	if( xPortStatus[ pxPort->ucIRQ ] == NULL )
	{	
		xPortStatus[ pxPort->ucIRQ ] = pxPort;
	}
	
	xOldISRs[ pxPort->ucIRQ ] = _dos_getvect( pxPort->usIRQVector );
	_dos_setvect( pxPort->usIRQVector, xISRs[ pxPort->ucIRQ ] );

	/* enable interrupt pxPort->ucIRQ level */
	portOUTPUT_BYTE( pxPort->us8259InterruptMaskReg, portINPUT_BYTE( pxPort->us8259InterruptMaskReg ) & pxPort->ucInterruptEnableMast );

	/* And allow interrupts again now the hairy bit's done */
	portEXIT_CRITICAL();		

	/* This version does not allow flow control. */
	portOUTPUT_BYTE( pxPort->usModemCtrlReg, serALL_MODEM_CTRL_INTERRUPTS );

	/* enable all communication's interrupts */
	portOUTPUT_BYTE( pxPort->usInterruptEnableReg, serALL_COMS_INTERRUPTS );
}
/*-----------------------------------------------------------*/

static portSHORT sComPortISR( const xComPort * const pxPort )
{
portSHORT sInterruptID;
portCHAR cIn, cOut;
portBASE_TYPE xTaskWokenByPost = pdFALSE, xAnotherTaskWokenByPost = pdFALSE, xTaskWokenByTx = pdFALSE;
extern void vComTestUnsuspendTask( void );

	portOUTPUT_BYTE( pxPort->us8259InterruptMaskReg, ( portINPUT_BYTE( pxPort->us8259InterruptMaskReg) | ~pxPort->ucInterruptEnableMast ) );

	/* Decide which UART has issued the interrupt */
	sInterruptID = portINPUT_BYTE( pxPort->usInterruptIDReg );

	/* service whatever requests the calling UART may have. The top 4 bits are
	either unused or indicate the presence of a functioning FIFO, which we don't
	need to know. So trim them off to simplify the switch statement below. */
	sInterruptID &= 0x0f;
	do
	{
		switch( sInterruptID )
		{
			case 0x0c:	/* Timeout
						Called when FIFO not up to trigger level but no activity for 
						a while. Handled exactly as RDAINT, see below for 
						description. */
						do
						{
							cIn = ( portCHAR ) portINPUT_BYTE( pxPort->usReceiveDataRegister );						
							xTaskWokenByPost = xQueueSendFromISR( pxPort->xRxedChars, &cIn, xTaskWokenByPost );

							/* Also release the semaphore - this does nothing interesting and is just a test.
							We first attempt to unsuspend the task to check the scheduler correctely detects
							this as an invalid call, then give the semaphore for real. */
							vComTestUnsuspendTask();
							xAnotherTaskWokenByPost = xSemaphoreGiveFromISR( pxPort->xTestSem, xAnotherTaskWokenByPost );

						} while( portINPUT_BYTE( pxPort->usLineStatusReg ) & 0x01 );
						break;

			case 0x06:	/* LSINT */
						portINPUT_BYTE( pxPort->usLineStatusReg );
						break;

			case 0x04:	/* RDAINT */
						/* The usInterruptIDReg flag tested above stops when the 
						FIFO is below the trigger level rather than empty, whereas 
						this flag allows one to empty it: (do loop because there 
						must be at least one to read by virtue of having got here.) */
						do
						{
							cIn = ( portCHAR ) portINPUT_BYTE( pxPort->usReceiveDataRegister );						
							xTaskWokenByPost = xQueueSendFromISR( pxPort->xRxedChars, &cIn, xTaskWokenByPost );

							/* Also release the semaphore - this does nothing interesting and is just a test.
							We first attempt to unsuspend the task to check the scheduler correctely detects
							this as an invalid call, then give the semaphore for real. */
							vComTestUnsuspendTask();
							xAnotherTaskWokenByPost = xSemaphoreGiveFromISR( pxPort->xTestSem, xAnotherTaskWokenByPost );

						} while( portINPUT_BYTE( pxPort->usLineStatusReg ) & 0x01 );
						break;

			case 0x02:	/* serTRANSMIT_HOLD_EMPTY_INT */
						if( xQueueReceiveFromISR( pxPort->xCharsForTx, &cOut, &xTaskWokenByTx ) != pdTRUE )						
						{																						
							/* Queue empty, nothing to send */													
							vInterruptOff( pxPort, serTRANSMIT_HOLD_EMPTY_INT);									
						}																						
						else																					
						{																						
							portOUTPUT_BYTE( pxPort->usTransmitHoldReg, ( portSHORT ) cOut );					
						}
						break;

			case 0x00:	/* MSINT */
						portINPUT_BYTE( pxPort->usModemStatusReg );
						break;
		}		

		/* Get the next instruction, trimming as above */
		sInterruptID = portINPUT_BYTE( pxPort->usInterruptIDReg ) & 0x0f;

	} while( !( sInterruptID & 0x01 ) );

	if( pxPort->ucIRQ > 7 )
	{
		portOUTPUT_BYTE( 0xA0, 0x60 + ( pxPort->ucIRQ & 0x07 ) );
		portOUTPUT_BYTE( 0x20, 0x62);
	}
	else
	{
		portOUTPUT_BYTE( 0x20, 0x60 + pxPort->ucIRQ );
	}

	portOUTPUT_BYTE( pxPort->us8259InterruptMaskReg, portINPUT_BYTE( pxPort->us8259InterruptMaskReg ) & pxPort->ucInterruptEnableMast );

	/* If posting any of the characters to a queue woke a task that was blocked on
	the queue we may want to return to the task just woken (depending on its 
	priority relative to the task this ISR interrupted. */
	if( xTaskWokenByPost || xAnotherTaskWokenByPost || xTaskWokenByTx )
	{
		return pdTRUE;
	}
	else
	{
		return pdFALSE;
	}
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialGetChar( xComPortHandle pxPort, portCHAR *pcRxedChar, portTickType xBlockTime )
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

portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, portCHAR cOutChar, portTickType xBlockTime )
{
	if( xQueueSend( pxPort->xCharsForTx, &cOutChar, xBlockTime ) != pdPASS )
	{
		return pdFAIL;
	}

	vInterruptOn( pxPort, serTRANSMIT_HOLD_EMPTY_INT );

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const portCHAR * const pcString, unsigned portSHORT usStringLength )
{
portCHAR * pcNextChar;
const portTickType xNoBlock = ( portTickType ) 0;

	/* Stop warnings. */
	( void ) usStringLength;

	pcNextChar = ( portCHAR * ) pcString;
	while( *pcNextChar )
	{
		xSerialPutChar( pxPort, *pcNextChar, xNoBlock );
		pcNextChar++;
	}
}
/*-----------------------------------------------------------*/

portBASE_TYPE xSerialWaitForSemaphore( xComPortHandle xPort )
{
const portTickType xBlockTime = ( portTickType ) 0xffff;

	/* This function does nothing interesting, but test the 
	semaphore from ISR mechanism. */
	return xSemaphoreTake( xPort->xTestSem, xBlockTime );	
}
/*-----------------------------------------------------------*/

void vSerialClose( xComPortHandle xPort )
{
	portENTER_CRITICAL();

	/* Turn off the interrupts. */
	portOUTPUT_BYTE( xPort->usModemCtrlReg, serNO_INTERRUPTS );
	portOUTPUT_BYTE( xPort->usInterruptEnableReg, serNO_INTERRUPTS );

	/* Put back the original ISR. */
	_dos_setvect( xPort->usIRQVector, xOldISRs[ xPort->ucIRQ ] );

	/* Remove the reference in the array of xComPort structures. */
	xPortStatus[ xPort->ucIRQ ] = NULL;

	/* Delete the queues. */
	vQueueDelete( xPort->xRxedChars );
	vQueueDelete( xPort->xCharsForTx );

	vPortFree( ( void * ) xPort );

	portEXIT_CRITICAL();
}

