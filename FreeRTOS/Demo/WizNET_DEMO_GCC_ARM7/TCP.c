/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/*
	Changes from V3.2.3
	
	+ Modified char* types to compile without warning when using GCC V4.0.1.
	+ Corrected the address to which the MAC address is written.  Thanks to
	  Bill Knight for this correction.

	Changes from V3.2.4

	+ Changed the default MAC address to something more realistic.

*/

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"
#include "tcp.h"
#include "serial.h"

/* Application includes. */
#include "i2c.h"
#include "html_pages.h"

/*-----------------------------------------------------------*/

/* Hardwired i2c address of the WIZNet device. */
#define tcpDEVICE_ADDRESS 				( ( unsigned char ) 0x00 )

/* Constants used to configure the Tx and Rx buffer sizes within the WIZnet
device. */
#define tcp8K_RX						( ( unsigned char ) 0x03 )
#define tcp8K_TX						( ( unsigned char ) 0x03 )

/* Constants used to generate the WIZnet internal buffer addresses. */
#define tcpSINGLE_SOCKET_ADDR_MASK		( ( unsigned long ) 0x1fff )
#define tcpSINGLE_SOCKET_ADDR_OFFSET	( ( unsigned long ) 0x4000 )

/* Bit definitions of the commands that can be sent to the command register. */
#define tcpRESET_CMD					( ( unsigned char ) 0x80 )
#define tcpSYS_INIT_CMD					( ( unsigned char ) 0x01 )
#define tcpSOCK_STREAM					( ( unsigned char ) 0x01 )
#define tcpSOCK_INIT					( ( unsigned char ) 0x02 )
#define tcpLISTEN_CMD					( ( unsigned char ) 0x08 )
#define tcpRECEIVE_CMD					( ( unsigned char ) 0x40 )
#define tcpDISCONNECT_CMD				( ( unsigned char ) 0x10 )
#define tcpSEND_CMD						( ( unsigned char ) 0x20 )

/* Constants required to handle the interrupts. */
#define tcpCLEAR_EINT0					( 1 )
#define i2cCLEAR_ALL_INTERRUPTS			( ( unsigned char ) 0xff )
#define i2cCHANNEL_0_ISR_ENABLE			( ( unsigned char ) 0x01 )
#define i2cCHANNEL_0_ISR_DISABLE		( ( unsigned char ) 0x00 )
#define tcpWAKE_ON_EINT0				( 1 )
#define tcpENABLE_EINT0_FUNCTION		( ( unsigned long ) 0x01 )
#define tcpEINT0_VIC_CHANNEL_BIT		( ( unsigned long ) 0x4000 )
#define tcpEINT0_VIC_CHANNEL			( ( unsigned long ) 14 )
#define tcpEINT0_VIC_ENABLE				( ( unsigned long ) 0x0020 )

/* Various delays used in the driver. */
#define tcpRESET_DELAY					( ( TickType_t ) 16 / portTICK_PERIOD_MS )
#define tcpINIT_DELAY					( ( TickType_t ) 500 / portTICK_PERIOD_MS  )
#define tcpLONG_DELAY					( ( TickType_t ) 500 / portTICK_PERIOD_MS  )
#define tcpSHORT_DELAY					( ( TickType_t ) 5 / portTICK_PERIOD_MS )
#define tcpCONNECTION_WAIT_DELAY		( ( TickType_t ) 100 / portTICK_PERIOD_MS )
#define tcpNO_DELAY						( ( TickType_t ) 0 )

/* Length of the data to read for various register reads. */
#define tcpSTATUS_READ_LEN				( ( unsigned long ) 1 )
#define tcpSHADOW_READ_LEN				( ( unsigned long ) 1 )
	
/* Register addresses within the WIZnet device. */
#define tcpCOMMAND_REG					( ( unsigned short ) 0x0000 )
#define tcpGATEWAY_ADDR_REG				( ( unsigned short ) 0x0080 )
#define tcpSUBNET_MASK_REG				( ( unsigned short ) 0x0084 )
#define tcpSOURCE_HA_REG				( ( unsigned short ) 0x0088 )
#define tpcSOURCE_IP_REG				( ( unsigned short ) 0x008E )
#define tpcSOCKET_OPT_REG				( ( unsigned short ) 0x00A1 )
#define tcpSOURCE_PORT_REG				( ( unsigned short ) 0x00AE )
#define tcpTX_WRITE_POINTER_REG			( ( unsigned short ) 0x0040 )
#define tcpTX_READ_POINTER_REG			( ( unsigned short ) 0x0044 )
#define tcpTX_ACK_POINTER_REG			( ( unsigned short ) 0x0018 )
#define tcpTX_MEM_SIZE_REG				( ( unsigned short ) 0x0096 )
#define tcpRX_MEM_SIZE_REG				( ( unsigned short ) 0x0095 )
#define tcpINTERRUPT_STATUS_REG			( ( unsigned short ) 0x0004 )
#define tcpTX_WRITE_SHADOW_REG			( ( unsigned short ) 0x01F0 )
#define tcpTX_ACK_SHADOW_REG			( ( unsigned short ) 0x01E2 )
#define tcpISR_MASK_REG					( ( unsigned short ) 0x0009 )
#define tcpINTERRUPT_REG				( ( unsigned short ) 0x0008 )
#define tcpSOCKET_STATE_REG				( ( unsigned short ) 0x00a0 )

/* Constants required for hardware setup. */
#define tcpRESET_ACTIVE_LOW 			( ( unsigned long ) 0x20 )
#define tcpRESET_ACTIVE_HIGH 			( ( unsigned long ) 0x10 )

/* Constants defining the source of the WIZnet ISR. */
#define tcpISR_SYS_INIT					( ( unsigned char ) 0x01 )
#define tcpISR_SOCKET_INIT				( ( unsigned char ) 0x02 )
#define tcpISR_ESTABLISHED				( ( unsigned char ) 0x04 )
#define tcpISR_CLOSED					( ( unsigned char ) 0x08 )
#define tcpISR_TIMEOUT					( ( unsigned char ) 0x10 )
#define tcpISR_TX_COMPLETE				( ( unsigned char ) 0x20 )
#define tcpISR_RX_COMPLETE				( ( unsigned char ) 0x40 )

/* Constants defining the socket status bits. */
#define tcpSTATUS_ESTABLISHED			( ( unsigned char ) 0x06 )
#define tcpSTATUS_LISTEN				( ( unsigned char ) 0x02 )

/* Misc constants. */
#define tcpNO_STATUS_BITS				( ( unsigned char ) 0x00 )
#define i2cNO_ADDR_REQUIRED				( ( unsigned short ) 0x0000 )
#define i2cNO_DATA_REQUIRED				( 0x0000 )
#define tcpISR_QUEUE_LENGTH				( ( unsigned portBASE_TYPE ) 10 )
#define tcpISR_QUEUE_ITEM_SIZE			( ( unsigned portBASE_TYPE ) 0 )
#define tcpBUFFER_LEN					( 4 * 1024 )
#define tcpMAX_REGISTER_LEN				( 4 )
#define tcpMAX_ATTEMPTS_TO_CHECK_BUFFER	( 6 )
#define tcpMAX_NON_LISTEN_STAUS_READS	( 5 )

/* Message definitions.  The IP address, MAC address, gateway address, etc.
is set here! */
const unsigned char const ucDataGAR[]				= { 172, 25, 218, 3 };	/* Gateway address. */
const unsigned char const ucDataMSR[]				= { 255, 255, 255, 0 };	/* Subnet mask.		*/
const unsigned char const ucDataSIPR[]				= { 172, 25, 218, 201 };/* IP address.		*/
const unsigned char const ucDataSHAR[]				= { 00, 23, 30, 41, 15, 26 }; /* MAC address - DO NOT USE THIS ON A PUBLIC NETWORK! */

/* Other fixed messages. */
const unsigned char const ucDataReset[]				= { tcpRESET_CMD }; 
const unsigned char const ucDataInit[]				= { tcpSYS_INIT_CMD }; 
const unsigned char const ucDataProtocol[]			= { tcpSOCK_STREAM };
const unsigned char const ucDataPort[]				= { 0xBA, 0xCC };
const unsigned char const ucDataSockInit[]			= { tcpSOCK_INIT };
const unsigned char const ucDataTxWritePointer[]	= { 0x11, 0x22, 0x00, 0x00 };
const unsigned char const ucDataTxAckPointer[]		= { 0x11, 0x22, 0x00, 0x00 };
const unsigned char const ucDataTxReadPointer[]		= { 0x11, 0x22, 0x00, 0x00 };
const unsigned char const ucDataListen[]			= { tcpLISTEN_CMD };
const unsigned char const ucDataReceiveCmd[]		= { tcpRECEIVE_CMD };
const unsigned char const ucDataSetTxBufSize[]		= { tcp8K_TX };
const unsigned char const ucDataSetRxBufSize[] 		= { tcp8K_RX };
const unsigned char const ucDataSend[]				= { tcpSEND_CMD };
const unsigned char const ucDataDisconnect[]		= { tcpDISCONNECT_CMD };
const unsigned char const ucDataEnableISR[]			= { i2cCHANNEL_0_ISR_ENABLE };
const unsigned char const ucDataDisableISR[]		= { i2cCHANNEL_0_ISR_DISABLE };
const unsigned char const ucDataClearInterrupt[]	= { i2cCLEAR_ALL_INTERRUPTS };

static SemaphoreHandle_t xMessageComplete = NULL;
QueueHandle_t xTCPISRQueue = NULL;

/* Dynamically generate and send an html page. */
static void prvSendSamplePage( void );

/* Read a register from the WIZnet device via the i2c interface. */
static void prvReadRegister( unsigned char *pucDestination, unsigned short usAddress, unsigned long ulLength );

/* Send the entire Tx buffer (the Tx buffer within the WIZnet device). */
static void prvFlushBuffer( unsigned long ulTxAddress );

/* Write a string to the WIZnet Tx buffer. */
static void prvWriteString( const char * const pucTxBuffer, long lTxLen, unsigned long *pulTxAddress );

/* Convert a number to a string. */
void ultoa( unsigned long ulVal, char *pcBuffer, long lIgnore );

/*-----------------------------------------------------------*/

void ultoa( unsigned long ulVal, char *pcBuffer, long lIgnore )
{
unsigned long lNibble;
long lIndex;

	/* Simple routine to convert an unsigned long value into a string in hex 
	format. */

	/* For each nibble in the number we are converting. */
	for( lIndex = 0; lIndex < ( sizeof( ulVal ) * 2 ); lIndex++ )
	{
		/* Take the top four bits of the number. */
		lNibble = ( ulVal >> 28 );

		/* We are converting it to a hex string, so is the number in the range
		0-10 or A-F? */
		if( lNibble < 10 )
		{
			pcBuffer[ lIndex ] = '0' + lNibble;
		}
		else
		{
			lNibble -= 10;
			pcBuffer[ lIndex ] = 'A' + lNibble;
		}

		/* Shift off the top nibble so we use the next nibble next time around. */
		ulVal <<= 4;
	}	

	/* Mark the end of the string with a null terminator. */
	pcBuffer[ lIndex ] = 0x00;
}
/*-----------------------------------------------------------*/

static void prvReadRegister( unsigned char *pucDestination, unsigned short usAddress, unsigned long ulLength )
{
unsigned char ucRxBuffer[ tcpMAX_REGISTER_LEN ];

	/* Read a register value from the WIZnet device. */

	/* First write out the address of the register we want to read. */
	i2cMessage( ucRxBuffer, i2cNO_DATA_REQUIRED, tcpDEVICE_ADDRESS, usAddress, i2cWRITE, NULL, portMAX_DELAY );
	
	/* Then read back from that address. */
	i2cMessage( ( unsigned char * ) pucDestination, ulLength, tcpDEVICE_ADDRESS, i2cNO_ADDR_REQUIRED, i2cREAD, xMessageComplete, portMAX_DELAY );

	/* I2C messages are queued so use the semaphore to wait for the read to 
	complete - otherwise we will leave this function before the I2C 
	transactions have completed. */
	xSemaphoreTake( xMessageComplete, tcpLONG_DELAY );
}
/*-----------------------------------------------------------*/

void vTCPHardReset( void )
{
	/* Physical reset of the WIZnet device by using the GPIO lines to hold the 
	WIZnet reset lines active for a few milliseconds. */

	/* Make sure the interrupt from the WIZnet is disabled. */
	VICIntEnClear |= tcpEINT0_VIC_CHANNEL_BIT;

	/* If xMessageComplete is NULL then this is the first time that this 
	function has been called and the queue and semaphore used in this file
	have not yet been created. */
	if( xMessageComplete == NULL )
	{
		/* Create and obtain the semaphore used when we want to wait for an i2c
		message to be completed. */
		vSemaphoreCreateBinary( xMessageComplete );
		xSemaphoreTake( xMessageComplete, tcpNO_DELAY );

		/* Create the queue used to communicate between the WIZnet and TCP tasks. */
		xTCPISRQueue = xQueueCreate( tcpISR_QUEUE_LENGTH, tcpISR_QUEUE_ITEM_SIZE );
	}

	/* Use the GPIO to reset the network hardware. */
	GPIO_IOCLR = tcpRESET_ACTIVE_LOW;
	GPIO_IOSET = tcpRESET_ACTIVE_HIGH;

	/* Delay with the network hardware in reset for a short while. */
	vTaskDelay( tcpRESET_DELAY );

	GPIO_IOCLR = tcpRESET_ACTIVE_HIGH;
	GPIO_IOSET = tcpRESET_ACTIVE_LOW;

	vTaskDelay( tcpINIT_DELAY );

	/* Setup the EINT0 to interrupt on required events from the WIZnet device.
	First enable the EINT0 function of the pin. */
	PCB_PINSEL1 |= tcpENABLE_EINT0_FUNCTION;
	
	/* We want the TCP comms to wake us from power save. */
	SCB_EXTWAKE = tcpWAKE_ON_EINT0;

	/* Install the ISR into the VIC - but don't enable it yet! */
	portENTER_CRITICAL();
	{
		extern void ( vEINT0_ISR_Wrapper )( void );

		VICIntSelect &= ~( tcpEINT0_VIC_CHANNEL_BIT );
		VICVectAddr3 = ( long ) vEINT0_ISR_Wrapper;

		VICVectCntl3 = tcpEINT0_VIC_CHANNEL | tcpEINT0_VIC_ENABLE;
	}
	portEXIT_CRITICAL();

	/* Enable interrupts in the WIZnet itself. */
	i2cMessage( ucDataEnableISR, sizeof( ucDataEnableISR ), tcpDEVICE_ADDRESS, tcpISR_MASK_REG, i2cWRITE, NULL, portMAX_DELAY );

	vTaskDelay( tcpLONG_DELAY );
}
/*-----------------------------------------------------------*/

long lTCPSoftReset( void )
{
unsigned char ucStatus;
extern volatile long lTransactionCompleted;

	/* Send a message to the WIZnet device to tell it set all it's registers
	back to their default states.  Then setup the WIZnet device as required. */

	/* Reset the internal WIZnet registers. */
	i2cMessage( ucDataReset,	sizeof( ucDataReset ),	tcpDEVICE_ADDRESS, tcpCOMMAND_REG, i2cWRITE, NULL, portMAX_DELAY );

	/* Now we can configure the protocol.   Here the MAC address, gateway 
	address, subnet mask and IP address are configured. */
	i2cMessage( ucDataSHAR,		sizeof( ucDataSHAR ),	tcpDEVICE_ADDRESS, tcpSOURCE_HA_REG, i2cWRITE, NULL, portMAX_DELAY );
	i2cMessage( ucDataGAR,		sizeof( ucDataGAR ),	tcpDEVICE_ADDRESS, tcpGATEWAY_ADDR_REG, i2cWRITE, NULL, portMAX_DELAY );
	i2cMessage( ucDataMSR,		sizeof( ucDataMSR ),	tcpDEVICE_ADDRESS, tcpSUBNET_MASK_REG,	i2cWRITE, NULL, portMAX_DELAY );
	i2cMessage( ucDataSIPR,		sizeof( ucDataSIPR ),	tcpDEVICE_ADDRESS, tpcSOURCE_IP_REG,	i2cWRITE, NULL, portMAX_DELAY );
	
	/* Next the memory buffers are configured to give all the WIZnet internal
	memory over to a single socket.  This gives the socket the maximum internal
	Tx and Rx buffer space. */
	i2cMessage( ucDataSetTxBufSize, sizeof( ucDataSetTxBufSize ), tcpDEVICE_ADDRESS, tcpTX_MEM_SIZE_REG, i2cWRITE, NULL, portMAX_DELAY );
	i2cMessage( ucDataSetRxBufSize, sizeof( ucDataSetRxBufSize ), tcpDEVICE_ADDRESS, tcpRX_MEM_SIZE_REG, i2cWRITE, NULL, portMAX_DELAY );

	/* Send the sys init command so the above parameters take effect. */
	i2cMessage( ucDataInit,		sizeof( ucDataInit ),	tcpDEVICE_ADDRESS, tcpCOMMAND_REG, i2cWRITE, NULL, portMAX_DELAY );

	/* Seems to like a little wait here. */
	vTaskDelay( tcpINIT_DELAY );

	/* Read back the status to ensure the system initialised ok. */
	prvReadRegister( &ucStatus, tcpINTERRUPT_STATUS_REG, tcpSTATUS_READ_LEN );

	/* We should find that the sys init was successful. */
	if( ucStatus != tcpISR_SYS_INIT )
	{
		return ( long ) pdFAIL;
	}

	/* No i2c errors yet. */
	portENTER_CRITICAL();
		lTransactionCompleted = pdTRUE;
	portEXIT_CRITICAL();

	return ( long ) pdPASS;
}
/*-----------------------------------------------------------*/

long lTCPCreateSocket( void )
{
unsigned char ucStatus;

	/* Create and configure a socket. */

	/* Setup and init the socket.  Here the port number is set and the socket
	is initialised. */
	i2cMessage( ucDataProtocol, sizeof( ucDataProtocol),tcpDEVICE_ADDRESS, tpcSOCKET_OPT_REG, i2cWRITE, NULL, portMAX_DELAY );
	i2cMessage( ucDataPort,		sizeof( ucDataPort),	tcpDEVICE_ADDRESS, tcpSOURCE_PORT_REG, i2cWRITE, NULL, portMAX_DELAY );
	i2cMessage( ucDataSockInit, sizeof( ucDataSockInit),tcpDEVICE_ADDRESS, tcpCOMMAND_REG, i2cWRITE, xMessageComplete, portMAX_DELAY );

	/* Wait for the Init command to be sent. */
	if( !xSemaphoreTake( xMessageComplete, tcpLONG_DELAY ) )
	{
		/* For some reason the message was not transmitted within our block
		period. */
		return ( long ) pdFAIL;
	}

	/* Allow the socket to initialise. */
	vTaskDelay( tcpINIT_DELAY );

	/* Read back the status to ensure the socket initialised ok. */
	prvReadRegister( &ucStatus, tcpINTERRUPT_STATUS_REG, tcpSTATUS_READ_LEN );
	
	/* We should find that the socket init was successful. */
	if( ucStatus != tcpISR_SOCKET_INIT )
	{
		return ( long ) pdFAIL;
	}


	/* Setup the Tx pointer registers to indicate that the Tx buffer is empty. */
	i2cMessage( ucDataTxReadPointer, sizeof( ucDataTxReadPointer ), tcpDEVICE_ADDRESS, tcpTX_READ_POINTER_REG, i2cWRITE, NULL, portMAX_DELAY );
	vTaskDelay( tcpSHORT_DELAY );
	i2cMessage( ucDataTxWritePointer, sizeof( ucDataTxWritePointer ), tcpDEVICE_ADDRESS, tcpTX_WRITE_POINTER_REG, i2cWRITE, NULL, portMAX_DELAY );
	vTaskDelay( tcpSHORT_DELAY );
	i2cMessage( ucDataTxAckPointer,	  sizeof( ucDataTxAckPointer ),	  tcpDEVICE_ADDRESS, tcpTX_ACK_POINTER_REG, i2cWRITE, NULL, portMAX_DELAY );
	vTaskDelay( tcpSHORT_DELAY );

	return ( long ) pdPASS;
}
/*-----------------------------------------------------------*/

void vTCPListen( void )
{
unsigned char ucISR;

	/* Start a passive listen on the socket. */

	/* Enable interrupts in the WizNet device after ensuring none are 
	currently pending. */
	while( SCB_EXTINT & tcpCLEAR_EINT0 )
	{
		/* The WIZnet device is still asserting and interrupt so tell it to 
		clear. */
		i2cMessage( ucDataClearInterrupt, sizeof( ucDataClearInterrupt ), tcpDEVICE_ADDRESS, tcpINTERRUPT_REG, i2cWRITE, xMessageComplete, portMAX_DELAY );
		xSemaphoreTake( xMessageComplete, tcpLONG_DELAY );

		vTaskDelay( 1 );
		SCB_EXTINT = tcpCLEAR_EINT0;
	}

	while( xQueueReceive( xTCPISRQueue, &ucISR, tcpNO_DELAY ) )
	{
		/* Just clearing the queue used by the ISR routine to tell this task
		that the WIZnet device needs attention. */
	}

	/* Now all the pending interrupts have been cleared we can enable the 
	processor interrupts. */
	VICIntEnable |= tcpEINT0_VIC_CHANNEL_BIT;

	/* Then start listening for incoming connections. */
	i2cMessage( ucDataListen, sizeof( ucDataListen ), tcpDEVICE_ADDRESS, tcpCOMMAND_REG, i2cWRITE, NULL, portMAX_DELAY );
}
/*-----------------------------------------------------------*/

long lProcessConnection( void )
{
unsigned char ucISR, ucState, ucLastState = 2, ucShadow;
extern volatile long lTransactionCompleted;
long lSameStateCount = 0, lDataSent = pdFALSE;
unsigned long ulWritePointer, ulAckPointer;

	/* No I2C errors can yet have occurred. */
	portENTER_CRITICAL();
		lTransactionCompleted = pdTRUE;
	portEXIT_CRITICAL();

	/* Keep looping - processing interrupts, until we have completed a 
	transaction.   This uses the WIZnet in it's simplest form.  The socket
	accepts a connection - we process the connection - then close the socket.
	We then go back to reinitialise everything and start again. */
	while( lTransactionCompleted == pdTRUE )
	{
		/* Wait for a message on the queue from the WIZnet ISR.  When the 
		WIZnet device asserts an interrupt the ISR simply posts a message
		onto this queue to wake this task. */
		if( xQueueReceive( xTCPISRQueue, &ucISR, tcpCONNECTION_WAIT_DELAY ) )
		{
			/* The ISR posted a message on this queue to tell us that the
			WIZnet device asserted an interrupt.  The ISR cannot process
			an I2C message so cannot tell us what caused the interrupt so
			we have to query the device here.  This task is the highest
			priority in the system so will run immediately following the ISR. */
			prvReadRegister( &ucISR, tcpINTERRUPT_STATUS_REG, tcpSTATUS_READ_LEN );

			/* Once we have read what caused the ISR we can clear the interrupt
			in the WIZnet. */
			i2cMessage( ucDataClearInterrupt, sizeof( ucDataClearInterrupt ), tcpDEVICE_ADDRESS, tcpINTERRUPT_REG, i2cWRITE, NULL, portMAX_DELAY );

			/* Now we can clear the processor interrupt and re-enable ready for
			the next. */
			SCB_EXTINT = tcpCLEAR_EINT0;
			VICIntEnable |= tcpEINT0_VIC_CHANNEL_BIT;
	
			/* Process the interrupt ... */

			if( ucISR & tcpISR_ESTABLISHED )
			{
				/* A connection has been established - respond by sending
				a receive command. */
				i2cMessage( ucDataReceiveCmd, sizeof( ucDataReceiveCmd ), tcpDEVICE_ADDRESS, tcpCOMMAND_REG, i2cWRITE, NULL, portMAX_DELAY );
			}
		
			if( ucISR & tcpISR_RX_COMPLETE )
			{
				/* We message has been received.  This will be an HTTP get 
				command.  We only have one page to send so just send it without
				regard to what the actual requested page was. */
				prvSendSamplePage();
			}
		
		 	if( ucISR & tcpISR_TX_COMPLETE )
			{
				/* We have a TX complete interrupt - which oddly does not 
				indicate that the message being sent is complete so we cannot
				yet close the socket.  Instead we read the position of the Tx
				pointer within the WIZnet device so we know how much data it
				has to send.  Later we will read the ack pointer and compare 
				this to the Tx pointer to ascertain whether the transmission 
				has completed. */

				/* First read the shadow register. */
				prvReadRegister( &ucShadow, tcpTX_WRITE_SHADOW_REG, tcpSHADOW_READ_LEN );
			
				/* Now a short delay is required. */
				vTaskDelay( tcpSHORT_DELAY );

				/* Then we can read the real register. */
				prvReadRegister( ( unsigned char * ) &ulWritePointer, tcpTX_WRITE_POINTER_REG, sizeof( ulWritePointer ) );

				/* We cannot do anything more here but need to remember that 
				this interrupt has occurred. */
				lDataSent = pdTRUE;
			}
		
			if( ucISR & tcpISR_CLOSED )
			{
				/* The socket has been closed so we can leave this function. */
				lTransactionCompleted = pdFALSE;
			}
		}
		else
		{
			/* We have not received an interrupt from the WIZnet device for a 
			while.  Read the socket status and check that everything is as
			expected. */
			prvReadRegister( &ucState, tcpSOCKET_STATE_REG, tcpSTATUS_READ_LEN );
			
			if( ( ucState == tcpSTATUS_ESTABLISHED ) && ( lDataSent > 0 ) ) 
			{
				/* The socket is established and we have already received a Tx
				end interrupt.  We must therefore be waiting for the Tx buffer
				inside the WIZnet device to be empty before we can close the
				socket. 

				Read the Ack pointer register to see if it has caught up with
				the Tx pointer register.  First we have to read the shadow 
				register. */
				prvReadRegister( &ucShadow, tcpTX_ACK_SHADOW_REG, tcpSHADOW_READ_LEN );
				vTaskDelay( tcpSHORT_DELAY );
				prvReadRegister( ( unsigned char * ) &ulAckPointer, tcpTX_ACK_POINTER_REG, sizeof( ulWritePointer ) );

				if( ulAckPointer == ulWritePointer )
				{
					/* The Ack and write pointer are now equal and we can 
					safely close the socket. */
					i2cMessage( ucDataDisconnect, sizeof( ucDataDisconnect ), tcpDEVICE_ADDRESS, tcpCOMMAND_REG, i2cWRITE, NULL, portMAX_DELAY );
				}
				else
				{
					/* Keep a count of how many times we encounter the Tx
					buffer still containing data. */
					lDataSent++;
					if( lDataSent > tcpMAX_ATTEMPTS_TO_CHECK_BUFFER )
					{
						/* Assume we cannot complete sending the data and 
						therefore cannot safely close the socket.  Start over. */
						vTCPHardReset();
						lTransactionCompleted = pdFALSE;
					}
				}
			}
			else if( ucState != tcpSTATUS_LISTEN )
			{
				/* If we have not yet received a Tx end interrupt we would only 
				ever expect to find the socket still listening for any 
				sustained period. */
				if( ucState == ucLastState )
				{
					lSameStateCount++;
					if( lSameStateCount > tcpMAX_NON_LISTEN_STAUS_READS )
					{						
						/* We are persistently in an unexpected state.  Assume
						we cannot safely close the socket and start over. */
						vTCPHardReset();
						lTransactionCompleted = pdFALSE;
					}
				}
			}
			else
			{
				/* We are in the listen state so are happy that everything
				is as expected. */
				lSameStateCount = 0;
			}

			/* Remember what state we are in this time around so we can check
			for a persistence on an unexpected state. */
			ucLastState = ucState;
		}
	}

	/* We are going to reinitialise the WIZnet device so do not want our 
	interrupts from the WIZnet to be processed. */
	VICIntEnClear |= tcpEINT0_VIC_CHANNEL_BIT;
	return lTransactionCompleted;
}
/*-----------------------------------------------------------*/

static void prvWriteString( const char * const pucTxBuffer, long lTxLen, unsigned long *pulTxAddress )
{
unsigned long ulSendAddress;

	/* Send a string to the Tx buffer internal to the WIZnet device. */

	/* Calculate the address to which we are going to write in the buffer. */
	ulSendAddress = ( *pulTxAddress & tcpSINGLE_SOCKET_ADDR_MASK ) + tcpSINGLE_SOCKET_ADDR_OFFSET;

	/* Send the buffer to the calculated address.  Use the semaphore so we
	can wait until the entire message has been transferred. */
	i2cMessage( ( unsigned char * ) pucTxBuffer, lTxLen, tcpDEVICE_ADDRESS, ( unsigned short ) ulSendAddress, i2cWRITE, xMessageComplete, portMAX_DELAY );

	/* Wait until the semaphore indicates that the message has been transferred. */
	if( !xSemaphoreTake( xMessageComplete, tcpLONG_DELAY ) )
	{
		return;
	}

	/* Return the new address of the end of the buffer (within the WIZnet 
	device). */
	*pulTxAddress += ( unsigned long ) lTxLen;
}
/*-----------------------------------------------------------*/

static void prvFlushBuffer( unsigned long ulTxAddress )
{
unsigned char ucTxBuffer[ tcpMAX_REGISTER_LEN ];

	/* We have written some data to the Tx buffer internal to the WIZnet
	device.  Now we update the Tx pointer inside the WIZnet then send a
	Send command - which causes	the data up to the new Tx pointer to be 
	transmitted. */

	/* Make sure endieness is correct for transmission. */
	ulTxAddress = htonl( ulTxAddress );

	/* Place the new Tx pointer in the string to be transmitted. */
	ucTxBuffer[ 0 ] = ( unsigned char ) ( ulTxAddress & 0xff );
	ulTxAddress >>= 8;
	ucTxBuffer[ 1 ] = ( unsigned char ) ( ulTxAddress & 0xff );
	ulTxAddress >>= 8;
	ucTxBuffer[ 2 ] = ( unsigned char ) ( ulTxAddress & 0xff );
	ulTxAddress >>= 8;
	ucTxBuffer[ 3 ] = ( unsigned char ) ( ulTxAddress & 0xff );
	ulTxAddress >>= 8;

	/* And send it to the WIZnet device. */
	i2cMessage( ucTxBuffer, sizeof( ulTxAddress ), tcpDEVICE_ADDRESS, tcpTX_WRITE_POINTER_REG, i2cWRITE, xMessageComplete, portMAX_DELAY );

	if( !xSemaphoreTake( xMessageComplete, tcpLONG_DELAY ) )
	{
		return;
	}

	vTaskDelay( tcpSHORT_DELAY );

	/* Transmit! */
	i2cMessage( ucDataSend, sizeof( ucDataSend ), tcpDEVICE_ADDRESS, tcpCOMMAND_REG, i2cWRITE, xMessageComplete, portMAX_DELAY );

	if( !xSemaphoreTake( xMessageComplete, tcpLONG_DELAY ) )
	{
		return;
	}
}
/*-----------------------------------------------------------*/

static void prvSendSamplePage( void )
{
extern long lErrorInTask;
unsigned long ulTxAddress;
unsigned char ucShadow;
long lIndex;
static unsigned long ulRefreshCount = 0x00;
static char cPageBuffer[ tcpBUFFER_LEN ];


	/* This function just generates a sample page of HTML which gets
	sent each time a client attaches to the socket.  The page is created
	from two fixed strings (cSamplePageFirstPart and cSamplePageSecondPart)
	with a bit of dynamically generated data in the middle. */

	/* We need to know the address to which the html string should be sent
	in the WIZnet Tx buffer.  First read the shadow register. */
	prvReadRegister( &ucShadow, tcpTX_WRITE_SHADOW_REG, tcpSHADOW_READ_LEN );

	/* Now a short delay is required. */
	vTaskDelay( tcpSHORT_DELAY );

	/* Now we can read the real pointer value. */
	prvReadRegister( ( unsigned char * ) &ulTxAddress, tcpTX_WRITE_POINTER_REG, sizeof( ulTxAddress ) );

	/* Make sure endieness is correct. */
	ulTxAddress = htonl( ulTxAddress );

	/* Send the start of the page. */
	prvWriteString( cSamplePageFirstPart, strlen( cSamplePageFirstPart ), &ulTxAddress );

	/* Generate a bit of dynamic data and place it in the buffer ready to be
	transmitted. */
	strcpy( cPageBuffer, "<BR>Number of ticks since boot = 0x" );
	lIndex = strlen( cPageBuffer );
	ultoa( xTaskGetTickCount(), &( cPageBuffer[ lIndex ] ), 0 );
	strcat( cPageBuffer, "<br>Number of tasks executing = ");
	lIndex = strlen( cPageBuffer );
	ultoa( ( unsigned long ) uxTaskGetNumberOfTasks(), &( cPageBuffer[ lIndex ] ), 0 );
	strcat( cPageBuffer, "<br>IO port 0 state (used by flash tasks) = 0x" );
	lIndex = strlen( cPageBuffer );
	ultoa( ( unsigned long ) GPIO0_IOPIN, &( cPageBuffer[ lIndex ] ), 0 );
	strcat( cPageBuffer, "<br>Refresh = 0x" );
	lIndex = strlen( cPageBuffer );
	ultoa( ( unsigned long ) ulRefreshCount, &( cPageBuffer[ lIndex ] ), 0 );
	
	if( lErrorInTask )
	{
		strcat( cPageBuffer, "<p>An error has occurred in at least one task." );
	}
	else
	{
		strcat( cPageBuffer, "<p>All tasks executing without error." );		
	}

	ulRefreshCount++;

	/* Send the dynamically generated string. */
	prvWriteString( cPageBuffer, strlen( cPageBuffer ), &ulTxAddress );

	/* Finish the page. */
	prvWriteString( cSamplePageSecondPart, strlen( cSamplePageSecondPart ), &ulTxAddress );

	/* Tell the WIZnet to send the data we have just written to its Tx buffer. */
	prvFlushBuffer( ulTxAddress );
}

