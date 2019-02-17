/*
 * FreeRTOS Kernel V10.2.0
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
	USB Communications Device Class driver.
	Implements task vUSBCDCTask and provides an Abstract Control Model serial 
	interface.  Control is through endpoint 0, device-to-host notification is 
	provided by interrupt-in endpoint 3, and raw data is transferred through 
	bulk endpoints 1 and 2.

	- developed from original FreeRTOS HID example by Scott Miller
	- modified to support 3.2 GCC by najay
*/

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* Demo board includes. */
#include "Board.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo app includes. */
#include "USB-CDC.h"
#include "descriptors.h"

#define usbNO_BLOCK ( ( TickType_t ) 0 )

/* Reset all endpoints */
static void prvResetEndPoints( void );

/* Clear pull up resistor to detach device from host */
static void vDetachUSBInterface( void );

/* Set up interface and initialize variables */
static void vInitUSBInterface( void );

/* Handle control endpoint events. */
static void prvProcessEndPoint0Interrupt( xISRStatus *pxMessage );

/* Handle standard device requests. */
static void prvHandleStandardDeviceRequest( xUSB_REQUEST *pxRequest );

/* Handle standard interface requests. */
static void prvHandleStandardInterfaceRequest( xUSB_REQUEST *pxRequest );

/* Handle endpoint requests. */
static void prvHandleStandardEndPointRequest( xUSB_REQUEST *pxRequest );

/* Handle class interface requests. */
static void prvHandleClassInterfaceRequest( xUSB_REQUEST *pxRequest );

/* Prepare control data transfer.  prvSendNextSegment starts transfer. */
static void prvSendControlData( unsigned char *pucData, unsigned short usRequestedLength, unsigned long ulLengthLeftToSend, long lSendingDescriptor );

/* Send next segment of data for the control transfer */
static void prvSendNextSegment( void );

/* Send stall - used to respond to unsupported requests */
static void prvSendStall( void );

/* Send a zero-length (null) packet */
static void prvSendZLP( void );

/* Handle requests for standard interface descriptors */
static void prvGetStandardInterfaceDescriptor( xUSB_REQUEST *pxRequest );

/*------------------------------------------------------------*/

/* File scope static variables */
static unsigned char ucUSBConfig = ( unsigned char ) 0;
static unsigned long ulReceivedAddress = ( unsigned long ) 0;
static eDRIVER_STATE eDriverState = eNOTHING;

/* Incoming and outgoing control data structures */
static xCONTROL_MESSAGE pxControlTx;
static xCONTROL_MESSAGE pxControlRx;

/* Queue holding pointers to pending messages */
QueueHandle_t xUSBInterruptQueue; 

/* Queues used to hold received characters, and characters waiting to be
transmitted.  Rx queue must be larger than FIFO size. */
static QueueHandle_t xRxCDC; 
static QueueHandle_t xTxCDC; 

/* Line coding - 115,200 baud, N-8-1 */
static const unsigned char pxLineCoding[] = { 0x00, 0xC2, 0x01, 0x00, 0x00, 0x00, 0x08 };

/* Status variables. */
static unsigned char ucControlState;
static unsigned int uiCurrentBank;


/*------------------------------------------------------------*/


void vUSBCDCTask( void *pvParameters )
{
xISRStatus *pxMessage;
unsigned long ulStatus;
unsigned long ulRxBytes;
unsigned char ucByte;
portBASE_TYPE xByte;

	( void ) pvParameters;

	/* Disconnect USB device from hub.  For debugging - causes host to register reset */
	portENTER_CRITICAL();
		 vDetachUSBInterface();
	portEXIT_CRITICAL();
	
	vTaskDelay( portTICK_PERIOD_MS * 60 );

	/* Init USB interface */
	portENTER_CRITICAL();
		vInitUSBInterface();
	portEXIT_CRITICAL();
	
	/* Main task loop.  Process incoming endpoint 0 interrupts, handle data transfers. */
	 
	for( ;; )
	{
		/* Look for data coming from the ISR. */
		if( xQueueReceive( xUSBInterruptQueue, &pxMessage, usbSHORTEST_DELAY ) )
		{
			if( pxMessage->ulISR & AT91C_UDP_EPINT0 )
			{
				/* All endpoint 0 interrupts are handled here. */
				prvProcessEndPoint0Interrupt( pxMessage );
			}

			if( pxMessage->ulISR & AT91C_UDP_ENDBUSRES )
			{
				/* End of bus reset - reset the endpoints and de-configure. */
				prvResetEndPoints();		
			}
		}
		
		/* See if we're ready to send and receive data. */
		if( eDriverState == eREADY_TO_SEND && ucControlState ) 
		{
			if( ( !(AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_2 ] & AT91C_UDP_TXPKTRDY) ) && uxQueueMessagesWaiting( xTxCDC ) )
			{
				for( xByte = 0; xByte < 64; xByte++ )
				{				   
					if( !xQueueReceive( xTxCDC, &ucByte, 0 ) ) 
					{
						/* No data buffered to transmit. */
						break;
					}

					/* Got a byte to transmit. */
					AT91C_BASE_UDP->UDP_FDR[ usbEND_POINT_2 ] = ucByte;
				} 
				AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_2 ] |= AT91C_UDP_TXPKTRDY;
			}

			/* Check for incoming data (host-to-device) on endpoint 1. */
			while( AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] & (AT91C_UDP_RX_DATA_BK0 | AT91C_UDP_RX_DATA_BK1) )
			{
				ulRxBytes = (AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] >> 16) & usbRX_COUNT_MASK;

				/* Only process FIFO if there's room to store it in the queue */
				if( ulRxBytes < ( USB_CDC_QUEUE_SIZE - uxQueueMessagesWaiting( xRxCDC ) ) )
				{
					while( ulRxBytes-- )
					{
						ucByte = AT91C_BASE_UDP->UDP_FDR[ usbEND_POINT_1 ];
						xQueueSend( xRxCDC, &ucByte, 0 );
					}

					/* Release the FIFO */
					portENTER_CRITICAL();
					{
						ulStatus = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ];
						usbCSR_CLEAR_BIT( &ulStatus, uiCurrentBank );
						AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] = ulStatus;
					}
					portEXIT_CRITICAL();

					/* Re-enable endpoint 1's interrupts */
					AT91C_BASE_UDP->UDP_IER = AT91C_UDP_EPINT1;
				
					/* Update the current bank in use */
					if( uiCurrentBank == AT91C_UDP_RX_DATA_BK0 ) 
					{
						uiCurrentBank = AT91C_UDP_RX_DATA_BK1;
					}
					else 
					{
						uiCurrentBank = AT91C_UDP_RX_DATA_BK0;
					}

				}
				else 
				{
					break;
				}
			}
		}
	}
}
/*------------------------------------------------------------*/

void vUSBSendByte( char cByte )
{
	/* Queue the byte to be sent.  The USB task will send it. */
	xQueueSend( xTxCDC, &cByte, usbNO_BLOCK );
}
/*------------------------------------------------------------*/

static void prvSendZLP( void )
{
unsigned long ulStatus;

	/* Wait until the FIFO is free - even though we are not going to use it.
	THERE IS NO TIMEOUT HERE! */
	while( AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] & AT91C_UDP_TXPKTRDY )
	{
		vTaskDelay( usbSHORTEST_DELAY );
	}

	portENTER_CRITICAL();
	{
		/* Cancel any further pending data */
		pxControlTx.ulTotalDataLength = pxControlTx.ulNextCharIndex;

		/* Set the TXPKTRDY bit to cause a transmission with no data. */
		ulStatus = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];
		usbCSR_SET_BIT( &ulStatus, AT91C_UDP_TXPKTRDY );
		AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulStatus;
	}
	portEXIT_CRITICAL();
}
/*------------------------------------------------------------*/

static void prvSendStall( void )
{
	unsigned long ulStatus;

	portENTER_CRITICAL();
	{
		/* Force a stall by simply setting the FORCESTALL bit in the CSR. */
		ulStatus = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];
		usbCSR_SET_BIT( &ulStatus, AT91C_UDP_FORCESTALL );
		AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulStatus;
	}
	portEXIT_CRITICAL();
}
/*------------------------------------------------------------*/

static void prvResetEndPoints( void )
{
unsigned long ulTemp;

	eDriverState = eJUST_RESET;
	ucControlState = 0;

	/* Reset all the end points. */
	AT91C_BASE_UDP->UDP_RSTEP  = usbEND_POINT_RESET_MASK;
	AT91C_BASE_UDP->UDP_RSTEP  = ( unsigned long ) 0x00;

	/* Enable data to be sent and received. */
	AT91C_BASE_UDP->UDP_FADDR = AT91C_UDP_FEN;

	/* Repair the configuration end point. */
	portENTER_CRITICAL();
	{
		ulTemp = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];
		usbCSR_SET_BIT( &ulTemp, ( ( unsigned long ) ( AT91C_UDP_EPEDS | AT91C_UDP_EPTYPE_CTRL ) ) );
		AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulTemp;
		AT91C_BASE_UDP->UDP_IER = AT91C_UDP_EPINT0;
	}
	portEXIT_CRITICAL();
	uiCurrentBank = AT91C_UDP_RX_DATA_BK0;
}
/*------------------------------------------------------------*/

static void prvProcessEndPoint0Interrupt( xISRStatus *pxMessage )
{
static xUSB_REQUEST xRequest;
unsigned long ulRxBytes;

	/* Get number of bytes received, if any */
	ulRxBytes = pxMessage->ulCSR0 >> 16;
	ulRxBytes &= usbRX_COUNT_MASK;

	if( pxMessage->ulCSR0 & AT91C_UDP_TXCOMP )
	{
		/* We received a TX complete interrupt.  What we do depends on
		what we sent to get this interrupt. */

		if( eDriverState == eJUST_GOT_CONFIG )
		{
			/* We sent an acknowledgement of a SET_CONFIG request.  We
			are now at the end of the enumeration.
			
			TODO: Config 0 sets unconfigured state, should enter Address state.
			Request for unsupported config should stall. */
			AT91C_BASE_UDP->UDP_GLBSTATE = AT91C_UDP_CONFG;
			
			/* Set up endpoints */
			portENTER_CRITICAL();
			{
				unsigned long ulTemp;

				/* Set endpoint 1 to bulk-out */
				ulTemp = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ];					
				usbCSR_SET_BIT( &ulTemp, AT91C_UDP_EPEDS | AT91C_UDP_EPTYPE_BULK_OUT );
				AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] = ulTemp;		
				AT91C_BASE_UDP->UDP_IER = AT91C_UDP_EPINT1;
				/* Set endpoint 2 to bulk-in */
				ulTemp = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_2 ];					
				usbCSR_SET_BIT( &ulTemp, AT91C_UDP_EPEDS | AT91C_UDP_EPTYPE_BULK_IN );
				AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_2 ] = ulTemp;		
				AT91C_BASE_UDP->UDP_IER = AT91C_UDP_EPINT2;
					/* Set endpoint 3 to interrupt-in, enable it, and enable interrupts */
				ulTemp = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_3 ];					
				usbCSR_SET_BIT( &ulTemp, AT91C_UDP_EPEDS | AT91C_UDP_EPTYPE_INT_IN );
				AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_3 ] = ulTemp;		
				/*AT91F_UDP_EnableIt( AT91C_BASE_UDP, AT91C_UDP_EPINT3 );				 */
			}
			portEXIT_CRITICAL();

			eDriverState = eREADY_TO_SEND;
		}		
		else if( eDriverState == eJUST_GOT_ADDRESS )
		{
			/* We sent an acknowledgement of a SET_ADDRESS request.  Move
			to the addressed state. */
			if( ulReceivedAddress != ( unsigned long ) 0 )
			{			
				AT91C_BASE_UDP->UDP_GLBSTATE = AT91C_UDP_FADDEN;
			}
			else
			{
				AT91C_BASE_UDP->UDP_GLBSTATE = 0;
			}			

			AT91C_BASE_UDP->UDP_FADDR = ( AT91C_UDP_FEN | ulReceivedAddress );		
			eDriverState = eNOTHING;
		}
		else
		{		
			/* The TXCOMP was not for any special type of transmission.  See
			if there is any more data to send. */
			prvSendNextSegment();
		}
	}

	if( pxMessage->ulCSR0 & AT91C_UDP_RX_DATA_BK0 )
	{
		/* Received a control data packet.  May be a 0-length ACK or a data stage. */
		unsigned char ucBytesToGet;
	 
		/* Got data.  Cancel any outgoing data. */
		pxControlTx.ulNextCharIndex = pxControlTx.ulTotalDataLength;
		
		 /* Determine how many bytes we need to receive. */
		ucBytesToGet = pxControlRx.ulTotalDataLength - pxControlRx.ulNextCharIndex;
		if( ucBytesToGet > ulRxBytes ) 
		{	
			ucBytesToGet = ulRxBytes;
		}

		/* If we're not expecting any data, it's an ack - just quit now. */
		if( !ucBytesToGet )
		{
			 return;
		}

		/* Get the required data and update the index. */
		memcpy( pxControlRx.ucBuffer, pxMessage->ucFifoData, ucBytesToGet );
		pxControlRx.ulNextCharIndex += ucBytesToGet;	
	}

	if( pxMessage->ulCSR0 & AT91C_UDP_RXSETUP )
	{
		/* Received a SETUP packet.  May be followed by data packets. */

		if( ulRxBytes >= usbEXPECTED_NUMBER_OF_BYTES )
		{		 		
			/* Create an xUSB_REQUEST variable from the raw bytes array. */

			xRequest.ucReqType = pxMessage->ucFifoData[ usbREQUEST_TYPE_INDEX ];
			xRequest.ucRequest = pxMessage->ucFifoData[ usbREQUEST_INDEX ];

			xRequest.usValue = pxMessage->ucFifoData[ usbVALUE_HIGH_BYTE ];
			xRequest.usValue <<= 8;
			xRequest.usValue |= pxMessage->ucFifoData[ usbVALUE_LOW_BYTE ];
						
			xRequest.usIndex = pxMessage->ucFifoData[ usbINDEX_HIGH_BYTE ];
			xRequest.usIndex <<= 8;
			xRequest.usIndex |= pxMessage->ucFifoData[ usbINDEX_LOW_BYTE ];
			
			xRequest.usLength = pxMessage->ucFifoData[ usbLENGTH_HIGH_BYTE ];
			xRequest.usLength <<= 8;
			xRequest.usLength |= pxMessage->ucFifoData[ usbLENGTH_LOW_BYTE ];

			pxControlRx.ulNextCharIndex = 0;
			if( ! (xRequest.ucReqType & 0x80) ) /* Host-to-Device transfer, may need to get data first */
			{
				if( xRequest.usLength > usbMAX_CONTROL_MESSAGE_SIZE )
				{	
					/* Too big!  No space for control data, stall and abort. */
					prvSendStall();
					return;
				}

				pxControlRx.ulTotalDataLength = xRequest.usLength;
			}
			else
			{
				/* We're sending the data, don't wait for any. */
				pxControlRx.ulTotalDataLength = 0; 
			}
		}
	}

	/* See if we've got a pending request and all its associated data ready */
	if( ( pxMessage->ulCSR0 & ( AT91C_UDP_RX_DATA_BK0 | AT91C_UDP_RXSETUP ) ) 
		&& ( pxControlRx.ulNextCharIndex >= pxControlRx.ulTotalDataLength ) )
	{
		unsigned char ucRequest;

		/* Manipulate the ucRequestType and the ucRequest parameters to 
		generate a zero based request selection.  This is just done to 
		break up the requests into subsections for clarity.  The 
		alternative would be to have more huge switch statement that would
		be difficult to optimise. */
		ucRequest = ( ( xRequest.ucReqType & 0x60 ) >> 3 );
		ucRequest |= ( xRequest.ucReqType & 0x03 );
			
		switch( ucRequest )
		{
			case usbSTANDARD_DEVICE_REQUEST:	
				/* Standard Device request */
				prvHandleStandardDeviceRequest( &xRequest );
				break;

			case usbSTANDARD_INTERFACE_REQUEST:	
				/* Standard Interface request */
				prvHandleStandardInterfaceRequest( &xRequest );
				break;

			case usbSTANDARD_END_POINT_REQUEST:	
				/* Standard Endpoint request */
				prvHandleStandardEndPointRequest( &xRequest );
				break;

			case usbCLASS_INTERFACE_REQUEST:	
				/* Class Interface request */
				prvHandleClassInterfaceRequest( &xRequest );
				break;

			default:	/* This is not something we want to respond to. */
				prvSendStall();	
		}
	}
}
/*------------------------------------------------------------*/

static void prvGetStandardDeviceDescriptor( xUSB_REQUEST *pxRequest )
{
	/* The type is in the high byte.  Return whatever has been requested. */
	switch( ( pxRequest->usValue & 0xff00 ) >> 8 )
	{
		case usbDESCRIPTOR_TYPE_DEVICE:
			prvSendControlData( ( unsigned char * ) &pxDeviceDescriptor, pxRequest->usLength, sizeof( pxDeviceDescriptor ), pdTRUE );
			break;

		case usbDESCRIPTOR_TYPE_CONFIGURATION:
			prvSendControlData( ( unsigned char * ) &( pxConfigDescriptor ), pxRequest->usLength, sizeof( pxConfigDescriptor ), pdTRUE );
			break;

		case usbDESCRIPTOR_TYPE_STRING:

			/* The index to the string descriptor is the lower byte. */
			switch( pxRequest->usValue & 0xff )
			{			
				case usbLANGUAGE_STRING:
					prvSendControlData( ( unsigned char * ) &pxLanguageStringDescriptor, pxRequest->usLength, sizeof(pxLanguageStringDescriptor), pdTRUE );
					break;

				case usbMANUFACTURER_STRING:
					prvSendControlData( ( unsigned char * ) &pxManufacturerStringDescriptor, pxRequest->usLength, sizeof( pxManufacturerStringDescriptor ), pdTRUE );
					break;

				case usbPRODUCT_STRING:
					prvSendControlData( ( unsigned char * ) &pxProductStringDescriptor, pxRequest->usLength, sizeof( pxProductStringDescriptor ), pdTRUE );
					break;

				case usbCONFIGURATION_STRING:
					prvSendControlData( ( unsigned char * ) &pxConfigurationStringDescriptor, pxRequest->usLength, sizeof( pxConfigurationStringDescriptor ), pdTRUE );
					break;

				case usbINTERFACE_STRING:
					prvSendControlData( ( unsigned char * ) &pxInterfaceStringDescriptor, pxRequest->usLength, sizeof( pxInterfaceStringDescriptor ), pdTRUE );
					break;

				default:
					prvSendStall();
					break;
			}
			break;

		default:
			prvSendStall();
			break;
	}
}
/*------------------------------------------------------------*/

static void prvHandleStandardDeviceRequest( xUSB_REQUEST *pxRequest )
{
unsigned short usStatus = 0;

	switch( pxRequest->ucRequest )
	{
		case usbGET_STATUS_REQUEST:
			/* Just send two byte dummy status. */
			prvSendControlData( ( unsigned char * ) &usStatus, sizeof( usStatus ), sizeof( usStatus ), pdFALSE );
			break;

		case usbGET_DESCRIPTOR_REQUEST:
			/* Send device descriptor */
			prvGetStandardDeviceDescriptor( pxRequest );
			break;

		case usbGET_CONFIGURATION_REQUEST:
			/* Send selected device configuration */
			prvSendControlData( ( unsigned char * ) &ucUSBConfig, sizeof( ucUSBConfig ), sizeof( ucUSBConfig ), pdFALSE );
			break;

		case usbSET_FEATURE_REQUEST:
			prvSendZLP();
			break;

		case usbSET_ADDRESS_REQUEST:			
			/* Get assigned address and send ack, but don't implement new address until we get a TXCOMP */
			prvSendZLP();			
			eDriverState = eJUST_GOT_ADDRESS;			
			ulReceivedAddress = ( unsigned long ) pxRequest->usValue;
			break;

		case usbSET_CONFIGURATION_REQUEST:
			/* Ack SET_CONFIGURATION request, but don't implement until TXCOMP */
			ucUSBConfig = ( unsigned char ) ( pxRequest->usValue & 0xff );
			eDriverState = eJUST_GOT_CONFIG;
			prvSendZLP();
			break;

		default:
			/* Any unsupported request results in a STALL response. */
			prvSendStall();
			break;
	}
}
/*------------------------------------------------------------*/

static void prvHandleClassInterfaceRequest( xUSB_REQUEST *pxRequest )
{
	switch( pxRequest->ucRequest )
	{
		case usbSEND_ENCAPSULATED_COMMAND:
			prvSendStall();
			break;

		case usbGET_ENCAPSULATED_RESPONSE:
			prvSendStall();
			break;

		case usbSET_LINE_CODING:
			/* Set line coding - baud rate, data bits, parity, stop bits */
			prvSendZLP();
			memcpy( ( void * ) pxLineCoding, pxControlRx.ucBuffer, sizeof( pxLineCoding ) );
			break;

		case usbGET_LINE_CODING:
			/* Get line coding */
			prvSendControlData( (unsigned char *) &pxLineCoding, pxRequest->usLength, sizeof( pxLineCoding ), pdFALSE );
			break;

		case usbSET_CONTROL_LINE_STATE:
			/* D0: 1=DTR, 0=No DTR,  D1: 1=Activate Carrier, 0=Deactivate carrier (RTS, half-duplex) */
			prvSendZLP();
			ucControlState = pxRequest->usValue;
			break;

		default:
			prvSendStall();
			break;
	}
}
/*------------------------------------------------------------*/

static void prvGetStandardInterfaceDescriptor( xUSB_REQUEST *pxRequest )
{
	switch( ( pxRequest->usValue & ( unsigned short ) 0xff00 ) >> 8 )
	{
		default:
			prvSendStall();
			break;
	}
}
/*-----------------------------------------------------------*/

static void prvHandleStandardInterfaceRequest( xUSB_REQUEST *pxRequest )
{
unsigned short usStatus = 0;

	switch( pxRequest->ucRequest )
	{
		case usbGET_STATUS_REQUEST:
			/* Send dummy 2 bytes. */
			prvSendControlData( ( unsigned char * ) &usStatus, sizeof( usStatus ), sizeof( usStatus ), pdFALSE );
			break;

		case usbGET_DESCRIPTOR_REQUEST:
			prvGetStandardInterfaceDescriptor( pxRequest ); 
			break;

		/* This minimal implementation does not respond to these. */
		case usbGET_INTERFACE_REQUEST:
		case usbSET_FEATURE_REQUEST:
		case usbSET_INTERFACE_REQUEST:	

		default:
			prvSendStall();
			break;
	}
}
/*-----------------------------------------------------------*/

static void prvHandleStandardEndPointRequest( xUSB_REQUEST *pxRequest )
{
	switch( pxRequest->ucRequest )
	{
		/* This minimal implementation does not expect to respond to these. */
		case usbGET_STATUS_REQUEST:
		case usbCLEAR_FEATURE_REQUEST: 
		case usbSET_FEATURE_REQUEST:

		default:			
			prvSendStall();
			break;
	}
}
/*-----------------------------------------------------------*/

static void vDetachUSBInterface( void)
{
	/* Setup the PIO for the USB pull up resistor. */
	AT91C_BASE_PIOA->PIO_PER = AT91C_PIO_PA16;
	AT91C_BASE_PIOA->PIO_OER = AT91C_PIO_PA16;


	/* Disable pull up */
	AT91C_BASE_PIOA->PIO_SODR = AT91C_PIO_PA16;
} 
/*-----------------------------------------------------------*/

static void vInitUSBInterface( void )
{
extern void ( vUSB_ISR_Wrapper )( void );

	/* Create the queue used to communicate between the USB ISR and task. */
	xUSBInterruptQueue = xQueueCreate( usbQUEUE_LENGTH + 1, sizeof( xISRStatus * ) );
	
	/* Create the queues used to hold Rx and Tx characters. */
	xRxCDC = xQueueCreate( USB_CDC_QUEUE_SIZE, ( unsigned char ) sizeof( signed char ) );
	xTxCDC = xQueueCreate( USB_CDC_QUEUE_SIZE + 1, ( unsigned char ) sizeof( signed char ) );

	if( (!xUSBInterruptQueue) || (!xRxCDC) || (!xTxCDC) )
	{	
		/* Not enough RAM to create queues!. */
		return;
	}
	
	/* Initialise a few state variables. */
	pxControlTx.ulNextCharIndex = ( unsigned long ) 0;
	pxControlRx.ulNextCharIndex = ( unsigned long ) 0;
	ucUSBConfig = ( unsigned char ) 0;
	eDriverState = eNOTHING;
	ucControlState = 0;
	uiCurrentBank = AT91C_UDP_RX_DATA_BK0;


	/* HARDWARE SETUP */

	/* Set the PLL USB Divider */
	AT91C_BASE_CKGR->CKGR_PLLR |= AT91C_CKGR_USBDIV_1;

	/* Enables the 48MHz USB clock UDPCK and System Peripheral USB Clock. */
	AT91C_BASE_PMC->PMC_SCER = AT91C_PMC_UDP;
	AT91C_BASE_PMC->PMC_PCER = (1 << AT91C_ID_UDP);

	/* Setup the PIO for the USB pull up resistor. */
	AT91C_BASE_PIOA->PIO_PER = AT91C_PIO_PA16;
	AT91C_BASE_PIOA->PIO_OER = AT91C_PIO_PA16;


	/* Start without the pullup - this will get set at the end of this 
	function. */
   	AT91C_BASE_PIOA->PIO_SODR = AT91C_PIO_PA16;


	/* When using the USB debugger the peripheral registers do not always get
	set to the correct default values.  To make sure set the relevant registers
	manually here. */
	AT91C_BASE_UDP->UDP_IDR = ( unsigned long ) 0xffffffff;
	AT91C_BASE_UDP->UDP_ICR = ( unsigned long ) 0xffffffff;
	AT91C_BASE_UDP->UDP_CSR[ 0 ] = ( unsigned long ) 0x00;
	AT91C_BASE_UDP->UDP_CSR[ 1 ] = ( unsigned long ) 0x00;
	AT91C_BASE_UDP->UDP_CSR[ 2 ] = ( unsigned long ) 0x00;
	AT91C_BASE_UDP->UDP_CSR[ 3 ] = ( unsigned long ) 0x00;
	AT91C_BASE_UDP->UDP_GLBSTATE = 0;
	AT91C_BASE_UDP->UDP_FADDR = 0;

	/* Enable the transceiver. */
	AT91C_UDP_TRANSCEIVER_ENABLE = 0;

	/* Enable the USB interrupts - other interrupts get enabled as the 
	enumeration process progresses. */
	AT91F_AIC_ConfigureIt( AT91C_ID_UDP, usbINTERRUPT_PRIORITY, AT91C_AIC_SRCTYPE_INT_HIGH_LEVEL, ( void (*)( void ) ) vUSB_ISR_Wrapper );
	AT91C_BASE_AIC->AIC_IECR = 0x1 << AT91C_ID_UDP;


	/* Wait a short while before making our presence known. */
	vTaskDelay( usbINIT_DELAY );
	AT91C_BASE_PIOA->PIO_CODR = AT91C_PIO_PA16;
}
/*-----------------------------------------------------------*/

static void prvSendControlData( unsigned char *pucData, unsigned short usRequestedLength, unsigned long ulLengthToSend, long lSendingDescriptor )
{
	if( ( ( unsigned long ) usRequestedLength < ulLengthToSend ) )
	{
		/* Cap the data length to that requested. */
		ulLengthToSend = ( unsigned short ) usRequestedLength;
	}
	else if( ( ulLengthToSend < ( unsigned long ) usRequestedLength ) && lSendingDescriptor )
	{
		/* We are sending a descriptor.  If the descriptor is an exact 
		multiple of the FIFO length then it will have to be terminated
		with a NULL packet.  Set the state to indicate this if
		necessary. */
		if( ( ulLengthToSend % usbFIFO_LENGTH ) == 0 )
		{
			eDriverState = eSENDING_EVEN_DESCRIPTOR;
		}
	}

	/* Here we assume that the previous message has been sent.  THERE IS NO
	BUFFER OVERFLOW PROTECTION HERE.

	Copy the data to send into the buffer as we cannot send it all at once
	(if it is greater than 8 bytes in length). */
	memcpy( pxControlTx.ucBuffer, pucData, ulLengthToSend );

	/* Reinitialise the buffer index so we start sending from the start of 
	the data. */
	pxControlTx.ulTotalDataLength = ulLengthToSend;
	pxControlTx.ulNextCharIndex = ( unsigned long ) 0;

	/* Send the first 8 bytes now.  The rest will get sent in response to 
	TXCOMP interrupts. */
	prvSendNextSegment();
}
/*-----------------------------------------------------------*/

static void prvSendNextSegment( void )
{
volatile unsigned long ulNextLength, ulStatus, ulLengthLeftToSend;

	/* Is there any data to send? */
	if( pxControlTx.ulTotalDataLength > pxControlTx.ulNextCharIndex )
	{
		ulLengthLeftToSend = pxControlTx.ulTotalDataLength - pxControlTx.ulNextCharIndex;
	
		/* We can only send 8 bytes to the fifo at a time. */
		if( ulLengthLeftToSend > usbFIFO_LENGTH )
		{
			ulNextLength = usbFIFO_LENGTH;
		}
		else
		{
			ulNextLength = ulLengthLeftToSend;
		}

		/* Wait until we can place data in the fifo.  THERE IS NO TIMEOUT
		HERE! */
		while( AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] & AT91C_UDP_TXPKTRDY )
		{
			vTaskDelay( usbSHORTEST_DELAY );
		}

		/* Write the data to the FIFO. */
		while( ulNextLength > ( unsigned long ) 0 )
		{
			AT91C_BASE_UDP->UDP_FDR[ usbEND_POINT_0 ] = pxControlTx.ucBuffer[ pxControlTx.ulNextCharIndex ];
	
			ulNextLength--;
			pxControlTx.ulNextCharIndex++;
		}
	
		/* Start the transmission. */
		portENTER_CRITICAL();
		{
			ulStatus = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];
			usbCSR_SET_BIT( &ulStatus, ( ( unsigned long ) 0x10 ) );
			AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulStatus;
		}
		portEXIT_CRITICAL();
	}
	else
	{
		/* There is no data to send.  If we were sending a descriptor and the 
		descriptor was an exact multiple of the max packet size then we need
		to send a null to terminate the transmission. */
		if( eDriverState == eSENDING_EVEN_DESCRIPTOR )
		{
			prvSendZLP();
			eDriverState = eNOTHING;
		}
	}
}


