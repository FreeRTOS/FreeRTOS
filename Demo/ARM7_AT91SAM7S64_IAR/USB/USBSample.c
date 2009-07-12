/*
	FreeRTOS V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

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
	Sample interrupt driven USB device driver.  This is a minimal implementation
	for demonstration only.  Although functional, it is not a full and compliant
	implementation.
	
	The USB device enumerates as a simple 3 axis joystick, and once configured
	transmits 3 axis of data which can be viewed from the USB host machine.

	This file implements the USB interrupt service routine, and a demo FreeRTOS
	task.  The interrupt service routine handles the USB hardware - taking a
	snapshot of the USB status at the point of the interrupt.  The task receives
	the status information from the interrupt for processing at the task level.
	
	See the FreeRTOS.org WEB documentation for more information.
*/

/*
	Changes from V2.5.5
	
	+ Descriptors that have a length that is an exact multiple of usbFIFO_LENGTH
	  can now be transmitted.  To this end an extra parameter has been
	  added to the prvSendControlData() function, and the state
	  eSENDING_EVEN_DESCRIPTOR has been introduced.  Thanks to Scott Miller for
	  assisting with this contribution.

	Changes from V2.6.0

	+ Replaced the duplicated RX_DATA_BK0 in the interrupt mask with the
	  RX_DATA_BK1.
*/

/* Standard includes. */
#include <string.h>

/* Demo board includes. */
#include "board.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"


/* Descriptor type definitions. */
#define usbDESCRIPTOR_TYPE_DEVICE			( 0x01 )
#define usbDESCRIPTOR_TYPE_CONFIGURATION	( 0x02 )
#define usbDESCRIPTOR_TYPE_STRING			( 0x03 )

/* USB request type definitions. */
#define usbGET_REPORT_REQUEST				( 0x01 )
#define usbGET_IDLE_REQUEST					( 0x02 )
#define usbGET_PROTOCOL_REQUEST				( 0x03 )
#define usbSET_REPORT_REQUEST				( 0x09 )
#define usbSET_IDLE_REQUEST					( 0x0A )
#define usbSET_PROTOCOL_REQUEST				( 0x0B )
#define usbGET_CONFIGURATION_REQUEST		( 0x08 )
#define usbGET_STATUS_REQUEST				( 0x00 )
#define usbCLEAR_FEATURE_REQUEST			( 0x01 )
#define usbSET_FEATURE_REQUEST				( 0x03 )
#define usbSET_ADDRESS_REQUEST				( 0x05 )
#define usbGET_DESCRIPTOR_REQUEST			( 0x06 )
#define usbSET_CONFIGURATION_REQUEST		( 0x09 )
#define usbGET_INTERFACE_REQUEST			( 0x0A )
#define usbSET_INTERFACE_REQUEST			( 0x0B )


/* Misc USB definitions. */
#define usbDEVICE_CLASS_VENDOR_SPECIFIC		( 0xFF )
#define usbBUS_POWERED						( 0x80 )
#define usbHID_REPORT_DESCRIPTOR			( 0x22 )
#define AT91C_UDP_TRANSCEIVER_ENABLE			( *( ( unsigned long * ) 0xfffb0074 ) )

/* Index to the various string. */
#define usbLANGUAGE_STRING					( 0 )
#define usbMANUFACTURER_STRING				( 1 )
#define usbPRODUCT_STRING					( 2 )
#define usbCONFIGURATION_STRING				( 3 )
#define usbINTERFACE_STRING					( 4 )

/* Data indexes for reading the request from the xISRStatus.ucFifoData[]
into xUSB_REQUEST.  The data order is designed for speed - so looks a
little odd. */
#define usbREQUEST_TYPE_INDEX				( 7 )
#define usbREQUEST_INDEX					( 6 )
#define usbVALUE_HIGH_BYTE					( 4 )
#define usbVALUE_LOW_BYTE					( 5 )
#define usbINDEX_HIGH_BYTE					( 2 )
#define usbINDEX_LOW_BYTE					( 3 )
#define usbLENGTH_HIGH_BYTE					( 0 )
#define usbLENGTH_LOW_BYTE					( 1 )

/* Misc application definitions. */
#define usbINTERRUPT_PRIORITY				( 3 )
#define usbQUEUE_LENGTH						( 0x3 )	/* Must have all bits set! */
#define usbFIFO_LENGTH						( ( unsigned portLONG ) 8 )
#define usbEND_POINT_0						( 0 )
#define usbEND_POINT_1						( 1 )
#define usbXUP								( 1 )
#define usbXDOWN							( 2 )
#define usbYUP								( 3 )
#define usbYDOWN							( 4 )
#define usbMAX_COORD						( 120 )
#define usbMAX_TX_MESSAGE_SIZE				( 128 )
#define usbRX_COUNT_MASK					( ( unsigned portLONG ) 0x7ff )
#define AT91C_UDP_STALLSENT					AT91C_UDP_ISOERROR
#define usbSHORTEST_DELAY					( ( portTickType ) 1 )
#define usbINIT_DELAY						( ( portTickType ) 500 / portTICK_RATE_MS )
#define usbSHORT_DELAY						( ( portTickType ) 50 / portTICK_RATE_MS )
#define usbEND_POINT_RESET_MASK				( ( unsigned portLONG ) 0x0f )
#define usbDATA_INC							( ( portCHAR ) 5 )
#define usbEXPECTED_NUMBER_OF_BYTES			( ( unsigned portLONG ) 8 )

/* Control request types. */
#define usbSTANDARD_DEVICE_REQUEST			( 0 )
#define usbSTANDARD_INTERFACE_REQUEST		( 1 )
#define usbSTANDARD_END_POINT_REQUEST		( 2 )
#define usbCLASS_INTERFACE_REQUEST			( 5 )

/*-----------------------------------------------------------*/

/* Structure used to take a snapshot of the USB status from within the ISR. */
typedef struct X_ISR_STATUS
{
	unsigned portLONG ulISR;
	unsigned portLONG ulCSR0;
	unsigned portCHAR ucFifoData[ 8 ];
} xISRStatus;

/* Structure used to hold the received requests. */
typedef struct
{
	unsigned portCHAR ucReqType;
	unsigned portCHAR ucRequest;
	unsigned portSHORT usValue;
	unsigned portSHORT usIndex;
	unsigned portSHORT usLength;
} xUSB_REQUEST;

typedef enum
{
	eNOTHING,
	eJUST_RESET,
	eJUST_GOT_CONFIG,
	eJUST_GOT_ADDRESS,
	eSENDING_EVEN_DESCRIPTOR,
	eREADY_TO_SEND
} eDRIVER_STATE;

/* Structure used to control the data being sent to the host. */
typedef struct
{
	unsigned portCHAR ucTxBuffer[ usbMAX_TX_MESSAGE_SIZE ];
	unsigned portLONG ulNextCharIndex;
	unsigned portLONG ulTotalDataLength;
} xTX_MESSAGE;

/*-----------------------------------------------------------*/

/*
 * The USB interrupt service routine.  This takes a snapshot of the USB
 * device at the time of the interrupt, clears the interrupts, and posts
 * the data to the USB processing task.
 */
__arm void vUSB_ISR( void );

/*
 * Called after the bus reset interrupt - this function readies all the
 * end points for communication.
 */
static void prvResetEndPoints( void );

/*
 * Setup the USB hardware, install the interrupt service routine and
 * initialise all the state variables.
 */
static void vInitUSBInterface( void );

/*
 * Decode and act upon an interrupt generated by the control end point.
 */
static void prvProcessEndPoint0Interrupt( xISRStatus *pxMessage );

/*
 * For simplicity requests are separated into device, interface, class
 * interface and end point requests.
 *
 * Decode and handle standard device requests originating on the control
 * end point.
 */
static void prvHandleStandardDeviceRequest( xUSB_REQUEST *pxRequest );

/*
 * For simplicity requests are separated into device, interface, class
 * interface and end point requests.
 *
 * Decode and handle standard interface requests originating on the control
 * end point.
 */
static void prvHandleStandardInterfaceRequest( xUSB_REQUEST *pxRequest );

/*
 * For simplicity requests are separated into device, interface, class
 * interface and end point requests.
 *
 * Decode and handle standard end point requests originating on the control
 * end point.
 */
static void prvHandleStandardEndPointRequest( xUSB_REQUEST *pxRequest );

/*
 * For simplicity requests are separated into device, interface, class
 * interface and end point requests.
 *
 * Decode and handle the class interface requests.
 */
static void prvHandleClassInterfaceRequest( xUSB_REQUEST *pxRequest );

/*
 * Setup the Tx buffer to send data in response to a control request.
 *
 * The data to be transmitted is buffered, the state variables are updated,
 * then prvSendNextSegment() is called to start the transmission off.  Once
 * the first segment has been sent the remaining segments are transmitted
 * in response to TXCOMP interrupts until the entire buffer has been
 * sent.
 */
static void prvSendControlData( unsigned portCHAR *pucData, unsigned portSHORT usRequestedLength, unsigned portLONG ulLengthLeftToSend, portLONG lSendingDescriptor );

/*
 * Examine the Tx buffer to see if there is any more data to be transmitted.
 *
 * If there is data to be transmitted then send the next segment.  A segment
 * can have a maximum of 8 bytes (this is defined as the maximum for the end
 * point by the descriptor).  The final segment may be less than 8 bytes if
 * the total data length was not an exact multiple of 8.
 */
static void prvSendNextSegment( void );

/*
 * A stall condition is forced each time the host makes a request that is not
 * supported by this minimal implementation.
 *
 * A stall is forced by setting the appropriate bit in the end points control
 * and status register.
 */
static void prvSendStall( void );

/*
 * A NULL (or zero length packet) is transmitted in acknowledge the reception
 * of certain events from the host.
 */
static void prvUSBTransmitNull( void );

/*
 * When the host requests a descriptor this function is called to determine
 * which descriptor is being requested and start its transmission.
 */
static void prvGetStandardInterfaceDescriptor( xUSB_REQUEST *pxRequest );

/*
 * This demo USB device enumerates as a simple 3 axis joystick.  Once
 * configured this function is periodically called to generate some sample
 * joystick data.
 *
 * The x and y axis are made to move in a square.  The z axis is made to
 * repeatedly increment up to its maximum.
 */
static void prvTransmitSampleValues( void );

/*
 * The created task to handle the USB demo functionality.
 */
void vUSBDemoTask( void *pvParameters );

/*-----------------------------------------------------------*/

/*
	- DESCRIPTOR DEFINITIONS -
*/

/* String descriptors used during the enumeration process.
These take the form:

{
	Length of descriptor,
	Descriptor type,
	Data
}
*/
const portCHAR pxLanguageStringDescriptor[] =
{
	4,
	usbDESCRIPTOR_TYPE_STRING,
	0x09, 0x04
};

const portCHAR pxManufacturerStringDescriptor[] =
{
	18,
	usbDESCRIPTOR_TYPE_STRING,

	'F', 0x00,
	'r', 0x00,
	'e', 0x00,
	'e', 0x00,
	'R', 0x00,
	'T', 0x00,
	'O', 0x00,
	'S', 0x00	
};

const portCHAR pxProductStringDescriptor[] =
{
	44,
	usbDESCRIPTOR_TYPE_STRING,

	'F', 0x00,
	'r', 0x00,
	'e', 0x00,
	'e', 0x00,
	'R', 0x00,
	'T', 0x00,
	'O', 0x00,
	'S', 0x00,
	'.', 0x00,
	'o', 0x00,
	'r', 0x00,
	'g', 0x00,
	' ', 0x00,
	'J', 0x00,
	'o', 0x00,
	'y', 0x00,
	's', 0x00,
	't', 0x00,
	'i', 0x00,
	'c', 0x00,
	'k', 0x00
};

const portCHAR pxConfigurationStringDescriptor[] =
{
	38,
	usbDESCRIPTOR_TYPE_STRING,

	'C', 0x00,
	'o', 0x00,
	'n', 0x00,
	'f', 0x00,
	'i', 0x00,
	'g', 0x00,
	'u', 0x00,
	'r', 0x00,
	'a', 0x00,
	't', 0x00,
	'i', 0x00,
	'o', 0x00,
	'n', 0x00,
	' ', 0x00,
	'N', 0x00,
	'a', 0x00,
	'm', 0x00,
	'e', 0x00
};

const portCHAR pxInterfaceStringDescriptor[] =
{
	30,
	usbDESCRIPTOR_TYPE_STRING,

	'I', 0x00,
	'n', 0x00,
	't', 0x00,
	'e', 0x00,
	'r', 0x00,
	'f', 0x00,
	'a', 0x00,
	'c', 0x00,
	'e', 0x00,
	' ', 0x00,
	'N', 0x00,
	'a', 0x00,
	'm', 0x00,
	'e', 0x00
};

/* Enumeration descriptors. */
const portCHAR pxReportDescriptor[] =
{
	 0x05,  0x01,	/* USAGE_PAGE (Generic Desktop)		*/
	 0x09,  0x04,	/* USAGE (Joystick)					*/
	 0xa1,  0x01,	/* COLLECTION (Application)			*/
	 0x05,  0x01,	/*   USAGE_PAGE (Generic Desktop)	*/
	 0x09,  0x01,	/*   USAGE (Pointer)				*/
	 0xa1,  0x00,	/*   COLLECTION (Physical)			*/
	 0x09,  0x30,	/*     USAGE (X)					*/
	 0x09,  0x31,	/*     USAGE (Y)					*/
	 0x09,  0x32,	/*     USAGE (Z)					*/
	 0x15,  0x81,	/*     LOGICAL_MINIMUM (-127)		*/
	 0x25,  0x7f,	/*     LOGICAL_MAXIMUM (127)		*/
	 0x75,  0x08,	/*     REPORT_SIZE (8)				*/
	 0x95,  0x03,	/*     REPORT_COUNT (3)				*/
	 0x81,  0x02,	/*     INPUT (Data,Var,Abs)			*/
	 0xc0,			/*   END_COLLECTION					*/
	 0xc0			/* END_COLLECTION					*/
};

const char pxDeviceDescriptor[] =
{
	/* Device descriptor */
	0x12,								/* bLength				*/
	0x01,								/* bDescriptorType		*/
	0x10, 0x01,							/* bcdUSBL				*/
	usbDEVICE_CLASS_VENDOR_SPECIFIC,	/* bDeviceClass:		*/
	0x00,								/* bDeviceSubclass:		*/
	0x00,								/* bDeviceProtocol:		*/
	0x08,								/* bMaxPacketSize0		*/
	0xFF, 0xFF,							/* idVendorL			*/
	0x01, 0x00,							/* idProductL			*/
	0x00, 0x01,							/* bcdDeviceL			*/
	usbMANUFACTURER_STRING,				/* iManufacturer		*/
	usbPRODUCT_STRING,					/* iProduct				*/
	0x00,								/* SerialNumber			*/
	0x01								/* bNumConfigs			*/
};

const char pxConfigDescriptor[] = {
	/* Configuration 1 descriptor */
	0x09,			/* CbLength									*/
	0x02,			/* CbDescriptorType							*/
	0x22, 0x00,		/* CwTotalLength 2 EP + Control				*/
	0x01,			/* CbNumInterfaces							*/
	0x01,			/* CbConfigurationValue						*/
	usbCONFIGURATION_STRING,/* CiConfiguration					*/
	usbBUS_POWERED,	/* CbmAttributes Bus powered + Remote Wakeup*/
	0x32,			/* CMaxPower: 100mA							*/

	/* Joystick Interface Descriptor Requirement */
	0x09,			/* bLength									*/
	0x04,			/* bDescriptorType							*/
	0x00,			/* bInterfaceNumber							*/
	0x00,			/* bAlternateSetting						*/
	0x01,			/* bNumEndpoints							*/
	0x03,			/* bInterfaceClass: HID code				*/
	0x00,			/* bInterfaceSubclass						*/
	0x00,			/* bInterfaceProtocol						*/
	usbINTERFACE_STRING,/* iInterface							*/

	/* HID Descriptor */
	0x09,			/* bLength									*/
	0x21,			/* bDescriptor type: HID Descriptor Type	*/
	0x00, 0x01,		/* bcdHID									*/
	0x00,			/* bCountryCode								*/
	0x01,			/* bNumDescriptors							*/
	usbHID_REPORT_DESCRIPTOR,	  /* bDescriptorType			*/
	sizeof( pxReportDescriptor ), 0x00, /* wItemLength			*/

	/* Endpoint 1 descriptor */
	0x07,			/* bLength									*/
	0x05,			/* bDescriptorType							*/
	0x81,			/* bEndpointAddress, Endpoint 01 - IN		*/
	0x03,			/* bmAttributes      INT					*/
	0x03, 0x00,		/* wMaxPacketSize: 3 bytes (x, y, z)		*/
	0x0A			/* bInterval								*/
};

/*-----------------------------------------------------------*/

/* File scope state variables. */
static unsigned portCHAR ucUSBConfig = ( unsigned portCHAR ) 0;
static unsigned portLONG ulReceivedAddress = ( unsigned portLONG ) 0;
static eDRIVER_STATE eDriverState = eNOTHING;

/* Array in which the USB interrupt status is passed between the ISR and task. */
static xISRStatus xISRMessages[ usbQUEUE_LENGTH + 1 ];

/* Structure used to control the characters being sent to the host. */
static xTX_MESSAGE pxCharsForTx;

/* Queue used to pass messages between the ISR and the task. */
static xQueueHandle xUSBInterruptQueue;

/* ISR entry has to be written in the asm file as we want a context switch
to occur from within the ISR.  See the port documentation on the FreeRTOS.org
WEB site for more information. */
extern void vUSBISREntry( void );

/*-----------------------------------------------------------*/

/* Macros to manipulate the control and status registers.  These registers
cannot be accessed using a direct read modify write operation outside of the
ISR as some bits are left unchanged by writing with a 0, and some are left
unchanged by writing with a 1. */

#define usbINT_CLEAR_MASK	(AT91C_UDP_TXCOMP | AT91C_UDP_STALLSENT | AT91C_UDP_RXSETUP | AT91C_UDP_RX_DATA_BK0 | AT91C_UDP_RX_DATA_BK1 )

#define usbCSR_SET_BIT( pulValueNow, ulBit )											\
{																						\
	/* Set TXCOMP, RX_DATA_BK0, RXSETUP, */												\
	/* STALLSENT and RX_DATA_BK1 to 1 so the */											\
	/* write has no effect. */															\
	( * ( ( unsigned portLONG * ) pulValueNow ) ) |= ( unsigned portLONG ) 0x4f;		\
																						\
	/* Clear the FORCE_STALL and TXPKTRDY bits */										\
	/* so the write has no effect. */													\
	( * ( ( unsigned portLONG * ) pulValueNow ) ) &= ( unsigned portLONG ) 0xffffffcf;	\
																						\
	/* Set whichever bit we want set. */												\
	( * ( ( unsigned portLONG * ) pulValueNow ) ) |= ( ulBit );							\
}

#define usbCSR_CLEAR_BIT( pulValueNow, ulBit )											\
{																						\
	/* Set TXCOMP, RX_DATA_BK0, RXSETUP, */												\
	/* STALLSENT and RX_DATA_BK1 to 1 so the */											\
	/* write has no effect. */															\
	( * ( ( unsigned portLONG * ) pulValueNow ) ) |= ( unsigned portLONG ) 0x4f;		\
																						\
	/* Clear the FORCE_STALL and TXPKTRDY bits */										\
	/* so the write has no effect. */													\
	( * ( ( unsigned portLONG * ) pulValueNow ) ) &= ( unsigned portLONG ) 0xffffffcf;	\
																						\
	/* Clear whichever bit we want clear. */											\
	( * ( ( unsigned portLONG * ) pulValueNow ) ) &= ( ~ulBit );						\
}

/*-----------------------------------------------------------*/

__arm void vUSB_ISR( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
static volatile unsigned portLONG ulNextMessage = 0;
xISRStatus *pxMessage;
unsigned portLONG ulTemp, ulRxBytes;

	/* Take the next message from the queue.  Note that usbQUEUE_LENGTH *must*
	be all 1's, as in 0x01, 0x03, 0x07, etc. */
	pxMessage = &( xISRMessages[ ( ulNextMessage & usbQUEUE_LENGTH ) ] );
	ulNextMessage++;

	/* Take a snapshot of the current USB state for processing at the task
	level. */
	pxMessage->ulISR = AT91C_BASE_UDP->UDP_ISR;
	pxMessage->ulCSR0 = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];

	/* Clear the interrupts from the ICR register.  The bus end interrupt is
	cleared separately as it does not appear in the mask register. */
	AT91C_BASE_UDP->UDP_ICR = AT91C_BASE_UDP->UDP_IMR | AT91C_UDP_ENDBUSRES;
	
	/* If there are bytes in the FIFO then we have to retrieve them here.
	Ideally this would be done at the task level.  However we need to clear the
	RXSETUP interrupt before leaving the ISR, and this may cause the data in
	the FIFO to be overwritten.  Also the DIR bit has to be changed before the
	RXSETUP bit is cleared (as per the SAM7 manual). */
	ulTemp = pxMessage->ulCSR0;
	
	/* Are there any bytes in the FIFO? */
	ulRxBytes = ulTemp >> 16;
	ulRxBytes &= usbRX_COUNT_MASK;
	
	/* With this minimal implementation we are only interested in receiving
	setup bytes on the control end point. */
	if( ( ulRxBytes > 0 ) && ( ulTemp & AT91C_UDP_RXSETUP ) )
	{
		/* Take off 1 for a zero based index. */
		while( ulRxBytes > 0 )
		{
			ulRxBytes--;
			pxMessage->ucFifoData[ ulRxBytes ] = AT91C_BASE_UDP->UDP_FDR[ usbEND_POINT_0 ];			
		}
		
		/* The direction must be changed first. */
		usbCSR_SET_BIT( &ulTemp, ( AT91C_UDP_DIR ) );
		AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulTemp;
	}
	
	/* Must write zero's to TXCOMP, STALLSENT, RXSETUP, and the RX DATA
	registers to clear the interrupts in the CSR register. */
	usbCSR_CLEAR_BIT( &ulTemp, usbINT_CLEAR_MASK );
	AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulTemp;

	/* Also clear the interrupts in the CSR1 register. */
	ulTemp = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ];
	usbCSR_CLEAR_BIT( &ulTemp, usbINT_CLEAR_MASK );	
	AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] = ulTemp;

	/* The message now contains the entire state and optional data from
	the USB interrupt.  This can now be posted on the Rx queue ready for
	processing at the task level. */
	xQueueSendFromISR( xUSBInterruptQueue, &pxMessage, &xHigherPriorityTaskWoken );

	/* We may want to switch to the USB task, if this message has made
	it the highest priority task that is ready to execute. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );

	/* Clear the AIC ready for the next interrupt. */		
	AT91C_BASE_AIC->AIC_EOICR = 0;
}
/*-----------------------------------------------------------*/

void vUSBDemoTask( void *pvParameters )
{
xISRStatus *pxMessage;

	/* The parameters are not used in this task. */
	( void ) pvParameters;

    /* Init USB device */
    portENTER_CRITICAL();
	    vInitUSBInterface();
    portEXIT_CRITICAL();

	/* Process interrupts as they arrive.   The ISR takes a snapshot of the
	interrupt status then posts the information on this queue for processing
	at the task level.  This simple demo implementation only processes
	a few interrupt sources. */
	for( ;; )
	{
		if( xQueueReceive( xUSBInterruptQueue, &pxMessage, usbSHORT_DELAY ) )
		{
			if( pxMessage->ulISR & AT91C_UDP_EPINT0 )
			{
				/* Process end point 0 interrupt. */
				prvProcessEndPoint0Interrupt( pxMessage );
			}

			if( pxMessage->ulISR & AT91C_UDP_ENDBUSRES )
			{
				/* Process an end of bus reset interrupt. */
				prvResetEndPoints();		
			}
		}
		else
		{
			/* The ISR did not post any data for us to process on the queue, so
			just generate and send some sample data. */
			if( eDriverState == eREADY_TO_SEND )
			{
				prvTransmitSampleValues();
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvTransmitSampleValues( void )
{
unsigned portLONG ulStatus;
static portLONG lState = usbXUP;

/* Variables to hold dummy x, y and z joystick axis data. */
static signed portCHAR x = 0, y = 0, z = 0;

	/* Generate some sample data in the x and y axis - draw a square. */
	switch( lState )
	{
		case usbXUP	:	x += usbDATA_INC;
						if( x >= usbMAX_COORD )
						{
							lState = usbYUP;
						}
						break;
						
		case usbXDOWN :	x -= usbDATA_INC;
						if( x <= -usbMAX_COORD )
						{
							lState = usbYDOWN;
						}
						break;
						
		case usbYUP :	y += usbDATA_INC;
						if( y >= usbMAX_COORD )
						{
							lState = usbXDOWN;
						}
						break;
						
		case usbYDOWN :	y -= usbDATA_INC;
						if( y <= -usbMAX_COORD )
						{
							lState = usbXUP;
						}
						break;
	}

	/* Just make the z axis go up and down. */
	z += usbDATA_INC;

	/* Can we place data in the fifo? */
	if( !( AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] & AT91C_UDP_TXPKTRDY ) )
	{
		/* Write our sample data to the fifo. */
		AT91C_BASE_UDP->UDP_FDR[ usbEND_POINT_1 ] = x;
		AT91C_BASE_UDP->UDP_FDR[ usbEND_POINT_1 ] = y;
		AT91C_BASE_UDP->UDP_FDR[ usbEND_POINT_1 ] = z;
		
		/* Send the data. */
		portENTER_CRITICAL();
		{
			ulStatus = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ];
			usbCSR_SET_BIT( &ulStatus, ( AT91C_UDP_TXPKTRDY ) );
			AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] = ulStatus;
		}
		portEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

static void prvUSBTransmitNull( void )
{
unsigned portLONG ulStatus;

	/* Wait until the FIFO is free - even though we are not going to use it.
	THERE IS NO TIMEOUT HERE! */
	while( AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] & AT91C_UDP_TXPKTRDY )
	{
		vTaskDelay( usbSHORTEST_DELAY );
	}

	portENTER_CRITICAL();
	{
		/* Set the length of data to send to equal the index of the next byte
		to send.  This will prevent the ACK to this NULL packet causing any
		further data transmissions. */
		pxCharsForTx.ulTotalDataLength = pxCharsForTx.ulNextCharIndex;

		/* Set the TXPKTRDY bit to cause a transmission with no data. */
		ulStatus = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];
		usbCSR_SET_BIT( &ulStatus, ( AT91C_UDP_TXPKTRDY ) );
		AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulStatus;
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

static void prvSendStall( void )
{
unsigned portLONG ulStatus;

	portENTER_CRITICAL();
	{
		/* Force a stall by simply setting the FORCESTALL bit in the CSR. */
		ulStatus = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];
		usbCSR_SET_BIT( &ulStatus, AT91C_UDP_FORCESTALL );
		AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulStatus;
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

static void prvResetEndPoints( void )
{
unsigned portLONG ulTemp;

	eDriverState = eJUST_RESET;

	/* Reset all the end points. */
	AT91C_BASE_UDP->UDP_RSTEP  = usbEND_POINT_RESET_MASK;
	AT91C_BASE_UDP->UDP_RSTEP  = ( unsigned portLONG ) 0x00;

	/* Enable data to be sent and received. */
	AT91C_BASE_UDP->UDP_FADDR = AT91C_UDP_FEN;

	/* Repair the configuration end point. */
	portENTER_CRITICAL();
	{
		ulTemp = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];
		usbCSR_SET_BIT( &ulTemp, ( ( unsigned portLONG ) ( AT91C_UDP_EPEDS | AT91C_UDP_EPTYPE_CTRL ) ) );
		AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ] = ulTemp;
		AT91F_UDP_EnableIt( AT91C_BASE_UDP, AT91C_UDP_EPINT0 );
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

static void prvProcessEndPoint0Interrupt( xISRStatus *pxMessage )
{
	if( pxMessage->ulCSR0 & AT91C_UDP_RX_DATA_BK0 )
	{		
		/* We only expect to receive zero length data here as ACK's.
		Set the data pointer to the end of the current Tx packet to
		ensure we don't send out any more data. */	
		pxCharsForTx.ulNextCharIndex = pxCharsForTx.ulTotalDataLength;
	}

	if( pxMessage->ulCSR0 & AT91C_UDP_TXCOMP )
	{
		/* We received a TX complete interrupt.  What we do depends on
		what we sent to get this interrupt. */

		if( eDriverState == eJUST_GOT_CONFIG )
		{
			/* We sent an acknowledgement of a SET_CONFIG request.  We
			are now at the end of the enumeration. */
			AT91C_BASE_UDP->UDP_GLBSTATE = AT91C_UDP_CONFG;

			/* Read the end point for data transfer. */
			portENTER_CRITICAL();
			{
				unsigned portLONG ulTemp;

				ulTemp = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ];					
				usbCSR_SET_BIT( &ulTemp, AT91C_UDP_EPEDS | AT91C_UDP_EPTYPE_INT_IN );
				AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_1 ] = ulTemp;		
				AT91F_UDP_EnableIt( AT91C_BASE_UDP, AT91C_UDP_EPINT1 );
			}
			portEXIT_CRITICAL();

			eDriverState = eREADY_TO_SEND;
		}		
		else if( eDriverState == eJUST_GOT_ADDRESS )
		{
			/* We sent an acknowledgement of a SET_ADDRESS request.  Move
			to the addressed state. */
			if( ulReceivedAddress != ( unsigned portLONG ) 0 )
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

	if( pxMessage->ulCSR0 & AT91C_UDP_RXSETUP )
	{
		xUSB_REQUEST xRequest;
		unsigned portCHAR ucRequest;
		unsigned portLONG ulRxBytes;

		/* A data packet is available. */	
		ulRxBytes = pxMessage->ulCSR0 >> 16;
		ulRxBytes &= usbRX_COUNT_MASK;

		if( ulRxBytes >= usbEXPECTED_NUMBER_OF_BYTES )
		{
			/* Create an xUSB_REQUEST variable from the raw bytes array. */

			xRequest.ucReqType = pxMessage->ucFifoData[ usbREQUEST_TYPE_INDEX ];
			xRequest.ucRequest = pxMessage->ucFifoData[ usbREQUEST_INDEX ];

			/* NOT PORTABLE CODE! */
			xRequest.usValue = pxMessage->ucFifoData[ usbVALUE_HIGH_BYTE ];
			xRequest.usValue <<= 8;
			xRequest.usValue |= pxMessage->ucFifoData[ usbVALUE_LOW_BYTE ];
						
			xRequest.usIndex = pxMessage->ucFifoData[ usbINDEX_HIGH_BYTE ];
			xRequest.usIndex <<= 8;
			xRequest.usIndex |= pxMessage->ucFifoData[ usbINDEX_LOW_BYTE ];
			
			xRequest.usLength = pxMessage->ucFifoData[ usbLENGTH_HIGH_BYTE ];
			xRequest.usLength <<= 8;
			xRequest.usLength |= pxMessage->ucFifoData[ usbLENGTH_LOW_BYTE ];
	
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
}
/*-----------------------------------------------------------*/

static void prvGetStandardDeviceDescriptor( xUSB_REQUEST *pxRequest )
{
	/* The type is in the high byte.  Return whatever has been requested. */
	switch( ( pxRequest->usValue & 0xff00 ) >> 8 )
	{
	    case usbDESCRIPTOR_TYPE_DEVICE:
			prvSendControlData( ( unsigned portCHAR * ) &pxDeviceDescriptor, pxRequest->usLength, sizeof( pxDeviceDescriptor ), pdTRUE );
		    break;
	
	    case usbDESCRIPTOR_TYPE_CONFIGURATION:
			prvSendControlData( ( unsigned portCHAR * ) &( pxConfigDescriptor ), pxRequest->usLength, sizeof( pxConfigDescriptor ), pdTRUE );
		    break;

	    case usbDESCRIPTOR_TYPE_STRING:

			/* The index to the string descriptor is the lower byte. */
		    switch( pxRequest->usValue & 0xff )
			{			
		        case usbLANGUAGE_STRING:
					prvSendControlData( ( unsigned portCHAR * ) &pxLanguageStringDescriptor, pxRequest->usLength, sizeof(pxLanguageStringDescriptor), pdTRUE );
			        break;

		        case usbMANUFACTURER_STRING:
					prvSendControlData( ( unsigned portCHAR * ) &pxManufacturerStringDescriptor, pxRequest->usLength, sizeof( pxManufacturerStringDescriptor ), pdTRUE );
			        break;

		        case usbPRODUCT_STRING:
					prvSendControlData( ( unsigned portCHAR * ) &pxProductStringDescriptor, pxRequest->usLength, sizeof( pxProductStringDescriptor ), pdTRUE );
			        break;

		        case usbCONFIGURATION_STRING:
					prvSendControlData( ( unsigned portCHAR * ) &pxConfigurationStringDescriptor, pxRequest->usLength, sizeof( pxConfigurationStringDescriptor ), pdTRUE );
			        break;

		        case usbINTERFACE_STRING:
					prvSendControlData( ( unsigned portCHAR * ) &pxInterfaceStringDescriptor, pxRequest->usLength, sizeof( pxInterfaceStringDescriptor ), pdTRUE );
			        break;

		        default:
			        /* Don't know what this string is. */
					prvSendStall();
					break;
			}

			break;

	    default:
			/* We are not responding to anything else. */
			prvSendStall();
		    break;
	}
}
/*-----------------------------------------------------------*/

static void prvHandleStandardDeviceRequest( xUSB_REQUEST *pxRequest )
{
unsigned portSHORT usStatus = 0;

	switch( pxRequest->ucRequest )
	{
	    case usbGET_STATUS_REQUEST:
			/* Just send two byte dummy status. */
			prvSendControlData( ( unsigned portCHAR * ) &usStatus, sizeof( usStatus ), sizeof( usStatus ), pdFALSE );
		    break;

	    case usbGET_DESCRIPTOR_REQUEST:
			/* Send device descriptor */
		    prvGetStandardDeviceDescriptor( pxRequest );
		    break;

	    case usbGET_CONFIGURATION_REQUEST:
			/* Send selected device configuration */
			prvSendControlData( ( unsigned portCHAR * ) &ucUSBConfig, sizeof( ucUSBConfig ), sizeof( ucUSBConfig ), pdFALSE );
		    break;

		case usbSET_FEATURE_REQUEST:
		    prvUSBTransmitNull();
		    break;

	    case usbSET_ADDRESS_REQUEST:
	    	
			/* Acknowledge the SET_ADDRESS, but (according to the manual) we
			cannot actually move to the addressed state until we get a TXCOMP
			interrupt from this NULL packet.  Therefore we just remember the
			address and set our state so we know we have received the address. */
	    	prvUSBTransmitNull();			
			eDriverState = eJUST_GOT_ADDRESS;	    	
			ulReceivedAddress = ( unsigned portLONG ) pxRequest->usValue;
		    break;

	    case usbSET_CONFIGURATION_REQUEST:

			/* Acknowledge the SET_CONFIGURATION, but (according to the manual)
			we cannot actually move to the configured state until we get a
			TXCOMP interrupt from this NULL packet.  Therefore we just remember the
			config and set our state so we know we have received the go ahead. */			
			ucUSBConfig = ( unsigned portCHAR ) ( pxRequest->usValue & 0xff );
			eDriverState = eJUST_GOT_CONFIG;
			prvUSBTransmitNull();
		    break;

	    default:

		    /* We don't answer to anything else. */
			prvSendStall();
		    break;
	}
}
/*-----------------------------------------------------------*/

static void prvHandleClassInterfaceRequest( xUSB_REQUEST *pxRequest )
{
	switch( pxRequest->ucRequest )
	{
	    case usbSET_IDLE_REQUEST:
	    	prvUSBTransmitNull();
			break;

		/* This minimal implementation ignores these. */
	    case usbGET_REPORT_REQUEST:
	    case usbGET_IDLE_REQUEST:
	    case usbGET_PROTOCOL_REQUEST:
	    case usbSET_REPORT_REQUEST:
	    case usbSET_PROTOCOL_REQUEST:	
	    default:

			prvSendStall();
			break;
	}
}
/*-----------------------------------------------------------*/

static void prvGetStandardInterfaceDescriptor( xUSB_REQUEST *pxRequest )
{
	switch( ( pxRequest->usValue & ( unsigned portSHORT ) 0xff00 ) >> 8 )
	{
	    case usbHID_REPORT_DESCRIPTOR:
			prvSendControlData( ( unsigned portCHAR * ) pxReportDescriptor, pxRequest->usLength, sizeof( pxReportDescriptor ), pdTRUE );
		    break;

	    default:

			/* Don't expect to send any others. */
			prvSendStall();
		    break;
	}
}
/*-----------------------------------------------------------*/

static void prvHandleStandardInterfaceRequest( xUSB_REQUEST *pxRequest )
{
unsigned portSHORT usStatus = 0;

	switch( pxRequest->ucRequest )
	{
	    case usbGET_STATUS_REQUEST:
			/* Send dummy 2 bytes. */
			prvSendControlData( ( unsigned portCHAR * ) &usStatus, sizeof( usStatus ), sizeof( usStatus ), pdFALSE );
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

static void vInitUSBInterface( void )
{
volatile unsigned portLONG ulTemp;

	/* Create the queue used to communicate between the USB ISR and task. */
	xUSBInterruptQueue = xQueueCreate( usbQUEUE_LENGTH + 1, sizeof( xISRStatus * ) );

	/* Initialise a few state variables. */
	pxCharsForTx.ulNextCharIndex = ( unsigned portLONG ) 0;
	ucUSBConfig = ( unsigned portCHAR ) 0;
	eDriverState = eNOTHING;

	/* HARDWARE SETUP */

    /* Set the PLL USB Divider */
    AT91C_BASE_CKGR->CKGR_PLLR |= AT91C_CKGR_USBDIV_1;

    /* Enables the 48MHz USB clock UDPCK and System Peripheral USB Clock. */
    AT91C_BASE_PMC->PMC_SCER = AT91C_PMC_UDP;
    AT91C_BASE_PMC->PMC_PCER = (1 << AT91C_ID_UDP);

    /* Setup the PIO for the USB pull up resistor. */
    AT91F_PIO_CfgOutput(AT91C_BASE_PIOA,AT91C_PIO_PA16);

    /* Start without the pullup - this will get set at the end of this
	function. */
    AT91F_PIO_SetOutput( AT91C_BASE_PIOA, AT91C_PIO_PA16 );

	/* When using the USB debugger the peripheral registers do not always get
	set to the correct default values.  To make sure set the relevant registers
	manually here. */
	AT91C_BASE_UDP->UDP_IDR = ( unsigned portLONG ) 0xffffffff;
	AT91C_BASE_UDP->UDP_ICR = ( unsigned portLONG ) 0xffffffff;
	AT91C_BASE_UDP->UDP_CSR[ 0 ] = ( unsigned portLONG ) 0x00;
	AT91C_BASE_UDP->UDP_CSR[ 1 ] = ( unsigned portLONG ) 0x00;
	AT91C_BASE_UDP->UDP_GLBSTATE = 0;
	AT91C_BASE_UDP->UDP_FADDR = 0;

	/* Enable the transceiver. */
	AT91C_UDP_TRANSCEIVER_ENABLE = 0;

	/* Enable the USB interrupts - other interrupts get enabled as the
	enumeration process progresses. */
	AT91F_AIC_ConfigureIt( AT91C_BASE_AIC, AT91C_ID_UDP, usbINTERRUPT_PRIORITY, AT91C_AIC_SRCTYPE_INT_LEVEL_SENSITIVE, ( void (*)( void ) ) vUSBISREntry );
	AT91F_AIC_EnableIt( AT91C_BASE_AIC, AT91C_ID_UDP );

	/* Wait a short while before making our presence known. */
	vTaskDelay( usbINIT_DELAY );
    AT91F_PIO_ClearOutput(AT91C_BASE_PIOA, AT91C_PIO_PA16 );
}
/*-----------------------------------------------------------*/

static void prvSendControlData( unsigned portCHAR *pucData, unsigned portSHORT usRequestedLength, unsigned portLONG ulLengthToSend, portLONG lSendingDescriptor )
{
	if( ( ( unsigned portLONG ) usRequestedLength < ulLengthToSend ) )
	{
		/* Cap the data length to that requested. */
		ulLengthToSend = ( unsigned portSHORT ) usRequestedLength;
	}
	else if( ( ulLengthToSend < ( unsigned portLONG ) usRequestedLength ) && lSendingDescriptor )
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
	memcpy( pxCharsForTx.ucTxBuffer, pucData, ulLengthToSend );

	/* Reinitialise the buffer index so we start sending from the start of
	the data. */
	pxCharsForTx.ulTotalDataLength = ulLengthToSend;
	pxCharsForTx.ulNextCharIndex = ( unsigned portLONG ) 0;

	/* Send the first 8 bytes now.  The rest will get sent in response to
	TXCOMP interrupts. */
	prvSendNextSegment();
}
/*-----------------------------------------------------------*/

static void prvSendNextSegment( void )
{
volatile unsigned portLONG ulNextLength, ulStatus, ulLengthLeftToSend;

	/* Is there any data to send? */
	if( pxCharsForTx.ulTotalDataLength > pxCharsForTx.ulNextCharIndex )
	{
		ulLengthLeftToSend = pxCharsForTx.ulTotalDataLength - pxCharsForTx.ulNextCharIndex;
	
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
		while( ulNextLength > ( unsigned portLONG ) 0 )
		{
			AT91C_BASE_UDP->UDP_FDR[ usbEND_POINT_0 ] = pxCharsForTx.ucTxBuffer[ pxCharsForTx.ulNextCharIndex ];
	
			ulNextLength--;
			pxCharsForTx.ulNextCharIndex++;
		}
	
		/* Start the transmission. */
		portENTER_CRITICAL();
		{
			ulStatus = AT91C_BASE_UDP->UDP_CSR[ usbEND_POINT_0 ];
			usbCSR_SET_BIT( &ulStatus, ( ( unsigned portLONG ) 0x10 ) );
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
			prvUSBTransmitNull();
			eDriverState = eNOTHING;
		}
	}
}



