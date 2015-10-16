/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
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

/* ACM Requests */
#define usbSEND_ENCAPSULATED_COMMAND		( 0x00 )
#define usbGET_ENCAPSULATED_RESPONSE		( 0x01 )
#define usbSET_LINE_CODING					( 0x20 )
#define usbGET_LINE_CODING					( 0x21 )
#define usbSET_CONTROL_LINE_STATE			( 0x22 )

/* Misc USB definitions. */
#define usbDEVICE_CLASS_VENDOR_SPECIFIC		( 0xFF )
#define usbBUS_POWERED						( 0x80 )
#define usbHID_REPORT_DESCRIPTOR			( 0x22 )
#define AT91C_UDP_TRANSCEIVER_ENABLE		( *( ( unsigned long * ) 0xfffb0074 ) )

/* Index to the various string. */
#define usbLANGUAGE_STRING					( 0 )
#define usbMANUFACTURER_STRING				( 1 )
#define usbPRODUCT_STRING					( 2 )
#define usbCONFIGURATION_STRING				( 3 )
#define usbINTERFACE_STRING					( 4 )

/* Defines fields of standard SETUP request.  Now in normal order. */
#define usbREQUEST_TYPE_INDEX				( 0 )
#define usbREQUEST_INDEX					( 1 )
#define usbVALUE_HIGH_BYTE					( 3 )
#define usbVALUE_LOW_BYTE					( 2 )
#define usbINDEX_HIGH_BYTE					( 5 )
#define usbINDEX_LOW_BYTE					( 4 )
#define usbLENGTH_HIGH_BYTE					( 7 )
#define usbLENGTH_LOW_BYTE					( 6 )

/* Misc application definitions. */
#define usbINTERRUPT_PRIORITY				( 3 )
#define usbQUEUE_LENGTH						( 0x3 )	/* Must have all bits set! */
#define usbFIFO_LENGTH						( ( unsigned long ) 8 )
#define usbEND_POINT_0						( 0 )
#define usbEND_POINT_1						( 1 )
#define usbEND_POINT_2						( 2 )
#define usbEND_POINT_3						( 3 )
#define usbMAX_CONTROL_MESSAGE_SIZE			( 128 )
#define usbRX_COUNT_MASK					( ( unsigned long ) 0x7ff )
#define AT91C_UDP_STALLSENT					AT91C_UDP_ISOERROR
#define usbSHORTEST_DELAY					( ( TickType_t ) 1 )
#define usbINIT_DELAY						( ( TickType_t ) 1000 / portTICK_PERIOD_MS )
#define usbSHORT_DELAY						( ( TickType_t ) 50 / portTICK_PERIOD_MS )
#define usbEND_POINT_RESET_MASK				( ( unsigned long ) 0x0f )
#define usbDATA_INC							( ( char ) 5 )
#define usbEXPECTED_NUMBER_OF_BYTES			( ( unsigned long ) 8 )

/* Control request types. */
#define usbSTANDARD_DEVICE_REQUEST			( 0 )
#define usbSTANDARD_INTERFACE_REQUEST		( 1 )
#define usbSTANDARD_END_POINT_REQUEST		( 2 )
#define usbCLASS_INTERFACE_REQUEST			( 5 )


/* Macros to manipulate the control and status registers.  These registers 
cannot be accessed using a direct read modify write operation outside of the 
ISR as some bits are left unchanged by writing with a 0, and some are left 
unchanged by writing with a 1. */


#define usbCSR_SET_BIT( pulValueNow, ulBit )											\
{																						\
	/* Set TXCOMP, RX_DATA_BK0, RXSETUP, */												\
	/* STALLSENT and RX_DATA_BK1 to 1 so the */											\
	/* write has no effect. */															\
	( * ( ( unsigned long * ) pulValueNow ) ) |= ( unsigned long ) 0x4f;		\
																						\
	/* Clear the FORCE_STALL and TXPKTRDY bits */										\
	/* so the write has no effect. */													\
	( * ( ( unsigned long * ) pulValueNow ) ) &= ( unsigned long ) 0xffffffcf;	\
																						\
	/* Set whichever bit we want set. */												\
	( * ( ( unsigned long * ) pulValueNow ) ) |= ( ulBit );							\
}

#define usbCSR_CLEAR_BIT( pulValueNow, ulBit )											\
{																						\
	/* Set TXCOMP, RX_DATA_BK0, RXSETUP, */												\
	/* STALLSENT and RX_DATA_BK1 to 1 so the */											\
	/* write has no effect. */															\
	( * ( ( unsigned long * ) pulValueNow ) ) |= ( unsigned long ) 0x4f;		\
																						\
	/* Clear the FORCE_STALL and TXPKTRDY bits */										\
	/* so the write has no effect. */													\
	( * ( ( unsigned long * ) pulValueNow ) ) &= ( unsigned long ) 0xffffffcf;	\
																						\
	/* Clear whichever bit we want clear. */											\
	( * ( ( unsigned long * ) pulValueNow ) ) &= ( ~ulBit );						\
}
