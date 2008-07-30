/*
	FreeRTOS.org V5.0.3 - Copyright (C) 2003-2008 Richard Barry.

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
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
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

#ifndef USB_DEMO_H
#define USB_DEMO_H


/*-----------------------------------------------------------*/

#define usbQUEUE_LENGTH						( 0x3 )	/* Must have all bits set! */
#define usbEND_POINT_0						( 0 )
#define usbEND_POINT_1						( 1 )
#define usbRX_COUNT_MASK					( ( unsigned portLONG ) 0x7ff )
#define AT91C_UDP_STALLSENT					AT91C_UDP_ISOERROR

/* Structure used to take a snapshot of the USB status from within the ISR. */
typedef struct X_ISR_STATUS
{
	unsigned portLONG ulISR;
	unsigned portLONG ulCSR0;
	unsigned portCHAR ucFifoData[ 8 ];
} xISRStatus;

/* Macros to manipulate the control and status registers.  These registers 
cannot be accessed using a direct read modify write operation outside of the 
ISR as some bits are left unchanged by writing with a 0, and some are left 
unchanged by writing with a 1. */

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

/*
 * Creates the queue used to communicate between the USB task and the USB ISR, then
 * createst the task that manages the USB peripheral.
 */
void vStartUSBTask( unsigned portBASE_TYPE uxPriority );

#endif

