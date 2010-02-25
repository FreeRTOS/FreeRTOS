/*
    FreeRTOS V6.0.3 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

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
#define usbRX_COUNT_MASK					( ( unsigned long ) 0x7ff )
#define AT91C_UDP_STALLSENT					AT91C_UDP_ISOERROR

/* Structure used to take a snapshot of the USB status from within the ISR. */
typedef struct X_ISR_STATUS
{
	unsigned long ulISR;
	unsigned long ulCSR0;
	unsigned char ucFifoData[ 8 ];
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
	( * ( ( unsigned long * ) pulValueNow ) ) |= ( unsigned long ) 0x4f;		\
																						\
	/* Clear the FORCE_STALL and TXPKTRDY bits */										\
	/* so the write has no effect. */													\
	( * ( ( unsigned long * ) pulValueNow ) ) &= ( unsigned long ) 0xffffffcf;	\
																						\
	/* Set whichever bit we want set. */												\
	( * ( ( unsigned long * ) pulValueNow ) ) |= ( ulBit );							\
}

/*
 * Creates the queue used to communicate between the USB task and the USB ISR, then
 * createst the task that manages the USB peripheral.
 */
void vStartUSBTask( unsigned portBASE_TYPE uxPriority );

#endif

