/*
    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it    under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation and modified by the FreeRTOS exception.
    **NOTE** The exception to the GPL is included to allow you to distribute a
    combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    Alternative commercial license and support terms are also available upon
    request.  See the licensing section of http://www.FreeRTOS.org for full
    license details.

    FreeRTOS is distributed in the hope that it will be useful,    but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details.

    You should have received a copy of the GNU General Public License along
    with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
    Temple Place, Suite 330, Boston, MA  02111-1307  USA.


    ***************************************************************************
    *                                                                         *
    * The FreeRTOS eBook and reference manual are available to purchase for a *
    * small fee. Help yourself get started quickly while also helping the     *
    * FreeRTOS project! See http://www.FreeRTOS.org/Documentation for details *
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
Changes from V3.2.4

	+ Modified the default MAC address as the one used previously was not liked
	  by some routers.

*/

#ifndef SAM_7_EMAC_H
#define SAM_7_EMAC_H

/* MAC address definition.  The MAC address must be unique on the network. */
#define emacETHADDR0 0
#define emacETHADDR1 0xbd
#define emacETHADDR2 0x33
#define emacETHADDR3 0x06
#define emacETHADDR4 0x68
#define emacETHADDR5 0x22

/* The IP address being used. */
#define emacIPADDR0 172
#define emacIPADDR1 25
#define emacIPADDR2 218
#define emacIPADDR3 205

/* The gateway address being used. */
#define emacGATEWAY_ADDR0 172
#define emacGATEWAY_ADDR1 25
#define emacGATEWAY_ADDR2 218
#define emacGATEWAY_ADDR3 3

/* The network mask being used. */
#define emacNET_MASK0 255
#define emacNET_MASK1 255
#define emacNET_MASK2 0
#define emacNET_MASK3 0

/*
 * Initialise the EMAC driver.  If successful a semaphore is returned that
 * is used by the EMAC ISR to indicate that Rx packets have been received.
 * If the initialisation fails then NULL is returned.
 */
xSemaphoreHandle xEMACInit( void );

/*
 * Send ulLength bytes from pcFrom.  This copies the buffer to one of the
 * EMAC Tx buffers, then indicates to the EMAC that the buffer is ready.
 * If lEndOfFrame is true then the data being copied is the end of the frame
 * and the frame can be transmitted. 
 */
long lEMACSend( char *pcFrom, unsigned long ulLength, long lEndOfFrame );

/*
 * Frames can be read from the EMAC in multiple sections.
 * Read ulSectionLength bytes from the EMAC receive buffers to pcTo.  
 * ulTotalFrameLength is the size of the entire frame.  Generally vEMACRead
 * will be repetedly called until the sum of all the ulSectionLenths totals
 * the value of ulTotalFrameLength.
 */
void vEMACRead( char *pcTo, unsigned long ulSectionLength, unsigned long ulTotalFrameLength );

/*
 * The EMAC driver and interrupt service routines are defined in different 
 * files as the driver is compiled to THUMB, and the ISR to ARM.  This function
 * simply passes the semaphore used to communicate between the two.
 */
void vPassEMACSemaphore( xSemaphoreHandle xCreatedSemaphore );

/* 
 * Called by the Tx interrupt, this function traverses the buffers used to
 * hold the frame that has just completed transmission and marks each as
 * free again.
 */
void vClearEMACTxBuffer( void );

/*
 * Suspend on a semaphore waiting either for the semaphore to be obtained 
 * or a timeout.  The semaphore is used by the EMAC ISR to indicate that
 * data has been received and is ready for processing.
 */
void vEMACWaitForInput( void );

/*
 * Return the length of the next frame in the receive buffers.
 */
unsigned long ulEMACInputLength( void );

#endif
