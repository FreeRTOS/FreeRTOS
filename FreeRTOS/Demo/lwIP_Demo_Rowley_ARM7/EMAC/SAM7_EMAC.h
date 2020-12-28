/*
 * FreeRTOS V202012.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
SemaphoreHandle_t xEMACInit( void );

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
void vPassEMACSemaphore( SemaphoreHandle_t xCreatedSemaphore );

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
