/*
	FreeRTOS.org V4.1.0 - Copyright (C) 2003-2006 Richard Barry.

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
	See http://www.FreeRTOS.org for documentation, latest information, license
	and contact details.  Please ensure to read the configuration and relevant
	port sections of the online documentation.
	***************************************************************************
*/

/*
 * Interrupt driven driver for the EMAC peripheral.  This driver is not
 * reentrant, re-entrancy is handled by a semaphore at the network interface
 * level. 
 */


/*
Changes from V3.2.2

	+ Corrected the byte order when writing the MAC address to the MAC.
	+ Support added for MII interfaces.  Previously only RMII was supported.

Changes from V3.2.3

	+ The MII interface is now the default.
	+ Modified the initialisation sequence slightly to allow auto init more
	  time to complete.

Changes from V4.0.1

	+ Made the function vClearEMACTxBuffer() more robust by moving the index
	  manipulation into the if() statement.  This allows the tx interrupt to
	  execute even when there is no data to handle.

Changes from V4.0.4

	+ Corrected the Rx frame length mask when obtaining the length from the
	  rx descriptor.
*/


/* Standard includes. */
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "semphr.h"
#include "task.h"

/* Demo app includes. */
#include "SAM7_EMAC.h"

/* Hardware specific includes. */
#include "Emac.h"
#include "mii.h"
#include "AT91SAM7X256.h"


/* USE_RMII_INTERFACE must be defined as 1 to use an RMII interface, or 0
to use an MII interface. */
#define USE_RMII_INTERFACE 0


/* The buffer addresses written into the descriptors must be aligned so the
last few bits are zero.  These bits have special meaning for the EMAC
peripheral and cannot be used as part of the address. */
#define emacADDRESS_MASK			( ( unsigned portLONG ) 0xFFFFFFFC )

/* Bit used within the address stored in the descriptor to mark the last
descriptor in the array. */
#define emacRX_WRAP_BIT				( ( unsigned portLONG ) 0x02 )

/* Bit used within the Tx descriptor status to indicate whether the
descriptor is under the control of the EMAC or the software. */
#define emacTX_BUF_USED				( ( unsigned portLONG ) 0x80000000 )

/* A short delay is used to wait for a buffer to become available, should
one not be immediately available when trying to transmit a frame. */
#define emacBUFFER_WAIT_DELAY		( 2 )
#define emacMAX_WAIT_CYCLES			( ( portBASE_TYPE ) ( configTICK_RATE_HZ / 40 ) )

/* The time to block waiting for input. */
#define emacBLOCK_TIME_WAITING_FOR_INPUT	( ( portTickType ) 100 )

/* Peripheral setup for the EMAC. */
#define emacPERIPHERAL_A_SETUP 		( ( unsigned portLONG ) AT91C_PB2_ETX0			) | \
									( ( unsigned portLONG ) AT91C_PB12_ETXER		) | \
									( ( unsigned portLONG ) AT91C_PB16_ECOL			) | \
									( ( unsigned portLONG ) AT91C_PB11_ETX3			) | \
									( ( unsigned portLONG ) AT91C_PB6_ERX1			) | \
									( ( unsigned portLONG ) AT91C_PB15_ERXDV		) | \
									( ( unsigned portLONG ) AT91C_PB13_ERX2			) | \
									( ( unsigned portLONG ) AT91C_PB3_ETX1			) | \
									( ( unsigned portLONG ) AT91C_PB8_EMDC			) | \
									( ( unsigned portLONG ) AT91C_PB5_ERX0			) | \
									( ( unsigned portLONG ) AT91C_PB14_ERX3			) | \
									( ( unsigned portLONG ) AT91C_PB4_ECRS_ECRSDV	) | \
									( ( unsigned portLONG ) AT91C_PB1_ETXEN			) | \
									( ( unsigned portLONG ) AT91C_PB10_ETX2			) | \
									( ( unsigned portLONG ) AT91C_PB0_ETXCK_EREFCK	) | \
									( ( unsigned portLONG ) AT91C_PB9_EMDIO			) | \
									( ( unsigned portLONG ) AT91C_PB7_ERXER			) | \
									( ( unsigned portLONG ) AT91C_PB17_ERXCK		);

/* Misc defines. */
#define emacINTERRUPT_LEVEL			( 5 )
#define emacNO_DELAY				( 0 )
#define emacTOTAL_FRAME_HEADER_SIZE	( 54 )
#define emacPHY_INIT_DELAY			( 5000 / portTICK_RATE_MS )
#define emacRESET_KEY				( ( unsigned portLONG ) 0xA5000000 )
#define emacRESET_LENGTH			( ( unsigned portLONG ) ( 0x01 << 8 ) )

/* The Atmel header file only defines the TX frame length mask. */
#define emacRX_LENGTH_FRAME			( 0xfff )

/*-----------------------------------------------------------*/

/* Buffer written to by the EMAC DMA.  Must be aligned as described by the
comment above the emacADDRESS_MASK definition. */
static volatile portCHAR pcRxBuffer[ NB_RX_BUFFERS * ETH_RX_BUFFER_SIZE ] __attribute__ ((aligned (8)));

/* Buffer read by the EMAC DMA.  Must be aligned as described by the comment
above the emacADDRESS_MASK definition. */
static portCHAR pcTxBuffer[ NB_TX_BUFFERS * ETH_TX_BUFFER_SIZE ] __attribute__ ((aligned (8)));

/* Descriptors used to communicate between the program and the EMAC peripheral.
These descriptors hold the locations and state of the Rx and Tx buffers. */
static volatile AT91S_TxTdDescriptor xTxDescriptors[ NB_TX_BUFFERS ];
static volatile AT91S_RxTdDescriptor xRxDescriptors[ NB_RX_BUFFERS ];

/* The IP and Ethernet addresses are read from the header files. */
const portCHAR cMACAddress[ 6 ] = { emacETHADDR0, emacETHADDR1, emacETHADDR2, emacETHADDR3, emacETHADDR4, emacETHADDR5 };
const unsigned char ucIPAddress[ 4 ]  = { emacIPADDR0, emacIPADDR1, emacIPADDR2, emacIPADDR3 };

/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */

/*
 * Prototype for the EMAC interrupt function - called by the asm wrapper.
 */
void vEMACISR( void ) __attribute__ ((naked));

/*
 * Initialise both the Tx and Rx descriptors used by the EMAC.
 */
static void prvSetupDescriptors(void);

/*
 * Write our MAC address into the EMAC.  
 */
static void prvSetupMACAddress( void );

/*
 * Configure the EMAC and AIC for EMAC interrupts.
 */
static void prvSetupEMACInterrupt( void );

/*
 * Some initialisation functions taken from the Atmel EMAC sample code.
 */
static void vReadPHY( unsigned portCHAR ucPHYAddress, unsigned portCHAR ucAddress, unsigned portLONG *pulValue );
static portBASE_TYPE xGetLinkSpeed( void );
static portBASE_TYPE prvProbePHY( void );
#if USE_RMII_INTERFACE != 1
	static void vWritePHY( unsigned portCHAR ucPHYAddress, unsigned portCHAR ucAddress, unsigned portLONG ulValue);
#endif


/* The semaphore used by the EMAC ISR to wake the EMAC task. */
static xSemaphoreHandle xSemaphore = NULL;

/* Holds the index to the next buffer from which data will be read. */
static volatile unsigned portLONG ulNextRxBuffer = 0;

/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */
portLONG lEMACSend( portCHAR *pcFrom, unsigned portLONG ulLength, portLONG lEndOfFrame )
{
static unsigned portBASE_TYPE uxTxBufferIndex = 0;
portBASE_TYPE xWaitCycles = 0;
portLONG lReturn = pdPASS;
portCHAR *pcBuffer;
unsigned portLONG ulLastBuffer, ulDataBuffered = 0, ulDataRemainingToSend, ulLengthToSend;

	/* If the length of data to be transmitted is greater than each individual
	transmit buffer then the data will be split into more than one buffer.
	Loop until the entire length has been buffered. */
	while( ulDataBuffered < ulLength )
	{
		/* Is a buffer available? */
		while( !( xTxDescriptors[ uxTxBufferIndex ].U_Status.status & AT91C_TRANSMIT_OK ) )
		{
			/* There is no room to write the Tx data to the Tx buffer.  Wait a
			short while, then try again. */
			xWaitCycles++;
			if( xWaitCycles > emacMAX_WAIT_CYCLES )
			{
				/* Give up. */
				lReturn = pdFAIL;
				break;
			}
			else
			{
				vTaskDelay( emacBUFFER_WAIT_DELAY );
			}
		}
	
		/* lReturn will only be pdPASS if a buffer is available. */
		if( lReturn == pdPASS )
		{
			portENTER_CRITICAL();
			{
				/* Get the address of the buffer from the descriptor, then copy 
				the data into the buffer. */
				pcBuffer = ( portCHAR * ) xTxDescriptors[ uxTxBufferIndex ].addr;

				/* How much can we write to the buffer? */
				ulDataRemainingToSend = ulLength - ulDataBuffered;
				if( ulDataRemainingToSend <= ETH_TX_BUFFER_SIZE )
				{
					/* We can write all the remaining bytes. */
					ulLengthToSend = ulDataRemainingToSend;
				}
				else
				{
					/* We can not write more than ETH_TX_BUFFER_SIZE in one go. */
					ulLengthToSend = ETH_TX_BUFFER_SIZE;
				}

				/* Copy the data into the buffer. */
				memcpy( ( void * ) pcBuffer, ( void * ) &( pcFrom[ ulDataBuffered ] ), ulLengthToSend );
				ulDataBuffered += ulLengthToSend;

				/* Is this the last data for the frame? */
				if( lEndOfFrame && ( ulDataBuffered >= ulLength ) )
				{
					/* No more data remains for this frame so we can start the 
					transmission. */
					ulLastBuffer = AT91C_LAST_BUFFER;
				}
				else
				{
					/* More data to come for this frame. */
					ulLastBuffer = 0;
				}
	
				/* Fill out the necessary in the descriptor to get the data sent, 
				then move to the next descriptor, wrapping if necessary. */
				if( uxTxBufferIndex >= ( NB_TX_BUFFERS - 1 ) )
				{				
					xTxDescriptors[ uxTxBufferIndex ].U_Status.status = 	( ulLengthToSend & ( unsigned portLONG ) AT91C_LENGTH_FRAME )
																			| ulLastBuffer
																			| AT91C_TRANSMIT_WRAP;
					uxTxBufferIndex = 0;
				}
				else
				{
					xTxDescriptors[ uxTxBufferIndex ].U_Status.status = 	( ulLengthToSend & ( unsigned portLONG ) AT91C_LENGTH_FRAME )
																			| ulLastBuffer;
					uxTxBufferIndex++;
				}
	
				/* If this is the last buffer to be sent for this frame we can
				start the transmission. */
				if( ulLastBuffer )
				{
					AT91C_BASE_EMAC->EMAC_NCR |= AT91C_EMAC_TSTART;
				}
			}
			portEXIT_CRITICAL();
		}
		else
		{
			break;
		}
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */
unsigned portLONG ulEMACInputLength( void )
{
register unsigned portLONG ulIndex, ulLength = 0;

	/* Skip any fragments.  We are looking for the first buffer that contains
	data and has the SOF (start of frame) bit set. */
	while( ( xRxDescriptors[ ulNextRxBuffer ].addr & AT91C_OWNERSHIP_BIT ) && !( xRxDescriptors[ ulNextRxBuffer ].U_Status.status & AT91C_SOF ) )
	{
		/* Ignoring this buffer.  Mark it as free again. */
		xRxDescriptors[ ulNextRxBuffer ].addr &= ~( AT91C_OWNERSHIP_BIT );		
		ulNextRxBuffer++;
		if( ulNextRxBuffer >= NB_RX_BUFFERS )
		{
			ulNextRxBuffer = 0;
		}
	}

	/* We are going to walk through the descriptors that make up this frame, 
	but don't want to alter ulNextRxBuffer as this would prevent vEMACRead()
	from finding the data.  Therefore use a copy of ulNextRxBuffer instead. */
	ulIndex = ulNextRxBuffer;

	/* Walk through the descriptors until we find the last buffer for this 
	frame.  The last buffer will give us the length of the entire frame. */
	while( ( xRxDescriptors[ ulIndex ].addr & AT91C_OWNERSHIP_BIT ) && !ulLength )
	{
		ulLength = xRxDescriptors[ ulIndex ].U_Status.status & emacRX_LENGTH_FRAME;

		/* Increment to the next buffer, wrapping if necessary. */
		ulIndex++;
		if( ulIndex >= NB_RX_BUFFERS )
		{
			ulIndex = 0;
		}
	}

	return ulLength;
}
/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */
void vEMACRead( portCHAR *pcTo, unsigned portLONG ulSectionLength, unsigned portLONG ulTotalFrameLength )
{
static unsigned portLONG ulSectionBytesReadSoFar = 0, ulBufferPosition = 0, ulFameBytesReadSoFar = 0;
static portCHAR *pcSource;
register unsigned portLONG ulBytesRemainingInBuffer, ulRemainingSectionBytes;

	/* Read ulSectionLength bytes from the Rx buffers.  This is not necessarily any
	correspondence between the length of our Rx buffers, and the length of the
	data we are returning or the length of the data being requested.  Therefore, 
	between calls  we have to remember not only which buffer we are currently 
	processing, but our position within that buffer.  This would be greatly
	simplified if PBUF_POOL_BUFSIZE could be guaranteed to be greater than
	the size of each Rx buffer, and that memory fragmentation did not occur.
	
	This function should only be called after a call to ulEMACInputLength().
	This will ensure ulNextRxBuffer is set to the correct buffer. */



	/* vEMACRead is called with pcTo set to NULL to indicate that we are about
	to read a new frame.  Any fragments remaining in the frame we were 
	processing during the last call should be dropped. */
	if( pcTo == NULL )
	{
		/* How many bytes are indicated as being in this buffer?  If none then
		the buffer is completely full and the frame is contained within more
		than one buffer. */

		/* Reset our state variables ready for the next read from this buffer. */
        pcSource = ( portCHAR * )( xRxDescriptors[ ulNextRxBuffer ].addr & emacADDRESS_MASK );
        ulFameBytesReadSoFar = ( unsigned portLONG ) 0;
		ulBufferPosition = ( unsigned portLONG ) 0;
	}
	else
	{
		/* Loop until we have obtained the required amount of data. */
        ulSectionBytesReadSoFar = 0;
		while( ulSectionBytesReadSoFar < ulSectionLength )
		{
			/* We may have already read some data from this buffer.  How much
			data remains in the buffer? */
			ulBytesRemainingInBuffer = ( ETH_RX_BUFFER_SIZE - ulBufferPosition );

			/* How many more bytes do we need to read before we have the 
			required amount of data? */
            ulRemainingSectionBytes = ulSectionLength - ulSectionBytesReadSoFar;

			/* Do we want more data than remains in the buffer? */
			if( ulRemainingSectionBytes > ulBytesRemainingInBuffer )
			{
				/* We want more data than remains in the buffer so we can 
				write the remains of the buffer to the destination, then move
				onto the next buffer to get the rest. */
				memcpy( &( pcTo[ ulSectionBytesReadSoFar ] ), &( pcSource[ ulBufferPosition ] ), ulBytesRemainingInBuffer );
				ulSectionBytesReadSoFar += ulBytesRemainingInBuffer;
                ulFameBytesReadSoFar += ulBytesRemainingInBuffer;

				/* Mark the buffer as free again. */
				xRxDescriptors[ ulNextRxBuffer ].addr &= ~( AT91C_OWNERSHIP_BIT );

				/* Move onto the next buffer. */
				ulNextRxBuffer++;
				if( ulNextRxBuffer >= NB_RX_BUFFERS )
				{
					ulNextRxBuffer = ( unsigned portLONG ) 0;
				}

				/* Reset the variables for the new buffer. */
				pcSource = ( portCHAR * )( xRxDescriptors[ ulNextRxBuffer ].addr & emacADDRESS_MASK );
				ulBufferPosition = ( unsigned portLONG ) 0;
			}
			else
			{
				/* We have enough data in this buffer to send back.  Read out
				enough data and remember how far we read up to. */
				memcpy( &( pcTo[ ulSectionBytesReadSoFar ] ), &( pcSource[ ulBufferPosition ] ), ulRemainingSectionBytes );

				/* There may be more data in this buffer yet.  Increment our 
				position in this buffer past the data we have just read. */
				ulBufferPosition += ulRemainingSectionBytes;
				ulSectionBytesReadSoFar += ulRemainingSectionBytes;
                ulFameBytesReadSoFar += ulRemainingSectionBytes;

				/* Have we now finished with this buffer? */
				if( ( ulBufferPosition >= ETH_RX_BUFFER_SIZE ) || ( ulFameBytesReadSoFar >= ulTotalFrameLength ) )
				{
					/* Mark the buffer as free again. */
					xRxDescriptors[ ulNextRxBuffer ].addr &= ~( AT91C_OWNERSHIP_BIT );

					/* Move onto the next buffer. */
					ulNextRxBuffer++;
					if( ulNextRxBuffer >= NB_RX_BUFFERS )
					{
						ulNextRxBuffer = 0;
					}
	
					pcSource = ( portCHAR * )( xRxDescriptors[ ulNextRxBuffer ].addr & emacADDRESS_MASK );
					ulBufferPosition = 0;
				}
			}
		}
	}
}
/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */
xSemaphoreHandle xEMACInit( void )
{
	/* Code supplied by Atmel -------------------------------*/

	/* Disable pull up on RXDV => PHY normal mode (not in test mode),
	PHY has internal pull down. */
	AT91C_BASE_PIOB->PIO_PPUDR = 1 << 15;

	#if USE_RMII_INTERFACE != 1
	  	/* PHY has internal pull down : set MII mode. */
	  	AT91C_BASE_PIOB->PIO_PPUDR = 1 << 16;
	#endif

	/* Clear PB18 <=> PHY powerdown. */
   	AT91C_BASE_PIOB->PIO_PER = 1 << 18;
	AT91C_BASE_PIOB->PIO_OER = 1 << 18;
	AT91C_BASE_PIOB->PIO_CODR = 1 << 18;

	/* After PHY power up, hardware reset. */
	AT91C_BASE_RSTC->RSTC_RMR = emacRESET_KEY | emacRESET_LENGTH;
	AT91C_BASE_RSTC->RSTC_RCR = emacRESET_KEY | AT91C_RSTC_EXTRST;

	/* Wait for hardware reset end. */
	while( !( AT91C_BASE_RSTC->RSTC_RSR & AT91C_RSTC_NRSTL ) )
	{
		__asm volatile ( "NOP" );
	}
    __asm volatile ( "NOP" );

	/* Setup the pins. */
	AT91C_BASE_PIOB->PIO_ASR = emacPERIPHERAL_A_SETUP;
	AT91C_BASE_PIOB->PIO_PDR = emacPERIPHERAL_A_SETUP;

	/* Enable com between EMAC PHY.

	Enable management port. */
	AT91C_BASE_EMAC->EMAC_NCR |= AT91C_EMAC_MPE;	

	/* MDC = MCK/32. */
	AT91C_BASE_EMAC->EMAC_NCFGR |= ( 2 ) << 10;	

	/* Wait for PHY auto init end (rather crude delay!). */
	vTaskDelay( emacPHY_INIT_DELAY );

	/* PHY configuration. */
	#if USE_RMII_INTERFACE != 1
	{
		unsigned portLONG ulControl;

		/* PHY has internal pull down : disable MII isolate. */
		vReadPHY( AT91C_PHY_ADDR, MII_BMCR, &ulControl );
		vReadPHY( AT91C_PHY_ADDR, MII_BMCR, &ulControl );
		ulControl &= ~BMCR_ISOLATE;
		vWritePHY( AT91C_PHY_ADDR, MII_BMCR, ulControl );
	}
	#endif

	/* Disable management port again. */
	AT91C_BASE_EMAC->EMAC_NCR &= ~AT91C_EMAC_MPE;

	#if USE_RMII_INTERFACE != 1
		/* Enable EMAC in MII mode, enable clock ERXCK and ETXCK. */
		AT91C_BASE_EMAC->EMAC_USRIO = AT91C_EMAC_CLKEN ;
	#else
		/* Enable EMAC in RMII mode, enable RMII clock (50MHz from oscillator
		on ERFCK). */
		AT91C_BASE_EMAC->EMAC_USRIO = AT91C_EMAC_RMII | AT91C_EMAC_CLKEN ;
	#endif

	/* End of code supplied by Atmel ------------------------*/

	/* Setup the buffers and descriptors. */
	prvSetupDescriptors();
	
	/* Load our MAC address into the EMAC. */
	prvSetupMACAddress();

	/* Are we connected? */
	if( prvProbePHY() )
	{
		/* Enable the interrupt! */
		portENTER_CRITICAL();
		{
			prvSetupEMACInterrupt();
			vPassEMACSemaphore( xSemaphore );
		}
		portEXIT_CRITICAL();
	}

	return xSemaphore;
}
/*-----------------------------------------------------------*/

/* See the header file for descriptions of public functions. */
void vClearEMACTxBuffer( void )
{
static unsigned portBASE_TYPE uxNextBufferToClear = 0;

	/* Called on Tx interrupt events to reset the AT91C_TRANSMIT_OK bit in each 
	Tx buffer within the frame just transmitted.  This marks all the buffers
	as available again.

	The first buffer in the frame should have the bit set automatically. */
	if( xTxDescriptors[ uxNextBufferToClear ].U_Status.status & AT91C_TRANSMIT_OK )
	{
		/* Loop through the other buffers in the frame. */
		while( !( xTxDescriptors[ uxNextBufferToClear ].U_Status.status & AT91C_LAST_BUFFER ) )
		{
			uxNextBufferToClear++;

			if( uxNextBufferToClear >= NB_TX_BUFFERS )
			{
				uxNextBufferToClear = 0;
			}

			xTxDescriptors[ uxNextBufferToClear ].U_Status.status |= AT91C_TRANSMIT_OK;
		}

		/* Start with the next buffer the next time a Tx interrupt is called. */
		uxNextBufferToClear++;

		/* Do we need to wrap back to the first buffer? */
		if( uxNextBufferToClear >= NB_TX_BUFFERS )
		{
			uxNextBufferToClear = 0;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetupDescriptors(void)
{
unsigned portBASE_TYPE xIndex;
unsigned portLONG ulAddress;

	/* Initialise xRxDescriptors descriptor. */
	for( xIndex = 0; xIndex < NB_RX_BUFFERS; ++xIndex )
	{
		/* Calculate the address of the nth buffer within the array. */
		ulAddress = ( unsigned portLONG )( pcRxBuffer + ( xIndex * ETH_RX_BUFFER_SIZE ) );

		/* Write the buffer address into the descriptor.  The DMA will place
		the data at this address when this descriptor is being used.  Mask off
		the bottom bits of the address as these have special meaning. */
		xRxDescriptors[ xIndex ].addr = ulAddress & emacADDRESS_MASK;
	}	

	/* The last buffer has the wrap bit set so the EMAC knows to wrap back
	to the first buffer. */
	xRxDescriptors[ NB_RX_BUFFERS - 1 ].addr |= emacRX_WRAP_BIT;

	/* Initialise xTxDescriptors. */
	for( xIndex = 0; xIndex < NB_TX_BUFFERS; ++xIndex )
	{
		/* Calculate the address of the nth buffer within the array. */
		ulAddress = ( unsigned portLONG )( pcTxBuffer + ( xIndex * ETH_TX_BUFFER_SIZE ) );

		/* Write the buffer address into the descriptor.  The DMA will read
		data from here when the descriptor is being used. */
		xTxDescriptors[ xIndex ].addr = ulAddress & emacADDRESS_MASK;
		xTxDescriptors[ xIndex ].U_Status.status = AT91C_TRANSMIT_OK;
	}	

	/* The last buffer has the wrap bit set so the EMAC knows to wrap back
	to the first buffer. */
	xTxDescriptors[ NB_TX_BUFFERS - 1 ].U_Status.status = AT91C_TRANSMIT_WRAP | AT91C_TRANSMIT_OK;

	/* Tell the EMAC where to find the descriptors. */
	AT91C_BASE_EMAC->EMAC_RBQP = ( unsigned portLONG ) xRxDescriptors;
	AT91C_BASE_EMAC->EMAC_TBQP = ( unsigned portLONG ) xTxDescriptors;
	
	/* Clear all the bits in the receive status register. */
	AT91C_BASE_EMAC->EMAC_RSR = ( AT91C_EMAC_OVR | AT91C_EMAC_REC | AT91C_EMAC_BNA );

	/* Enable the copy of data into the buffers, ignore broadcasts, 
	and don't copy FCS. */
	AT91C_BASE_EMAC->EMAC_NCFGR |= ( AT91C_EMAC_CAF | AT91C_EMAC_NBC | AT91C_EMAC_DRFCS);

	/* Enable Rx and Tx, plus the stats register. */
	AT91C_BASE_EMAC->EMAC_NCR |= ( AT91C_EMAC_TE | AT91C_EMAC_RE | AT91C_EMAC_WESTAT );
}	
/*-----------------------------------------------------------*/

static void prvSetupMACAddress( void )
{
	/* Must be written SA1L then SA1H. */
	AT91C_BASE_EMAC->EMAC_SA1L =	( ( unsigned portLONG ) cMACAddress[ 3 ] << 24 ) |
									( ( unsigned portLONG ) cMACAddress[ 2 ] << 16 ) |
									( ( unsigned portLONG ) cMACAddress[ 1 ] << 8  ) |
									cMACAddress[ 0 ];

	AT91C_BASE_EMAC->EMAC_SA1H =	( ( unsigned portLONG ) cMACAddress[ 5 ] << 8 ) |
									cMACAddress[ 4 ];
}
/*-----------------------------------------------------------*/

static void prvSetupEMACInterrupt( void )
{
	/* Create the semaphore used to trigger the EMAC task. */
	vSemaphoreCreateBinary( xSemaphore );
	if( xSemaphore )
	{
		/* We start by 'taking' the semaphore so the ISR can 'give' it when the
		first interrupt occurs. */
		xSemaphoreTake( xSemaphore, emacNO_DELAY );
		portENTER_CRITICAL();
		{
			/* We want to interrupt on Rx and Tx events. */
			AT91C_BASE_EMAC->EMAC_IER = AT91C_EMAC_RCOMP | AT91C_EMAC_TCOMP;

			/* Enable the interrupts in the AIC. */
			AT91F_AIC_ConfigureIt( AT91C_ID_EMAC, emacINTERRUPT_LEVEL, AT91C_AIC_SRCTYPE_INT_HIGH_LEVEL, ( void (*)( void ) ) vEMACISR );
            AT91C_BASE_AIC->AIC_IECR = 0x1 << AT91C_ID_EMAC;
		}
		portEXIT_CRITICAL();
	}
}





/*
 * The following functions are initialisation functions taken from the Atmel
 * EMAC sample code.
 */


static portBASE_TYPE prvProbePHY( void )
{
unsigned portLONG ulPHYId1, ulPHYId2, ulStatus;
portBASE_TYPE xReturn = pdPASS;
	
	/* Code supplied by Atmel (reformatted) -----------------*/

	/* Enable management port */
	AT91C_BASE_EMAC->EMAC_NCR |= AT91C_EMAC_MPE;	
   	AT91C_BASE_EMAC->EMAC_NCFGR |= ( 2 ) << 10;

	/* Read the PHY ID. */
	vReadPHY( AT91C_PHY_ADDR, MII_PHYSID1, &ulPHYId1 );
	vReadPHY(AT91C_PHY_ADDR, MII_PHYSID2, &ulPHYId2 );

	/* AMD AM79C875:
			PHY_ID1 = 0x0022
			PHY_ID2 = 0x5541
			Bits 3:0 Revision Number Four bit manufacturer?s revision number.
				0001 stands for Rev. A, etc.
	*/
	if( ( ( ulPHYId1 << 16 ) | ( ulPHYId2 & 0xfff0 ) ) != MII_DM9161_ID )
	{
		/* Did not expect this ID. */
		xReturn = pdFAIL;
	}
	else
	{
		ulStatus = xGetLinkSpeed();

		if( ulStatus != pdPASS )
		{
			xReturn = pdFAIL;
		}
	}

	/* Disable management port */
	AT91C_BASE_EMAC->EMAC_NCR &= ~AT91C_EMAC_MPE;	

	/* End of code supplied by Atmel ------------------------*/

	return xReturn;
}
/*-----------------------------------------------------------*/

static void vReadPHY( unsigned portCHAR ucPHYAddress, unsigned portCHAR ucAddress, unsigned portLONG *pulValue )
{
	/* Code supplied by Atmel (reformatted) ----------------------*/

	AT91C_BASE_EMAC->EMAC_MAN = 	(AT91C_EMAC_SOF & (0x01<<30))
									| (2 << 16) | (2 << 28)
									| ((ucPHYAddress & 0x1f) << 23)
									| (ucAddress << 18);

	/* Wait until IDLE bit in Network Status register is cleared. */
	while( !( AT91C_BASE_EMAC->EMAC_NSR & AT91C_EMAC_IDLE ) )
	{
		__asm( "NOP" );
	}

	*pulValue = ( AT91C_BASE_EMAC->EMAC_MAN & 0x0000ffff );	

	/* End of code supplied by Atmel ------------------------*/
}
/*-----------------------------------------------------------*/

#if USE_RMII_INTERFACE != 1
static void vWritePHY( unsigned portCHAR ucPHYAddress, unsigned portCHAR ucAddress, unsigned portLONG ulValue )
{
	/* Code supplied by Atmel (reformatted) ----------------------*/

	AT91C_BASE_EMAC->EMAC_MAN = (( AT91C_EMAC_SOF & (0x01<<30))
								| (2 << 16) | (1 << 28)
								| ((ucPHYAddress & 0x1f) << 23)
								| (ucAddress << 18))
								| (ulValue & 0xffff);

	/* Wait until IDLE bit in Network Status register is cleared */
	while( !( AT91C_BASE_EMAC->EMAC_NSR & AT91C_EMAC_IDLE ) )
	{
		__asm( "NOP" );
	};

	/* End of code supplied by Atmel ------------------------*/
}
#endif
/*-----------------------------------------------------------*/

static portBASE_TYPE xGetLinkSpeed( void )
{
	unsigned portLONG ulBMSR, ulBMCR, ulLPA, ulMACCfg, ulSpeed, ulDuplex;

	/* Code supplied by Atmel (reformatted) -----------------*/

	/* Link status is latched, so read twice to get current value */
	vReadPHY(AT91C_PHY_ADDR, MII_BMSR, &ulBMSR);
	vReadPHY(AT91C_PHY_ADDR, MII_BMSR, &ulBMSR);

	if( !( ulBMSR & BMSR_LSTATUS ) )
	{	
		/* No Link. */
		return pdFAIL;
	}

	vReadPHY(AT91C_PHY_ADDR, MII_BMCR, &ulBMCR);
	if (ulBMCR & BMCR_ANENABLE)
	{				
		/* AutoNegotiation is enabled. */
		if (!(ulBMSR & BMSR_ANEGCOMPLETE))
		{
			/* Auto-negotitation in progress. */
			return pdFAIL;				
		}		

		vReadPHY(AT91C_PHY_ADDR, MII_LPA, &ulLPA);
		if( ( ulLPA & LPA_100FULL ) || ( ulLPA & LPA_100HALF ) )
		{
			ulSpeed = SPEED_100;
		}
		else
		{
			ulSpeed = SPEED_10;
		}

		if( ( ulLPA & LPA_100FULL ) || ( ulLPA & LPA_10FULL ) )
		{
			ulDuplex = DUPLEX_FULL;
		}
		else
		{
			ulDuplex = DUPLEX_HALF;
		}
	}
	else
	{
		ulSpeed = ( ulBMCR & BMCR_SPEED100 ) ? SPEED_100 : SPEED_10;
		ulDuplex = ( ulBMCR & BMCR_FULLDPLX ) ? DUPLEX_FULL : DUPLEX_HALF;
	}

	/* Update the MAC */
	ulMACCfg = AT91C_BASE_EMAC->EMAC_NCFGR & ~( AT91C_EMAC_SPD | AT91C_EMAC_FD );
	if( ulSpeed == SPEED_100 )
	{
		if( ulDuplex == DUPLEX_FULL )
		{
			/* 100 Full Duplex */
			AT91C_BASE_EMAC->EMAC_NCFGR = ulMACCfg | AT91C_EMAC_SPD | AT91C_EMAC_FD;
		}
		else
		{					
			/* 100 Half Duplex */
			AT91C_BASE_EMAC->EMAC_NCFGR = ulMACCfg | AT91C_EMAC_SPD;
		}
	}
	else
	{
		if (ulDuplex == DUPLEX_FULL)
		{
			/* 10 Full Duplex */
			AT91C_BASE_EMAC->EMAC_NCFGR = ulMACCfg | AT91C_EMAC_FD;
		}
		else
		{			/* 10 Half Duplex */
			AT91C_BASE_EMAC->EMAC_NCFGR = ulMACCfg;
		}
	}

	/* End of code supplied by Atmel ------------------------*/

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vEMACWaitForInput( void )
{
	/* Just wait until we are signled from an ISR that data is available, or
	we simply time out. */
	xSemaphoreTake( xSemaphore, emacBLOCK_TIME_WAITING_FOR_INPUT );
}
