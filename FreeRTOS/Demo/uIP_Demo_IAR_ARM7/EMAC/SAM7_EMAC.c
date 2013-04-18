/*
    FreeRTOS V7.4.1 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************


    http://www.FreeRTOS.org - Documentation, books, training, latest versions, 
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
*/

/*
 * Basic interrupt driven driver for the EMAC peripheral.  This driver is not
 * reentrant as with uIP the buffers are only ever accessed from a single task.
 *
 * The simple buffer management used within uIP allows the EMAC driver to also
 * be simplistic.  The driver contained within the lwIP demo is more
 * comprehensive.
 */


/*
Changes from V3.2.2

	+ Corrected the byte order when writing the MAC address to the MAC.
	+ Support added for MII interfaces.  Previously only RMII was supported.

Changes from V3.2.3

	+ The MII interface is now the default.
	+ Modified the initialisation sequence slightly to allow auto init more
	  time to complete.

Changes from V3.2.4

	+ Also read the EMAC_RSR register in the EMAC ISR as a work around the 
	  the EMAC bug that can reset the RX bit in EMAC_ISR register before the
	  bit has been read.

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

/* uIP includes. */
#include "uip.h"

/* Hardware specific includes. */
#include "Emac.h"
#include "mii.h"


/* USE_RMII_INTERFACE must be defined as 1 to use an RMII interface, or 0
to use an MII interface. */
#define USE_RMII_INTERFACE 0

/* The buffer addresses written into the descriptors must be aligned so the
last few bits are zero.  These bits have special meaning for the EMAC
peripheral and cannot be used as part of the address. */
#define emacADDRESS_MASK			( ( unsigned long ) 0xFFFFFFFC )

/* Bit used within the address stored in the descriptor to mark the last
descriptor in the array. */
#define emacRX_WRAP_BIT				( ( unsigned long ) 0x02 )

/* Bit used within the Tx descriptor status to indicate whether the
descriptor is under the control of the EMAC or the software. */
#define emacTX_BUF_USED				( ( unsigned long ) 0x80000000 )

/* A short delay is used to wait for a buffer to become available, should
one not be immediately available when trying to transmit a frame. */
#define emacBUFFER_WAIT_DELAY		( 2 )
#define emacMAX_WAIT_CYCLES			( configTICK_RATE_HZ / 40 )

/* Misc defines. */
#define emacINTERRUPT_LEVEL			( 5 )
#define emacNO_DELAY				( 0 )
#define emacTOTAL_FRAME_HEADER_SIZE	( 54 )
#define emacPHY_INIT_DELAY			( 5000 / portTICK_RATE_MS )
#define emacRESET_KEY				( ( unsigned long ) 0xA5000000 )
#define emacRESET_LENGTH			( ( unsigned long ) ( 0x01 << 8 ) )

/* The Atmel header file only defines the TX frame length mask. */
#define emacRX_LENGTH_FRAME			( 0xfff )

/*-----------------------------------------------------------*/

/*
 * Prototype for the EMAC interrupt asm wrapper.
 */
extern void vEMACISREntry( void );

/*
 * Prototype for the EMAC interrupt function - called by the asm wrapper.
 */
__arm void vEMACISR( void );

/*
 * Initialise both the Tx and Rx descriptors used by the EMAC.
 */
static void prvSetupDescriptors(void);

/*
 * Write our MAC address into the EMAC.  The MAC address is set as one of the
 * uip options.
 */
static void prvSetupMACAddress( void );

/*
 * Configure the EMAC and AIC for EMAC interrupts.
 */
static void prvSetupEMACInterrupt( void );

/*
 * Some initialisation functions taken from the Atmel EMAC sample code.
 */
static void vReadPHY( unsigned char ucPHYAddress, unsigned char ucAddress, unsigned long *pulValue );
#if USE_RMII_INTERFACE != 1
	static void vWritePHY( unsigned char ucPHYAddress, unsigned char ucAddress, unsigned long ulValue);
#endif
static portBASE_TYPE xGetLinkSpeed( void );
static portBASE_TYPE prvProbePHY( void );

/*-----------------------------------------------------------*/

/* Buffer written to by the EMAC DMA.  Must be aligned as described by the
comment above the emacADDRESS_MASK definition. */
#pragma data_alignment=8
static volatile char pcRxBuffer[ NB_RX_BUFFERS * ETH_RX_BUFFER_SIZE ];

/* Buffer read by the EMAC DMA.  Must be aligned as described by he comment
above the emacADDRESS_MASK definition. */
#pragma data_alignment=8
static char pcTxBuffer[ NB_TX_BUFFERS * ETH_TX_BUFFER_SIZE ];

/* Descriptors used to communicate between the program and the EMAC peripheral.
These descriptors hold the locations and state of the Rx and Tx buffers. */
static volatile AT91S_TxTdDescriptor xTxDescriptors[ NB_TX_BUFFERS ];
static volatile AT91S_RxTdDescriptor xRxDescriptors[ NB_RX_BUFFERS ];

/* The IP and Ethernet addresses are read from the uIP setup. */
const char cMACAddress[ 6 ] = { UIP_ETHADDR0, UIP_ETHADDR1, UIP_ETHADDR2, UIP_ETHADDR3, UIP_ETHADDR4, UIP_ETHADDR5 };
const unsigned char ucIPAddress[ 4 ]  = { UIP_IPADDR0, UIP_IPADDR1, UIP_IPADDR2, UIP_IPADDR3 };

/* The semaphore used by the EMAC ISR to wake the EMAC task. */
static xSemaphoreHandle xSemaphore = NULL;

/*-----------------------------------------------------------*/

xSemaphoreHandle xEMACInit( void )
{
	/* Code supplied by Atmel (modified) --------------------*/

	/* disable pull up on RXDV => PHY normal mode (not in test mode),
	PHY has internal pull down. */
	AT91C_BASE_PIOB->PIO_PPUDR = 1 << 15;

	#if USE_RMII_INTERFACE != 1
	  	/* PHY has internal pull down : set MII mode. */
	  	AT91C_BASE_PIOB->PIO_PPUDR= 1 << 16;
	#endif

	/* clear PB18 <=> PHY powerdown. */
	AT91F_PIO_CfgOutput( AT91C_BASE_PIOB, 1 << 18 ) ;
	AT91F_PIO_ClearOutput( AT91C_BASE_PIOB,  1 << 18) ;

	/* After PHY power up, hardware reset. */
	AT91C_BASE_RSTC->RSTC_RMR = emacRESET_KEY | emacRESET_LENGTH;
	AT91C_BASE_RSTC->RSTC_RCR = emacRESET_KEY | AT91C_RSTC_EXTRST;
	
	/* Wait for hardware reset end. */
	while( !( AT91C_BASE_RSTC->RSTC_RSR & AT91C_RSTC_NRSTL ) )
	{
		__asm( "NOP" );
	}
	__asm( "NOP" );
  	
	/* EMAC IO init for EMAC-PHY com. Remove EF100 config. */
	AT91F_EMAC_CfgPIO();

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
		unsigned long ulControl;

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

	/* Try to connect. */
	if( prvProbePHY() )
	{
		/* Enable the interrupt! */
		prvSetupEMACInterrupt();
	}

	return xSemaphore;
}
/*-----------------------------------------------------------*/

long lEMACSend( void )
{
static unsigned portBASE_TYPE uxTxBufferIndex = 0;
portBASE_TYPE xWaitCycles = 0;
long lReturn = pdPASS;
char *pcBuffer;

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
		/* Copy the headers into the Tx buffer.  These will be in the uIP buffer. */
		pcBuffer = ( char * ) xTxDescriptors[ uxTxBufferIndex ].addr;
		memcpy( ( void * ) pcBuffer, ( void * ) uip_buf, emacTOTAL_FRAME_HEADER_SIZE );
		if( uip_len > emacTOTAL_FRAME_HEADER_SIZE )
		{
			memcpy( ( void * ) &( pcBuffer[ emacTOTAL_FRAME_HEADER_SIZE ] ), ( void * ) uip_appdata, ( uip_len - emacTOTAL_FRAME_HEADER_SIZE ) );
		}

		/* Send. */	
		portENTER_CRITICAL();
		{
			if( uxTxBufferIndex >= ( NB_TX_BUFFERS - 1 ) )
			{
				/* Fill out the necessary in the descriptor to get the data sent. */
				xTxDescriptors[ uxTxBufferIndex ].U_Status.status = 	( uip_len & ( unsigned long ) AT91C_LENGTH_FRAME )
																		| AT91C_LAST_BUFFER
																		| AT91C_TRANSMIT_WRAP;
				uxTxBufferIndex = 0;
			}
			else
			{
				/* Fill out the necessary in the descriptor to get the data sent. */
				xTxDescriptors[ uxTxBufferIndex ].U_Status.status = 	( uip_len & ( unsigned long ) AT91C_LENGTH_FRAME )
																		| AT91C_LAST_BUFFER;
				uxTxBufferIndex++;
			}
	
			AT91C_BASE_EMAC->EMAC_NCR |= AT91C_EMAC_TSTART;
		}
		portEXIT_CRITICAL();
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

unsigned long ulEMACPoll( void )
{
static unsigned portBASE_TYPE ulNextRxBuffer = 0;
unsigned long ulSectionLength = 0, ulLengthSoFar = 0, ulEOF = pdFALSE;
char *pcSource;

	/* Skip any fragments. */
	while( ( xRxDescriptors[ ulNextRxBuffer ].addr & AT91C_OWNERSHIP_BIT ) && !( xRxDescriptors[ ulNextRxBuffer ].U_Status.status & AT91C_SOF ) )
	{
		/* Mark the buffer as free again. */
		xRxDescriptors[ ulNextRxBuffer ].addr &= ~( AT91C_OWNERSHIP_BIT );		
		ulNextRxBuffer++;
		if( ulNextRxBuffer >= NB_RX_BUFFERS )
		{
			ulNextRxBuffer = 0;
		}
	}

	/* Is there a packet ready? */

	while( ( xRxDescriptors[ ulNextRxBuffer ].addr & AT91C_OWNERSHIP_BIT ) && !ulSectionLength )
	{
		pcSource = ( char * )( xRxDescriptors[ ulNextRxBuffer ].addr & emacADDRESS_MASK );
		ulSectionLength = xRxDescriptors[ ulNextRxBuffer ].U_Status.status & emacRX_LENGTH_FRAME;

		if( ulSectionLength == 0 )
		{
			/* The frame is longer than the buffer pointed to by this
			descriptor so copy the entire buffer to uIP - then move onto
			the next descriptor to get the rest of the frame. */
			if( ( ulLengthSoFar + ETH_RX_BUFFER_SIZE ) <= UIP_BUFSIZE )
			{
				memcpy( &( uip_buf[ ulLengthSoFar ] ), pcSource, ETH_RX_BUFFER_SIZE );
				ulLengthSoFar += ETH_RX_BUFFER_SIZE;
			}			
		}
		else
		{
			/* This is the last section of the frame.  Copy the section to
			uIP. */
			if( ulSectionLength < UIP_BUFSIZE )
			{
				/* The section length holds the length of the entire frame.
				ulLengthSoFar holds the length of the frame sections already
				copied to uIP, so the length of the final section is
				ulSectionLength - ulLengthSoFar; */
				if( ulSectionLength > ulLengthSoFar )
				{
					memcpy( &( uip_buf[ ulLengthSoFar ] ), pcSource, ( ulSectionLength - ulLengthSoFar ) );
				}
			}			

			/* Is this the last buffer for the frame?  If not why? */
			ulEOF = xRxDescriptors[ ulNextRxBuffer ].U_Status.status & AT91C_EOF;
		}

		/* Mark the buffer as free again. */
		xRxDescriptors[ ulNextRxBuffer ].addr &= ~( AT91C_OWNERSHIP_BIT );

		/* Increment to the next buffer, wrapping if necessary. */
		ulNextRxBuffer++;
		if( ulNextRxBuffer >= NB_RX_BUFFERS )
		{
			ulNextRxBuffer = 0;
		}
	}

	/* If we obtained data but for some reason did not find the end of the
	frame then discard the data as it must contain an error. */
	if( !ulEOF )
	{
		ulSectionLength = 0;
	}

	return ulSectionLength;
}
/*-----------------------------------------------------------*/

static void prvSetupDescriptors(void)
{
unsigned portBASE_TYPE xIndex;
unsigned long ulAddress;

	/* Initialise xRxDescriptors descriptor. */
	for( xIndex = 0; xIndex < NB_RX_BUFFERS; ++xIndex )
	{
		/* Calculate the address of the nth buffer within the array. */
		ulAddress = ( unsigned long )( pcRxBuffer + ( xIndex * ETH_RX_BUFFER_SIZE ) );

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
		ulAddress = ( unsigned long )( pcTxBuffer + ( xIndex * ETH_TX_BUFFER_SIZE ) );

		/* Write the buffer address into the descriptor.  The DMA will read
		data from here when the descriptor is being used. */
		xTxDescriptors[ xIndex ].addr = ulAddress & emacADDRESS_MASK;
		xTxDescriptors[ xIndex ].U_Status.status = AT91C_TRANSMIT_OK;
	}	

	/* The last buffer has the wrap bit set so the EMAC knows to wrap back
	to the first buffer. */
	xTxDescriptors[ NB_TX_BUFFERS - 1 ].U_Status.status = AT91C_TRANSMIT_WRAP | AT91C_TRANSMIT_OK;

	/* Tell the EMAC where to find the descriptors. */
	AT91C_BASE_EMAC->EMAC_RBQP = ( unsigned long ) xRxDescriptors;
	AT91C_BASE_EMAC->EMAC_TBQP = ( unsigned long ) xTxDescriptors;
	
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
	AT91C_BASE_EMAC->EMAC_SA1L =	( ( unsigned long ) cMACAddress[ 3 ] << 24 ) |
									( ( unsigned long ) cMACAddress[ 2 ] << 16 ) |
									( ( unsigned long ) cMACAddress[ 1 ] << 8  ) |
									cMACAddress[ 0 ];

	AT91C_BASE_EMAC->EMAC_SA1H =	( ( unsigned long ) cMACAddress[ 5 ] << 8 ) |
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
			/* We want to interrupt on Rx events. */
			AT91C_BASE_EMAC->EMAC_IER = AT91C_EMAC_RCOMP;

			/* Enable the interrupts in the AIC. */
			AT91F_AIC_ConfigureIt( AT91C_BASE_AIC, AT91C_ID_EMAC, emacINTERRUPT_LEVEL, AT91C_AIC_SRCTYPE_INT_HIGH_LEVEL, ( void (*)( void ) ) vEMACISREntry );
			AT91F_AIC_EnableIt( AT91C_BASE_AIC, AT91C_ID_EMAC );
		}
		portEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

__arm void vEMACISR( void )
{
volatile unsigned long ulIntStatus, ulRxStatus;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	ulIntStatus = AT91C_BASE_EMAC->EMAC_ISR;
	ulRxStatus = AT91C_BASE_EMAC->EMAC_RSR;

	if( ( ulIntStatus & AT91C_EMAC_RCOMP ) || ( ulRxStatus & AT91C_EMAC_REC ) )
	{
		/* A frame has been received, signal the uIP task so it can process
		the Rx descriptors. */
		xSemaphoreGiveFromISR( xSemaphore, &xHigherPriorityTaskWoken );
		AT91C_BASE_EMAC->EMAC_RSR = AT91C_EMAC_REC;
	}

	/* If a task was woken by either a character being received or a character
	being transmitted then we may need to switch to another task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );

	/* Clear the interrupt. */
	AT91C_BASE_AIC->AIC_EOICR = 0;
}
/*-----------------------------------------------------------*/



/*
 * The following functions are initialisation functions taken from the Atmel
 * EMAC sample code.
 */

static portBASE_TYPE prvProbePHY( void )
{
unsigned long ulPHYId1, ulPHYId2, ulStatus;
portBASE_TYPE xReturn = pdPASS;
	
	/* Code supplied by Atmel (reformatted) -----------------*/

	/* Enable management port */
	AT91C_BASE_EMAC->EMAC_NCR |= AT91C_EMAC_MPE;	
	AT91C_BASE_EMAC->EMAC_NCFGR |= ( 2 ) << 10;

	/* Read the PHY ID. */
	vReadPHY( AT91C_PHY_ADDR, MII_PHYSID1, &ulPHYId1 );
	vReadPHY( AT91C_PHY_ADDR, MII_PHYSID2, &ulPHYId2 );

	/* AMD AM79C875:
			PHY_ID1 = 0x0022
			PHY_ID2 = 0x5541
			Bits 3:0 Revision Number Four bit manufacturer’s revision number.
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

static void vReadPHY( unsigned char ucPHYAddress, unsigned char ucAddress, unsigned long *pulValue )
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
static void vWritePHY( unsigned char ucPHYAddress, unsigned char ucAddress, unsigned long ulValue )
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
	unsigned long ulBMSR, ulBMCR, ulLPA, ulMACCfg, ulSpeed, ulDuplex;

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
			/* Auto-negotiation in progress. */
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
		{
			/* 10 Half Duplex */
			AT91C_BASE_EMAC->EMAC_NCFGR = ulMACCfg;
		}
	}

	/* End of code supplied by Atmel ------------------------*/

	return pdPASS;
}
