/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
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

/* Hardware specific includes. */
#include "iodefine.h"
#include "typedefine.h"
#include "r_ether.h"
#include "phy.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* uIP includes. */
#include "net/uip.h"

/* The time to wait between attempts to obtain a free buffer. */
#define emacBUFFER_WAIT_DELAY_ms		( 3 / portTICK_PERIOD_MS )

/* The number of times emacBUFFER_WAIT_DELAY_ms should be waited before giving
up on attempting to obtain a free buffer all together. */
#define emacBUFFER_WAIT_ATTEMPTS	( 30 )

/* The number of Rx descriptors. */
#define emacNUM_RX_DESCRIPTORS	8

/* The number of Tx descriptors.  When using uIP there is not point in having
more than two. */
#define emacNUM_TX_BUFFERS	2

/* The total number of EMAC buffers to allocate. */
#define emacNUM_BUFFERS		( emacNUM_RX_DESCRIPTORS + emacNUM_TX_BUFFERS )

/* The time to wait for the Tx descriptor to become free. */
#define emacTX_WAIT_DELAY_ms ( 10 / portTICK_PERIOD_MS )

/* The total number of times to wait emacTX_WAIT_DELAY_ms for the Tx descriptor to
become free. */
#define emacTX_WAIT_ATTEMPTS ( 50 )

/* Only Rx end and Tx end interrupts are used by this driver. */
#define emacTX_END_INTERRUPT	( 1UL << 21UL )
#define emacRX_END_INTERRUPT	( 1UL << 18UL )

/*-----------------------------------------------------------*/

/* The buffers and descriptors themselves.  */
#pragma section _RX_DESC
	volatile ethfifo xRxDescriptors[ emacNUM_RX_DESCRIPTORS ];
#pragma section _TX_DESC
	volatile ethfifo xTxDescriptors[ emacNUM_TX_BUFFERS ];
#pragma section _ETHERNET_BUFFERS
	struct
	{
		unsigned long ulAlignmentVariable;
		char cBuffer[ emacNUM_BUFFERS ][ UIP_BUFSIZE ];
	} xEthernetBuffers;
#pragma section




/* Used to indicate which buffers are free and which are in use.  If an index
contains 0 then the corresponding buffer in xEthernetBuffers is free, otherwise 
the buffer is in use or about to be used. */
static unsigned char ucBufferInUse[ emacNUM_BUFFERS ];

/*-----------------------------------------------------------*/

/*
 * Initialise both the Rx and Tx descriptors.
 */
static void prvInitialiseDescriptors( void );

/*
 * Return a pointer to a free buffer within xEthernetBuffers.
 */
static unsigned char *prvGetNextBuffer( void );

/*
 * Return a buffer to the list of free buffers.
 */
static void prvReturnBuffer( unsigned char *pucBuffer );

/*
 * Examine the status of the next Rx FIFO to see if it contains new data.
 */
static unsigned long prvCheckRxFifoStatus( void );

/*
 * Setup the microcontroller for communication with the PHY.
 */
static void prvResetMAC( void );

/*
 * Configure the Ethernet interface peripherals.
 */
static void prvConfigureEtherCAndEDMAC( void );

/*
 * Something has gone wrong with the descriptor usage.  Reset all the buffers
 * and descriptors.
 */
static void prvResetEverything( void );

/*-----------------------------------------------------------*/

/* Points to the Rx descriptor currently in use. */
static ethfifo *pxCurrentRxDesc = NULL;

/* The buffer used by the uIP stack to both receive and send.  This points to
one of the Ethernet buffers when its actually in use. */
unsigned char *uip_buf = NULL;

/*-----------------------------------------------------------*/

void vInitEmac( void )
{
	/* Software reset. */
	prvResetMAC();
	
	/* Set the Rx and Tx descriptors into their initial state. */
	prvInitialiseDescriptors();

	/* Set the MAC address into the ETHERC */
	ETHERC.MAHR = 	( ( unsigned long ) configMAC_ADDR0 << 24UL ) | 
					( ( unsigned long ) configMAC_ADDR1 << 16UL ) | 
					( ( unsigned long ) configMAC_ADDR2 << 8UL ) | 
					( unsigned long ) configMAC_ADDR3;
					
	ETHERC.MALR.BIT.MA = ( ( unsigned long ) configMAC_ADDR4 << 8UL ) |
						 ( unsigned long ) configMAC_ADDR5;

	/* Perform rest of interface hardware configuration. */
	prvConfigureEtherCAndEDMAC();
	
	/* Nothing received yet, so uip_buf points nowhere. */
	uip_buf = NULL;

	/* Initialize the PHY */
	phy_init();
}
/*-----------------------------------------------------------*/

void vEMACWrite( void )
{
long x;

	/* Wait until the second transmission of the last packet has completed. */
	for( x = 0; x < emacTX_WAIT_ATTEMPTS; x++ )
	{
		if( ( xTxDescriptors[ 1 ].status & ACT ) != 0 )
		{
			/* Descriptor is still active. */
			vTaskDelay( emacTX_WAIT_DELAY_ms );
		}
		else
		{
			break;
		}
	}
	
	/* Is the descriptor free after waiting for it? */
	if( ( xTxDescriptors[ 1 ].status & ACT ) != 0 )
	{
		/* Something has gone wrong. */
		prvResetEverything();
	}
	
	/* Setup both descriptors to transmit the frame. */
	xTxDescriptors[ 0 ].buf_p = ( char * ) uip_buf;
	xTxDescriptors[ 0 ].bufsize = uip_len;	
	xTxDescriptors[ 1 ].buf_p = ( char * ) uip_buf;
	xTxDescriptors[ 1 ].bufsize = uip_len;

	/* uip_buf is being sent by the Tx descriptor.  Allocate a new buffer
	for use by the stack. */
	uip_buf = prvGetNextBuffer();

	/* Clear previous settings and go. */
	xTxDescriptors[0].status &= ~( FP1 | FP0 );
	xTxDescriptors[0].status |= ( FP1 | FP0 | ACT );
	xTxDescriptors[1].status &= ~( FP1 | FP0 );
	xTxDescriptors[1].status |= ( FP1 | FP0 | ACT );

	EDMAC.EDTRR.LONG = 0x00000001;
}
/*-----------------------------------------------------------*/

unsigned long ulEMACRead( void )
{
unsigned long ulBytesReceived;

	ulBytesReceived = prvCheckRxFifoStatus();

	if( ulBytesReceived > 0 )
	{
		/* Mark the pxDescriptor buffer as free as uip_buf is going to be set to
		the buffer that contains the received data. */
		prvReturnBuffer( uip_buf );

		/* Point uip_buf to the data about ot be processed. */
		uip_buf = ( void * ) pxCurrentRxDesc->buf_p;
		
		/* Allocate a new buffer to the descriptor, as uip_buf is now using it's
		old descriptor. */
		pxCurrentRxDesc->buf_p = prvGetNextBuffer();

		/* Prepare the descriptor to go again. */
		pxCurrentRxDesc->status &= ~( FP1 | FP0 );
		pxCurrentRxDesc->status |= ACT;

		/* Move onto the next buffer in the ring. */
		pxCurrentRxDesc = pxCurrentRxDesc->next;
		
		if( EDMAC.EDRRR.LONG == 0x00000000L )
		{
			/* Restart Ethernet if it has stopped */
			EDMAC.EDRRR.LONG = 0x00000001L;
		}
	}

	return ulBytesReceived;
}
/*-----------------------------------------------------------*/

long lEMACWaitForLink( void )
{
long lReturn;

	/* Set the link status. */
	switch( phy_set_autonegotiate() )
	{
		/* Half duplex link */
		case PHY_LINK_100H:
								ETHERC.ECMR.BIT.DM = 0;
								ETHERC.ECMR.BIT.RTM = 1;
								lReturn = pdPASS;
								break;

		case PHY_LINK_10H:
								ETHERC.ECMR.BIT.DM = 0;
								ETHERC.ECMR.BIT.RTM = 0;
								lReturn = pdPASS;
								break;


		/* Full duplex link */
		case PHY_LINK_100F:
								ETHERC.ECMR.BIT.DM = 1;
								ETHERC.ECMR.BIT.RTM = 1;
								lReturn = pdPASS;
								break;
		
		case PHY_LINK_10F:
								ETHERC.ECMR.BIT.DM = 1;
								ETHERC.ECMR.BIT.RTM = 0;
								lReturn = pdPASS;
								break;

		default:
								lReturn = pdFAIL;
								break;
	}

	if( lReturn == pdPASS )
	{
		/* Enable receive and transmit. */
		ETHERC.ECMR.BIT.RE = 1;
		ETHERC.ECMR.BIT.TE = 1;

		/* Enable EDMAC receive */
		EDMAC.EDRRR.LONG = 0x1;
	}
	
	return lReturn;
}
/*-----------------------------------------------------------*/

static void prvInitialiseDescriptors( void )
{
ethfifo *pxDescriptor;
long x;

	for( x = 0; x < emacNUM_BUFFERS; x++ )
	{
		/* Ensure none of the buffers are shown as in use at the start. */
		ucBufferInUse[ x ] = pdFALSE;
	}

	/* Initialise the Rx descriptors. */
	for( x = 0; x < emacNUM_RX_DESCRIPTORS; x++ )
	{
		pxDescriptor = &( xRxDescriptors[ x ] );
		pxDescriptor->buf_p = &( xEthernetBuffers.cBuffer[ x ][ 0 ] );

		pxDescriptor->bufsize = UIP_BUFSIZE;
		pxDescriptor->size = 0;
		pxDescriptor->status = ACT;
		pxDescriptor->next = &xRxDescriptors[ x + 1 ];	
		
		/* Mark this buffer as in use. */
		ucBufferInUse[ x ] = pdTRUE;
	}

	/* The last descriptor points back to the start. */
	pxDescriptor->status |= DL;
	pxDescriptor->next = &xRxDescriptors[ 0 ];
	
	/* Initialise the Tx descriptors. */
	for( x = 0; x < emacNUM_TX_BUFFERS; x++ )
	{
		pxDescriptor = &( xTxDescriptors[ x ] );
		
		/* A buffer is not allocated to the Tx descriptor until a send is
		actually required. */
		pxDescriptor->buf_p = NULL;

		pxDescriptor->bufsize = UIP_BUFSIZE;
		pxDescriptor->size = 0;
		pxDescriptor->status = 0;
		pxDescriptor->next = &xTxDescriptors[ x + 1 ];	
	}

	/* The last descriptor points back to the start. */
	pxDescriptor->status |= DL;
	pxDescriptor->next = &( xTxDescriptors[ 0 ] );
	
	/* Use the first Rx descriptor to start with. */
	pxCurrentRxDesc = &( xRxDescriptors[ 0 ] );
}
/*-----------------------------------------------------------*/

static unsigned char *prvGetNextBuffer( void )
{
long x;
unsigned char *pucReturn = NULL;
unsigned long ulAttempts = 0;

	while( pucReturn == NULL )
	{
		/* Look through the buffers to find one that is not in use by
		anything else. */
		for( x = 0; x < emacNUM_BUFFERS; x++ )
		{
			if( ucBufferInUse[ x ] == pdFALSE )
			{
				ucBufferInUse[ x ] = pdTRUE;
				pucReturn = ( unsigned char * ) &( xEthernetBuffers.cBuffer[ x ][ 0 ] );
				break;
			}
		}

		/* Was a buffer found? */
		if( pucReturn == NULL )
		{
			ulAttempts++;

			if( ulAttempts >= emacBUFFER_WAIT_ATTEMPTS )
			{
				break;
			}

			/* Wait then look again. */
			vTaskDelay( emacBUFFER_WAIT_DELAY_ms );
		}
	}

	return pucReturn;
}
/*-----------------------------------------------------------*/

static void prvReturnBuffer( unsigned char *pucBuffer )
{
unsigned long ul;

	/* Return a buffer to the pool of free buffers. */
	for( ul = 0; ul < emacNUM_BUFFERS; ul++ )
	{
		if( &( xEthernetBuffers.cBuffer[ ul ][ 0 ] ) == ( void * ) pucBuffer )
		{
			ucBufferInUse[ ul ] = pdFALSE;
			break;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvResetEverything( void )
{
	/* Temporary code just to see if this gets called.  This function has not
	been implemented. */
	portDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

static unsigned long prvCheckRxFifoStatus( void )
{
unsigned long ulReturn = 0;

	if( ( pxCurrentRxDesc->status & ACT ) != 0 )
	{
		/* Current descriptor is still active. */
	}
	else if( ( pxCurrentRxDesc->status & FE ) != 0 )
	{
		/* Frame error.  Clear the error. */
		pxCurrentRxDesc->status &= ~( FP1 | FP0 | FE );
		pxCurrentRxDesc->status &= ~( RMAF | RRF | RTLF | RTSF | PRE | CERF );
		pxCurrentRxDesc->status |= ACT;
		pxCurrentRxDesc = pxCurrentRxDesc->next;

		if( EDMAC.EDRRR.LONG == 0x00000000UL )
		{
			/* Restart Ethernet if it has stopped. */
			EDMAC.EDRRR.LONG = 0x00000001UL;
		}	
	}
	else
	{
		/* The descriptor contains a frame.  Because of the size of the buffers
		the frame should always be complete. */
		if( ( pxCurrentRxDesc->status & FP0 ) == FP0 )
		{
			ulReturn = pxCurrentRxDesc->size;
		}
		else
		{
			/* Do not expect to get here. */
			prvResetEverything();
		}
	}
	
	return ulReturn;
}
/*-----------------------------------------------------------*/

static void prvResetMAC( void )
{
	/* Ensure the EtherC and EDMAC are enabled. */
	SYSTEM.MSTPCRB.BIT.MSTPB15 = 0;
	vTaskDelay( 100 / portTICK_PERIOD_MS );
	
	EDMAC.EDMR.BIT.SWR = 1;	
	
	/* Crude wait for reset to complete. */
	vTaskDelay( 500 / portTICK_PERIOD_MS );	
}
/*-----------------------------------------------------------*/

static void prvConfigureEtherCAndEDMAC( void )
{
	/* Initialisation code taken from Renesas example project. */
	
	/* TODO:    Check   bit 5   */
	ETHERC.ECSR.LONG = 0x00000037;				/* Clear all ETHERC statuS BFR, PSRTO, LCHNG, MPD, ICD */

	/* Set the EDMAC interrupt priority. */
	_IPR( _ETHER_EINT ) = configKERNEL_INTERRUPT_PRIORITY;

	/* Enable interrupts of interest only. */
	EDMAC.EESIPR.LONG = emacTX_END_INTERRUPT | emacRX_END_INTERRUPT;
	ETHERC.RFLR.LONG = 1518;					/* Ether payload is 1500+ CRC */
	ETHERC.IPGR.LONG = 0x00000014;				/* Intergap is 96-bit time */

	/* EDMAC */
	EDMAC.EESR.LONG = 0x47FF0F9F;				/* Clear all ETHERC and EDMAC status bits */
	#ifdef __LIT
		EDMAC.EDMR.BIT.DE = 1;
	#endif
	EDMAC.RDLAR = ( void * ) pxCurrentRxDesc;	/* Initialaize Rx Descriptor List Address */
	EDMAC.TDLAR = &( xTxDescriptors[ 0 ] );		/* Initialaize Tx Descriptor List Address */
	EDMAC.TRSCER.LONG = 0x00000000;				/* Copy-back status is RFE & TFE only   */
	EDMAC.TFTR.LONG = 0x00000000;				/* Threshold of Tx_FIFO */
	EDMAC.FDR.LONG = 0x00000000;				/* Transmit fifo & receive fifo is 256 bytes */
	EDMAC.RMCR.LONG = 0x00000003;				/* Receive function is normal mode(continued) */
	ETHERC.ECMR.BIT.PRM = 0;					/* Ensure promiscuous mode is off. */
		
	/* Enable the interrupt... */
	_IEN( _ETHER_EINT ) = 1;	
}
/*-----------------------------------------------------------*/

#pragma interrupt ( vEMAC_ISR_Handler( vect = VECT_ETHER_EINT, enable ) )
void vEMAC_ISR_Handler( void )
{
unsigned long ul = EDMAC.EESR.LONG;
long lHigherPriorityTaskWoken = pdFALSE;
extern QueueHandle_t xEMACEventQueue;
const unsigned long ulRxEvent = uipETHERNET_RX_EVENT;

	/* Has a Tx end occurred? */
	if( ul & emacTX_END_INTERRUPT )
	{
		/* Only return the buffer to the pool once both Txes have completed. */
		prvReturnBuffer( ( void * ) xTxDescriptors[ 0 ].buf_p );
		EDMAC.EESR.LONG = emacTX_END_INTERRUPT;
	}

	/* Has an Rx end occurred? */
	if( ul & emacRX_END_INTERRUPT )
	{
		/* Make sure the Ethernet task is not blocked waiting for a packet. */
		xQueueSendFromISR( xEMACEventQueue, &ulRxEvent, &lHigherPriorityTaskWoken );
		portYIELD_FROM_ISR( lHigherPriorityTaskWoken );
		EDMAC.EESR.LONG = emacRX_END_INTERRUPT;
	}
}

