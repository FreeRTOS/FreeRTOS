/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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

/* Freescale includes. */
#include "common.h"
#include "eth_phy.h"
#include "enet.h"
#include "mii.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* uIP includes. */
#include "net/uip.h"

/* The time to wait between attempts to obtain a free buffer. */
#define emacBUFFER_WAIT_DELAY_ms		( 3 / portTICK_PERIOD_MS )

/* The number of times emacBUFFER_WAIT_DELAY_ms should be waited before giving
up on attempting to obtain a free buffer all together. */
#define emacBUFFER_WAIT_ATTEMPTS		( 30 )

/* The number of Rx descriptors. */
#define emacNUM_RX_DESCRIPTORS			8

/* The number of Tx descriptors.  When using uIP there is not point in having
more than two. */
#define emacNUM_TX_BUFFERS				2

/* The total number of EMAC buffers to allocate. */
#define emacNUM_BUFFERS					( emacNUM_RX_DESCRIPTORS + emacNUM_TX_BUFFERS )

/* The time to wait for the Tx descriptor to become free. */
#define emacTX_WAIT_DELAY_ms 			( 10 / portTICK_PERIOD_MS )

/* The total number of times to wait emacTX_WAIT_DELAY_ms for the Tx descriptor to
become free. */
#define emacTX_WAIT_ATTEMPTS 			( 50 )

/* Constants used for set up and initialisation. */
#define emacTX_INTERRUPT_NO			( 76 )
#define emacRX_INTERRUPT_NO			( 77 )
#define emacERROR_INTERRUPT_NO		( 78 )
#define emacLINK_DELAY				( 500 / portTICK_PERIOD_MS )
#define emacPHY_STATUS				( 0x1F )
#define emacPHY_DUPLEX_STATUS		( 4 << 2 )
#define emacPHY_SPEED_STATUS		( 1 << 2 )

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
 * Examine the status of the next Rx descriptor to see if it contains new data.
 */
static unsigned short prvCheckRxStatus( void );

/*
 * Something has gone wrong with the descriptor usage.  Reset all the buffers
 * and descriptors.
 */
static void prvResetEverything( void );

/*-----------------------------------------------------------*/

/* The buffers and descriptors themselves.  */
#pragma data_alignment=16
volatile NBUF xRxDescriptors[ emacNUM_RX_DESCRIPTORS ];

#pragma data_alignment=16
volatile NBUF xTxDescriptors[ emacNUM_TX_BUFFERS ];

#pragma data_alignment=16
char xEthernetBuffers[ emacNUM_BUFFERS ][ UIP_BUFSIZE ];

/* Used to indicate which buffers are free and which are in use.  If an index
contains 0 then the corresponding buffer in xEthernetBuffers is free, otherwise
the buffer is in use or about to be used. */
static unsigned char ucBufferInUse[ emacNUM_BUFFERS ];

/* Points to the Rx descriptor currently in use. */
static volatile NBUF *pxCurrentRxDesc = NULL;

/* pxCurrentRxDesc points to descriptor within the xRxDescriptors array that
has an index defined by ulRxDescriptorIndex. */
static unsigned long ulRxDescriptorIndex = 0UL;

/* The buffer used by the uIP stack to both receive and send.  This points to
one of the Ethernet buffers when its actually in use. */
unsigned char *uip_buf = NULL;

/*-----------------------------------------------------------*/

void vEMACInit( void )
{
int iData;
extern int periph_clk_khz;
const unsigned char ucMACAddress[] =
{
	configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5
};

	/* Enable the ENET clock. */
	SIM_SCGC2 |= SIM_SCGC2_ENET_MASK;

	/* Allow concurrent access to MPU controller to avoid bus errors. */
	MPU_CESR = 0;

	prvInitialiseDescriptors();

	/* Reset and enable. */
	ENET_ECR = ENET_ECR_RESET_MASK;
	
	/* Wait at least 8 clock cycles */
	vTaskDelay( 2 );
	
	/* Start the MII interface*/
	mii_init( 0, periph_clk_khz / 1000L );

	/* Configure the transmit interrupt. */
	set_irq_priority( emacTX_INTERRUPT_NO, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
	enable_irq( emacTX_INTERRUPT_NO );

	/* Configure the receive interrupt. */
	set_irq_priority( emacRX_INTERRUPT_NO, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
	enable_irq( emacRX_INTERRUPT_NO );

	/* Configure the error interrupt. */
	set_irq_priority( emacERROR_INTERRUPT_NO, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
	enable_irq( emacERROR_INTERRUPT_NO );

	/* Configure the pins to the PHY - RMII mode used. */
	PORTB_PCR0  = PORT_PCR_MUX( 4 ); /* RMII0_MDIO / MII0_MDIO. */
	PORTB_PCR1  = PORT_PCR_MUX( 4 ); /* RMII0_MDC / MII0_MDC */
	PORTA_PCR14 = PORT_PCR_MUX( 4 ); /* RMII0_CRS_DV / MII0_RXDV */
	PORTA_PCR12 = PORT_PCR_MUX( 4 ); /* RMII0_RXD1 / MII0_RXD1 */
	PORTA_PCR13 = PORT_PCR_MUX( 4 ); /* RMII0_RXD0/MII0_RXD0 */
	PORTA_PCR15 = PORT_PCR_MUX( 4 ); /* RMII0_TXEN/MII0_TXEN */
	PORTA_PCR16 = PORT_PCR_MUX( 4 ); /* RMII0_TXD0/MII0_TXD0 */
	PORTA_PCR17 = PORT_PCR_MUX( 4 ); /* RMII0_TXD1/MII0_TXD1 */

	/* Is there communication with the PHY? */
	do
	{
		vTaskDelay( emacLINK_DELAY );
		iData = 0xFFFF;
		mii_read( 0, configPHY_ADDRESS, PHY_PHYIDR1, &iData );
	
	} while( iData == 0xFFFF );

	/* Start to auto negotiate. */
	mii_write( 0, configPHY_ADDRESS, PHY_BMCR, ( PHY_BMCR_AN_RESTART | PHY_BMCR_AN_ENABLE ) );
	
	/* Wait for auto negotiate to complete. */
	do
	{
		vTaskDelay( emacLINK_DELAY );
		mii_read( 0, configPHY_ADDRESS, PHY_BMSR, &iData );
	
	} while( !( iData & PHY_BMSR_AN_COMPLETE ) );

	/* A link has been established.  What was negotiated? */
	iData = 0;
	mii_read( 0, configPHY_ADDRESS, emacPHY_STATUS, &iData );

	/* Clear the Individual and Group Address Hash registers */
	ENET_IALR = 0;
	ENET_IAUR = 0;
	ENET_GALR = 0;
	ENET_GAUR = 0;

	/* Set the Physical Address for the selected ENET */
	enet_set_address( 0, ucMACAddress );

	ENET_RCR = ENET_RCR_MAX_FL( UIP_BUFSIZE ) | ENET_RCR_MII_MODE_MASK | ENET_RCR_CRCFWD_MASK | ENET_RCR_RMII_MODE_MASK;

	/* Clear the control registers. */
	ENET_TCR = 0;

	if( iData & emacPHY_DUPLEX_STATUS )
	{
		/* Full duplex */
		ENET_RCR &= ( unsigned long )~ENET_RCR_DRT_MASK;
		ENET_TCR |= ENET_TCR_FDEN_MASK;
	}
	else
	{
		/* Half duplex */
		ENET_RCR |= ENET_RCR_DRT_MASK;
		ENET_TCR &= (unsigned long)~ENET_TCR_FDEN_MASK;
	}

	if( iData & emacPHY_SPEED_STATUS )
	{
		/* 10Mbps */
		ENET_RCR |= ENET_RCR_RMII_10T_MASK;
	}

    ENET_ECR = ENET_ECR_EN1588_MASK;

	/* Store and forward checksum. */
	ENET_TFWR = ENET_TFWR_STRFWD_MASK;

	/* Set Rx Buffer Size */
	ENET_MRBR = ( unsigned short ) UIP_BUFSIZE;
	
	/* Point to the start of the circular Rx buffer descriptor queue */
	ENET_RDSR = ( unsigned long ) &( xRxDescriptors[ 0 ] );
	
	/* Point to the start of the circular Tx buffer descriptor queue */
	ENET_TDSR = ( unsigned long ) &( xTxDescriptors[ 0 ] );
	
	/* Clear all ENET interrupt events */
	ENET_EIR = ( unsigned long ) -1;
	
	/* Enable interrupts. */
	ENET_EIMR = 0
			/*rx irqs*/
			| ENET_EIMR_RXF_MASK/* only for complete frame, not partial buffer descriptor | ENET_EIMR_RXB_MASK*/
			/*xmit irqs*/
			| ENET_EIMR_TXF_MASK/* only for complete frame, not partial buffer descriptor | ENET_EIMR_TXB_MASK*/
			/*enet irqs*/
			| ENET_EIMR_UN_MASK | ENET_EIMR_RL_MASK | ENET_EIMR_LC_MASK | ENET_EIMR_BABT_MASK | ENET_EIMR_BABR_MASK | ENET_EIMR_EBERR_MASK
			;
	
	/* Enable the MAC itself. */
	ENET_ECR |= ENET_ECR_ETHEREN_MASK;
	
	/* Indicate that there have been empty receive buffers produced */
	ENET_RDAR = ENET_RDAR_RDAR_MASK;
}
/*-----------------------------------------------------------*/

static void prvInitialiseDescriptors( void )
{
volatile NBUF *pxDescriptor;
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
		pxDescriptor->data = ( uint8_t* ) &( xEthernetBuffers[ x ][ 0 ] );
		pxDescriptor->data = ( uint8_t* ) __REV( ( unsigned long ) pxDescriptor->data );
		pxDescriptor->length = 0;
		pxDescriptor->status = RX_BD_E;
		pxDescriptor->bdu = 0;
		pxDescriptor->ebd_status = RX_BD_INT;
		
		/* Mark this buffer as in use. */
		ucBufferInUse[ x ] = pdTRUE;
	}

	/* The last descriptor points back to the start. */
	pxDescriptor->status |= RX_BD_W;
	
	/* Initialise the Tx descriptors. */
	for( x = 0; x < emacNUM_TX_BUFFERS; x++ )
	{
		pxDescriptor = &( xTxDescriptors[ x ] );
		
		/* A buffer is not allocated to the Tx descriptor until a send is
		actually required. */
		pxDescriptor->data = NULL;
		pxDescriptor->length = 0;
		pxDescriptor->status = TX_BD_TC;
		pxDescriptor->ebd_status = TX_BD_INT;
	}

	/* The last descriptor points back to the start. */
	pxDescriptor->status |= TX_BD_W;
	
	/* Use the first Rx descriptor to start with. */
	ulRxDescriptorIndex = 0UL;
	pxCurrentRxDesc = &( xRxDescriptors[ 0 ] );
}
/*-----------------------------------------------------------*/

void vEMACWrite( void )
{
long x;

	/* Wait until the second transmission of the last packet has completed. */
	for( x = 0; x < emacTX_WAIT_ATTEMPTS; x++ )
	{
		if( ( xTxDescriptors[ 1 ].status & TX_BD_R ) != 0 )
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
	if( ( xTxDescriptors[ 1 ].status & TX_BD_R ) != 0 )
	{
		/* Something has gone wrong. */
		prvResetEverything();
	}
	
	/* Setup both descriptors to transmit the frame. */
	xTxDescriptors[ 0 ].data = ( uint8_t * ) __REV( ( unsigned long ) uip_buf );
	xTxDescriptors[ 0 ].length = __REVSH( uip_len );
	xTxDescriptors[ 1 ].data = ( uint8_t * ) __REV( ( unsigned long ) uip_buf );
	xTxDescriptors[ 1 ].length = __REVSH( uip_len );

	/* uip_buf is being sent by the Tx descriptor.  Allocate a new buffer
	for use by the stack. */
	uip_buf = prvGetNextBuffer();

	/* Clear previous settings and go. */
	xTxDescriptors[ 0 ].status |= ( TX_BD_R | TX_BD_L );
	xTxDescriptors[ 1 ].status |= ( TX_BD_R | TX_BD_L );

	/* Start the Tx. */
	ENET_TDAR = ENET_TDAR_TDAR_MASK;
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
				pucReturn = ( unsigned char * ) &( xEthernetBuffers[ x ][ 0 ] );
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

static void prvResetEverything( void )
{
	/* Temporary code just to see if this gets called.  This function has not
	been implemented. */
	portDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

unsigned short usEMACRead( void )
{
unsigned short usBytesReceived;

	usBytesReceived = prvCheckRxStatus();
	usBytesReceived = __REVSH( usBytesReceived );

	if( usBytesReceived > 0 )
	{
		/* Mark the pxDescriptor buffer as free as uip_buf is going to be set to
		the buffer that contains the received data. */
		prvReturnBuffer( uip_buf );

		/* Point uip_buf to the data about to be processed. */
		uip_buf = ( void * ) pxCurrentRxDesc->data;
		uip_buf = ( void * ) __REV( ( unsigned long ) uip_buf );
		
		/* Allocate a new buffer to the descriptor, as uip_buf is now using it's
		old descriptor. */
		pxCurrentRxDesc->data = ( uint8_t * ) prvGetNextBuffer();
		pxCurrentRxDesc->data = ( uint8_t* ) __REV( ( unsigned long ) pxCurrentRxDesc->data );

		/* Prepare the descriptor to go again. */
		pxCurrentRxDesc->status |= RX_BD_E;

		/* Move onto the next buffer in the ring. */
		ulRxDescriptorIndex++;
		if( ulRxDescriptorIndex >= emacNUM_RX_DESCRIPTORS )
		{
			ulRxDescriptorIndex = 0UL;
		}
		pxCurrentRxDesc = &( xRxDescriptors[ ulRxDescriptorIndex ] );
		
		/* Restart Ethernet if it has stopped */
		ENET_RDAR = ENET_RDAR_RDAR_MASK;
	}

	return usBytesReceived;
}
/*-----------------------------------------------------------*/

static void prvReturnBuffer( unsigned char *pucBuffer )
{
unsigned long ul;

	/* Return a buffer to the pool of free buffers. */
	for( ul = 0; ul < emacNUM_BUFFERS; ul++ )
	{
		if( &( xEthernetBuffers[ ul ][ 0 ] ) == ( void * ) pucBuffer )
		{
			ucBufferInUse[ ul ] = pdFALSE;
			break;
		}
	}
}
/*-----------------------------------------------------------*/

static unsigned short prvCheckRxStatus( void )
{
unsigned long usReturn = 0;

	if( ( pxCurrentRxDesc->status & RX_BD_E ) != 0 )
	{
		/* Current descriptor is still active. */
	}
	else
	{
		/* The descriptor contains a frame.  Because of the size of the buffers
		the frame should always be complete. */
		usReturn = pxCurrentRxDesc->length;
	}
	
	return usReturn;
}
/*-----------------------------------------------------------*/

void vEMAC_TxISRHandler( void )
{
	/* Clear the interrupt. */
	ENET_EIR = ENET_EIR_TXF_MASK;

	/* Check the buffers have not already been freed in the first of the
	two Tx interrupts - which could potentially happen if the second Tx completed
	during the interrupt for the first Tx. */
	if( xTxDescriptors[ 0 ].data != NULL )
	{
		if( ( ( xTxDescriptors[ 0 ].status & TX_BD_R ) == 0 ) && ( ( xTxDescriptors[ 0 ].status & TX_BD_R ) == 0 ) )
		{
			configASSERT( xTxDescriptors[ 0 ].data == xTxDescriptors[ 1 ].data );
			
			xTxDescriptors[ 0 ].data = ( uint8_t* ) __REV( ( unsigned long ) xTxDescriptors[ 0 ].data );
			prvReturnBuffer( xTxDescriptors[ 0 ].data );
			
			/* Just to mark the fact that the buffer has already been released. */
			xTxDescriptors[ 0 ].data = NULL;
		}
	}
}
/*-----------------------------------------------------------*/

void vEMAC_RxISRHandler( void )
{
const unsigned long ulRxEvent = uipETHERNET_RX_EVENT;
long lHigherPriorityTaskWoken = pdFALSE;
extern QueueHandle_t xEMACEventQueue;

	/* Clear the interrupt. */
	ENET_EIR = ENET_EIR_RXF_MASK;

	/* An Ethernet Rx event has occurred. */
	xQueueSendFromISR( xEMACEventQueue, &ulRxEvent, &lHigherPriorityTaskWoken );
	portEND_SWITCHING_ISR( lHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void vEMAC_ErrorISRHandler( void )
{
	/* Clear the interrupt. */
	ENET_EIR = ENET_EIR & ENET_EIMR;

	/* Attempt recovery.  Not very sophisticated. */
	prvInitialiseDescriptors();
	ENET_RDAR = ENET_RDAR_RDAR_MASK;
}
/*-----------------------------------------------------------*/


