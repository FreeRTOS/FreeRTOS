/*
 * FreeRTOS+UDP V1.0.4
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
 
/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"

/* Library includes. */
#include "board.h"

/* Descriptors that reference received buffers are expected to have both the
first and last frame bits set because buffers are dimensioned to hold complete
Ethernet frames. */
#define emacEXPECTED_RX_STATUS_MASK	( RDES_LS | RDES_FS )

/*-----------------------------------------------------------*/

/*
 * Set the Rx and Tx descriptors into their expected initial state.
 */
static void prvResetRxDescriptors( void );
static void prvResetTxDescriptors( void );

/*
 * Returns the length of the data pointed to by the next Rx descriptor.
 */
static uint32_t prvReceivedDataLength( void );


/*-----------------------------------------------------------*/

/* Rx and Tx descriptors and data array. */
static volatile IP_ENET_001_ENHRXDESC_T xRXDescriptors[ configNUM_RX_ETHERNET_DMA_DESCRIPTORS ];
static volatile IP_ENET_001_ENHTXDESC_T xTxDescriptors[ configNUM_TX_ETHERNET_DMA_DESCRIPTORS ];

/* Indexes into the Rx and Tx descriptor arrays. */
static unsigned int xRxDescriptorIndex = 0;
static unsigned int xTxDescriptorIndex = 0;

/*-----------------------------------------------------------*/

BaseType_t xEMACInit( uint8_t ucMACAddress[ 6 ] )
{
BaseType_t xReturn;
uint32_t ulPHYStatus;

	/* Configure the hardware. */
	Chip_ENET_Init( LPC_ETHERNET );

	if( lpc_phy_init( pdTRUE, vTaskDelay ) == SUCCESS )
	{
		/* The MAC address is passed in as the function parameter. */
		Chip_ENET_SetADDR( LPC_ETHERNET, ucMACAddress );

		/* Wait for autonegotiation to complete. */
		do
		{
			vTaskDelay( 100 );
			ulPHYStatus = lpcPHYStsPoll();
		} while( ( ulPHYStatus & PHY_LINK_CONNECTED ) == 0x00 );

		/* Configure the hardware as per the negotiated link. */
		if( ( ulPHYStatus & PHY_LINK_FULLDUPLX ) == PHY_LINK_FULLDUPLX )
		{
			IP_ENET_SetDuplex( LPC_ETHERNET, pdTRUE );
		}
		else
		{
			IP_ENET_SetDuplex( LPC_ETHERNET, pdFALSE );
		}

		if( ( ulPHYStatus & PHY_LINK_SPEED100 ) == PHY_LINK_SPEED100 )
		{
			IP_ENET_SetSpeed( LPC_ETHERNET, pdTRUE );
		}
		else
		{
			IP_ENET_SetSpeed( LPC_ETHERNET, pdFALSE );
		}

		/* Set descriptors to their initial state. */
		prvResetRxDescriptors();
		prvResetTxDescriptors();

		/* Enable RX and TX. */
		Chip_ENET_TXEnable( LPC_ETHERNET );
		Chip_ENET_RXEnable( LPC_ETHERNET );

		/* Enable the interrupt and set its priority as configured.  THIS
		DRIVER REQUIRES configMAC_INTERRUPT_PRIORITY TO BE DEFINED, PREFERABLY
		IN FreeRTOSConfig.h. */
		NVIC_SetPriority( ETHERNET_IRQn, configMAC_INTERRUPT_PRIORITY );
		NVIC_EnableIRQ( ETHERNET_IRQn );

		/* Enable interrupts. */
		LPC_ETHERNET->DMA_INT_EN =  DMA_IE_NIE | DMA_IE_RIE;

		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t xEMACIsTxDescriptorAvailable( void )
{
BaseType_t xReturn;

	if( ( xTxDescriptors[ xTxDescriptorIndex ].CTRLSTAT & RDES_OWN ) == 0 )
	{
		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void vEMACAssignBufferToDescriptor( uint8_t * pucBuffer )
{
	/* The old packet is now finished with and can be freed. */
	vEthernetBufferRelease( ( void * ) xTxDescriptors[ xTxDescriptorIndex ].B1ADD );

	/* Assign the new packet to the descriptor. */
	xTxDescriptors[ xTxDescriptorIndex ].B1ADD = ( uint32_t ) pucBuffer;
}
/*-----------------------------------------------------------*/

void vEMACStartNextTransmission( uint32_t ulLength )
{
	xTxDescriptors[ xTxDescriptorIndex ].BSIZE = ulLength;
	xTxDescriptors[ xTxDescriptorIndex ].CTRLSTAT |= RDES_OWN;

	/* Wake Up the DMA if it's in Suspended Mode. */
	LPC_ETHERNET->DMA_TRANS_POLL_DEMAND = 1;
	xTxDescriptorIndex++;

	if( xTxDescriptorIndex == configNUM_TX_ETHERNET_DMA_DESCRIPTORS )
	{
		xTxDescriptorIndex = 0;
	}
}
/*-----------------------------------------------------------*/

static uint32_t prvReceivedDataLength( void )
{
unsigned short RxLen = 0;

	RxLen = ( xRXDescriptors[ xRxDescriptorIndex ].STATUS >> 16 ) & 0x03FFF;
	return RxLen;
}
/*-----------------------------------------------------------*/

void vEMACReturnRxDescriptor( void )
{
	xRXDescriptors[ xRxDescriptorIndex ].STATUS = RDES_OWN;
	xRxDescriptorIndex++;

	if( xRxDescriptorIndex == configNUM_RX_ETHERNET_DMA_DESCRIPTORS )
	{
		xRxDescriptorIndex = 0;
	}
}
/*-----------------------------------------------------------*/

BaseType_t xEMACRxDataAvailable( void )
{
BaseType_t xReturn;

	if( ( xRXDescriptors[ xRxDescriptorIndex ].STATUS & RDES_OWN ) == 0 )
	{
		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void vEMACSwapEmptyBufferForRxedData( xNetworkBufferDescriptor_t *pxNetworkBuffer )
{
uint8_t *pucTemp;

	/* Swap the buffer in the network buffer with the buffer used by the DMA.
	This allows the data to be passed out without having to perform any copies. */
	pucTemp = ( uint8_t * ) xRXDescriptors[ xRxDescriptorIndex ].B1ADD;
	xRXDescriptors[ xRxDescriptorIndex ].B1ADD = ( uint32_t ) pxNetworkBuffer->pucEthernetBuffer;
	pxNetworkBuffer->pucEthernetBuffer = pucTemp;

	/* Only supports frames coming in single buffers.  If this frame is split
	across multiple buffers then reject it (and if the frame is needed increase
	the ipconfigNETWORK_MTU setting). */
	if( ( xRXDescriptors[ xRxDescriptorIndex ].STATUS & emacEXPECTED_RX_STATUS_MASK ) != emacEXPECTED_RX_STATUS_MASK )
	{
		pxNetworkBuffer->xDataLength = 0;
	}
	else
	{
		pxNetworkBuffer->xDataLength = ( size_t ) prvReceivedDataLength() - ( ipETHERNET_CRC_BYTES - 1U );;
	}
}
/*-----------------------------------------------------------*/

static void prvResetRxDescriptors( void )
{
uint32_t x;
size_t xBufferSize = ipTOTAL_ETHERNET_FRAME_SIZE;

	for( x = 0; x < configNUM_RX_ETHERNET_DMA_DESCRIPTORS; x++ )
	{
		/* Obtain the buffer first, as the size of the buffer might be changed
		within the pucEthernetBufferGet() call. */
		xRXDescriptors[ x ].B1ADD  = ( uint32_t ) pucEthernetBufferGet( &xBufferSize );
		xRXDescriptors[ x ].STATUS = RDES_OWN;
		xRXDescriptors[ x ].CTRL  = xBufferSize;
		xRXDescriptors[ x ].B2ADD = ( uint32_t ) &xRXDescriptors[ x + 1 ];
		
		configASSERT( ( ( ( uint32_t ) xRXDescriptors[x].B1ADD ) & 0x07 ) == 0 );
	}

	/* Last Descriptor */
	xRXDescriptors[ configNUM_RX_ETHERNET_DMA_DESCRIPTORS - 1 ].CTRL |= RDES_ENH_RER;

	xRxDescriptorIndex = 0;

	/* Set Starting address of RX Descriptor list */
	LPC_ETHERNET->DMA_REC_DES_ADDR = ( uint32_t ) xRXDescriptors;
}
/*-----------------------------------------------------------*/

static void prvResetTxDescriptors( void )
{
/* Initialize Transmit Descriptor and Status array. */
uint32_t x;

	for( x = 0; x < configNUM_TX_ETHERNET_DMA_DESCRIPTORS; x++ )
	{
		xTxDescriptors[ x ].CTRLSTAT = TDES_ENH_FS | TDES_ENH_LS;
		xTxDescriptors[ x ].BSIZE  = 0;
		xTxDescriptors[ x ].B2ADD = ( uint32_t ) &xTxDescriptors[ x + 1 ];

		/* Packet is assigned when a Tx is initiated. */
		xTxDescriptors[ x ].B1ADD   = ( uint32_t )NULL;
	}

	/* Last Descriptor? */
	xTxDescriptors[ configNUM_TX_ETHERNET_DMA_DESCRIPTORS-1 ].CTRLSTAT |= TDES_ENH_TER;

	/* Set Starting address of TX Descriptor list */
	LPC_ETHERNET->DMA_TRANS_DES_ADDR = ( uint32_t ) xTxDescriptors;
}
/*-----------------------------------------------------------*/

void ETH_IRQHandler( void )
{
uint32_t ulInterruptCause;
extern xSemaphoreHandle xEMACRxEventSemaphore;

	configASSERT( xEMACRxEventSemaphore );

	ulInterruptCause = LPC_ETHERNET->DMA_STAT ;

	/* Clear the interrupt. */
	LPC_ETHERNET->DMA_STAT |= ( DMA_ST_NIS | DMA_ST_RI );

	/* Clear fatal error conditions.  NOTE:  The driver does not clear all
	errors, only those actually experienced.  For future reference, range
	errors are not actually errors so can be ignored. */
	if( ( ulInterruptCause & DMA_ST_FBI ) != 0U )
	{
		LPC_ETHERNET->DMA_STAT |= DMA_ST_FBI;
	}

	/* Unblock the deferred interrupt handler task if the event was an Rx. */
	if( ( ulInterruptCause & DMA_IE_RIE ) != 0UL )
	{
		xSemaphoreGiveFromISR( xEMACRxEventSemaphore, NULL );
	}

	/* ulInterruptCause is used for convenience here.  A context switch is
	wanted, but coding portEND_SWITCHING_ISR( 1 ) would likely result in a
	compiler warning. */
	portEND_SWITCHING_ISR( ulInterruptCause );
}

