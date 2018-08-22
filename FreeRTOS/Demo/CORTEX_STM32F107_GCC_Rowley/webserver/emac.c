/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#include "semphr.h"
#include "task.h"
#include "emac.h"

/* Library includes. */
#include "stm32fxxx_eth.h"
#include "stm32f10x_gpio.h"
#include "stm32f10x_rcc.h"
#include "stm32f10x_nvic.h"

/*-----------------------------------------------------------*/

/* Hardware specifics. */
#define uipRCC_MAC_CLOCK			( 1UL << 14UL )
#define uipRCC_MAC_TX_CLOCK			( 1UL << 15UL )
#define uipRCC_MAC_RX_CLOCK			( 1UL << 16UL )
#define uipPHY_ADDRESS				( 1 )
#define uipENET_IRQ_NUM				( 61 )
#define uipMODE_MII					( 1UL << 23UL )
#define uipREMAP_MAC_IO				( 1UL << 21UL )

/* The number of descriptors to chain together for use by the Rx DMA. */
#define uipNUM_RX_DESCRIPTORS		4

/* The total number of buffers to be available.  At most (?) there should be
one available for each Rx descriptor, one for current use, and one that is
in the process of being transmitted. */
#define uipNUM_BUFFERS				( uipNUM_RX_DESCRIPTORS + 2 )

/* Each buffer is sized to fit an entire Ethernet packet.  This is for
simplicity and speed, but could waste RAM. */
#define uipMAX_PACKET_SIZE			1520

/* The field in the descriptor that is unused by this configuration is used to
hold the send count.  This is just #defined to a meaningful name. */
#define SendCount Buffer2NextDescAddr

/* If no buffers are available, then wait this long before looking again.... */
#define uipBUFFER_WAIT_DELAY	( 3 / portTICK_PERIOD_MS )

/* ...and don't look more than this many times. */
#define uipBUFFER_WAIT_ATTEMPTS	( 30 )

/* Let the DMA know that a new descriptor has been made available to it. */
#define prvRxDescriptorAvailable()		ETH_DMA->DMARPDR = 0

/*-----------------------------------------------------------*/

/*
 * Configure the IO for Ethernet use.
 */
static void prvSetupEthGPIO( void );

/*
 * Return a pointer to an unused buffer, marking the returned buffer as now
 * in use.
 */
static unsigned char *prvGetNextBuffer( void );

/*-----------------------------------------------------------*/

/* Allocate the Rx descriptors used by the DMA. */
static ETH_DMADESCTypeDef  xRxDescriptors[ uipNUM_RX_DESCRIPTORS ] __attribute__((aligned(4)));

/* Allocate the descriptor used for transmitting.  It might be that better
performance could be achieved by having more than one Tx descriptor, but
in this simple case only one is used. */
static volatile ETH_DMADESCTypeDef  xTxDescriptor __attribute__((aligned(4)));

/* Buffers used for receiving and transmitting data. */
static unsigned char ucMACBuffers[ uipNUM_BUFFERS ][ uipMAX_PACKET_SIZE ] __attribute__((aligned(4)));

/* Each ucBufferInUse index corresponds to a position in the same index in the
ucMACBuffers array.  If the index contains a 1 then the buffer within
ucMACBuffers is in use, if it contains a 0 then the buffer is free. */
static unsigned char ucBufferInUse[ uipNUM_BUFFERS ] = { 0 };

/* Index to the Rx descriptor to inspect next when looking for a received
packet. */
static unsigned long ulNextDescriptor;

/* The uip_buffer is not a fixed array, but instead gets pointed to the buffers
allocated within this file. */
extern unsigned char * uip_buf;

/*-----------------------------------------------------------*/

portBASE_TYPE xEthInitialise( void )
{
static ETH_InitTypeDef xEthInit; /* Static so as not to take up too much stack space. */
NVIC_InitTypeDef xNVICInit;
const unsigned char ucMACAddress[] = { configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 };
portBASE_TYPE xReturn;
unsigned long ul;

	/* Start with things in a safe known state. */
	ETH_DeInit();
	for( ul = 0; ul < uipNUM_RX_DESCRIPTORS; ul++ )
	{
		ETH_DMARxDescReceiveITConfig( &( xRxDescriptors[ ul ] ), DISABLE );
	}

	/* Route clock to the peripheral. */
    RCC->AHBENR |= ( uipRCC_MAC_CLOCK | uipRCC_MAC_TX_CLOCK | uipRCC_MAC_RX_CLOCK );

	/* Set the MAC address. */
	ETH_MACAddressConfig( ETH_MAC_Address0, ( unsigned char * ) ucMACAddress );

	/* Use MII mode. */
    AFIO->MAPR &= ~( uipMODE_MII );

	/* Configure all the GPIO as required for MAC/PHY interfacing. */
	prvSetupEthGPIO();

	/* Reset the peripheral. */
	ETH_SoftwareReset();
	while( ETH_GetSoftwareResetStatus() == SET );

	/* Initialise using the whopping big structure.  Code space could be saved
	by making this a const struct, however that would mean changes to the
	structure within the library header files could break the code, so for now
	just set everything manually at run time. */
	xEthInit.ETH_AutoNegotiation = ETH_AutoNegotiation_Enable;
	xEthInit.ETH_Watchdog = ETH_Watchdog_Disable;
	xEthInit.ETH_Jabber = ETH_Jabber_Disable;
	xEthInit.ETH_JumboFrame = ETH_JumboFrame_Disable;
	xEthInit.ETH_InterFrameGap = ETH_InterFrameGap_96Bit;
	xEthInit.ETH_CarrierSense = ETH_CarrierSense_Enable;
	xEthInit.ETH_Speed = ETH_Speed_10M;
	xEthInit.ETH_ReceiveOwn = ETH_ReceiveOwn_Disable;
	xEthInit.ETH_LoopbackMode = ETH_LoopbackMode_Disable;
	xEthInit.ETH_Mode = ETH_Mode_HalfDuplex;
	xEthInit.ETH_ChecksumOffload = ETH_ChecksumOffload_Disable;
	xEthInit.ETH_RetryTransmission = ETH_RetryTransmission_Disable;
	xEthInit.ETH_AutomaticPadCRCStrip = ETH_AutomaticPadCRCStrip_Disable;
	xEthInit.ETH_BackOffLimit = ETH_BackOffLimit_10;
	xEthInit.ETH_DeferralCheck = ETH_DeferralCheck_Disable;
	xEthInit.ETH_ReceiveAll = ETH_ReceiveAll_Enable;
	xEthInit.ETH_SourceAddrFilter = ETH_SourceAddrFilter_Disable;
	xEthInit.ETH_PassControlFrames = ETH_PassControlFrames_ForwardPassedAddrFilter;
	xEthInit.ETH_BroadcastFramesReception = ETH_BroadcastFramesReception_Disable;
	xEthInit.ETH_DestinationAddrFilter = ETH_DestinationAddrFilter_Normal;
	xEthInit.ETH_PromiscuousMode = ETH_PromiscuousMode_Disable;
	xEthInit.ETH_MulticastFramesFilter = ETH_MulticastFramesFilter_Perfect;
	xEthInit.ETH_UnicastFramesFilter = ETH_UnicastFramesFilter_Perfect;
	xEthInit.ETH_HashTableHigh = 0x0;
	xEthInit.ETH_HashTableLow = 0x0;
	xEthInit.ETH_PauseTime = 0x0;
	xEthInit.ETH_ZeroQuantaPause = ETH_ZeroQuantaPause_Disable;
	xEthInit.ETH_PauseLowThreshold = ETH_PauseLowThreshold_Minus4;
	xEthInit.ETH_UnicastPauseFrameDetect = ETH_UnicastPauseFrameDetect_Disable;
	xEthInit.ETH_ReceiveFlowControl = ETH_ReceiveFlowControl_Disable;
	xEthInit.ETH_TransmitFlowControl = ETH_TransmitFlowControl_Disable;
	xEthInit.ETH_VLANTagComparison = ETH_VLANTagComparison_16Bit;
	xEthInit.ETH_VLANTagIdentifier = 0x0;
	xEthInit.ETH_DropTCPIPChecksumErrorFrame = ETH_DropTCPIPChecksumErrorFrame_Disable;
	xEthInit.ETH_ReceiveStoreForward = ETH_ReceiveStoreForward_Enable;
	xEthInit.ETH_FlushReceivedFrame = ETH_FlushReceivedFrame_Disable;
	xEthInit.ETH_TransmitStoreForward = ETH_TransmitStoreForward_Enable;
	xEthInit.ETH_TransmitThresholdControl = ETH_TransmitThresholdControl_64Bytes;
	xEthInit.ETH_ForwardErrorFrames = ETH_ForwardErrorFrames_Disable;
	xEthInit.ETH_ForwardUndersizedGoodFrames = ETH_ForwardUndersizedGoodFrames_Disable;
	xEthInit.ETH_ReceiveThresholdControl = ETH_ReceiveThresholdControl_64Bytes;
	xEthInit.ETH_SecondFrameOperate = ETH_SecondFrameOperate_Disable;
	xEthInit.ETH_AddressAlignedBeats = ETH_AddressAlignedBeats_Enable;
	xEthInit.ETH_FixedBurst = ETH_FixedBurst_Disable;
	xEthInit.ETH_RxDMABurstLength = ETH_RxDMABurstLength_1Beat;
	xEthInit.ETH_TxDMABurstLength = ETH_TxDMABurstLength_1Beat;
	xEthInit.ETH_DescriptorSkipLength = 0x0;
	xEthInit.ETH_DMAArbitration = ETH_DMAArbitration_RoundRobin_RxTx_1_1;

	xReturn = ETH_Init( &xEthInit, uipPHY_ADDRESS );

	/* Check a link was established. */
	if( xReturn != pdFAIL )
	{
		/* Rx and Tx interrupts are used. */
		ETH_DMAITConfig( ETH_DMA_IT_NIS | ETH_DMA_IT_R | ETH_DMA_IT_T, ENABLE );

		/* Only a single Tx descriptor is used.  For now it is set to use an Rx
		buffer, but will get updated to point to where ever uip_buf is
		pointing prior to its use. */
		ETH_DMATxDescChainInit( ( void * ) &xTxDescriptor, ( void * ) ucMACBuffers, 1 );
		ETH_DMARxDescChainInit( xRxDescriptors, ( void * ) ucMACBuffers, uipNUM_RX_DESCRIPTORS );
		for( ul = 0; ul < uipNUM_RX_DESCRIPTORS; ul++ )
		{
			/* Ensure received data generates an interrupt. */
			ETH_DMARxDescReceiveITConfig( &( xRxDescriptors[ ul ] ), ENABLE );

			/* Fix up the addresses used by the descriptors.
			The way ETH_DMARxDescChainInit() is not compatible with the buffer
			declarations in this file. */
			xRxDescriptors[ ul ].Buffer1Addr = ( unsigned long ) &( ucMACBuffers[ ul ][ 0 ] );

			/* Mark the buffer used by this descriptor as in use. */
            ucBufferInUse[ ul ] = pdTRUE;
		}

		/* When receiving data, start at the first descriptor. */
		ulNextDescriptor = 0;

		/* Initialise uip_buf to ensure it points somewhere valid. */
		uip_buf = prvGetNextBuffer();

		/* SendCount must be initialised to 2 to ensure the Tx descriptor looks
		as if its available (as if it has already been sent twice. */
        xTxDescriptor.SendCount = 2;

		/* Switch on the interrupts in the NVIC. */
		xNVICInit.NVIC_IRQChannel = uipENET_IRQ_NUM;
		xNVICInit.NVIC_IRQChannelPreemptionPriority = configLIBRARY_KERNEL_INTERRUPT_PRIORITY;
		xNVICInit.NVIC_IRQChannelSubPriority = 0;
		xNVICInit.NVIC_IRQChannelCmd = ENABLE;
		NVIC_Init( &xNVICInit );

		/* Buffers and descriptors are all set up, now enable the MAC. */
		ETH_Start();

		/* Let the DMA know there are Rx descriptors available. */
		prvRxDescriptorAvailable();
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static unsigned char *prvGetNextBuffer( void )
{
portBASE_TYPE x;
unsigned char *ucReturn = NULL;
unsigned long ulAttempts = 0;

	while( ucReturn == NULL )
	{
		/* Look through the buffers to find one that is not in use by
		anything else. */
		for( x = 0; x < uipNUM_BUFFERS; x++ )
		{
			if( ucBufferInUse[ x ] == pdFALSE )
			{
				ucBufferInUse[ x ] = pdTRUE;
				ucReturn = &( ucMACBuffers[ x ][ 0 ] );
				break;
			}
		}

		/* Was a buffer found? */
		if( ucReturn == NULL )
		{
			ulAttempts++;

			if( ulAttempts >= uipBUFFER_WAIT_ATTEMPTS )
			{
				break;
			}

			/* Wait then look again. */
			vTaskDelay( uipBUFFER_WAIT_DELAY );
		}
	}

	return ucReturn;
}
/*-----------------------------------------------------------*/

unsigned short usGetMACRxData( void )
{
unsigned short usReturn;

	if( ( xRxDescriptors[ ulNextDescriptor ].Status & ETH_DMARxDesc_ES ) != 0 )
	{
		/* Error in Rx.  Discard the frame and give it back to the DMA. */
		xRxDescriptors[ ulNextDescriptor ].Status = ETH_DMARxDesc_OWN;
		prvRxDescriptorAvailable();

		/* No data to return. */
		usReturn = 0UL;

		/* Start from the next descriptor the next time this function is called. */
		ulNextDescriptor++;
		if( ulNextDescriptor >= uipNUM_RX_DESCRIPTORS )
		{
			ulNextDescriptor = 0UL;
		}
	}
	else if( ( xRxDescriptors[ ulNextDescriptor ].Status & ETH_DMARxDesc_OWN ) == 0 )
	{
		/* Mark the current buffer as free as uip_buf is going to be set to
		the buffer that contains the received data. */
		vReturnBuffer( uip_buf );

		/* Get the received data length	from the top 2 bytes of the Status
		word and the data itself. */
		usReturn = ( unsigned short ) ( ( xRxDescriptors[ ulNextDescriptor ].Status & ETH_DMARxDesc_FL ) >> 16UL );
		uip_buf = ( unsigned char * ) ( xRxDescriptors[ ulNextDescriptor ].Buffer1Addr );

		/* Allocate a new buffer to the descriptor. */
		xRxDescriptors[ ulNextDescriptor ].Buffer1Addr = ( unsigned long ) prvGetNextBuffer();

		/* Give the descriptor back to the DMA. */
		xRxDescriptors[ ulNextDescriptor ].Status = ETH_DMARxDesc_OWN;
		prvRxDescriptorAvailable();

		/* Start from the next descriptor the next time this function is called. */
		ulNextDescriptor++;
		if( ulNextDescriptor >= uipNUM_RX_DESCRIPTORS )
		{
			ulNextDescriptor = 0UL;
		}
	}
	else
	{
		/* No received data at all. */
		usReturn = 0UL;
	}

	return usReturn;
}
/*-----------------------------------------------------------*/

void vSendMACData( unsigned short usDataLen )
{
unsigned long ulAttempts = 0UL;

	/* Check to see if the Tx descriptor is free.  The check against <2 is to
	ensure the buffer has been sent twice and in so doing preventing a race
	condition with the DMA on the ETH_DMATxDesc_OWN bit. */
	while( ( xTxDescriptor.SendCount < 2 ) && ( xTxDescriptor.Status & ETH_DMATxDesc_OWN ) == ETH_DMATxDesc_OWN )
	{
		/* Wait for the Tx descriptor to become available. */
		vTaskDelay( uipBUFFER_WAIT_DELAY );

		ulAttempts++;
		if( ulAttempts > uipBUFFER_WAIT_ATTEMPTS )
		{
			/* Something has gone wrong as the Tx descriptor is still in use.
			Clear it down manually, the data it was sending will probably be
			lost. */
			xTxDescriptor.Status &= ~ETH_DMATxDesc_OWN;
			vReturnBuffer( ( unsigned char * ) xTxDescriptor.Buffer1Addr );
			break;
		}
	}

	/* Setup the Tx descriptor for transmission. */
	xTxDescriptor.SendCount = 0;
	xTxDescriptor.Buffer1Addr = ( unsigned long ) uip_buf;
	xTxDescriptor.ControlBufferSize = ( unsigned long ) usDataLen;
	xTxDescriptor.Status = ETH_DMATxDesc_OWN | ETH_DMATxDesc_LS | ETH_DMATxDesc_FS | ETH_DMATxDesc_TER | ETH_DMATxDesc_TCH | ETH_DMATxDesc_IC;
	ETH_DMA->DMASR = ETH_DMASR_TBUS;
	ETH_DMA->DMATPDR = 0;

	/* uip_buf is being sent by the Tx descriptor.  Allocate a new buffer. */
	uip_buf = prvGetNextBuffer();
}
/*-----------------------------------------------------------*/

static void prvSetupEthGPIO( void )
{
GPIO_InitTypeDef xEthInit;

	/* Remap MAC IO. */
	AFIO->MAPR |=  ( uipREMAP_MAC_IO );

	/* Set PA2, PA8, PB5, PB8, PB11, PB12, PB13, PC1 and PC2 for Ethernet
	interfacing. */
	xEthInit.GPIO_Pin = GPIO_Pin_2;/* | GPIO_Pin_8; This should be set when the 25MHz is generated by MCO. */
	xEthInit.GPIO_Speed = GPIO_Speed_50MHz;
	xEthInit.GPIO_Mode = GPIO_Mode_AF_PP;
	GPIO_Init( GPIOA, &xEthInit );

	xEthInit.GPIO_Pin = GPIO_Pin_5 | GPIO_Pin_8 | GPIO_Pin_11 | GPIO_Pin_12 | GPIO_Pin_13; /*5*/
	GPIO_Init( GPIOB, &xEthInit );

	xEthInit.GPIO_Pin = GPIO_Pin_1 | GPIO_Pin_2;
	GPIO_Init( GPIOC, &xEthInit );


	/* Configure PA0, PA1, PA3, PB10, PC3, PD8, PD9, PD10, PD11 and PD12 as
	inputs. */
	xEthInit.GPIO_Pin = GPIO_Pin_0 | GPIO_Pin_1 | GPIO_Pin_3;
	xEthInit.GPIO_Mode = GPIO_Mode_IN_FLOATING;
	GPIO_Init( GPIOA, &xEthInit );

	xEthInit.GPIO_Pin = GPIO_Pin_10;
	GPIO_Init( GPIOB, &xEthInit );

	xEthInit.GPIO_Pin = GPIO_Pin_3;
	GPIO_Init( GPIOC, &xEthInit );

	xEthInit.GPIO_Pin = GPIO_Pin_8 | GPIO_Pin_9 | GPIO_Pin_10 | GPIO_Pin_11 | GPIO_Pin_12;
	GPIO_Init( GPIOD, &xEthInit );
}
/*-----------------------------------------------------------*/

void vReturnBuffer( unsigned char *pucBuffer )
{
unsigned long ul;

	/* Mark a buffer as free for use. */
	for( ul = 0; ul < uipNUM_BUFFERS; ul++ )
	{
		if( ucMACBuffers[ ul ] == pucBuffer )
		{
			ucBufferInUse[ ul ] = pdFALSE;
			break;
		}
	}
}
/*-----------------------------------------------------------*/

void vMAC_ISR( void )
{
unsigned long ulStatus;
extern SemaphoreHandle_t xEMACSemaphore;
long xHigherPriorityTaskWoken = pdFALSE;

	/* What caused the interrupt? */
	ulStatus = ETH_DMA->DMASR;

	/* Clear everything before leaving. */
    ETH_DMA->DMASR = ulStatus;

	if( ulStatus & ETH_DMA_IT_R )
	{
		/* Data was received.  Ensure the uIP task is not blocked as data has
		arrived. */
		xSemaphoreGiveFromISR( xEMACSemaphore, &xHigherPriorityTaskWoken );
	}

	if( ulStatus & ETH_DMA_IT_T )
	{
		/* Data was transmitted. */
		if( xTxDescriptor.SendCount == 0 )
		{
			/* Send again! */
			( xTxDescriptor.SendCount )++;

			xTxDescriptor.Status = ETH_DMATxDesc_OWN | ETH_DMATxDesc_LS | ETH_DMATxDesc_FS | ETH_DMATxDesc_TER | ETH_DMATxDesc_TCH | ETH_DMATxDesc_IC;
			ETH_DMA->DMASR = ETH_DMASR_TBUS;
			ETH_DMA->DMATPDR = 0;
		}
		else
		{
			/* The Tx buffer is no longer required. */
			vReturnBuffer( ( unsigned char * ) xTxDescriptor.Buffer1Addr );
		}
	}

	/* If xSemaphoreGiveFromISR() unblocked a task, and the unblocked task has
	a higher priority than the currently executing task, then
	xHigherPriorityTaskWoken will have been set to pdTRUE and this ISR should
	return directly to the higher priority unblocked task. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}

