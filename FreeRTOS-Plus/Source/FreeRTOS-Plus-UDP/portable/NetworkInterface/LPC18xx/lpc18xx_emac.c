/**********************************************************************
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
* Heavily modified by Real Time Engineers ltd.
***********************************************************************
* Software that is described herein is for illustrative purposes only
* which provides customers with programming information regarding the
* products. This software is supplied "AS IS" without any warranties.
* NXP Semiconductors assumes no responsibility or liability for the
* use of the software, conveys no license or title under any patent,
* copyright, or mask work right to the product. NXP Semiconductors
* reserves the right to make changes in the software without
* notification. NXP Semiconductors also make no representation or
* warranty that such application will be suitable for the specified
* use without further testing or modification.
**********************************************************************/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"

/* Library includes. */
#include "lpc18xx_emac.h"
#include "lpc18xx_rgu.h"
#include "lpc18xx_scu.h"
#include "lpc18xx_gpio.h"


#define emacTIMEOUT_DELAY	( 2 )
#define emacNEGOTIATE_DELAY	( 10 / portTICK_RATE_MS )

#define emacEXPECTED_RX_STATUS_MASK	( RX_FIRST_SEGM | RX_LAST_SEGM )

/* Rx descriptors and data array. */
static volatile RX_Desc Rx_Desc[ configNUM_RX_ETHERNET_DMA_DESCRIPTORS ];
static unsigned int RxDescIndex = 0;

/** Rx Status data array - Must be 8-Byte aligned */
#if defined ( __CC_ARM   )
	static __align(8) RX_Stat Rx_Stat[ configNUM_RX_ETHERNET_DMA_DESCRIPTORS ];
#elif defined ( __ICCARM__ )
	#pragma data_alignment=8
	static RX_Stat Rx_Stat[ configNUM_RX_ETHERNET_DMA_DESCRIPTORS ];
#elif defined   (  __GNUC__  )
	static volatile __attribute__ ((aligned (8))) RX_Stat Rx_Stat[ configNUM_RX_ETHERNET_DMA_DESCRIPTORS ];
#endif

/* Tx descriptors and status array. */
static volatile TX_Desc Tx_Desc[ configNUM_TX_ETHERNET_DMA_DESCRIPTORS ];
static volatile TX_Stat Tx_Stat[ configNUM_TX_ETHERNET_DMA_DESCRIPTORS ];
static unsigned int TxDescIndex = 0;

/* Private Functions ---------------------------------------------------------- */
static void rx_descr_init( void );
static void tx_descr_init( void );
static int32_t write_PHY( uint32_t PhyReg, uint16_t Value );
static int32_t read_PHY( uint32_t PhyReg );
static void setEmacAddr( uint8_t abStationAddr[] );

/*********************************************************************//**
 * @brief		Initializes the EMAC peripheral according to the specified
 *               parameters in the EMAC_ConfigStruct.
 * @param[in]	EMAC_ConfigStruct Pointer to a EMAC_CFG_Type structure
 *                    that contains the configuration information for the
 *                    specified EMAC peripheral.
 * @return		None
 *
 * Note: This function will initialize EMAC module according to procedure below:
 *  - Remove the soft reset condition from the MAC
 *  - Configure the PHY via the MIIM interface of the MAC
 *  - Select RMII mode
 *  - Configure the transmit and receive DMA engines, including the descriptor arrays
 *  - Configure the host registers (MAC1,MAC2 etc.) in the MAC
 *  - Enable the receive and transmit data paths
 *  In default state after initializing, only Rx Done and Tx Done interrupt are enabled,
 *  all remain interrupts are disabled
 *  (Ref. from LPC17xx UM)
 **********************************************************************/
portBASE_TYPE EMAC_Init(EMAC_CFG_Type *EMAC_ConfigStruct)
{
int32_t id1, id2, regv, phy = 0;
int32_t phy_linkstatus_reg, phy_linkstatus_mask;
uint32_t x;
const uint32_t ulMaxAttempts = 250UL;
portBASE_TYPE xReturn = pdPASS;

	/* Enable Ethernet Pins (NGX LPC1830 Xplorer. */
	scu_pinmux(0x2 ,0 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC7);
	scu_pinmux(0x1 ,17 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC3);
	scu_pinmux(0x1 ,18 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC3);
	scu_pinmux(0x1 ,20 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC3);
	scu_pinmux(0x1 ,19 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC0);
	scu_pinmux(0x0 ,1 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC6);
	scu_pinmux(0x1 ,15 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC3);
	scu_pinmux(0x0 ,0 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC2);
	scu_pinmux(0x1 ,16 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC3);
	scu_pinmux(0xC ,9 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC3);
	scu_pinmux(0x1 ,16 , (MD_EHS | MD_PLN | MD_EZI | MD_ZI), FUNC7);

	/* Ethernet RESET Pins */
	scu_pinmux(0x1 ,0 , MD_PUP, FUNC0);
	GPIO_SetDir(0,(1<<4), 1);
	GPIO_SetValue(0,(1<<4));


	#if MII				  /*   Select MII interface       */				 // check MUXING for new Eagle...
	  scu_pinmux(0xC ,6 , (MD_PLN | MD_EZI | MD_ZI), FUNC3); 	// ENET_RXD2: PC_6 -> FUNC3
	  scu_pinmux(0xC ,7 , (MD_PLN | MD_EZI | MD_ZI), FUNC3); 	// ENET_RXD3: PC_7 -> FUNC3
	  scu_pinmux(0xC ,0 , (MD_PLN | MD_EZI | MD_ZI), FUNC3); 	// ENET_RXLK: PC_0 -> FUNC3
	  scu_pinmux(0xC ,2 , (MD_PLN | MD_EZI | MD_ZI), FUNC3); 	// ENET_TXD2: PC_2 -> FUNC3
	  scu_pinmux(0xC ,3 , (MD_PLN | MD_EZI | MD_ZI), FUNC3); 	// ENET_TXD3: PC_3 -> FUNC3
	  scu_pinmux(0xC ,5 , (MD_PLN | MD_EZI | MD_ZI), FUNC3); 	// ENET_TX_ER:  PC_5 -> FUNC3
	  scu_pinmux(0x0 ,1 , (MD_PLN | MD_EZI | MD_ZI), FUNC2); 	// ENET_COL:  P0_1 -> FUNC2
	#else				   /*   Select RMII interface     */
	  LPC_CREG->CREG6 |= RMII_SELECT;
	#endif


	RGU_SoftReset( RGU_SIG_ETHERNET );

	/* Wait for reset. */
	while( !( LPC_RGU->RESET_ACTIVE_STATUS0 & ( 1 << ETHERNET_RST ) ) )
	{
		vTaskDelay( emacTIMEOUT_DELAY );
	}

	/* Reset all GMAC Subsystem internal registers and logic. */
	LPC_ETHERNET->DMA_BUS_MODE |= DMA_SOFT_RESET;

	/* Wait for software reset completion. */
	while( LPC_ETHERNET->DMA_BUS_MODE & DMA_SOFT_RESET )
	{
		vTaskDelay( emacTIMEOUT_DELAY );
	}

	/* Put the PHY in reset mode */
	write_PHY( PHY_REG_BMCR, PHY_BMCR_RESET );

	/* Wait for hardware reset to end. */
	for( x = 0; x < ulMaxAttempts; x++ )
	{
		regv = read_PHY (PHY_REG_BMCR);
		if( !( regv & PHY_BMCR_RESET ) )
		{
			/* Reset complete */
			break;
		}
		else
		{
			vTaskDelay( emacTIMEOUT_DELAY );
		}
	}

	if( x == ulMaxAttempts )
	{
		xReturn = pdFAIL;
	}

	/* Check if this is a DP83848C PHY. */
	id1 = read_PHY( PHY_REG_IDR1 );
	id2 = read_PHY( PHY_REG_IDR2 );
	if( ( ( id1 << 16 ) | ( id2 & 0xFFF0 ) ) == DP83848C_ID )
	{
		phy = DP83848C_ID;
	}
	else if( ( ( id1 << 16 ) | id2 ) == LAN8720_ID )
	{
		phy = LAN8720_ID;
	}

	if( phy != 0 )
	{
		/* Use autonegotiation about the link speed. */
		write_PHY( PHY_REG_BMCR, PHY_AUTO_NEG );

		/* Wait to complete Auto_Negotiation. */
		for( x = 0; x < ulMaxAttempts; x++ )
		{
			regv = read_PHY( PHY_REG_BMSR );

			if( ( regv & PHY_AUTO_NEG_DONE ) != 0 )
			{
				/* Auto negotiation Complete. */
				break;
			}
			else
			{
				vTaskDelay( emacNEGOTIATE_DELAY );
			}
		}

		if( x == ulMaxAttempts )
		{
			xReturn = pdFAIL;
		}
	}
	else
	{
		xReturn = pdFAIL;
	}


	if( xReturn == pdPASS )
	{
		/* Default to DP83848C. */
		phy_linkstatus_reg = PHY_REG_STS;
		phy_linkstatus_mask = 0x0001;

		if( phy == LAN8720_ID )
		{
			phy_linkstatus_reg = PHY_REG_BMSR;
			phy_linkstatus_mask = 0x0004;
		}

		/* Check the link status. */
		for( x = 0; x < ulMaxAttempts; x++ )
		{
			regv = read_PHY( phy_linkstatus_reg );

			if( ( regv & phy_linkstatus_mask ) != 0 )
			{
				/* Link is on. */
				break;
			}
			else
			{
				vTaskDelay( emacNEGOTIATE_DELAY );
			}
		}

		if( x == ulMaxAttempts )
		{
			xReturn = pdFAIL;
		}

		regv = read_PHY( PHY_REG_SPCON );
		regv &= PHY_REG_HCDSPEED_MASK;

		/* Configure 100MBit/10MBit mode and Full/Half Duplex mode. */
		switch( regv )
		{
			case PHY_REG_HCDSPEED_10MB_FULLD:
				LPC_ETHERNET->MAC_CONFIG |= MAC_DUPMODE;
				break;

			case PHY_REG_HCDSPEED_100MB_HALFD:
				LPC_ETHERNET->MAC_CONFIG |= MAC_100MPS;
				break;

			case PHY_REG_HCDSPEED_100MB_FULLD:
				LPC_ETHERNET->MAC_CONFIG |= MAC_DUPMODE;
				LPC_ETHERNET->MAC_CONFIG |= MAC_100MPS;
				break;

			default:
				break;
		}

		/* Set the Ethernet MAC Address registers */
		setEmacAddr( EMAC_ConfigStruct->pbEMAC_Addr );

		/* Initialize Descriptor Lists    */
		rx_descr_init();
		tx_descr_init();

		/* Configure Filter
		LPC_ETHERNET->MAC_FRAME_FILTER is left at its default value.
		MAC_PROMISCUOUS and MAC_RECEIVEALL can be set if required. */

		/* Enable Receiver and Transmitter   */
		LPC_ETHERNET->MAC_CONFIG |= (MAC_TX_ENABLE | MAC_RX_ENABLE);

		/* Enable interrupts    */
		LPC_ETHERNET->DMA_INT_EN =  DMA_INT_NOR_SUM | DMA_INT_RECEIVE ;

		/* Start Transmission & Receive processes   */
		LPC_ETHERNET->DMA_OP_MODE |= (DMA_SS_TRANSMIT | DMA_SS_RECEIVE );
	}

	return xReturn;
}

/*********************************************************************//**
 **********************************************************************/
portBASE_TYPE EMAC_CheckTransmitIndex( void )
{
portBASE_TYPE xReturn;

	if( ( Tx_Desc[ TxDescIndex ].Status & OWN_BIT ) == 0 )
	{
		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}

/*********************************************************************//**
 * @brief 		EMAC_SetNextPacketToSend
 * @param[in] 	pucBuffer
 * @return 		None
 ***********************************************************************/
void EMAC_SetNextPacketToSend( uint8_t * pucBuffer )
{
	/* The old packet is now finished with and can be freed. */
	vEthernetBufferRelease( ( void * ) Tx_Desc[ TxDescIndex ].Packet );

	/* Assign the new packet to the descriptor. */
	Tx_Desc[ TxDescIndex ].Packet = ( uint32_t ) pucBuffer;
}

void EMAC_StartTransmitNextBuffer( uint32_t ulLength )
{
	Tx_Desc[ TxDescIndex ].Ctrl = ulLength;
	Tx_Desc[ TxDescIndex ].Status |= OWN_BIT;

	/* Wake Up the DMA if it's in Suspended Mode. */
	LPC_ETHERNET->DMA_TRANS_POLL_DEMAND = 1;
	TxDescIndex++;

	if( TxDescIndex == configNUM_TX_ETHERNET_DMA_DESCRIPTORS )
	{
		TxDescIndex = 0;
	}
}

/*********************************************************************//**
 * @brief		Get size of current Received data in received buffer (due to
 * 				RxConsumeIndex)
 * @param[in]	None
 * @return		Size of received data
 **********************************************************************/
uint32_t EMAC_GetReceiveDataSize(void)
{
unsigned short RxLen = 0;

	RxLen = ( Rx_Desc[ RxDescIndex ].Status >> 16 ) & 0x03FFF;
	return RxLen;
}

/*********************************************************************//**
 * @brief		Increase the RxConsumeIndex (after reading the Receive buffer
 * 				to release the Receive buffer) and wrap-around the index if
 * 				it reaches the maximum Receive Number
 * @param[in]	None
 * @return		None
 **********************************************************************/
void EMAC_UpdateRxConsumeIndex( void )
{
	Rx_Desc[ RxDescIndex ].Status = OWN_BIT;
	RxDescIndex++;

	if( RxDescIndex == configNUM_RX_ETHERNET_DMA_DESCRIPTORS )
	{
		RxDescIndex = 0;
	}
}

/*********************************************************************//**
 * @brief		Check whether if the current RxConsumeIndex is not equal to the
 * 				current RxProduceIndex.
 * @param[in]	None
 * @return		TRUE if they're not equal, otherwise return FALSE
 *
 * Note: In case the RxConsumeIndex is not equal to the RxProduceIndex,
 * it means there're available data has been received. They should be read
 * out and released the Receive Data Buffer by updating the RxConsumeIndex value.
 **********************************************************************/
portBASE_TYPE EMAC_CheckReceiveIndex(void)
{
portBASE_TYPE xReturn;

	if( ( Rx_Desc[ RxDescIndex ].Status & OWN_BIT ) == 0 )
	{
		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}

void EMAC_NextPacketToRead( xNetworkBufferDescriptor_t *pxNetworkBuffer )
{
uint8_t *pucTemp;

	/* Swap the buffer in the network buffer with the buffer used by the DMA.
	This allows the data to be passed out without having to perform any copies. */
	pucTemp = ( uint8_t * ) Rx_Desc[ RxDescIndex ].Packet;
	Rx_Desc[ RxDescIndex ].Packet = ( uint32_t ) pxNetworkBuffer->pucEthernetBuffer;
	pxNetworkBuffer->pucEthernetBuffer = pucTemp;

	/* Only supports frames coming in single buffers.  If this frame is split
	across multiple buffers then reject it (and if the frame is needed increase
	the ipconfigNETWORK_MTU setting). */
	if( ( Rx_Desc[ RxDescIndex ].Status & emacEXPECTED_RX_STATUS_MASK ) != emacEXPECTED_RX_STATUS_MASK )
	{
		pxNetworkBuffer->xDataLength = 0;
	}
	else
	{
		pxNetworkBuffer->xDataLength = ( size_t ) EMAC_GetReceiveDataSize() - ( ipETHERNET_CRC_BYTES - 1U );;
	}
}

/*********************************************************************//**
 * @brief 		Initializes RX Descriptor
 * @param[in] 	None
 * @return 		None
 ***********************************************************************/
static void rx_descr_init( void )
{
uint32_t x;
size_t xBufferSize = ipTOTAL_ETHERNET_FRAME_SIZE;

	for( x = 0; x < configNUM_RX_ETHERNET_DMA_DESCRIPTORS; x++ )
	{
		/* Obtain the buffer first, as the size of the buffer might be changed
		within the pucEthernetBufferGet() call. */
		Rx_Desc[ x ].Packet  = ( uint32_t ) pucEthernetBufferGet( &xBufferSize );
		Rx_Desc[ x ].Status = OWN_BIT;
		Rx_Desc[ x ].Ctrl  = xBufferSize;
		Rx_Desc[ x ].NextDescripter = ( uint32_t ) &Rx_Desc[ x + 1 ];
		
		configASSERT( ( ( ( uint32_t ) Rx_Desc[x].Packet ) & 0x07 ) == 0 );
	}

	/* Last Descriptor */
	Rx_Desc[ configNUM_RX_ETHERNET_DMA_DESCRIPTORS - 1 ].Ctrl |= RX_END_RING;

	RxDescIndex = 0;

	/* Set Starting address of RX Descriptor list */
	LPC_ETHERNET->DMA_REC_DES_ADDR = ( uint32_t ) Rx_Desc;
}

/*********************************************************************//**
 * @brief 		Initializes TX Descriptor
 * @param[in] 	None
 * @return 		None
 ***********************************************************************/
static void tx_descr_init( void )
{
/* Initialize Transmit Descriptor and Status array. */
uint32_t x;

	for( x = 0; x < configNUM_TX_ETHERNET_DMA_DESCRIPTORS; x++ )
	{
		Tx_Desc[ x ].Status = TX_LAST_SEGM | TX_FIRST_SEGM;
		Tx_Desc[ x ].Ctrl  = 0;
		Tx_Desc[ x ].NextDescripter = ( uint32_t ) &Tx_Desc[ x + 1 ];

		/* Packet is assigned when a Tx is initiated. */
		Tx_Desc[ x ].Packet   = ( uint32_t )NULL;
	}

	/* Last Descriptor? */
	Tx_Desc[ configNUM_TX_ETHERNET_DMA_DESCRIPTORS-1 ].Status |= TX_END_RING;

	/* Set Starting address of TX Descriptor list */
	LPC_ETHERNET->DMA_TRANS_DES_ADDR = ( uint32_t ) Tx_Desc;
}


/*********************************************************************//**
 * @brief 		Write value to PHY device
 * @param[in] 	PhyReg: PHY Register address
 * @param[in] 	Value:  Value to write
 * @return 		0 - if success
 * 				1 - if fail
 ***********************************************************************/
static int32_t write_PHY (uint32_t PhyReg, uint16_t Value)
{
uint32_t x;
const uint32_t ulMaxAttempts = 250UL;
int32_t lReturn = pdPASS;

	/* Write a data 'Value' to PHY register 'PhyReg'. */
	x = 0;
	while( LPC_ETHERNET->MAC_MII_ADDR & GMII_BUSY )
	{
		x++;

		if( x >= ulMaxAttempts )
		{
			/* Time out. */
			lReturn = pdFAIL;
			break;
		}
		else
		{
			/* GMII is busy. */
			vTaskDelay( emacTIMEOUT_DELAY );
		}
	}

	if( lReturn == pdPASS )
	{
		LPC_ETHERNET->MAC_MII_ADDR = ( DP83848C_DEF_ADR << 11 ) | ( PhyReg << 6 ) | GMII_WRITE;
		LPC_ETHERNET->MAC_MII_DATA = Value;

		/* Start PHY Write Cycle. */
		LPC_ETHERNET->MAC_MII_ADDR |= GMII_BUSY;

		/* Wait untl operation completed. */
		for( x = 0; x < ulMaxAttempts; x++ )
		{
			if( ( LPC_ETHERNET->MAC_MII_ADDR & GMII_BUSY ) == 0 )
			{
				break;
			}
			else
			{
				vTaskDelay( emacTIMEOUT_DELAY );
			}
		}

		if( x == ulMaxAttempts )
		{
			/* Timeout. */
			lReturn = pdFAIL;
		}
	}

	return lReturn;
}

/*********************************************************************//**
 * @brief 		Read value from PHY device
 * @param[in] 	PhyReg: PHY Register address
 * @return 		0 - if success
 * 				1 - if fail
 ***********************************************************************/
static int32_t read_PHY( uint32_t PhyReg )
{
int32_t lValue = 0;
uint32_t x;
const uint32_t ulMaxAttempts = 250UL;

	/* Write a data 'Value' to PHY register 'PhyReg'. */
	x = 0;
	while( LPC_ETHERNET->MAC_MII_ADDR & GMII_BUSY )
	{
		x++;

		if( x >= ulMaxAttempts )
		{
			/* Time out. */
			break;
		}
		else
		{
			/* GMII is busy. */
			vTaskDelay( emacTIMEOUT_DELAY );
		}
	}

	if( x < ulMaxAttempts )
	{
		/* Read a PHY register 'PhyReg'. */
		LPC_ETHERNET->MAC_MII_ADDR = ( DP83848C_DEF_ADR << 11 ) | ( PhyReg << 6 ) | GMII_READ;

		/* Start PHY Read Cycle. */
		LPC_ETHERNET->MAC_MII_ADDR |= GMII_BUSY;

		/* Wait until operation completed */
		for( x = 0; x < ulMaxAttempts; x++ )
		{
			if( ( LPC_ETHERNET->MAC_MII_ADDR & GMII_BUSY ) == 0 )
			{
				break;
			}
			else
			{
				vTaskDelay( emacTIMEOUT_DELAY );
			}
		}

		configASSERT( x != ulMaxAttempts );
		lValue = LPC_ETHERNET->MAC_MII_DATA;
	}

	return lValue;
}

/*********************************************************************//**
 * @brief		Set Station MAC address for EMAC module
 * @param[in]	abStationAddr Pointer to Station address that contains 6-bytes
 * 				of MAC address (should be in order from MAC Address 1 to MAC Address 6)
 * @return		None
 **********************************************************************/
static void setEmacAddr( uint8_t abStationAddr[] )
{
	/* Set the Ethernet MAC Address registers */
	LPC_ETHERNET->MAC_ADDR0_HIGH = (( uint32_t ) abStationAddr[ 5 ] << 8 ) | ( uint32_t )abStationAddr[ 4 ];
	LPC_ETHERNET->MAC_ADDR0_LOW =	(( uint32_t )abStationAddr[ 3 ] << 24) | (( uint32_t )abStationAddr[ 2 ] << 16) | (( uint32_t )abStationAddr[ 1 ] << 8 ) | ( uint32_t )abStationAddr[ 0 ];
}



