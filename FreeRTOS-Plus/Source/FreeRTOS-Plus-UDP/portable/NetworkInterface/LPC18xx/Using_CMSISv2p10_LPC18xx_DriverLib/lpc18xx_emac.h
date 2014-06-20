/***********************************************************************//**
 * @file		lpc17xx_emac.h
 * @brief		Contains all macro definitions and function prototypes
 * 				support for Ethernet MAC firmware library on LPC17xx
 * @version		2.0
 * @date		21. May. 2010
 * @author		NXP MCU SW Application Team
 **************************************************************************
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
 **************************************************************************/

/* Peripheral group ----------------------------------------------------------- */
/** @defgroup EMAC EMAC
 * @ingroup LPC1700CMSIS_FwLib_Drivers
 * @{
 */

#ifndef LPC18XX_EMAC_H_
#define LPC18XX_EMAC_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"



#ifdef __cplusplus
extern "C"
{
#endif

#include "lpc_types.h"

/* Configuration */

/* Interface Selection */
#define MII				0		// =0 RMII  -  =1 MII

/* End of Configuration   */

/*  Descriptors Fields bits       */
#define OWN_BIT				(1U<<31)	/*  Own bit in RDES0 & TDES0              */
#define RX_END_RING			(1<<15)		/*  Receive End of Ring bit in RDES1      */
#define RX_NXTDESC_FLAG		(1<<14)		/*  Second Address Chained bit in RDES1   */
#define TX_LAST_SEGM		(1<<29)		/*  Last Segment bit in TDES0             */
#define RX_LAST_SEGM		(1<<9)
#define TX_FIRST_SEGM		(1<<28)		/*  First Segment bit in TDES0            */
#define RX_FIRST_SEGM		(1<<8)		/*  First Segment bit in TDES0            */
#define TX_END_RING			(1<<21)		/*  Transmit End of Ring bit in TDES0     */
#define TX_NXTDESC_FLAG		(1<<20)		/*  Second Address Chained bit in TDES0   */

/* EMAC Memory Buffer configuration for 16K Ethernet RAM */
#define EMAC_ETH_MAX_FLEN 		ipETHERNET_FRAME_SIZE_TO_USE

/* NOTE: EMAC_NUM_RX_FRAG is not used by the example FreeRTOS drivers - use
configNUM_RX_ETHERNET_DMA_DESCRIPTORS. */
#define EMAC_NUM_RX_FRAG         6           /**< Num.of RX Fragments */

/* NOTE: EMAC_NUM_TX_FRAG is not used by the example FreeRTOS drivers - use
configNUM_TX_ETHERNET_DMA_DESCRIPTORS. */
#define EMAC_NUM_TX_FRAG         2           /**< Num.of TX Fragments */

/* EMAC Control and Status bits   */
#define MAC_RX_ENABLE	 (1<<2)			/*  Receiver Enable in MAC_CONFIG reg      */
#define MAC_TX_ENABLE	 (1<<3)			/*  Transmitter Enable in MAC_CONFIG reg   */
#define MAC_PADCRC_STRIP (1<<7)			/*  Automatic Pad-CRC Stripping in MAC_CONFIG reg   */
#define MAC_DUPMODE		 (1<<11)		/*  Duplex Mode in  MAC_CONFIG reg         */
#define MAC_100MPS		 (1<<14)		/*  Speed is 100Mbps in MAC_CONFIG reg     */
#define MAC_PROMISCUOUS  (1U<<0)		/*  Promiscuous Mode bit in MAC_FRAME_FILTER reg    */
#define MAC_DIS_BROAD    (1U<<5)		/*  Disable Broadcast Frames bit in	MAC_FRAME_FILTER reg    */
#define MAC_RECEIVEALL   (1U<<31)       /*  Receive All bit in MAC_FRAME_FILTER reg    */
#define DMA_SOFT_RESET	  0x01          /*  Software Reset bit in DMA_BUS_MODE reg */
#define DMA_SS_RECEIVE   (1<<1)         /*  Start/Stop Receive bit in DMA_OP_MODE reg  */
#define DMA_SS_TRANSMIT  (1<<13)        /*  Start/Stop Transmission bit in DMA_OP_MODE reg  */
#define DMA_INT_TRANSMIT (1<<0)         /*  Transmit Interrupt Enable bit in DMA_INT_EN reg */
#define DMA_INT_OVERFLOW (1<<4)         /*  Overflow Interrupt Enable bit in DMA_INT_EN reg */
#define DMA_INT_UNDERFLW (1<<5)         /*  Underflow Interrupt Enable bit in DMA_INT_EN reg */
#define DMA_INT_RECEIVE  (1<<6)         /*  Receive Interrupt Enable bit in DMA_INT_EN reg */
#define DMA_INT_ABN_SUM  (1<<15)        /*  Abnormal Interrupt Summary Enable bit in DMA_INT_EN reg */
#define DMA_INT_NOR_SUM  (1<<16)        /*  Normal Interrupt Summary Enable bit in DMA_INT_EN reg */

/* MII Management Command Register */
#define GMII_READ           (0<<1)		/* GMII Read PHY                     */
#define GMII_WRITE          (1<<1)      /* GMII Write PHY                    */
#define GMII_BUSY           0x00000001  /* GMII is Busy / Start Read/Write   */
#define MII_WR_TOUT         0x00050000  /* MII Write timeout count           */
#define MII_RD_TOUT         0x00050000  /* MII Read timeout count            */

/* MII Management Address Register */
#define MADR_PHY_ADR        0x00001F00  /* PHY Address Mask                  */

/* LAN8720 PHY Registers */
#define PHY_REG_BMCR        0x00        /* Basic Mode Control Register       */
#define PHY_REG_BMSR        0x01        /* Basic Mode Status Register        */
#define PHY_REG_IDR1        0x02        /* PHY Identifier 1                  */
#define PHY_REG_IDR2        0x03        /* PHY Identifier 2                  */
#define PHY_REG_ANAR        0x04        /* Auto-Negotiation Advertisement    */
#define PHY_REG_ANLPAR      0x05        /* Auto-Neg. Link Partner Abitily    */
#define PHY_REG_ANER        0x06        /* Auto-Neg. Expansion Register      */
#define PHY_REG_ANNPTR      0x07        /* Auto-Neg. Next Page TX            */

/* LAN8720 PHY Speed identify */
#define PHY_REG_SPCON    				0x1f   /* Speed indication Register     */
#define PHY_REG_HCDSPEED_MASK    		0x1c   /* Speed indication Register mask*/
#define PHY_REG_HCDSPEED_10MB_HALFD    	0x04   /* Speed is 10Mbps HALF-duplex   */
#define PHY_REG_HCDSPEED_10MB_FULLD    	0x14   /* Speed is 10Mbps FULL-duplex   */
#define PHY_REG_HCDSPEED_100MB_HALFD    0x08   /* Speed is 100Mbps HALF-duplex  */
#define PHY_REG_HCDSPEED_100MB_FULLD    0x18   /* Speed is 100Mbps FULL-duplex  */


/* PHY Extended Registers */
#define PHY_REG_STS         0x10        /* Status Register                   */
#define PHY_REG_MICR        0x11        /* MII Interrupt Control Register    */
#define PHY_REG_MISR        0x12        /* MII Interrupt Status Register     */
#define PHY_REG_FCSCR       0x14        /* False Carrier Sense Counter       */
#define PHY_REG_RECR        0x15        /* Receive Error Counter             */
#define PHY_REG_PCSR        0x16        /* PCS Sublayer Config. and Status   */
#define PHY_REG_RBR         0x17        /* RMII and Bypass Register          */
#define PHY_REG_LEDCR       0x18        /* LED Direct Control Register       */
#define PHY_REG_PHYCR       0x19        /* PHY Control Register              */
#define PHY_REG_10BTSCR     0x1A        /* 10Base-T Status/Control Register  */
#define PHY_REG_CDCTRL1     0x1B        /* CD Test Control and BIST Extens.  */
#define PHY_REG_EDCR        0x1D        /* Energy Detect Control Register    */

/* PHY Control and Status bits  */
#define PHY_FULLD_100M      0x2100      /* Full Duplex 100Mbit               */
#define PHY_HALFD_100M      0x2000      /* Half Duplex 100Mbit               */
#define PHY_FULLD_10M       0x0100      /* Full Duplex 10Mbit                */
#define PHY_HALFD_10M       0x0000      /* Half Duplex 10MBit                */
#define PHY_AUTO_NEG        0x1000      /* Select Auto Negotiation           */
#define PHY_AUTO_NEG_DONE   0x0020		/* AutoNegotiation Complete in BMSR PHY reg  */
#define PHY_BMCR_RESET		0x8000		/* Reset bit at BMCR PHY reg         */
#define LINK_VALID_STS		0x0001		/* Link Valid Status at REG_STS PHY reg	 */
#define FULL_DUP_STS		0x0004		/* Full Duplex Status at REG_STS PHY reg */
#define SPEED_10M_STS		0x0002		/* 10Mbps Status at REG_STS PHY reg */

#define DP83848C_DEF_ADR    0x01        /* Default PHY device address        */
#define DP83848C_ID         0x20005C90  /* PHY Identifier (without Rev. info */
#define LAN8720_ID			0x0007C0F1  /* PHY Identifier for SMSC PHY       */

/*  Misc    */
#define ETHERNET_RST		22			/* 	Reset Output for EMAC at RGU     */
#define RMII_SELECT			0x04		/*  Select RMII in EMACCFG           */


/**
 * @brief EMAC configuration structure definition
 */
typedef struct {
	uint32_t	Mode;						/**< Supported EMAC PHY device speed, should be one of the following:
											- EMAC_MODE_AUTO
											- EMAC_MODE_10M_FULL
											- EMAC_MODE_10M_HALF
											- EMAC_MODE_100M_FULL
											- EMAC_MODE_100M_HALF
											*/
	uint8_t 	*pbEMAC_Addr;				/**< Pointer to EMAC Station address that contains 6-bytes
											of MAC address, it must be sorted in order (bEMAC_Addr[0]..[5])
											*/
} EMAC_CFG_Type;

/* Descriptor and status formats ---------------------------------------------- */
/**
 * @brief RX Descriptor structure type definition
 */
typedef struct {
	uint32_t Status;		/**< Receive Status  Descriptor */
	uint32_t Ctrl;			/**< Receive Control Descriptor */
	uint32_t Packet;		/**< Receive Packet Descriptor */
	uint32_t NextDescripter;/**< Receive Next Descriptor Address */
} RX_Desc;

/**
 * @brief RX Status structure type definition
 */
typedef struct {
	uint32_t Info;		/**< Receive Information Status */
	uint32_t HashCRC;	/**< Receive Hash CRC Status */
} RX_Stat;

/**
 * @brief TX Descriptor structure type definition
 */
typedef struct {
	uint32_t Status;		/**< Transmit Status  Descriptor */
	uint32_t Ctrl;		/**< Transmit Control Descriptor */
	uint32_t Packet;	/**< Transmit Packet Descriptor */
	uint32_t NextDescripter;	/**< Transmit Next Descriptor Address */
} TX_Desc;

/**
 * @brief TX Status structure type definition
 */
typedef struct {
   uint32_t Info;		/**< Transmit Information Status */
} TX_Stat;


/**
 * @brief TX Data Buffer structure definition
 */
typedef struct {
	uint32_t ulDataLen;			/**< Data length */
	uint32_t *pbDataBuf;		/**< A word-align data pointer to data buffer */
} EMAC_PACKETBUF_Type;



/*  Prototypes               */
BaseType_t EMAC_Init(EMAC_CFG_Type *EMAC_ConfigStruct);
int32_t EMAC_UpdatePHYStatus(void);
uint32_t EMAC_GetReceiveDataSize(void);
void EMAC_StartTransmitNextBuffer( uint32_t ulLength );
void EMAC_SetNextPacketToSend( uint8_t * pucBuffer );
void EMAC_NextPacketToRead( xNetworkBufferDescriptor_t *pxNetworkBuffer );
void EMAC_UpdateRxConsumeIndex(void);
BaseType_t EMAC_CheckReceiveIndex(void);
BaseType_t EMAC_CheckTransmitIndex(void);

#ifdef __cplusplus
}
#endif

#endif /* LPC18XX_EMAC_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
