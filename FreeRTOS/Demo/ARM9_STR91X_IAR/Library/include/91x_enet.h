/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_enet.h
* Author             : MCD Application Team
* Date First Issued  : May 2006
* Description        : ENET driver defines & function prototypes
********************************************************************************
* History:
* May 2006: v1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

#ifndef _ENET_H_
#define _ENET_H_

#include <91x_lib.h>

#define ENET_BUFFER_SIZE 1520
/*Structures typedef----------------------------------------------------------*/

/*Struct containing the DMA Descriptor data */
typedef struct  {
  volatile u32 dmaStatCntl;           /* DMA Status and Control Register          */
  volatile u32 dmaAddr;               /* DMA Start Address Register               */
  volatile u32 dmaNext;               /* DMA Next Descriptor Register             */
  volatile u32 dmaPackStatus;         /* DMA Packet Status and Control Register   */
} ENET_DMADSCRBase;


/* ENET_MACConfig Struct*/
typedef struct {
  FunctionalState ReceiveALL;                 /* Receive All frames: no address rule filtering */
  u32             MIIPrescaler;               /* MII Clock Prescaler value */
  FunctionalState LoopbackMode;               /* MAC Loopback mode */
  u32             AddressFilteringMode;       /* Address Filtering Mode */
  u32             VLANFilteringMode;          /* VLAN Filtering Mode */
  FunctionalState PassWrongFrame;             /* Pass wrong frame (CRC, overlength, runt..)*/
  FunctionalState LateCollision;              /* Retransmit frame when late collision*/
  FunctionalState BroadcastFrameReception;    /* Accept broardcast frame */
  FunctionalState PacketRetry;                /* Retransmit frame in case of collision */
  FunctionalState RxFrameFiltering;           /* Filter early runt frame and address filter fail frames*/
  FunctionalState AutomaticPadRemoval;        /* Automatic Padding removal */
  FunctionalState DeferralCheck;              /* Excessive Defferal check */
} ENET_MACConfig;

/* ENET_TxStatus Struct*/
typedef struct {
  FlagStatus PacketRetry;
  u8         ByteCount;
  u8         collisionCount;
  FlagStatus LateCollisionObserved;
  FlagStatus Deffered;
  FlagStatus UnderRun;
  FlagStatus ExcessiveCollision;
  FlagStatus LateCollision;
  FlagStatus ExcessiveDefferal;
  FlagStatus LossOfCarrier;
  FlagStatus NoCarrier;
  FlagStatus FrameAborted;
} ENET_TxStatus;

/* ENET_RxStatus Struct*/
typedef struct {
  FlagStatus FrameAborted;
  FlagStatus PacketFilter;
  FlagStatus FilteringFail;
  FlagStatus BroadCastFrame;
  FlagStatus MulticastFrame;
  FlagStatus UnsupportedControFrame;
  FlagStatus ControlFrame;
  FlagStatus LengthError;
  FlagStatus Vlan2Tag;
  FlagStatus Vlan1Tag;
  FlagStatus CRCError;
  FlagStatus ExtraBit;
  FlagStatus MIIError;
  FlagStatus FrameType;
  FlagStatus LateCollision;
  FlagStatus OverLength;
  FlagStatus RuntFrame;
  FlagStatus WatchDogTimout;
  FlagStatus FalseCarrierIndication;
  u16        FrameLength;
} ENET_RxStatus;

/*Constants-------------------------------------------------------------------*/


/* AddressFilteringMode */
#define MAC_Perfect_Multicast_Perfect 0x0
#define MAC_Perfect_Multicast_Hash    0x1<<17
#define MAC_Hash_Multicast_Hash       0x2<<17
#define MAC_Inverse                   0x3<<17
#define MAC_Promiscuous               0x4<<17
#define MAC_Perfect_Multicast_All     0x5<<17
#define MAC_Hash_Multicast_All        0x6<<17

/* VLANFilteringMode */
#define VLANFilter_VLTAG_VLID        1
#define VLANfilter_VLTAG             0

/* MIIPrescaler */
#define MIIPrescaler_1  0       /* Prescaler for MDC clock when HCLK < 50 MHz */
#define MIIPrescaler_2  1       /* Precaler for MDC when HCLK > = 50 MHz */


/* MAC Address*/
#define MAC_ADDR0 0x00
#define MAC_ADDR1 0x0A
#define MAC_ADDR2 0x08
#define MAC_ADDR3 0x04
#define MAC_ADDR4 0x02
#define MAC_ADDR5 0x01

/* Multicast Address */
#define MCAST_ADDR0   0xFF
#define MCAST_ADDR1   0x00
#define MCAST_ADDR2   0xFF
#define MCAST_ADDR3   0x00
#define MCAST_ADDR4   0xFF
#define MCAST_ADDR5   0x00



#define ENET_MAX_PACKET_SIZE 1520
#define ENET_NEXT_ENABLE	0x4000

/*ENET_OperatingMode*/
/* Set the full/half-duplex mode at 100 Mb/s */
#define PHY_FULLDUPLEX_100M       0x2100
#define PHY_HALFDUPLEX_100M       0x2000
/* Set the full/half-duplex mode at 10 Mb/s */
#define PHY_FULLDUPLEX_10M        0x0100
#define PHY_HALFDUPLEX_10M        0x0000


/*----------------------------functions----------------------------------------*/

void ENET_MACControlConfig(ENET_MACConfig *MAC_Config);
void ENET_GetRxStatus(ENET_RxStatus * RxStatus);
void ENET_GetTxStatus(ENET_TxStatus * TxStatus);
long ENET_SetOperatingMode(void);
void ENET_InitClocksGPIO(void);
void ENET_MIIWriteReg (u8 phyDev, u8 phyReg, u32  phyVal);
u32 ENET_MIIReadReg (u8 phyDev, u32 phyReg );
void ENET_RxDscrInit(void);
void ENET_TxDscrInit(void);
void ENET_Init(void);
void ENET_Start(void);
u32 ENET_RxPacketGetSize(void);
void ENET_TxPkt(void *ppkt, u16 size);
u32 ENET_HandleRxPkt(void *ppkt);


/*Driver internal constants---------------------------------------------------*/

/* MII Address */
/* Description of bit field values of the MII Address Register */
#define MAC_MIIA_PADDR         0x0000F800
#define MAC_MII_ADDR_PHY_ADDR  MAC_MIIA_PADDR /* Phy Address (default: 0): select one of 32 dev */
#define MAC_MII_ADDR_MII_REG   0x000007C0          /* MII Register (default: 0) */
#define MAC_MII_ADDR_MII_WRITE 0x00000002          /* MII Write */
#define MAC_MIIA_PHY_DEV_ADDR  (0x00005000 & MAC_MIIA_PADDR)  /*To be changed if PHY device address changes */
#define MAC_MII_ADDR_MII_BUSY  0x00000001 /* MII Busy */


/* MII DATA register */
#define MAC_MII_DATA_REG  0x0000FFFF /* MII Data */

/* MII Read / write timeouts*/
#define MII_READ_TO   0x0004FFFF
#define MII_WRITE_TO  0x0004FFFF

/* Description of common PHY registers */
#define MAC_MII_REG_XCR    0x00000000 /* Tranceiver control register */
#define MAC_MII_REG_XSR    0x00000001 /* Tranceiver status register */
#define MAC_MII_REG_PID1   0x00000002 /* Tranceiver PHY identifier 1 */
#define MAC_MII_REG_PID2   0x00000003 /* Tranceiver PHY identifier 2 */
#define MAC_MII_REG_ANA    0x00000004 /* Auto-Negociation Advertissement register */
#define MAC_MII_REG_ANLPA  0x00000005 /* Auto-Negociation  Link Partner Ability register */
#define MAC_MII_REG_ANE    0x00000006 /* Auto-Negociation  Expansion register */




/* MAC_MCR register fields */
#define MAC_MCR_RA    0x80000000
#define MAC_MCR_EN    0x40000000
#define MAC_MCR_PS    0x03000000
#define MAC_MCR_DRO   0x00800000
#define MAC_MCR_LM    0x00600000
#define MAC_MCR_FDM   0x00100000
#define MAC_MCR_AFM   0x000E0000
#define MAC_MCR_PWF   0x00010000
#define MAC_MCR_VFM   0x00008000
#define MAC_MCR_ELC   0x00001000
#define MAC_MCR_DBF   0x00000800
#define MAC_MCR_DPR   0x00000400
#define MAC_MCR_RVFF  0x00000200
#define MAC_MCR_APR   0x00000100
#define MAC_MCR_BL    0x000000C0
#define MAC_MCR_DCE   0x00000020
#define MAC_MCR_RVBE  0x00000010
#define MAC_MCR_TE    0x00000008
#define MAC_MCR_RE    0x00000004
#define MAC_MCR_RCFA  0x00000001

/* MTS */
#define MAC_MTS_FA  0x00000001
#define MAC_MTS_NC  0x00000004
#define MAC_MTS_LOC 0x00000008
#define MAC_MTS_ED  0x00000010
#define MAC_MTS_LC  0x00000020
#define MAC_MTS_EC  0x00000040
#define MAC_MTS_UR  0x00000080
#define MAC_MTS_DEF 0x00000100
#define MAC_MTS_LCO 0x00000200
#define MAC_MTS_CC  0x00003C00
#define MAC_MTS_BC  0x7FFC0000
#define MAC_MTS_PR  0x80000000

/* MRS */
#define MAC_MRS_FL  0x000007FF
#define MAC_MRS_FCI 0x00002000
#define MAC_MRS_WT  0x00004000
#define MAC_MRS_RF  0x00008000
#define MAC_MRS_OL  0x00010000
#define MAC_MRS_LC  0x00020000
#define MAC_MRS_FT  0x00040000
#define MAC_MRS_ME  0x00080000
#define MAC_MRS_EB  0x00100000
#define MAC_MRS_CE  0x00200000
#define MAC_MRS_VL1 0x00400000
#define MAC_MRS_VL2 0x00800000
#define MAC_MRS_LE  0x01000000
#define MAC_MRS_CF  0x02000000
#define MAC_MRS_UCF 0x04000000
#define MAC_MRS_MCF 0x08000000
#define MAC_MRS_BF  0x10000000
#define MAC_MRS_FF  0x20000000
#define MAC_MRS_PF  0x40000000
#define MAC_MRS_FA  0x80000000

/* SCR */
#define DMA_SCR_SRESET               0x00000001 /* Soft Reset (DMA_SCR_RESET) */
#define DMA_SCR_LOOPB                0x00000002 /* Loopback mode (DMA_SCR_LOOPB) */
#define DMA_SCR_RX_MBSIZE            0x00000010 /* Max defined burst length in RX mode (DMA_SCR_RX_MAX_BURST_...) */
#define DMA_SCR_TX_MBSIZE            0x000000C0 /* Max defined burst length in TX mode (DMA_SCR_TX_MAX_BURST_...) */
#define DMA_SCR_RX_MAX_BURST_SZ DMA_SCR_RX_MBSIZE /* Maximum value of defined burst length in RX mode */
#define DMA_SCR_RX_MAX_BURST_SZ_VAL     0x00000000 /* Default value of burst length in RX mode */
#define DMA_SCR_TX_MAX_BURST_SZ DMA_SCR_TX_MBSIZE /* Maximum value of defined burst length in TX mode */
#define DMA_SCR_TX_MAX_BURST_SZ_VAL     0x000000C0 /* Default value of burst length in TX mode */


/* DMA_RX_START   */
#define DMA_RX_START_DMAEN              0x00000001
#define DMA_RX_START_STFETCH            0x00000004
#define DMA_RX_START_FFAIL              0x00000020
#define DMA_RX_START_RUNT               0x00000040
#define DMA_RX_START_COLLS              0x00000080
#define DMA_RX_START_DMA_EN             0x00000001 /* set = 0 by sw force a DMA abort */
#define DMA_RX_START_FETCH              0x00000004 /* start fetching the 1st descriptor */
#define DMA_RX_START_FILTER_FAIL        0x00000020 /* if = 1 the address filtering failed cond */
#define DMA_RX_START_RUNT               0x00000040 /* discard damaged RX frames from cpu charge */
#define DMA_RX_START_COLLS_SEEN         0x00000080 /* Late Collision Seen Cond discard frame automat. */
#define DMA_RX_START_DFETCH_DLY         0x00FFFF00 /* Descriptor Fetch Delay */
#define DMA_RX_START_DFETCH_DLY_POS     8
#define DMA_RX_START_DFETCH_DEFAULT     0x00010000 /* Descriptor Fetch Delay default value */

/* DMA_DSCR_PACK_STAT    */
#define DMA_DSCR_PACK_STAT              0x00010000


/* DMA_TX_START   */
#define DMA_TX_START_DMAEN              0x00000001
#define DMA_TX_START_STFETCH            0x00000004
#define DMA_TX_START_URUN               0x00000020
#define DMA_TX_START_DISPAD             0x00000040
#define DMA_TX_START_ADDCTC             0x00000080
#define DMA_TX_START_DMA_EN             0x00000001 /* set = 0 by sw force a DMA abort */
#define DMA_TX_START_FETCH              0x00000004 /* start fetching the 1st descriptor */
#define DMA_RX_START_FILTER_FAIL        0x00000020 /* if = 1 the address filtering failed cond */
#define DMA_TX_START_DFETCH_DLY         0x00FFFF00 /* Descriptor Fetch Delay */
#define DMA_TX_START_DFETCH_DEFAULT     0x00010000 /* Descriptor Fetch Delay */
#define DMA_TX_START_DFETCH_DLY_POS     0x8
#define DMA_TX_START_URUN               0x00000020
#define DMA_TX_START_DIS_PADDING        0x00000040 /* Avoid automatic addition of padding bits by MAC*/
#define DMA_TX_START_ADD_CRC_DIS        0x00000080 /* Tell MAC not to ADD CRC field at end of frame */

/* DMA_DSCR_CNTL    */
#define DMA_DSCR_CNTL_XFERCOUNT         0x00000FFF
#define DMA_DSCR_CNTL_NXTEN             0x00004000

/* DMA_DSCR_ADDR    */
#define DMA_DSCR_ADDR                   0xFFFFFFFC /* for DMA Start Address (32 bit Word Align) */
#define DMA_DSCR_ADDR_FIX_ADDR          0x00000002 /* Disable incrementing of DMA_ADDR */
#define DMA_DSCR_ADDR_WRAPEN_SET        0x00000001
#define DMA_DSCR_ADDR_WRAPEN_RST        0x00000000

/* DMA_DSCR_NEXT_ADDR    TX/RX */
#define DMA_DSCR_NXT_DSCR_ADDR          0xFFFFFFFC /* Points to Next descriptor starting address */
#define DMA_DSCR_NXT_NPOL_EN            0x00000001 /* Next Descriptor Polling Enable */
#define DMA_DSCR_NXT_NEXT_EN            0x00000002 /* Next Descriptor Fetch mode Enable */

/* DMA Descriptor Packet Status: TX */
#define DMA_DSCR_TX_STATUS_FA_MSK       0x00000001 /* Frame Aborted */
#define DMA_DSCR_TX_STATUS_JTO_MSK      0x00000002 /* Jabber Timeout. */
#define DMA_DSCR_TX_STATUS_NOC_MSK      0x00000004 /* No Carrier */
#define DMA_DSCR_TX_STATUS_LOC_MSK      0x00000008 /* Loss of Carrier */
#define DMA_DSCR_TX_STATUS_EXCD_MSK     0x00000010 /* Excessive Deferral */
#define DMA_DSCR_TX_STATUS_LCOLL_MSK    0x00000020 /* Late Collision */
#define DMA_DSCR_TX_STATUS_ECOLL_MSK    0x00000040 /* Excessive Collisions */
#define DMA_DSCR_TX_STATUS_URUN_MSK     0x00000080 /* Under Run */
#define DMA_DSCR_TX_STATUS_DEFER_MSK    0x00000100 /* Deferred */
#define DMA_DSCR_TX_STATUS_LCOLLO_MSK   0x00000200 /* Late Collision Observed */
#define DMA_DSCR_TX_STATUS_CCNT_MSK     0x00003C00 /* Collision Count */
#define DMA_DSCR_TX_STATUS_HBFAIL_MSK   0x00004000 /* Heart Beat Fail */
#define DMA_DSCR_TX_STATUS_VALID_MSK    0x00010000 /* Valid bit indicator - This bit marks the dscriptors this word belong */
#define DMA_DSCR_TX_STATUS_PKT_RTRY_MSK 0x80000000 /* Packet Retry */
#define DMA_DSCR_TX_STATUS_ORED_ERR_MSK 0x000003D7 /* for total number of errors */

/* DMA Descriptor Packet Status: RX */
#define DMA_DSCR_RX_STATUS_FLEN_MSK     0x000007ff /* 0x00003FFF * Frame Length (max 2047) */
#define DMA_DSCR_RX_STATUS_FTLONG_MSK   0x00001000 /* Over Lenght */
#define DMA_DSCR_RX_STATUS_FCI_MSK      0x00002000 /* Frame too Long */
#define DMA_DSCR_RX_STATUS_WDTO_MSK     0x00004000 /* Watchdog Timeout */
#define DMA_DSCR_RX_STATUS_RUNTFR_MSK   0x00008000 /* Runt Frame */
#define DMA_DSCR_RX_STATUS_VALID_MSK    0x00010000 /* Valid bit indicator - This bit marks the dscriptors this word  */
#define DMA_DSCR_RX_STATUS_COLLSEEN_MSK 0x00020000 /* Collision Seen */
#define DMA_DSCR_RX_STATUS_FTYPE_MSK    0x00040000 /* Frame Type */
#define DMA_DSCR_RX_STATUS_MII_ERR_MSK  0x00080000 /* MII Error */
#define DMA_DSCR_RX_STATUS_DRBBIT_MSK   0x00100000 /* Dribbling Bit */
#define DMA_DSCR_RX_STATUS_CRC_ERR_MSK  0x00200000 /* CRC Error */
#define DMA_DSCR_RX_STATUS_VLAN1_FR_MSK 0x00400000 /* One-Level VLAN Frame */
#define DMA_DSCR_RX_STATUS_VLAN2_FR_MSK 0x00800000 /* Two-Level VLAN Frame */
#define DMA_DSCR_RX_STATUS_LEN_ERR_MSK  0x01000000 /* Length Error */
#define DMA_DSCR_RX_STATUS_CTL_FR_MSK   0x02000000 /* Control Frame */
#define DMA_DSCR_RX_STATUS_UCTRL_FR_MSK 0x04000000 /* Unsupported Control Frame */
#define DMA_DSCR_RX_STATUS_MCAST_FR_MSK 0x08000000 /* Multicast Frame */
#define DMA_DSCR_RX_STATUS_BCAST_FR_MSK 0x10000000 /* BroadCast Frame */
#define DMA_DSCR_RX_STATUS_FLT_FAIL_MSK 0x20000000 /* Filtering Fail */
#define DMA_DSCR_RX_STATUS_PKT_FILT_MSK 0x40000000 /* Packet Filter */
#define DMA_DSCR_RX_STATUS_MIS_FR_MSK   0x80000000 /* Missed Frame */
#define DMA_DSCR_RX_STATUS_ERROR_MSK   (DMA_DSCR_RX_STATUS_LEN_ERR | DMA_DSCR_RX_STATUS_CRC_ERR | \
                                        DMA_DSCR_RX_STATUS_MII_ERR | DMA_DSCR_RX_STATUS_RUNTFR |  \
                                        DMA_DSCR_RX_STATUS_FTLONG | DMA_DSCR_RX_STATUS_COLLSEEN)
#define DMA_DSCR_RX_STATUS_ORED_ERR_MSK 0x00000000 /*Mask for total number of errors */


#endif  /* _ENET_H_ */

/******************** (C) COPYRIGHT 2006 STMicroelectronics *******************/

