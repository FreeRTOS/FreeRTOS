/******************** (C) COPYRIGHT 2008 STMicroelectronics ********************
* File Name          : stm32fxxx_eth.h
* Author             : MCD Application Team
* Version            : V0.0.1
* Date               : 12/17/2008
* Desciption         : This file contains all the functions prototypes for the
*                      ETHERNET firmware library.
********************************************************************************
* THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32FXXX_ETH_H
#define __STM32FXXX_ETH_H

/* Includes ------------------------------------------------------------------*/
#include "stm32fxxx_eth_map.h"

/* Exported types ------------------------------------------------------------*/
/* ETHERNET MAC Init structure definition */
typedef struct {
  /* MAC ----------------------------------*/
  u32             ETH_AutoNegotiation;           /* Selects or not the AutoNegotiation with the external PHY */
  u32             ETH_Watchdog;                  /* Enable/disable Watchdog timer */
  u32             ETH_Jabber;                    /* Enable/disable Jabber timer */
  u32             ETH_JumboFrame;                /* Enable/disable Jumbo frame */
  u32             ETH_InterFrameGap;             /* Selects minimum IFG between frames during transmission */
  u32             ETH_CarrierSense;              /* Enable/disable Carrier Sense */
  u32             ETH_Speed;                     /* Indicates the Ethernet speed: 10/100 Mbps */
  u32             ETH_ReceiveOwn;                /* Enable/disable the reception of frames when the TX_EN signal is asserted in Half-Duplex mode */
  u32             ETH_LoopbackMode;              /* Enable/disable internal MAC MII Loopback mode */
  u32             ETH_Mode;                      /* Selects the MAC duplex mode: Half-Duplex or Full-Duplex mode */
  u32             ETH_ChecksumOffload;           /* Enable/disable the calculation of complement sum of all received Ethernet frame payloads */
  u32             ETH_RetryTransmission;         /* Enable/disable the MAC attempt retries transmission, based on the settings of BL, when a colision occurs (Half-Duplex mode) */
  u32             ETH_AutomaticPadCRCStrip;      /* Enable/disable Automatic MAC Pad/CRC Stripping */
  u32             ETH_BackOffLimit;              /* Selects the BackOff limit value */
  u32             ETH_DeferralCheck;             /* Enable/disable deferral check function (Half-Duplex mode) */
  u32             ETH_ReceiveAll;                /* Enable/disable all frames reception by the MAC (No fitering)*/
  u32             ETH_SourceAddrFilter;          /* Selects EnableNormal/EnableInverse/disable Source Address Filter comparison */
  u32             ETH_PassControlFrames;         /* Selects None/All/FilterPass of all control frames (including unicast and multicast PAUSE frames) */
  u32             ETH_BroadcastFramesReception;  /* Enable/disable reception of Broadcast Frames */
  u32             ETH_DestinationAddrFilter;     /* Selects EnableNormal/EnableInverse destination filter for both unicast and multicast frames */
  u32             ETH_PromiscuousMode;           /* Enable/disable Promiscuous Mode */
  u32             ETH_MulticastFramesFilter;     /* Selects the Multicast Frames filter: None/HashTableFilter/PerfectFilter/PerfectHashTableFilter */
  u32             ETH_UnicastFramesFilter;       /* Selects the Unicast Frames filter: HashTableFilter/PerfectFilter/PerfectHashTableFilter  */
  u32             ETH_HashTableHigh;             /* This field contains the higher 32 bits of Hash table.  */
  u32             ETH_HashTableLow;              /* This field contains the lower 32 bits of Hash table.  */
  u32             ETH_PauseTime;                 /* This field holds the value to be used in the Pause Time field in the transmit control frame */
  u32             ETH_ZeroQuantaPause;           /* Enable/disable the automatic generation of Zero-Quanta Pause Control frames */
  u32             ETH_PauseLowThreshold;         /* This field configures the threshold of the PAUSE to be checked for automatic retransmission of PAUSE Frame */
  u32             ETH_UnicastPauseFrameDetect;   /* Enable/disable MAC to detect the Pause frames (with MAC Address0 unicast address and unique multicast address) */
  u32             ETH_ReceiveFlowControl;        /* Enable/disable the MAC to decode the received Pause frame and disable its transmitter for a specified (Pause Time) time */
  u32             ETH_TransmitFlowControl;       /* Enable/disable the MAC to transmit Pause frames (Full-Duplex mode) or the MAC back-pressure operation (Half-Duplex mode) */
  u32             ETH_VLANTagComparison;         /* Selects the 12-bit VLAN identifier or the complete 16-bit VLAN tag for comparison and filtering */
  u32             ETH_VLANTagIdentifier;         /* VLAN tag identifier for receive frames */

  /* DMA --------------------------*/
  u32             ETH_DropTCPIPChecksumErrorFrame; /* Enable/disable Dropping of TCP/IP Checksum Error Frames */
  u32             ETH_ReceiveStoreForward;         /* Enable/disable Receive store and forward */
  u32             ETH_FlushReceivedFrame;          /* Enable/disable flushing of received frames */
  u32             ETH_TransmitStoreForward;        /* Enable/disable Transmit store and forward */
  u32             ETH_TransmitThresholdControl;    /* Selects the Transmit Threshold Control */
  u32             ETH_ForwardErrorFrames;          /* Enable/disable forward to DMA of all frames except runt error frames */
  u32             ETH_ForwardUndersizedGoodFrames; /* Enable/disable Rx FIFO to forward Undersized frames (frames with no Error and length less than 64 bytes) including pad-bytes and CRC) */
  u32             ETH_ReceiveThresholdControl;     /* Selects the threshold level of the Receive FIFO */
  u32             ETH_SecondFrameOperate;          /* Enable/disable the DMA process of a second frame of Transmit	data even before status for first frame is obtained */
  u32             ETH_AddressAlignedBeats;         /* Enable/disable Address Aligned Beats */
  u32             ETH_FixedBurst;                  /* Enable/disable the AHB Master interface fixed burst transfers */
  u32             ETH_RxDMABurstLength;            /* Indicate the maximum number of beats to be transferred in one Rx DMA transaction */
  u32             ETH_TxDMABurstLength;            /* Indicate the maximum number of beats to be transferred in one Tx DMA transaction */
  u32             ETH_DescriptorSkipLength;        /* Specifies the number of word to skip between two unchained descriptors (Ring mode) */
  u32             ETH_DMAArbitration;              /* Selects DMA Tx/Rx arbitration */
}ETH_InitTypeDef;

/*----------------------------------------------------------------------------*/
/*                          DMA descriptors types                             */
/*----------------------------------------------------------------------------*/
/* ETHERNET DMA Desciptors data structure definition  */
typedef struct  {
  volatile u32   Status;                /* Status */
  volatile u32   ControlBufferSize;     /* Control and Buffer1, Buffer2 lengths */
  volatile u32   Buffer1Addr;           /* Buffer1 address pointer */
  volatile u32   Buffer2NextDescAddr;   /* Buffer2 or next descriptor address pointer */
} ETH_DMADESCTypeDef;

/* Exported constants --------------------------------------------------------*/

/*----------------------------------------------------------------------------*/
/*                         ETHERNET Frames defines                            */
/*----------------------------------------------------------------------------*/
/* ENET Buffers setting */
#define ETH_MAX_PACKET_SIZE    1520    /* ETH_HEADER + ETH_EXTRA + MAX_ETH_PAYLOAD + ETH_CRC */
#define ETH_HEADER               14    /* 6 byte Dest addr, 6 byte Src addr, 2 byte length/type */
#define ETH_CRC                   4    /* Ethernet CRC */
#define ETH_EXTRA                 2    /* Extra bytes in some cases */
#define VLAN_TAG                  4    /* optional 802.1q VLAN Tag */
#define MIN_ETH_PAYLOAD          46    /* Minimum Ethernet payload size */
#define MAX_ETH_PAYLOAD        1500    /* Maximum Ethernet payload size */
#define JUMBO_FRAME_PAYLOAD    9000    /* Jumbo frame payload size */

/*--------------------------------------------------------*/
/*   Ethernet DMA descriptors registers bits definition   */
/*--------------------------------------------------------*/
/* DMA Tx Desciptor ---------------------------------------------------------*/
/*-----------------------------------------------------------------------------------------------
  TDES0 | OWN(31) | CTRL[30:26] | Reserved[25:24] | CTRL[23:20] | Reserved[19:17] | Status[16:0] |                                         |
  -----------------------------------------------------------------------------------------------
  TDES1 | Reserved[31:29] | Buffer2 ByteCount[28:16] | Reserved[15:13] | Buffer1 ByteCount[12:0] |
  -----------------------------------------------------------------------------------------------
  TDES2 |                         Buffer1 Address [31:0]                                         |
  -----------------------------------------------------------------------------------------------
  TDES3 |                   Buffer2 Address [31:0] / Next Desciptor Address [31:0]               |
  ----------------------------------------------------------------------------------------------*/

/* Bit definition of TDES0 register: DMA Tx descriptor status register */
#define ETH_DMATxDesc_OWN   (0x80000000UL)  /* OWN bit: descriptor is owned by DMA engine */
#define ETH_DMATxDesc_IC    ((u32)0x40000000)  /* Interrupt on Completion */
#define ETH_DMATxDesc_LS    ((u32)0x20000000)  /* Last Segment */
#define ETH_DMATxDesc_FS    ((u32)0x10000000)  /* First Segment */
#define ETH_DMATxDesc_DC    ((u32)0x08000000)  /* Disable CRC */
#define ETH_DMATxDesc_DP    ((u32)0x04000000)  /* Disable Padding */
#define ETH_DMATxDesc_TTSE  ((u32)0x02000000)  /* Transmit Time Stamp Enable */
#define ETH_DMATxDesc_CIC   ((u32)0x00C00000)  /* Checksum Insertion Control: 4 cases */
  #define ETH_DMATxDesc_CIC_ByPass              ((u32)0x00000000)  /* Do Nothing: Checksum Engine is bypassed */
  #define ETH_DMATxDesc_CIC_IPV4Header          ((u32)0x00400000)  /* IPV4 header Checksum Insertion */
  #define ETH_DMATxDesc_CIC_TCPUDPICMP_Segment  ((u32)0x00800000)  /* TCP/UDP/ICMP Checksum Insertion calculated over segment only */
  #define ETH_DMATxDesc_CIC_TCPUDPICMP_Full     ((u32)0x00C00000)  /* TCP/UDP/ICMP Checksum Insertion fully calculated */
#define ETH_DMATxDesc_TER   ((u32)0x00200000)  /* Transmit End of Ring */
#define ETH_DMATxDesc_TCH   ((u32)0x00100000)  /* Second Address Chained */
#define ETH_DMATxDesc_TTSS  ((u32)0x00020000)  /* Tx Time Stamp Status */
#define ETH_DMATxDesc_IHE   ((u32)0x00010000)  /* IP Header Error */
#define ETH_DMATxDesc_ES    ((u32)0x00008000)  /* Error summary: OR of the following bits: UE || ED || EC || LCO || NC || LCA || FF || JT */
#define ETH_DMATxDesc_JT    ((u32)0x00004000)  /* Jabber Timeout */
#define ETH_DMATxDesc_FF    ((u32)0x00002000)  /* Frame Flushed: DMA/MTL flushed the frame due to SW flush */
#define ETH_DMATxDesc_PCE   ((u32)0x00001000)  /* Payload Checksum Error */
#define ETH_DMATxDesc_LCA   ((u32)0x00000800)  /* Loss of Carrier: carrier lost during tramsmission */
#define ETH_DMATxDesc_NC    ((u32)0x00000400)  /* No Carrier: no carrier signal from the tranceiver */
#define ETH_DMATxDesc_LCO   ((u32)0x00000200)  /* Late Collision: transmission aborted due to collision */
#define ETH_DMATxDesc_EC    ((u32)0x00000100)  /* Excessive Collision: transmission aborted after 16 collisions */
#define ETH_DMATxDesc_VF    ((u32)0x00000080)  /* VLAN Frame */
#define ETH_DMATxDesc_CC    ((u32)0x00000078)  /* Collision Count */
#define ETH_DMATxDesc_ED    ((u32)0x00000004)  /* Excessive Deferral */
#define ETH_DMATxDesc_UF    ((u32)0x00000002)  /* Underflow Error: late data arrival from the memory */
#define ETH_DMATxDesc_DB    ((u32)0x00000001)  /* Deferred Bit */

/* Bit definition of TDES1 register */
#define ETH_DMATxDesc_TBS2  ((u32)0x1FFF0000)  /* Transmit Buffer2 Size */
#define ETH_DMATxDesc_TBS1  ((u32)0x00001FFF)  /* Transmit Buffer1 Size */

/* Bit definition of TDES2 register */
#define ETH_DMATxDesc_B1AP  ((u32)0xFFFFFFFF)  /* Buffer1 Address Pointer */

/* Bit definition of TDES3 register */
#define ETH_DMATxDesc_B2AP  ((u32)0xFFFFFFFF)  /* Buffer2 Address Pointer */

/* DMA Rx descriptor ---------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------------
  RDES0 | OWN(31) |                                             Status [30:0]                                          |
  ---------------------------------------------------------------------------------------------------------------------
  RDES1 | CTRL(31) | Reserved[30:29] | Buffer2 ByteCount[28:16] | CTRL[15:14] | Reserved(13) | Buffer1 ByteCount[12:0] |
  ---------------------------------------------------------------------------------------------------------------------
  RDES2 |                                       Buffer1 Address [31:0]                                                 |
  ---------------------------------------------------------------------------------------------------------------------
  RDES3 |                          Buffer2 Address [31:0] / Next Desciptor Address [31:0]                              |
  --------------------------------------------------------------------------------------------------------------------*/

/* Bit definition of RDES0 register: DMA Rx descriptor status register */
#define ETH_DMARxDesc_OWN         ((u32)0x80000000)  /* OWN bit: descriptor is owned by DMA engine  */
#define ETH_DMARxDesc_AFM         ((u32)0x40000000)  /* DA Filter Fail for the rx frame  */
#define ETH_DMARxDesc_FL          ((u32)0x3FFF0000)  /* Receive descriptor frame length  */
#define ETH_DMARxDesc_ES          ((u32)0x00008000)  /* Error summary: OR of the following bits: DE || OE || IPC || LC || RWT || RE || CE */
#define ETH_DMARxDesc_DE          ((u32)0x00004000)  /* Desciptor error: no more descriptors for receive frame  */
#define ETH_DMARxDesc_SAF         ((u32)0x00002000)  /* SA Filter Fail for the received frame */
#define ETH_DMARxDesc_LE          ((u32)0x00001000)  /* Frame size not matching with length field */
#define ETH_DMARxDesc_OE          ((u32)0x00000800)  /* Overflow Error: Frame was damaged due to buffer overflow */
#define ETH_DMARxDesc_VLAN        ((u32)0x00000400)  /* VLAN Tag: received frame is a VLAN frame */
#define ETH_DMARxDesc_FS          ((u32)0x00000200)  /* First descriptor of the frame  */
#define ETH_DMARxDesc_LS          ((u32)0x00000100)  /* Last descriptor of the frame  */
#define ETH_DMARxDesc_IPV4HCE     ((u32)0x00000080)  /* IPC Checksum Error/Giant Frame: Rx Ipv4 header checksum error   */
#define ETH_DMARxDesc_RxLongFrame ((u32)0x00000080)  /* (Giant Frame)Rx - frame is longer than 1518/1522   */
#define ETH_DMARxDesc_LC          ((u32)0x00000040)  /* Late collision occurred during reception   */
#define ETH_DMARxDesc_FT          ((u32)0x00000020)  /* Frame type - Ethernet, otherwise 802.3    */
#define ETH_DMARxDesc_RWT         ((u32)0x00000010)  /* Receive Watchdog Timeout: watchdog timer expired during reception    */
#define ETH_DMARxDesc_RE          ((u32)0x00000008)  /* Receive error: error reported by MII interface  */
#define ETH_DMARxDesc_DBE         ((u32)0x00000004)  /* Dribble bit error: frame contains non int multiple of 8 bits  */
#define ETH_DMARxDesc_CE          ((u32)0x00000002)  /* CRC error */
#define ETH_DMARxDesc_MAMPCE      ((u32)0x00000001)  /* Rx MAC Address/Payload Checksum Error: Rx MAC address matched/ Rx Payload Checksum Error */

/* Bit definition of RDES1 register */
#define ETH_DMARxDesc_DIC   ((u32)0x80000000)  /* Disable Interrupt on Completion */
#define ETH_DMARxDesc_RBS2  ((u32)0x1FFF0000)  /* Receive Buffer2 Size */
#define ETH_DMARxDesc_RER   ((u32)0x00008000)  /* Receive End of Ring */
#define ETH_DMARxDesc_RCH   ((u32)0x00004000)  /* Second Address Chained */
#define ETH_DMARxDesc_RBS1  ((u32)0x00001FFF)  /* Receive Buffer1 Size */

/* Bit definition of RDES2 register */
#define ETH_DMARxDesc_B1AP  ((u32)0xFFFFFFFF)  /* Buffer1 Address Pointer */

/* Bit definition of RDES3 register */
#define ETH_DMARxDesc_B2AP  ((u32)0xFFFFFFFF)  /* Buffer2 Address Pointer */

/*----------------------------------------------------------------------------*/
/*                   Desciption of common PHY registers                      */
/*----------------------------------------------------------------------------*/
/* PHY Read/write Timeouts */
#define PHY_READ_TO                     ((u32)0x0004FFFF)
#define PHY_WRITE_TO                    ((u32)0x0004FFFF)

/* PHY Reset Delay */
#define PHY_ResetDelay                  ((u32)0x000FFFFF)

/* PHY Config Delay */
#define PHY_ConfigDelay                 ((u32)0x00FFFFFF)

/* PHY Register address */
#define PHY_BCR                          0          /* Tranceiver Basic Control Register */
#define PHY_BSR                          1          /* Tranceiver Basic Status Register */

/* PHY basic Control register */
#define PHY_Reset                       ((u16)0x8000)      /* PHY Reset */
#define PHY_Loopback                    ((u16)0x4000)      /* Select loop-back mode */
#define PHY_FULLDUPLEX_100M             ((u16)0x2100)      /* Set the full-duplex mode at 100 Mb/s */
#define PHY_HALFDUPLEX_100M             ((u16)0x2000)      /* Set the half-duplex mode at 100 Mb/s */
#define PHY_FULLDUPLEX_10M              ((u16)0x0100)      /* Set the full-duplex mode at 10 Mb/s */
#define PHY_HALFDUPLEX_10M              ((u16)0x0000)      /* Set the half-duplex mode at 10 Mb/s */
#define PHY_AutoNegotiation             ((u16)0x1000)      /* Enable auto-negotiation function */
#define PHY_Restart_AutoNegotiation     ((u16)0x0200)      /* Restart auto-negotiation function */
#define PHY_Powerdown                   ((u16)0x0800)      /* Select the power down mode */
#define PHY_Isolate                     ((u16)0x0400)      /* Isolate PHY from MII */

/* PHY basic status register */
#define PHY_AutoNego_Complete           ((u16)0x0020)      /* Auto-Negotioation process completed */
#define PHY_Linked_Status               ((u16)0x0004)      /* Valid link established */
#define PHY_Jabber_detection            ((u16)0x0002)      /* Jabber condition detected */

/* The PHY status register value change from a PHY to another so the user have to update
   this value depending on the used external PHY */
/* For LAN8700 */
//#define PHY_SR                           31         /* Tranceiver Status Register */
/* For DP83848 */
#define PHY_SR                           16      /* Tranceiver Status Register */

/* PHY status register */
/* The Speed and Duplex mask values change from a PHY to another so the user have to update
   this value depending on the used external PHY */
/* For LAN8700 */
//#define PHY_Speed_Status            ((u16)0x0004)       /* Configured information of Speed: 10Mbps */
//#define PHY_Duplex_Status           ((u16)0x0010)       /* Configured information of Duplex: Full-duplex */
/* For DP83848 */
#define PHY_Speed_Status            ((u16)0x0002)    /* Configured information of Speed: 10Mbps */
#define PHY_Duplex_Status           ((u16)0x0004)    /* Configured information of Duplex: Full-duplex */

#define IS_ETH_PHY_ADDRESS(ADDRESS) ((ADDRESS) <= 0x20)
#define IS_ETH_PHY_REG(REG) (((REG) == PHY_BCR) || \
                             ((REG) == PHY_BSR) || \
                             ((REG) == PHY_SR))

/*----------------------------------------------------------------------------*/
/*                                 MAC defines                                */
/*----------------------------------------------------------------------------*/
/* ETHERNET AutoNegotiation --------------------------------------------------*/
#define ETH_AutoNegotiation_Enable     ((u32)0x00000001)
#define ETH_AutoNegotiation_Disable    ((u32)0x00000000)

#define IS_ETH_AUTONEGOTIATION(CMD) (((CMD) == ETH_AutoNegotiation_Enable) || \
                                     ((CMD) == ETH_AutoNegotiation_Disable))

/* ETHERNET watchdog ---------------------------------------------------------*/
#define ETH_Watchdog_Enable       ((u32)0x00000000)
#define ETH_Watchdog_Disable      ((u32)0x00800000)

#define IS_ETH_WATCHDOG(CMD) (((CMD) == ETH_Watchdog_Enable) || \
                              ((CMD) == ETH_Watchdog_Disable))

/* ETHERNET Jabber -----------------------------------------------------------*/
#define ETH_Jabber_Enable    ((u32)0x00000000)
#define ETH_Jabber_Disable   ((u32)0x00400000)

#define IS_ETH_JABBER(CMD) (((CMD) == ETH_Jabber_Enable) || \
                            ((CMD) == ETH_Jabber_Disable))

/* ETHERNET Jumbo Frame ------------------------------------------------------*/
#define ETH_JumboFrame_Enable     ((u32)0x00100000)
#define ETH_JumboFrame_Disable    ((u32)0x00000000)

#define IS_ETH_JUMBO_FRAME(CMD) (((CMD) == ETH_JumboFrame_Enable) || \
                                 ((CMD) == ETH_JumboFrame_Disable))

/* ETHERNET Inter Frame Gap --------------------------------------------------*/
#define ETH_InterFrameGap_96Bit   ((u32)0x00000000)  /* minimum IFG between frames during transmission is 96Bit */
#define ETH_InterFrameGap_88Bit   ((u32)0x00020000)  /* minimum IFG between frames during transmission is 88Bit */
#define ETH_InterFrameGap_80Bit   ((u32)0x00040000)  /* minimum IFG between frames during transmission is 80Bit */
#define ETH_InterFrameGap_72Bit   ((u32)0x00060000)  /* minimum IFG between frames during transmission is 72Bit */
#define ETH_InterFrameGap_64Bit   ((u32)0x00080000)  /* minimum IFG between frames during transmission is 64Bit */
#define ETH_InterFrameGap_56Bit   ((u32)0x000A0000)  /* minimum IFG between frames during transmission is 56Bit */
#define ETH_InterFrameGap_48Bit   ((u32)0x000C0000)  /* minimum IFG between frames during transmission is 48Bit */
#define ETH_InterFrameGap_40Bit   ((u32)0x000E0000)  /* minimum IFG between frames during transmission is 40Bit */

#define IS_ETH_INTER_FRAME_GAP(GAP) (((GAP) == ETH_InterFrameGap_96Bit) || \
                                     ((GAP) == ETH_InterFrameGap_88Bit) || \
                                     ((GAP) == ETH_InterFrameGap_80Bit) || \
                                     ((GAP) == ETH_InterFrameGap_72Bit) || \
                                     ((GAP) == ETH_InterFrameGap_64Bit) || \
                                     ((GAP) == ETH_InterFrameGap_56Bit) || \
                                     ((GAP) == ETH_InterFrameGap_48Bit) || \
                                     ((GAP) == ETH_InterFrameGap_40Bit))

/* ETHERNET Carrier Sense ----------------------------------------------------*/
#define ETH_CarrierSense_Enable   ((u32)0x00000000)
#define ETH_CarrierSense_Disable  ((u32)0x00010000)

#define IS_ETH_CARRIER_SENSE(CMD) (((CMD) == ETH_CarrierSense_Enable) || \
                                   ((CMD) == ETH_CarrierSense_Disable))

/* ETHERNET Speed ------------------------------------------------------------*/
#define ETH_Speed_10M        ((u32)0x00000000)
#define ETH_Speed_100M       ((u32)0x00004000)

#define IS_ETH_SPEED(SPEED) (((SPEED) == ETH_Speed_10M) || \
                             ((SPEED) == ETH_Speed_100M))

/* ETHERNET Receive Own ------------------------------------------------------*/
#define ETH_ReceiveOwn_Enable     ((u32)0x00000000)
#define ETH_ReceiveOwn_Disable    ((u32)0x00002000)

#define IS_ETH_RECEIVE_OWN(CMD) (((CMD) == ETH_ReceiveOwn_Enable) || \
                                 ((CMD) == ETH_ReceiveOwn_Disable))

/* ETHERNET Loop back Mode ---------------------------------------------------*/
#define ETH_LoopbackMode_Enable        ((u32)0x00001000)
#define ETH_LoopbackMode_Disable       ((u32)0x00000000)

#define IS_ETH_LOOPBACK_MODE(CMD) (((CMD) == ETH_LoopbackMode_Enable) || \
                                   ((CMD) == ETH_LoopbackMode_Disable))

/* ETHERNET Duplex mode ------------------------------------------------------*/
#define ETH_Mode_FullDuplex       ((u32)0x00000800)
#define ETH_Mode_HalfDuplex       ((u32)0x00000000)

#define IS_ETH_DUPLEX_MODE(MODE) (((MODE) == ETH_Mode_FullDuplex) || \
                                  ((MODE) == ETH_Mode_HalfDuplex))

/* ETHERNET Checksum Offload -------------------------------------------------*/
#define ETH_ChecksumOffload_Enable     ((u32)0x00000400)
#define ETH_ChecksumOffload_Disable    ((u32)0x00000000)

#define IS_ETH_CHECKSUM_OFFLOAD(CMD) (((CMD) == ETH_ChecksumOffload_Enable) || \
                                      ((CMD) == ETH_ChecksumOffload_Disable))

/* ETHERNET Retry Transmission -----------------------------------------------*/
#define ETH_RetryTransmission_Enable   ((u32)0x00000000)
#define ETH_RetryTransmission_Disable  ((u32)0x00000200)

#define IS_ETH_RETRY_TRANSMISSION(CMD) (((CMD) == ETH_RetryTransmission_Enable) || \
                                        ((CMD) == ETH_RetryTransmission_Disable))

/* ETHERNET Automatic Pad/CRC Strip ------------------------------------------*/
#define ETH_AutomaticPadCRCStrip_Enable     ((u32)0x00000080)
#define ETH_AutomaticPadCRCStrip_Disable    ((u32)0x00000000)

#define IS_ETH_AUTOMATIC_PADCRC_STRIP(CMD) (((CMD) == ETH_AutomaticPadCRCStrip_Enable) || \
                                            ((CMD) == ETH_AutomaticPadCRCStrip_Disable))

/* ETHERNET Back-Off limit ---------------------------------------------------*/
#define ETH_BackOffLimit_10  ((u32)0x00000000)
#define ETH_BackOffLimit_8   ((u32)0x00000020)
#define ETH_BackOffLimit_4   ((u32)0x00000040)
#define ETH_BackOffLimit_1   ((u32)0x00000060)

#define IS_ETH_BACKOFF_LIMIT(LIMIT) (((LIMIT) == ETH_BackOffLimit_10) || \
                                     ((LIMIT) == ETH_BackOffLimit_8) || \
                                     ((LIMIT) == ETH_BackOffLimit_4) || \
                                     ((LIMIT) == ETH_BackOffLimit_1))

/* ETHERNET Deferral Check ---------------------------------------------------*/
#define ETH_DeferralCheck_Enable       ((u32)0x00000010)
#define ETH_DeferralCheck_Disable      ((u32)0x00000000)

#define IS_ETH_DEFERRAL_CHECK(CMD) (((CMD) == ETH_DeferralCheck_Enable) || \
                                    ((CMD) == ETH_DeferralCheck_Disable))

/* ETHERNET Receive All ------------------------------------------------------*/
#define ETH_ReceiveAll_Enable     ((u32)0x80000000)
#define ETH_ReceiveAll_Disable    ((u32)0x00000000)

#define IS_ETH_RECEIVE_ALL(CMD) (((CMD) == ETH_ReceiveAll_Enable) || \
                                 ((CMD) == ETH_ReceiveAll_Disable))

/* ETHERNET Source Addr Filter ------------------------------------------------*/
#define ETH_SourceAddrFilter_Normal_Enable       ((u32)0x00000200)
#define ETH_SourceAddrFilter_Inverse_Enable      ((u32)0x00000300)
#define ETH_SourceAddrFilter_Disable             ((u32)0x00000000)

#define IS_ETH_SOURCE_ADDR_FILTER(CMD) (((CMD) == ETH_SourceAddrFilter_Normal_Enable) || \
                                        ((CMD) == ETH_SourceAddrFilter_Inverse_Enable) || \
                                        ((CMD) == ETH_SourceAddrFilter_Disable))

/* ETHERNET Pass Control Frames ----------------------------------------------*/
#define ETH_PassControlFrames_BlockAll                ((u32)0x00000040)  /* MAC filters all control frames from reaching the application */
#define ETH_PassControlFrames_ForwardAll              ((u32)0x00000080)  /* MAC forwards all control frames to application even if they fail the Address Filter */
#define ETH_PassControlFrames_ForwardPassedAddrFilter ((u32)0x000000C0)  /* MAC forwards control frames that pass the Address Filter. */

#define IS_ETH_CONTROL_FRAMES(PASS) (((PASS) == ETH_PassControlFrames_BlockAll) || \
                                     ((PASS) == ETH_PassControlFrames_ForwardAll) || \
                                     ((PASS) == ETH_PassControlFrames_ForwardPassedAddrFilter))

/* ETHERNET Broadcast Frames Reception ---------------------------------------*/
#define ETH_BroadcastFramesReception_Enable      ((u32)0x00000000)
#define ETH_BroadcastFramesReception_Disable     ((u32)0x00000020)

#define IS_ETH_BROADCAST_FRAMES_RECEPTION(CMD) (((CMD) == ETH_BroadcastFramesReception_Enable) || \
                                                ((CMD) == ETH_BroadcastFramesReception_Disable))

/* ETHERNET Destination Addr Filter ------------------------------------------*/
#define ETH_DestinationAddrFilter_Normal    ((u32)0x00000000)
#define ETH_DestinationAddrFilter_Inverse   ((u32)0x00000008)

#define IS_ETH_DESTINATION_ADDR_FILTER(FILTER) (((FILTER) == ETH_DestinationAddrFilter_Normal) || \
                                                ((FILTER) == ETH_DestinationAddrFilter_Inverse))

/* ETHERNET Promiscuous Mode -------------------------------------------------*/
#define ETH_PromiscuousMode_Enable     ((u32)0x00000001)
#define ETH_PromiscuousMode_Disable    ((u32)0x00000000)

#define IS_ETH_PROMISCUOUS_MODE(CMD) (((CMD) == ETH_PromiscuousMode_Enable) || \
                                      ((CMD) == ETH_PromiscuousMode_Disable))

/* ETHERNET multicast frames filter --------------------------------------------*/
#define ETH_MulticastFramesFilter_PerfectHashTable    ((u32)0x00000404)
#define ETH_MulticastFramesFilter_HashTable           ((u32)0x00000004)
#define ETH_MulticastFramesFilter_Perfect             ((u32)0x00000000)
#define ETH_MulticastFramesFilter_None                ((u32)0x00000010)

#define IS_ETH_MULTICAST_FRAMES_FILTER(FILTER) (((FILTER) == ETH_MulticastFramesFilter_PerfectHashTable) || \
                                                ((FILTER) == ETH_MulticastFramesFilter_HashTable) || \
                                                ((FILTER) == ETH_MulticastFramesFilter_Perfect) || \
                                                ((FILTER) == ETH_MulticastFramesFilter_None))

/* ETHERNET unicast frames filter --------------------------------------------*/
#define ETH_UnicastFramesFilter_PerfectHashTable ((u32)0x00000402)
#define ETH_UnicastFramesFilter_HashTable        ((u32)0x00000002)
#define ETH_UnicastFramesFilter_Perfect          ((u32)0x00000000)

#define IS_ETH_UNICAST_FRAMES_FILTER(FILTER) (((FILTER) == ETH_UnicastFramesFilter_PerfectHashTable) || \
                                              ((FILTER) == ETH_UnicastFramesFilter_HashTable) || \
                                              ((FILTER) == ETH_UnicastFramesFilter_Perfect))

/* ETHERNET Pause Time ------------------------------------------------*/
#define IS_ETH_PAUSE_TIME(TIME) ((TIME) <= 0xFFFF)

/* ETHERNET Zero Quanta Pause ------------------------------------------------*/
#define ETH_ZeroQuantaPause_Enable     ((u32)0x00000000)
#define ETH_ZeroQuantaPause_Disable    ((u32)0x00000080)

#define IS_ETH_ZEROQUANTA_PAUSE(CMD) (((CMD) == ETH_ZeroQuantaPause_Enable) || \
                                      ((CMD) == ETH_ZeroQuantaPause_Disable))

/* ETHERNET Pause Low Threshold ----------------------------------------------*/
#define ETH_PauseLowThreshold_Minus4        ((u32)0x00000000)  /* Pause time minus 4 slot times */
#define ETH_PauseLowThreshold_Minus28       ((u32)0x00000010)  /* Pause time minus 28 slot times */
#define ETH_PauseLowThreshold_Minus144      ((u32)0x00000020)  /* Pause time minus 144 slot times */
#define ETH_PauseLowThreshold_Minus256      ((u32)0x00000030)  /* Pause time minus 256 slot times */

#define IS_ETH_PAUSE_LOW_THRESHOLD(THRESHOLD) (((THRESHOLD) == ETH_PauseLowThreshold_Minus4) || \
                                               ((THRESHOLD) == ETH_PauseLowThreshold_Minus28) || \
                                               ((THRESHOLD) == ETH_PauseLowThreshold_Minus144) || \
                                               ((THRESHOLD) == ETH_PauseLowThreshold_Minus256))

/* ETHERNET Unicast Pause Frame Detect ---------------------------------------*/
#define ETH_UnicastPauseFrameDetect_Enable  ((u32)0x00000008)
#define ETH_UnicastPauseFrameDetect_Disable ((u32)0x00000000)

#define IS_ETH_UNICAST_PAUSE_FRAME_DETECT(CMD) (((CMD) == ETH_UnicastPauseFrameDetect_Enable) || \
                                                ((CMD) == ETH_UnicastPauseFrameDetect_Disable))

/* ETHERNET Receive Flow Control ---------------------------------------------*/
#define ETH_ReceiveFlowControl_Enable       ((u32)0x00000004)
#define ETH_ReceiveFlowControl_Disable      ((u32)0x00000000)

#define IS_ETH_RECEIVE_FLOWCONTROL(CMD) (((CMD) == ETH_ReceiveFlowControl_Enable) || \
                                         ((CMD) == ETH_ReceiveFlowControl_Disable))

/* ETHERNET Transmit Flow Control --------------------------------------------*/
#define ETH_TransmitFlowControl_Enable      ((u32)0x00000002)
#define ETH_TransmitFlowControl_Disable     ((u32)0x00000000)

#define IS_ETH_TRANSMIT_FLOWCONTROL(CMD) (((CMD) == ETH_TransmitFlowControl_Enable) || \
                                          ((CMD) == ETH_TransmitFlowControl_Disable))

/* ETHERNET VLAN Tag Comparison ----------------------------------------------*/
#define ETH_VLANTagComparison_12Bit    ((u32)0x00010000)
#define ETH_VLANTagComparison_16Bit    ((u32)0x00000000)

#define IS_ETH_VLAN_TAG_COMPARISON(COMPARISON) (((COMPARISON) == ETH_VLANTagComparison_12Bit) || \
                                                ((COMPARISON) == ETH_VLANTagComparison_16Bit))

#define IS_ETH_VLAN_TAG_IDENTIFIER(IDENTIFIER) ((IDENTIFIER) <= 0xFFFF)

/* ETHERNET MAC Flags ---------------------------------------------------*/
#define ETH_MAC_FLAG_TST     ((u32)0x00000200)  /* Time stamp trigger flag (on MAC) */
#define ETH_MAC_FLAG_MMCT    ((u32)0x00000040)  /* MMC transmit flag  */
#define ETH_MAC_FLAG_MMCR    ((u32)0x00000020)  /* MMC receive flag */
#define ETH_MAC_FLAG_MMC     ((u32)0x00000010)  /* MMC flag (on MAC) */
#define ETH_MAC_FLAG_PMT     ((u32)0x00000008)  /* PMT flag (on MAC) */

#define IS_ETH_MAC_GET_FLAG(FLAG) (((FLAG) == ETH_MAC_FLAG_TST) || ((FLAG) == ETH_MAC_FLAG_MMCT) || \
                                   ((FLAG) == ETH_MAC_FLAG_MMCR) || ((FLAG) == ETH_MAC_FLAG_MMC) || \
                                   ((FLAG) == ETH_MAC_FLAG_PMT))

/* ETHERNET MAC Interrupts ---------------------------------------------------*/
#define ETH_MAC_IT_TST       ((u32)0x00000200)  /* Time stamp trigger interrupt (on MAC) */
#define ETH_MAC_IT_MMCT      ((u32)0x00000040)  /* MMC transmit interrupt */
#define ETH_MAC_IT_MMCR      ((u32)0x00000020)  /* MMC receive interrupt */
#define ETH_MAC_IT_MMC       ((u32)0x00000010)  /* MMC interrupt (on MAC) */
#define ETH_MAC_IT_PMT       ((u32)0x00000008)  /* PMT interrupt (on MAC) */

#define IS_ETH_MAC_IT(IT) ((((IT) & (u32)0xFFFFFDF7) == 0x00) && ((IT) != 0x00))
#define IS_ETH_MAC_GET_IT(IT) (((IT) == ETH_MAC_IT_TST) || ((IT) == ETH_MAC_IT_MMCT) || \
                               ((IT) == ETH_MAC_IT_MMCR) || ((IT) == ETH_MAC_IT_MMC) || \
                               ((IT) == ETH_MAC_IT_PMT))

/* ETHERNET MAC addresses ----------------------------------------------------*/
#define ETH_MAC_Address0     ((u32)0x00000000)
#define ETH_MAC_Address1     ((u32)0x00000008)
#define ETH_MAC_Address2     ((u32)0x00000010)
#define ETH_MAC_Address3     ((u32)0x00000018)

#define IS_ETH_MAC_ADDRESS0123(ADDRESS) (((ADDRESS) == ETH_MAC_Address0) || \
                                         ((ADDRESS) == ETH_MAC_Address1) || \
                                         ((ADDRESS) == ETH_MAC_Address2) || \
                                         ((ADDRESS) == ETH_MAC_Address3))

#define IS_ETH_MAC_ADDRESS123(ADDRESS) (((ADDRESS) == ETH_MAC_Address1) || \
                                        ((ADDRESS) == ETH_MAC_Address2) || \
                                        ((ADDRESS) == ETH_MAC_Address3))

/* ETHERNET MAC addresses filter: SA/DA filed of received frames ------------*/
#define ETH_MAC_AddressFilter_SA       ((u32)0x00000000)
#define ETH_MAC_AddressFilter_DA       ((u32)0x00000008)

#define IS_ETH_MAC_ADDRESS_FILTER(FILTER) (((FILTER) == ETH_MAC_AddressFilter_SA) || \
                                           ((FILTER) == ETH_MAC_AddressFilter_DA))

/* ETHERNET MAC addresses filter: Mask bytes ---------------------------------*/
#define ETH_MAC_AddressMask_Byte6      ((u32)0x20000000)  /* Mask MAC Address high reg bits [15:8] */
#define ETH_MAC_AddressMask_Byte5      ((u32)0x10000000)  /* Mask MAC Address high reg bits [7:0] */
#define ETH_MAC_AddressMask_Byte4      ((u32)0x08000000)  /* Mask MAC Address low reg bits [31:24] */
#define ETH_MAC_AddressMask_Byte3      ((u32)0x04000000)  /* Mask MAC Address low reg bits [23:16] */
#define ETH_MAC_AddressMask_Byte2      ((u32)0x02000000)  /* Mask MAC Address low reg bits [15:8] */
#define ETH_MAC_AddressMask_Byte1      ((u32)0x01000000)  /* Mask MAC Address low reg bits [70] */

#define IS_ETH_MAC_ADDRESS_MASK(MASK) (((MASK) == ETH_MAC_AddressMask_Byte6) || \
                                       ((MASK) == ETH_MAC_AddressMask_Byte5) || \
                                       ((MASK) == ETH_MAC_AddressMask_Byte4) || \
                                       ((MASK) == ETH_MAC_AddressMask_Byte3) || \
                                       ((MASK) == ETH_MAC_AddressMask_Byte2) || \
                                       ((MASK) == ETH_MAC_AddressMask_Byte1))

/*----------------------------------------------------------------------------*/
/*                     Ethernet DMA Desciptors defines                       */
/*----------------------------------------------------------------------------*/
/* ETHERNET DMA Tx descriptor flags  --------------------------------------------------------*/
#define IS_ETH_DMATxDESC_GET_FLAG(FLAG) (((FLAG) == ETH_DMATxDesc_OWN) || \
                                         ((FLAG) == ETH_DMATxDesc_IC) || \
                                         ((FLAG) == ETH_DMATxDesc_LS) || \
                                         ((FLAG) == ETH_DMATxDesc_FS) || \
                                         ((FLAG) == ETH_DMATxDesc_DC) || \
                                         ((FLAG) == ETH_DMATxDesc_DP) || \
                                         ((FLAG) == ETH_DMATxDesc_TTSE) || \
                                         ((FLAG) == ETH_DMATxDesc_TER) || \
                                         ((FLAG) == ETH_DMATxDesc_TCH) || \
                                         ((FLAG) == ETH_DMATxDesc_TTSS) || \
                                         ((FLAG) == ETH_DMATxDesc_IHE) || \
                                         ((FLAG) == ETH_DMATxDesc_ES) || \
                                         ((FLAG) == ETH_DMATxDesc_JT) || \
                                         ((FLAG) == ETH_DMATxDesc_FF) || \
                                         ((FLAG) == ETH_DMATxDesc_PCE) || \
                                         ((FLAG) == ETH_DMATxDesc_LCA) || \
                                         ((FLAG) == ETH_DMATxDesc_NC) || \
                                         ((FLAG) == ETH_DMATxDesc_LCO) || \
                                         ((FLAG) == ETH_DMATxDesc_EC) || \
                                         ((FLAG) == ETH_DMATxDesc_VF) || \
                                         ((FLAG) == ETH_DMATxDesc_CC) || \
                                         ((FLAG) == ETH_DMATxDesc_ED) || \
                                         ((FLAG) == ETH_DMATxDesc_UF) || \
                                         ((FLAG) == ETH_DMATxDesc_DB))

/* ETHERNET DMA Tx descriptor segment ----------------------------------------*/
#define ETH_DMATxDesc_LastSegment      ((u32)0x40000000)  /* Last Segment */
#define ETH_DMATxDesc_FirstSegment     ((u32)0x20000000)  /* First Segment */

#define IS_ETH_DMA_TXDESC_SEGMENT(SEGMENT) (((SEGMENT) == ETH_DMATxDesc_LastSegment) || \
                                            ((SEGMENT) == ETH_DMATxDesc_FirstSegment))

/* ETHERNET DMA Tx descriptor Checksum Insertion Control  --------------------*/
#define ETH_DMATxDesc_ChecksumByPass             ((u32)0x00000000)   /* Checksum engine bypass */
#define ETH_DMATxDesc_ChecksumIPV4Header         ((u32)0x00400000)   /* IPv4 header checksum insertion  */
#define ETH_DMATxDesc_ChecksumTCPUDPICMPSegment  ((u32)0x00800000)   /* TCP/UDP/ICMP checksum insertion. Pseudo header checksum is assumed to be present */
#define ETH_DMATxDesc_ChecksumTCPUDPICMPFull     ((u32)0x00C00000)   /* TCP/UDP/ICMP checksum fully in hardware including pseudo header */

#define IS_ETH_DMA_TXDESC_CHECKSUM(CHECKSUM) (((CHECKSUM) == ETH_DMATxDesc_ChecksumByPass) || \
                                              ((CHECKSUM) == ETH_DMATxDesc_ChecksumIPV4Header) || \
                                              ((CHECKSUM) == ETH_DMATxDesc_ChecksumTCPUDPICMPSegment) || \
                                              ((CHECKSUM) == ETH_DMATxDesc_ChecksumTCPUDPICMPFull))

/* ETHERNET DMA Tx Desciptor buffer size */
#define IS_ETH_DMATxDESC_BUFFER_SIZE(SIZE) ((SIZE) <= 0x1FFF)

/* ETHERNET DMA Rx descriptor flags  --------------------------------------------------------*/
#define IS_ETH_DMARxDESC_GET_FLAG(FLAG) (((FLAG) == ETH_DMARxDesc_OWN) || \
                                         ((FLAG) == ETH_DMARxDesc_AFM) || \
                                         ((FLAG) == ETH_DMARxDesc_ES) || \
                                         ((FLAG) == ETH_DMARxDesc_DE) || \
                                         ((FLAG) == ETH_DMARxDesc_SAF) || \
                                         ((FLAG) == ETH_DMARxDesc_LE) || \
                                         ((FLAG) == ETH_DMARxDesc_OE) || \
                                         ((FLAG) == ETH_DMARxDesc_VLAN) || \
                                         ((FLAG) == ETH_DMARxDesc_FS) || \
                                         ((FLAG) == ETH_DMARxDesc_LS) || \
                                         ((FLAG) == ETH_DMARxDesc_IPV4HCE) || \
                                         ((FLAG) == ETH_DMARxDesc_RxLongFrame) || \
                                         ((FLAG) == ETH_DMARxDesc_LC) || \
                                         ((FLAG) == ETH_DMARxDesc_FT) || \
                                         ((FLAG) == ETH_DMARxDesc_RWT) || \
                                         ((FLAG) == ETH_DMARxDesc_RE) || \
                                         ((FLAG) == ETH_DMARxDesc_DBE) || \
                                         ((FLAG) == ETH_DMARxDesc_CE) || \
                                         ((FLAG) == ETH_DMARxDesc_MAMPCE))

/* ETHERNET DMA Rx descriptor buffers  ---------------------------------------*/
#define ETH_DMARxDesc_Buffer1     ((u32)0x00000000)  /* DMA Rx Desc Buffer1 */
#define ETH_DMARxDesc_Buffer2     ((u32)0x00000001)  /* DMA Rx Desc Buffer2 */

#define IS_ETH_DMA_RXDESC_BUFFER(BUFFER) (((BUFFER) == ETH_DMARxDesc_Buffer1) || \
                                          ((BUFFER) == ETH_DMARxDesc_Buffer2))

/*----------------------------------------------------------------------------*/
/*                          Ethernet DMA defines                              */
/*----------------------------------------------------------------------------*/
/* ETHERNET Drop TCP/IP Checksum Error Frame ---------------------------------*/
#define ETH_DropTCPIPChecksumErrorFrame_Enable   ((u32)0x00000000)
#define ETH_DropTCPIPChecksumErrorFrame_Disable  ((u32)0x04000000)

#define IS_ETH_DROP_TCPIP_CHECKSUM_FRAME(CMD) (((CMD) == ETH_DropTCPIPChecksumErrorFrame_Enable) || \
                                               ((CMD) == ETH_DropTCPIPChecksumErrorFrame_Disable))

/* ETHERNET Receive Store Forward --------------------------------------------*/
#define ETH_ReceiveStoreForward_Enable      ((u32)0x02000000)
#define ETH_ReceiveStoreForward_Disable     ((u32)0x00000000)

#define IS_ETH_RECEIVE_STORE_FORWARD(CMD) (((CMD) == ETH_ReceiveStoreForward_Enable) || \
                                           ((CMD) == ETH_ReceiveStoreForward_Disable))

/* ETHERNET Flush Received Frame ---------------------------------------------*/
#define ETH_FlushReceivedFrame_Enable       ((u32)0x00000000)
#define ETH_FlushReceivedFrame_Disable      ((u32)0x01000000)

#define IS_ETH_FLUSH_RECEIVE_FRAME(CMD) (((CMD) == ETH_FlushReceivedFrame_Enable) || \
                                         ((CMD) == ETH_FlushReceivedFrame_Disable))

/* ETHERNET Transmit Store Forward -------------------------------------------*/
#define ETH_TransmitStoreForward_Enable     ((u32)0x00200000)
#define ETH_TransmitStoreForward_Disable    ((u32)0x00000000)

#define IS_ETH_TRANSMIT_STORE_FORWARD(CMD) (((CMD) == ETH_TransmitStoreForward_Enable) || \
                                            ((CMD) == ETH_TransmitStoreForward_Disable))

/* ETHERNET Transmit Threshold Control ---------------------------------------*/
#define ETH_TransmitThresholdControl_64Bytes     ((u32)0x00000000)  /* threshold level of the MTL Transmit FIFO is 64 Bytes */
#define ETH_TransmitThresholdControl_128Bytes    ((u32)0x00004000)  /* threshold level of the MTL Transmit FIFO is 128 Bytes */
#define ETH_TransmitThresholdControl_192Bytes    ((u32)0x00008000)  /* threshold level of the MTL Transmit FIFO is 192 Bytes */
#define ETH_TransmitThresholdControl_256Bytes    ((u32)0x0000C000)  /* threshold level of the MTL Transmit FIFO is 256 Bytes */
#define ETH_TransmitThresholdControl_40Bytes     ((u32)0x00010000)  /* threshold level of the MTL Transmit FIFO is 40 Bytes */
#define ETH_TransmitThresholdControl_32Bytes     ((u32)0x00014000)  /* threshold level of the MTL Transmit FIFO is 32 Bytes */
#define ETH_TransmitThresholdControl_24Bytes     ((u32)0x00018000)  /* threshold level of the MTL Transmit FIFO is 24 Bytes */
#define ETH_TransmitThresholdControl_16Bytes     ((u32)0x0001C000)  /* threshold level of the MTL Transmit FIFO is 16 Bytes */

#define IS_ETH_TRANSMIT_THRESHOLD_CONTROL(THRESHOLD) (((THRESHOLD) == ETH_TransmitThresholdControl_64Bytes) || \
                                                      ((THRESHOLD) == ETH_TransmitThresholdControl_128Bytes) || \
                                                      ((THRESHOLD) == ETH_TransmitThresholdControl_192Bytes) || \
                                                      ((THRESHOLD) == ETH_TransmitThresholdControl_256Bytes) || \
                                                      ((THRESHOLD) == ETH_TransmitThresholdControl_40Bytes) || \
                                                      ((THRESHOLD) == ETH_TransmitThresholdControl_32Bytes) || \
                                                      ((THRESHOLD) == ETH_TransmitThresholdControl_24Bytes) || \
                                                      ((THRESHOLD) == ETH_TransmitThresholdControl_16Bytes))

/* ETHERNET Forward Error Frames ---------------------------------------------*/
#define ETH_ForwardErrorFrames_Enable       ((u32)0x00000080)
#define ETH_ForwardErrorFrames_Disable      ((u32)0x00000000)

#define IS_ETH_FORWARD_ERROR_FRAMES(CMD) (((CMD) == ETH_ForwardErrorFrames_Enable) || \
                                          ((CMD) == ETH_ForwardErrorFrames_Disable))

/* ETHERNET Forward Undersized Good Frames -----------------------------------*/
#define ETH_ForwardUndersizedGoodFrames_Enable   ((u32)0x00000040)
#define ETH_ForwardUndersizedGoodFrames_Disable  ((u32)0x00000000)

#define IS_ETH_FORWARD_UNDERSIZED_GOOD_FRAMES(CMD) (((CMD) == ETH_ForwardUndersizedGoodFrames_Enable) || \
                                                    ((CMD) == ETH_ForwardUndersizedGoodFrames_Disable))

/* ETHERNET Receive Threshold Control ----------------------------------------*/
#define ETH_ReceiveThresholdControl_64Bytes      ((u32)0x00000000)  /* threshold level of the MTL Receive FIFO is 64 Bytes */
#define ETH_ReceiveThresholdControl_32Bytes      ((u32)0x00000008)  /* threshold level of the MTL Receive FIFO is 32 Bytes */
#define ETH_ReceiveThresholdControl_96Bytes      ((u32)0x00000010)  /* threshold level of the MTL Receive FIFO is 96 Bytes */
#define ETH_ReceiveThresholdControl_128Bytes     ((u32)0x00000018)  /* threshold level of the MTL Receive FIFO is 128 Bytes */

#define IS_ETH_RECEIVE_THRESHOLD_CONTROL(THRESHOLD) (((THRESHOLD) == ETH_ReceiveThresholdControl_64Bytes) || \
                                                     ((THRESHOLD) == ETH_ReceiveThresholdControl_32Bytes) || \
                                                     ((THRESHOLD) == ETH_ReceiveThresholdControl_96Bytes) || \
                                                     ((THRESHOLD) == ETH_ReceiveThresholdControl_128Bytes))

/* ETHERNET Second Frame Operate ---------------------------------------------*/
#define ETH_SecondFrameOperate_Enable       ((u32)0x00000004)
#define ETH_SecondFrameOperate_Disable      ((u32)0x00000000)

#define IS_ETH_SECOND_FRAME_OPERATE(CMD) (((CMD) == ETH_SecondFrameOperate_Enable) || \
                                          ((CMD) == ETH_SecondFrameOperate_Disable))

/* ETHERNET Address Aligned Beats --------------------------------------------*/
#define ETH_AddressAlignedBeats_Enable      ((u32)0x02000000)
#define ETH_AddressAlignedBeats_Disable     ((u32)0x00000000)

#define IS_ETH_ADDRESS_ALIGNED_BEATS(CMD) (((CMD) == ETH_AddressAlignedBeats_Enable) || \
                                           ((CMD) == ETH_AddressAlignedBeats_Disable))

/* ETHERNET Fixed Burst ------------------------------------------------------*/
#define ETH_FixedBurst_Enable     ((u32)0x00010000)
#define ETH_FixedBurst_Disable    ((u32)0x00000000)

#define IS_ETH_FIXED_BURST(CMD) (((CMD) == ETH_FixedBurst_Enable) || \
                                 ((CMD) == ETH_FixedBurst_Disable))

/* ETHERNET Rx DMA Burst Length ----------------------------------------------*/
#define ETH_RxDMABurstLength_1Beat     ((u32)0x00020000)  /* maximum number of beats to be transferred in one RxDMA transaction is 1 */
#define ETH_RxDMABurstLength_2Beat     ((u32)0x00040000)  /* maximum number of beats to be transferred in one RxDMA transaction is 2 */
#define ETH_RxDMABurstLength_4Beat     ((u32)0x00080000)  /* maximum number of beats to be transferred in one RxDMA transaction is 4 */
#define ETH_RxDMABurstLength_8Beat     ((u32)0x00100000)  /* maximum number of beats to be transferred in one RxDMA transaction is 8 */
#define ETH_RxDMABurstLength_16Beat    ((u32)0x00200000)  /* maximum number of beats to be transferred in one RxDMA transaction is 16 */
#define ETH_RxDMABurstLength_32Beat    ((u32)0x00400000)  /* maximum number of beats to be transferred in one RxDMA transaction is 32 */

#define ETH_RxDMABurstLength_4xPBL_4Beat    ((u32)0x01020000)  /* maximum number of beats to be transferred in one RxDMA transaction is 4 */
#define ETH_RxDMABurstLength_4xPBL_8Beat    ((u32)0x01040000)  /* maximum number of beats to be transferred in one RxDMA transaction is 8 */
#define ETH_RxDMABurstLength_4xPBL_16Beat   ((u32)0x01080000)  /* maximum number of beats to be transferred in one RxDMA transaction is 16 */
#define ETH_RxDMABurstLength_4xPBL_32Beat   ((u32)0x01100000)  /* maximum number of beats to be transferred in one RxDMA transaction is 32 */
#define ETH_RxDMABurstLength_4xPBL_64Beat   ((u32)0x01200000)  /* maximum number of beats to be transferred in one RxDMA transaction is 64 */
#define ETH_RxDMABurstLength_4xPBL_128Beat  ((u32)0x01400000)  /* maximum number of beats to be transferred in one RxDMA transaction is 128 */

#define IS_ETH_RXDMA_BURST_LENGTH(LENGTH) (((LENGTH) == ETH_RxDMABurstLength_1Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_2Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_4Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_8Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_16Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_32Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_4xPBL_4Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_4xPBL_8Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_4xPBL_16Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_4xPBL_32Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_4xPBL_64Beat) || \
                                           ((LENGTH) == ETH_RxDMABurstLength_4xPBL_128Beat))

/* ETHERNET Tx DMA Burst Length ----------------------------------------------*/
#define ETH_TxDMABurstLength_1Beat     ((u32)0x00000100)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 1 */
#define ETH_TxDMABurstLength_2Beat     ((u32)0x00000200)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 2 */
#define ETH_TxDMABurstLength_4Beat     ((u32)0x00000400)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 4 */
#define ETH_TxDMABurstLength_8Beat     ((u32)0x00000800)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 8 */
#define ETH_TxDMABurstLength_16Beat    ((u32)0x00001000)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 16 */
#define ETH_TxDMABurstLength_32Beat    ((u32)0x00002000)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 32 */

#define ETH_TxDMABurstLength_4xPBL_4Beat    ((u32)0x01000100)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 4 */
#define ETH_TxDMABurstLength_4xPBL_8Beat    ((u32)0x01000200)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 8 */
#define ETH_TxDMABurstLength_4xPBL_16Beat   ((u32)0x01000400)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 16 */
#define ETH_TxDMABurstLength_4xPBL_32Beat   ((u32)0x01000800)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 32 */
#define ETH_TxDMABurstLength_4xPBL_64Beat   ((u32)0x01001000)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 64 */
#define ETH_TxDMABurstLength_4xPBL_128Beat  ((u32)0x01002000)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 128 */

#define IS_ETH_TXDMA_BURST_LENGTH(LENGTH) (((LENGTH) == ETH_TxDMABurstLength_1Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_2Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_4Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_8Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_16Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_32Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_4xPBL_4Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_4xPBL_8Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_4xPBL_16Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_4xPBL_32Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_4xPBL_64Beat) || \
                                           ((LENGTH) == ETH_TxDMABurstLength_4xPBL_128Beat))

/* ETHERNET DMA Desciptor SkipLength */
#define IS_ETH_DMA_DESC_SKIP_LENGTH(LENGTH) ((LENGTH) <= 0x1F)

/* ETHERNET DMA Arbitration --------------------------------------------------*/
#define ETH_DMAArbitration_RoundRobin_RxTx_1_1   ((u32)0x00000000)
#define ETH_DMAArbitration_RoundRobin_RxTx_2_1   ((u32)0x00004000)
#define ETH_DMAArbitration_RoundRobin_RxTx_3_1   ((u32)0x00008000)
#define ETH_DMAArbitration_RoundRobin_RxTx_4_1   ((u32)0x0000C000)
#define ETH_DMAArbitration_RxPriorTx             ((u32)0x00000002)

#define IS_ETH_DMA_ARBITRATION_ROUNDROBIN_RXTX(RATIO) (((RATIO) == ETH_DMAArbitration_RoundRobin_RxTx_1_1) || \
                                                       ((RATIO) == ETH_DMAArbitration_RoundRobin_RxTx_2_1) || \
                                                       ((RATIO) == ETH_DMAArbitration_RoundRobin_RxTx_3_1) || \
                                                       ((RATIO) == ETH_DMAArbitration_RoundRobin_RxTx_4_1) || \
                                                       ((RATIO) == ETH_DMAArbitration_RxPriorTx))

/* ETHERNET DMA Flags ---------------------------------------------------*/
#define ETH_DMA_FLAG_TST     ((u32)0x20000000)  /* Time-stamp trigger interrupt (on DMA) */
#define ETH_DMA_FLAG_PMT     ((u32)0x10000000)  /* PMT interrupt (on DMA) */
#define ETH_DMA_FLAG_MMC     ((u32)0x08000000)  /* MMC interrupt (on DMA) */

#define ETH_DMA_FLAG_DataTransferError ((u32)0x00800000)  /* Error bits 0-Rx DMA, 1-Tx DMA */
#define ETH_DMA_FLAG_ReadWriteError    ((u32)0x01000000)  /* Error bits 0-write trnsf, 1-read transfr */
#define ETH_DMA_FLAG_AccessError       ((u32)0x02000000)  /* Error bits 0-data buffer, 1-desc. access */
#define ETH_DMA_FLAG_NIS     ((u32)0x00010000)  /* Normal interrupt summary flag */
#define ETH_DMA_FLAG_AIS     ((u32)0x00008000)  /* Abnormal interrupt summary flag */
#define ETH_DMA_FLAG_ER      ((u32)0x00004000)  /* Early receive flag */
#define ETH_DMA_FLAG_FBE     ((u32)0x00002000)  /* Fatal bus error flag */
#define ETH_DMA_FLAG_ET      ((u32)0x00000400)  /* Early transmit flag */
#define ETH_DMA_FLAG_RWT     ((u32)0x00000200)  /* Receive watchdog timeout flag */
#define ETH_DMA_FLAG_RPS     ((u32)0x00000100)  /* Receive process stopped flag */
#define ETH_DMA_FLAG_RBU     ((u32)0x00000080)  /* Receive buffer unavailable flag */
#define ETH_DMA_FLAG_R       ((u32)0x00000040)  /* Receive flag */
#define ETH_DMA_FLAG_TU      ((u32)0x00000020)  /* Underflow flag */
#define ETH_DMA_FLAG_RO      ((u32)0x00000010)  /* Overflow flag */
#define ETH_DMA_FLAG_TJT     ((u32)0x00000008)  /* Transmit jabber timeout flag */
#define ETH_DMA_FLAG_TBU     ((u32)0x00000004)  /* Transmit buffer unavailable flag */
#define ETH_DMA_FLAG_TPS     ((u32)0x00000002)  /* Transmit process stopped flag */
#define ETH_DMA_FLAG_T       ((u32)0x00000001)  /* Transmit flag */

#define IS_ETH_DMA_FLAG(FLAG) ((((FLAG) & (u32)0xFFFE1800) == 0x00) && ((FLAG) != 0x00))
#define IS_ETH_DMA_GET_FLAG(FLAG) (((FLAG) == ETH_DMA_FLAG_TST) || ((FLAG) == ETH_DMA_FLAG_PMT) || \
                                   ((FLAG) == ETH_DMA_FLAG_MMC) || ((FLAG) == ETH_DMA_FLAG_DataTransferError) || \
                                   ((FLAG) == ETH_DMA_FLAG_ReadWriteError) || ((FLAG) == ETH_DMA_FLAG_AccessError) || \
                                   ((FLAG) == ETH_DMA_FLAG_NIS) || ((FLAG) == ETH_DMA_FLAG_AIS) || \
                                   ((FLAG) == ETH_DMA_FLAG_ER) || ((FLAG) == ETH_DMA_FLAG_FBE) || \
                                   ((FLAG) == ETH_DMA_FLAG_ET) || ((FLAG) == ETH_DMA_FLAG_RWT) || \
                                   ((FLAG) == ETH_DMA_FLAG_RPS) || ((FLAG) == ETH_DMA_FLAG_RBU) || \
                                   ((FLAG) == ETH_DMA_FLAG_R) || ((FLAG) == ETH_DMA_FLAG_TU) || \
                                   ((FLAG) == ETH_DMA_FLAG_RO) || ((FLAG) == ETH_DMA_FLAG_TJT) || \
                                   ((FLAG) == ETH_DMA_FLAG_TBU) || ((FLAG) == ETH_DMA_FLAG_TPS) || \
                                   ((FLAG) == ETH_DMA_FLAG_T))

/* ETHERNET DMA Interrupts ---------------------------------------------------*/
#define ETH_DMA_IT_TST       ((u32)0x20000000)  /* Time-stamp trigger interrupt (on DMA) */
#define ETH_DMA_IT_PMT       ((u32)0x10000000)  /* PMT interrupt (on DMA) */
#define ETH_DMA_IT_MMC       ((u32)0x08000000)  /* MMC interrupt (on DMA) */

#define ETH_DMA_IT_NIS       ((u32)0x00010000)  /* Normal interrupt summary */
#define ETH_DMA_IT_AIS       ((u32)0x00008000)  /* Abnormal interrupt summary */
#define ETH_DMA_IT_ER        ((u32)0x00004000)  /* Early receive interrupt */
#define ETH_DMA_IT_FBE       ((u32)0x00002000)  /* Fatal bus error interrupt */
#define ETH_DMA_IT_ET        ((u32)0x00000400)  /* Early transmit interrupt */
#define ETH_DMA_IT_RWT       ((u32)0x00000200)  /* Receive watchdog timeout interrupt */
#define ETH_DMA_IT_RPS       ((u32)0x00000100)  /* Receive process stopped interrupt */
#define ETH_DMA_IT_RBU       ((u32)0x00000080)  /* Receive buffer unavailable interrupt */
#define ETH_DMA_IT_R         ((u32)0x00000040)  /* Receive interrupt */
#define ETH_DMA_IT_TU        ((u32)0x00000020)  /* Underflow interrupt */
#define ETH_DMA_IT_RO        ((u32)0x00000010)  /* Overflow interrupt */
#define ETH_DMA_IT_TJT       ((u32)0x00000008)  /* Transmit jabber timeout interrupt */
#define ETH_DMA_IT_TBU       ((u32)0x00000004)  /* Transmit buffer unavailable interrupt */
#define ETH_DMA_IT_TPS       ((u32)0x00000002)  /* Transmit process stopped interrupt */
#define ETH_DMA_IT_T         ((u32)0x00000001)  /* Transmit interrupt */

#define IS_ETH_DMA_IT(IT) ((((IT) & (u32)0xFFFE1800) == 0x00) && ((IT) != 0x00))
#define IS_ETH_DMA_GET_IT(IT) (((IT) == ETH_DMA_IT_TST) || ((IT) == ETH_DMA_IT_PMT) || \
                               ((IT) == ETH_DMA_IT_MMC) || ((IT) == ETH_DMA_IT_NIS) || \
                               ((IT) == ETH_DMA_IT_AIS) || ((IT) == ETH_DMA_IT_ER) || \
                               ((IT) == ETH_DMA_IT_FBE) || ((IT) == ETH_DMA_IT_ET) || \
                               ((IT) == ETH_DMA_IT_RWT) || ((IT) == ETH_DMA_IT_RPS) || \
                               ((IT) == ETH_DMA_IT_RBU) || ((IT) == ETH_DMA_IT_R) || \
                               ((IT) == ETH_DMA_IT_TU) || ((IT) == ETH_DMA_IT_RO) || \
                               ((IT) == ETH_DMA_IT_TJT) || ((IT) == ETH_DMA_IT_TBU) || \
                               ((IT) == ETH_DMA_IT_TPS) || ((IT) == ETH_DMA_IT_T))

/* ETHERNET DMA transmit process state  --------------------------------------------------------*/
#define ETH_DMA_TransmitProcess_Stopped     ((u32)0x00000000)  /* Stopped - Reset or Stop Tx Command issued */
#define ETH_DMA_TransmitProcess_Fetching    ((u32)0x00100000)  /* Running - fetching the Tx descriptor */
#define ETH_DMA_TransmitProcess_Waiting     ((u32)0x00200000)  /* Running - waiting for status */
#define ETH_DMA_TransmitProcess_Reading     ((u32)0x00300000)  /* Running - reading the data from host memory */
#define ETH_DMA_TransmitProcess_Suspended   ((u32)0x00600000)  /* Suspended - Tx Desciptor unavailabe */
#define ETH_DMA_TransmitProcess_Closing     ((u32)0x00700000)  /* Running - closing Rx descriptor */

/* ETHERNET DMA receive process state  --------------------------------------------------------*/
#define ETH_DMA_ReceiveProcess_Stopped      ((u32)0x00000000)  /* Stopped - Reset or Stop Rx Command issued */
#define ETH_DMA_ReceiveProcess_Fetching     ((u32)0x00020000)  /* Running - fetching the Rx descriptor */
#define ETH_DMA_ReceiveProcess_Waiting      ((u32)0x00060000)  /* Running - waiting for packet */
#define ETH_DMA_ReceiveProcess_Suspended    ((u32)0x00080000)  /* Suspended - Rx Desciptor unavailable */
#define ETH_DMA_ReceiveProcess_Closing      ((u32)0x000A0000)  /* Running - closing descriptor */
#define ETH_DMA_ReceiveProcess_Queuing      ((u32)0x000E0000)  /* Running - queuing the recieve frame into host memory */

/* ETHERNET DMA overflow  --------------------------------------------------------*/
#define ETH_DMA_Overflow_RxFIFOCounter      ((u32)0x10000000)  /* Overflow bit for FIFO overflow counter */
#define ETH_DMA_Overflow_MissedFrameCounter ((u32)0x00010000)  /* Overflow bit for missed frame counter */

#define IS_ETH_DMA_GET_OVERFLOW(OVERFLOW) (((OVERFLOW) == ETH_DMA_Overflow_RxFIFOCounter) || \
                                           ((OVERFLOW) == ETH_DMA_Overflow_MissedFrameCounter))

/*----------------------------------------------------------------------------*/
/*                          Ethernet PMT defines                              */
/*----------------------------------------------------------------------------*/
/* ETHERNET PMT Flags --------------------------------------------------------*/
#define ETH_PMT_FLAG_WUFFRPR      ((u32)0x80000000)  /* Wake-Up Frame Filter Register Poniter Reset */
#define ETH_PMT_FLAG_WUFR         ((u32)0x00000040)  /* Wake-Up Frame Received */
#define ETH_PMT_FLAG_MPR          ((u32)0x00000020)  /* Magic Packet Received */

#define IS_ETH_PMT_GET_FLAG(FLAG) (((FLAG) == ETH_PMT_FLAG_WUFR) || \
                                   ((FLAG) == ETH_PMT_FLAG_MPR))

/*----------------------------------------------------------------------------*/
/*                          Ethernet MMC defines                              */
/*----------------------------------------------------------------------------*/
/* ETHERNET MMC Tx Interrupts */
#define ETH_MMC_IT_TGF       ((u32)0x00200000)  /* When Tx good frame counter reaches half the maximum value */
#define ETH_MMC_IT_TGFMSC    ((u32)0x00008000)  /* When Tx good multi col counter reaches half the maximum value */
#define ETH_MMC_IT_TGFSC     ((u32)0x00004000)  /* When Tx good single col counter reaches half the maximum value */

/* ETHERNET MMC Rx Interrupts */
#define ETH_MMC_IT_RGUF      ((u32)0x10020000)  /* When Rx good unicast frames counter reaches half the maximum value */
#define ETH_MMC_IT_RFAE      ((u32)0x10000040)  /* When Rx alignment error counter reaches half the maximum value */
#define ETH_MMC_IT_RFCE      ((u32)0x10000020)  /* When Rx crc error counter reaches half the maximum value */

#define IS_ETH_MMC_IT(IT) (((((IT) & (u32)0xFFDF3FFF) == 0x00) || (((IT) & (u32)0xEFFDFF9F) == 0x00)) && \
                           ((IT) != 0x00))
#define IS_ETH_MMC_GET_IT(IT) (((IT) == ETH_MMC_IT_TGF) || ((IT) == ETH_MMC_IT_TGFMSC) || \
                               ((IT) == ETH_MMC_IT_TGFSC) || ((IT) == ETH_MMC_IT_RGUF) || \
                               ((IT) == ETH_MMC_IT_RFAE) || ((IT) == ETH_MMC_IT_RFCE))

/* ETHERNET MMC Registers */
#define ETH_MMCCR            ((u32)0x00000100)  /* MMC CR register */
#define ETH_MMCRIR           ((u32)0x00000104)  /* MMC RIR register */
#define ETH_MMCTIR           ((u32)0x00000108)  /* MMC TIR register */
#define ETH_MMCRIMR          ((u32)0x0000010C)  /* MMC RIMR register */
#define ETH_MMCTIMR          ((u32)0x00000110)  /* MMC TIMR register */
#define ETH_MMCTGFSCCR       ((u32)0x0000014C)  /* MMC TGFSCCR register */
#define ETH_MMCTGFMSCCR      ((u32)0x00000150)  /* MMC TGFMSCCR register */
#define ETH_MMCTGFCR         ((u32)0x00000168)  /* MMC TGFCR register */
#define ETH_MMCRFCECR        ((u32)0x00000194)  /* MMC RFCECR register */
#define ETH_MMCRFAECR        ((u32)0x00000198)  /* MMC RFAECR register */
#define ETH_MMCRGUFCR        ((u32)0x000001C4)  /* MMC RGUFCR register */

/* ETHERNET MMC registers */
#define IS_ETH_MMC_REGISTER(REG) (((REG) == ETH_MMCCR)  || ((REG) == ETH_MMCRIR) || \
                                  ((REG) == ETH_MMCTIR)  || ((REG) == ETH_MMCRIMR) || \
                                  ((REG) == ETH_MMCTIMR) || ((REG) == ETH_MMCTGFSCCR) || \
                                  ((REG) == ETH_MMCTGFMSCCR) || ((REG) == ETH_MMCTGFCR) || \
                                  ((REG) == ETH_MMCRFCECR) || ((REG) == ETH_MMCRFAECR) || \
                                  ((REG) == ETH_MMCRGUFCR))

/*----------------------------------------------------------------------------*/
/*                          Ethernet PTP defines                              */
/*----------------------------------------------------------------------------*/
/* ETHERNET PTP time update method -------------------------------------------*/
#define ETH_PTP_FineUpdate        ((u32)0x00000001)  /* Fine Update method */
#define ETH_PTP_CoarseUpdate      ((u32)0x00000000)  /* Coarse Update method */

#define IS_ETH_PTP_UPDATE(UPDATE) (((UPDATE) == ETH_PTP_FineUpdate) || \
                                   ((UPDATE) == ETH_PTP_CoarseUpdate))

/* ETHERNET PTP Flags --------------------------------------------------------*/
#define ETH_PTP_FLAG_TSARU        ((u32)0x00000020)  /* Addend Register Update */
#define ETH_PTP_FLAG_TSITE        ((u32)0x00000010)  /* Time Stamp Interrupt Trigger */
#define ETH_PTP_FLAG_TSSTU        ((u32)0x00000008)  /* Time Stamp Update */
#define ETH_PTP_FLAG_TSSTI        ((u32)0x00000004)  /* Time Stamp Initialize */

#define IS_ETH_PTP_GET_FLAG(FLAG) (((FLAG) == ETH_PTP_FLAG_TSARU) || \
                                   ((FLAG) == ETH_PTP_FLAG_TSITE) || \
				                   ((FLAG) == ETH_PTP_FLAG_TSSTU) || \
                                   ((FLAG) == ETH_PTP_FLAG_TSSTI))

/* ETHERNET PTP subsecond increment */
#define IS_ETH_PTP_SUBSECOND_INCREMENT(SUBSECOND) ((SUBSECOND) <= 0xFF)

/* ETHERNET PTP time sign ----------------------------------------------------*/
#define ETH_PTP_PositiveTime      ((u32)0x00000000)  /* Positive time value */
#define ETH_PTP_NegativeTime      ((u32)0x80000000)  /* Negative time value */

#define IS_ETH_PTP_TIME_SIGN(SIGN) (((SIGN) == ETH_PTP_PositiveTime) || \
                                    ((SIGN) == ETH_PTP_NegativeTime))

/* ETHERNET PTP time stamp low update */
#define IS_ETH_PTP_TIME_STAMP_UPDATE_SUBSECOND(SUBSECOND) ((SUBSECOND) <= 0x7FFFFFFF)

/* ETHERNET PTP registers */
#define ETH_PTPTSCR     ((u32)0x00000700)  /* PTP TSCR register */
#define ETH_PTPSSIR     ((u32)0x00000704)  /* PTP SSIR register */
#define ETH_PTPTSHR     ((u32)0x00000708)  /* PTP TSHR register */
#define ETH_PTPTSLR     ((u32)0x0000070C)  /* PTP TSLR register */
#define ETH_PTPTSHUR    ((u32)0x00000710)  /* PTP TSHUR register */
#define ETH_PTPTSLUR    ((u32)0x00000714)  /* PTP TSLUR register */
#define ETH_PTPTSAR     ((u32)0x00000718)  /* PTP TSAR register */
#define ETH_PTPTTHR     ((u32)0x0000071C)  /* PTP TTHR register */
#define ETH_PTPTTLR     ((u32)0x00000720)  /* PTP TTLR register */

#define IS_ETH_PTP_REGISTER(REG) (((REG) == ETH_PTPTSCR) || ((REG) == ETH_PTPSSIR) || \
                                  ((REG) == ETH_PTPTSHR) || ((REG) == ETH_PTPTSLR) || \
								  ((REG) == ETH_PTPTSHUR) || ((REG) == ETH_PTPTSLUR) || \
								  ((REG) == ETH_PTPTSAR) || ((REG) == ETH_PTPTTHR) || \
								  ((REG) == ETH_PTPTTLR))

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void ETH_DeInit(void);
u32 ETH_Init(ETH_InitTypeDef* ETH_InitStruct, u16 PHYAddress);
void ETH_StructInit(ETH_InitTypeDef* ETH_InitStruct);
void ETH_SoftwareReset(void);
FlagStatus ETH_GetSoftwareResetStatus(void);
void  ETH_Start(void);
u32 ETH_HandleTxPkt(u32 addr, u16 FrameLength);
u32 ETH_HandleRxPkt(u32 addr);


u32 ETH_GetRxPktSize(void);
void ETH_DropRxPkt(void);

/*---------------------------------  PHY  ------------------------------------*/
u16 ETH_ReadPHYRegister(u16 PHYAddress, u16 PHYReg);
u32 ETH_WritePHYRegister(u16 PHYAddress, u16 PHYReg, u16 PHYValue);
u32 ETH_PHYLoopBackCmd(u16 PHYAddress, FunctionalState NewState);
/*---------------------------------  MAC  ------------------------------------*/
void ETH_MACTransmissionCmd(FunctionalState NewState);
void ETH_MACReceptionCmd(FunctionalState NewState);
FlagStatus ETH_GetFlowControlBusyStatus(void);
void ETH_InitiatePauseControlFrame(void);
void ETH_BackPressureActivationCmd(FunctionalState NewState);
FlagStatus ETH_GetMACFlagStatus(u32 ETH_MAC_FLAG);
ITStatus ETH_GetMACITStatus(u32 ETH_MAC_IT);
void ETH_MACITConfig(u32 ETH_MAC_IT, FunctionalState NewState);
void ETH_MACAddressConfig(u32 MacAddr, u8 *Addr);
void ETH_GetMACAddress(u32 MacAddr, u8 *Addr);
void ETH_MACAddressPerfectFilterCmd(u32 MacAddr, FunctionalState NewState);
void ETH_MACAddressFilterConfig(u32 MacAddr, u32 Filter);
void ETH_MACAddressMaskBytesFilterConfig(u32 MacAddr, u32 MaskByte);
/*-----------------------  DMA Tx/Rx descriptors  ----------------------------*/
void ETH_DMATxDescChainInit(ETH_DMADESCTypeDef *DMATxDescTab, u8 *TxBuff, u32 TxBuffCount);
void ETH_DMATxDescRingInit(ETH_DMADESCTypeDef *DMATxDescTab, u8 *TxBuff1, u8 *TxBuff2, u32 TxBuffCount);
FlagStatus ETH_GetDMATxDescFlagStatus(ETH_DMADESCTypeDef *DMATxDesc, u32 ETH_DMATxDescFlag);
u32 ETH_GetDMATxDescCollisionCount(ETH_DMADESCTypeDef *DMATxDesc);
void ETH_SetDMATxDescOwnBit(ETH_DMADESCTypeDef *DMATxDesc);
void ETH_DMATxDescTransmitITConfig(ETH_DMADESCTypeDef *DMATxDesc, FunctionalState NewState);
void ETH_DMATxDescFrameSegmentConfig(ETH_DMADESCTypeDef *DMATxDesc, u32 DMATxDesc_FrameSegment);
void ETH_DMATxDescChecksumInsertionConfig(ETH_DMADESCTypeDef *DMATxDesc, u32 DMATxDesc_Checksum);
void ETH_DMATxDescCRCCmd(ETH_DMADESCTypeDef *DMATxDesc, FunctionalState NewState);
void ETH_DMATxDescEndOfRingCmd(ETH_DMADESCTypeDef *DMATxDesc, FunctionalState NewState);
void ETH_DMATxDescSecondAddressChainedCmd(ETH_DMADESCTypeDef *DMATxDesc, FunctionalState NewState);
void ETH_DMATxDescShortFramePaddingCmd(ETH_DMADESCTypeDef *DMATxDesc, FunctionalState NewState);
void ETH_DMATxDescTimeStampCmd(ETH_DMADESCTypeDef *DMATxDesc, FunctionalState NewState);
void ETH_DMATxDescBufferSizeConfig(ETH_DMADESCTypeDef *DMATxDesc, u32 BufferSize1, u32 BufferSize2);
void ETH_DMARxDescChainInit(ETH_DMADESCTypeDef *DMARxDescTab, u8 *RxBuff, u32 RxBuffCount);
void ETH_DMARxDescRingInit(ETH_DMADESCTypeDef *DMARxDescTab, u8 *RxBuff1, u8 *RxBuff2, u32 RxBuffCount);
FlagStatus ETH_GetDMARxDescFlagStatus(ETH_DMADESCTypeDef *DMARxDesc, u32 ETH_DMARxDescFlag);
void ETH_SetDMARxDescOwnBit(ETH_DMADESCTypeDef *DMARxDesc);
u32 ETH_GetDMARxDescFrameLength(ETH_DMADESCTypeDef *DMARxDesc);
void ETH_DMARxDescReceiveITConfig(ETH_DMADESCTypeDef *DMARxDesc, FunctionalState NewState);
void ETH_DMARxDescEndOfRingCmd(ETH_DMADESCTypeDef *DMARxDesc, FunctionalState NewState);
void ETH_DMARxDescSecondAddressChainedCmd(ETH_DMADESCTypeDef *DMARxDesc, FunctionalState NewState);
u32 ETH_GetDMARxDescBufferSize(ETH_DMADESCTypeDef *DMARxDesc, u32 DMARxDesc_Buffer);
/*---------------------------------  DMA  ------------------------------------*/
FlagStatus ETH_GetDMAFlagStatus(u32 ETH_DMA_FLAG);
void ETH_DMAClearFlag(u32 ETH_DMA_FLAG);
ITStatus ETH_GetDMAITStatus(u32 ETH_DMA_IT);
void ETH_DMAClearITPendingBit(u32 ETH_DMA_IT);
u32 ETH_GetTransmitProcessState(void);
u32 ETH_GetReceiveProcessState(void);
void ETH_FlushTransmitFIFO(void);
FlagStatus ETH_GetFlushTransmitFIFOStatus(void);
void ETH_DMATransmissionCmd(FunctionalState NewState);
void ETH_DMAReceptionCmd(FunctionalState NewState);
void ETH_DMAITConfig(u32 ETH_DMA_IT, FunctionalState NewState);
FlagStatus ETH_GetDMAOverflowStatus(u32 ETH_DMA_Overflow);
u32 ETH_GetRxOverflowMissedFrameCounter(void);
u32 ETH_GetBufferUnavailableMissedFrameCounter(void);
u32 ETH_GetCurrentTxDescStartAddress(void);
u32 ETH_GetCurrentRxDescStartAddress(void);
u32 ETH_GetCurrentTxBufferAddress(void);
u32 ETH_GetCurrentRxBufferAddress(void);
void ETH_ResumeDMATransmission(void);
void ETH_ResumeDMAReception(void);
/*---------------------------------  PMT  ------------------------------------*/
void ETH_ResetWakeUpFrameFilterRegisterPointer(void);
void ETH_SetWakeUpFrameFilterRegister(u32 *Buffer);
void ETH_GlobalUnicastWakeUpCmd(FunctionalState NewState);
FlagStatus ETH_GetPMTFlagStatus(u32 ETH_PMT_FLAG);
void ETH_WakeUpFrameDetectionCmd(FunctionalState NewState);
void ETH_MagicPacketDetectionCmd(FunctionalState NewState);
void ETH_PowerDownCmd(FunctionalState NewState);
/*---------------------------------  MMC  ------------------------------------*/
void ETH_MMCCounterFreezeCmd(FunctionalState NewState);
void ETH_MMCResetOnReadCmd(FunctionalState NewState);
void ETH_MMCCounterRolloverCmd(FunctionalState NewState);
void ETH_MMCCountersReset(void);
void ETH_MMCITConfig(u32 ETH_MMC_IT, FunctionalState NewState);
ITStatus ETH_GetMMCITStatus(u32 ETH_MMC_IT);
u32 ETH_GetMMCRegister(u32 ETH_MMCReg);
/*---------------------------------  PTP  ------------------------------------*/
u32 ETH_HandlePTPTxPkt(u8 *ppkt, u16 FrameLength, u32 *PTPTxTab);
u32 ETH_HandlePTPRxPkt(u8 *ppkt, u32 *PTPRxTab);
void ETH_DMAPTPTxDescChainInit(ETH_DMADESCTypeDef *DMATxDescTab, ETH_DMADESCTypeDef *DMAPTPTxDescTab, u8* TxBuff, u32 TxBuffCount);
void ETH_DMAPTPRxDescChainInit(ETH_DMADESCTypeDef *DMARxDescTab, ETH_DMADESCTypeDef *DMAPTPRxDescTab, u8 *RxBuff, u32 RxBuffCount);
void ETH_EnablePTPTimeStampAddend(void);
void ETH_EnablePTPTimeStampInterruptTrigger(void);
void ETH_EnablePTPTimeStampUpdate(void);
void ETH_InitializePTPTimeStamp(void);
void ETH_PTPUpdateMethodConfig(u32 UpdateMethod);
void ETH_PTPTimeStampCmd(FunctionalState NewState);
FlagStatus ETH_GetPTPFlagStatus(u32 ETH_PTP_FLAG);
void ETH_SetPTPSubSecondIncrement(u32 SubSecondValue);
void ETH_SetPTPTimeStampUpdate(u32 Sign, u32 SecondValue, u32 SubSecondValue);
void ETH_SetPTPTimeStampAddend(u32 Value);
void ETH_SetPTPTargetTime(u32 HighValue, u32 LowValue);
u32 ETH_GetPTPRegister(u32 ETH_PTPReg);

#endif /* __STM32FXXX_ETH_H */

/******************* (C) COPYRIGHT 2008 STMicroelectronics *****END OF FILE****/
