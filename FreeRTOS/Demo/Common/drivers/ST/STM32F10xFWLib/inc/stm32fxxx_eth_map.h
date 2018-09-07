/******************** (C) COPYRIGHT 2008 STMicroelectronics ********************
* File Name          : stm32fxxx_eth_map.h
* Author             : MCD Application Team
* Version            : VX.Y.Z
* Date               : mm/dd/2008
* Description        : This file contains all ETHERNET peripheral register's
*                      definitions and memory mapping.
********************************************************************************
* THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32FXXX_ETH_MAP_H
#define __STM32FXXX_ETH_MAP_H

#ifndef EXT
  #define EXT extern
#endif /* EXT */

/* Includes ------------------------------------------------------------------*/

#include "stm32fxxx_eth_conf.h"
#include "stm32f10x_type.h"

/* Exported types ------------------------------------------------------------*/
/******************************************************************************/
/*                Ethernet Peripheral registers structures                    */
/******************************************************************************/

typedef struct
{
  vu32 MACCR;
  vu32 MACFFR;
  vu32 MACHTHR;
  vu32 MACHTLR;
  vu32 MACMIIAR;
  vu32 MACMIIDR;
  vu32 MACFCR;
  vu32 MACVLANTR;
  vu32 RESERVED0[2];
  vu32 MACRWUFFR;
  vu32 MACPMTCSR;
  vu32 RESERVED1[2];
  vu32 MACSR;
  vu32 MACIMR;
  vu32 MACA0HR;
  vu32 MACA0LR;
  vu32 MACA1HR;
  vu32 MACA1LR;
  vu32 MACA2HR;
  vu32 MACA2LR;
  vu32 MACA3HR;
  vu32 MACA3LR;
} ETH_MAC_TypeDef;

typedef struct
{
  vu32 MMCCR;
  vu32 MMCRIR;
  vu32 MMCTIR;
  vu32 MMCRIMR;
  vu32 MMCTIMR;
  vu32 RESERVED0[14];
  vu32 MMCTGFSCCR;
  vu32 MMCTGFMSCCR;
  vu32 RESERVED1[5];
  vu32 MMCTGFCR;
  vu32 RESERVED2[10];
  vu32 MMCRFCECR;
  vu32 MMCRFAER;
  vu32 RESERVED3[10];
  vu32 MMCRGUFCR;
} ETH_MMC_TypeDef;

typedef struct
{
  vu32 PTPTSCR;
  vu32 PTPSSIR;
  vu32 PTPTSHR;
  vu32 PTPTSLR;
  vu32 PTPTSHUR;
  vu32 PTPTSLUR;
  vu32 PTPTSAR;
  vu32 PTPTTHR;
  vu32 PTPTTLR;
} ETH_PTP_TypeDef;

typedef struct
{
  vu32 DMABMR;
  vu32 DMATPDR;
  vu32 DMARPDR;
  vu32 DMARDLAR;
  vu32 DMATDLAR;
  vu32 DMASR;
  vu32 DMAOMR;
  vu32 DMAIER;
  vu32 DMAMFBOCR;
  vu32 RESERVED0[9];
  vu32 DMACHTDR;
  vu32 DMACHRDR;
  vu32 DMACHTBAR;
  vu32 DMACHRBAR;
} ETH_DMA_TypeDef;

/******************************************************************************/
/*                Ethernet MAC Registers bits definitions                     */
/******************************************************************************/
//#define  IPNAME_REGNAME_BITNAME   /* BIT MASK */

/* Bit definition for Ethernet MAC Control Register register */
#define ETH_MACCR_WD      ((u32)0x00800000)  /* Watchdog disable */
#define ETH_MACCR_JD      ((u32)0x00400000)  /* Jabber disable */
#define ETH_MACCR_JFE     ((u32)0x00100000)  /* Jumbo frame enable */
#define ETH_MACCR_IFG     ((u32)0x000E0000)  /* Inter-frame gap */
  #define ETH_MACCR_IFG_96Bit     ((u32)0x00000000)  /* Minimum IFG between frames during transmission is 96Bit */
  #define ETH_MACCR_IFG_88Bit     ((u32)0x00020000)  /* Minimum IFG between frames during transmission is 88Bit */
  #define ETH_MACCR_IFG_80Bit     ((u32)0x00040000)  /* Minimum IFG between frames during transmission is 80Bit */
  #define ETH_MACCR_IFG_72Bit     ((u32)0x00060000)  /* Minimum IFG between frames during transmission is 72Bit */
  #define ETH_MACCR_IFG_64Bit     ((u32)0x00080000)  /* Minimum IFG between frames during transmission is 64Bit */
  #define ETH_MACCR_IFG_56Bit     ((u32)0x000A0000)  /* Minimum IFG between frames during transmission is 56Bit */
  #define ETH_MACCR_IFG_48Bit     ((u32)0x000C0000)  /* Minimum IFG between frames during transmission is 48Bit */
  #define ETH_MACCR_IFG_40Bit     ((u32)0x000E0000)  /* Minimum IFG between frames during transmission is 40Bit */
#define ETH_MACCR_CSD     ((u32)0x00010000)  /* Carrier sense disable (during transmission) */
#define ETH_MACCR_FES     ((u32)0x00004000)  /* Fast ethernet speed */
#define ETH_MACCR_ROD     ((u32)0x00002000)  /* Receive own disable */
#define ETH_MACCR_LM      ((u32)0x00001000)  /* loopback mode */
#define ETH_MACCR_DM      ((u32)0x00000800)  /* Duplex mode */
#define ETH_MACCR_IPCO    ((u32)0x00000400)  /* IP Checksum offload */
#define ETH_MACCR_RD      ((u32)0x00000200)  /* Retry disable */
#define ETH_MACCR_APCS    ((u32)0x00000080)  /* Automatic Pad/CRC stripping */
#define ETH_MACCR_BL      ((u32)0x00000060)  /* Back-off limit: random integer number (r) of slot time delays before rescheduling
                                                       a transmission attempt during retries after a collision: 0 =< r <2^k */
  #define ETH_MACCR_BL_10    ((u32)0x00000000)  /* k = min (n, 10) */
  #define ETH_MACCR_BL_8     ((u32)0x00000020)  /* k = min (n, 8) */
  #define ETH_MACCR_BL_4     ((u32)0x00000040)  /* k = min (n, 4) */
  #define ETH_MACCR_BL_1     ((u32)0x00000060)  /* k = min (n, 1) */
#define ETH_MACCR_DC      ((u32)0x00000010)  /* Defferal check */
#define ETH_MACCR_TE      ((u32)0x00000008)  /* Transmitter enable */
#define ETH_MACCR_RE      ((u32)0x00000004)  /* Receiver enable */

/* Bit definition for Ethernet MAC Frame Filter Register */
#define ETH_MACFFR_RA     ((u32)0x80000000)  /* Receive all */
#define ETH_MACFFR_HPF    ((u32)0x00000400)  /* Hash or perfect filter */
#define ETH_MACFFR_SAF    ((u32)0x00000200)  /* Source address filter enable */
#define ETH_MACFFR_SAIF   ((u32)0x00000100)  /* SA inverse filtering */
#define ETH_MACFFR_PCF    ((u32)0x000000C0)  /* Pass control frames: 3 cases */
  #define ETH_MACFFR_PCF_BlockAll                ((u32)0x00000040)  /* MAC filters all control frames from reaching the application */
  #define ETH_MACFFR_PCF_ForwardAll              ((u32)0x00000080)  /* MAC forwards all control frames to application even if they fail the Address Filter */
  #define ETH_MACFFR_PCF_ForwardPassedAddrFilter ((u32)0x000000C0)  /* MAC forwards control frames that pass the Address Filter. */
#define ETH_MACFFR_BFD    ((u32)0x00000020)  /* Broadcast frame disable */
#define ETH_MACFFR_PAM 	  ((u32)0x00000010)  /* Pass all mutlicast */
#define ETH_MACFFR_DAIF   ((u32)0x00000008)  /* DA Inverse filtering */
#define ETH_MACFFR_HM     ((u32)0x00000004)  /* Hash multicast */
#define ETH_MACFFR_HU     ((u32)0x00000002)  /* Hash unicast */
#define ETH_MACFFR_PM     ((u32)0x00000001)  /* Promiscuous mode */

/* Bit definition for Ethernet MAC Hash Table High Register */
#define ETH_MACHTHR_HTH   ((u32)0xFFFFFFFF)  /* Hash table high */

/* Bit definition for Ethernet MAC Hash Table Low Register */
#define ETH_MACHTLR_HTL   ((u32)0xFFFFFFFF)  /* Hash table low */

/* Bit definition for Ethernet MAC MII Address Register */
#define ETH_MACMIIAR_PA   ((u32)0x0000F800)  /* Physical layer address */
#define ETH_MACMIIAR_MR   ((u32)0x000007C0)  /* MII register in the selected PHY */
#define ETH_MACMIIAR_CR   ((u32)0x0000001C)  /* CR clock range: 6 cases */
  #define ETH_MACMIIAR_CR_Div42   ((u32)0x00000000)  /* HCLK:60-72 MHz; MDC clock= HCLK/42 */
  #define ETH_MACMIIAR_CR_Div16   ((u32)0x00000008)  /* HCLK:20-35 MHz; MDC clock= HCLK/16 */
  #define ETH_MACMIIAR_CR_Div26   ((u32)0x0000000C)  /* HCLK:35-60 MHz; MDC clock= HCLK/26 */
#define ETH_MACMIIAR_MW   ((u32)0x00000002)  /* MII write */
#define ETH_MACMIIAR_MB   ((u32)0x00000001)  /* MII busy */

/* Bit definition for Ethernet MAC MII Data Register */
#define ETH_MACMIIDR_MD   ((u32)0x0000FFFF)  /* MII data: read/write data from/to PHY */

/* Bit definition for Ethernet MAC Flow Control Register */
#define ETH_MACFCR_PT     ((u32)0xFFFF0000)  /* Pause time */
#define ETH_MACFCR_ZQPD   ((u32)0x00000080)  /* Zero-quanta pause disable */
#define ETH_MACFCR_PLT    ((u32)0x00000030)  /* Pause low threshold: 4 cases */
  #define ETH_MACFCR_PLT_Minus4   ((u32)0x00000000)  /* Pause time minus 4 slot times */
  #define ETH_MACFCR_PLT_Minus28  ((u32)0x00000010)  /* Pause time minus 28 slot times */
  #define ETH_MACFCR_PLT_Minus144 ((u32)0x00000020)  /* Pause time minus 144 slot times */
  #define ETH_MACFCR_PLT_Minus256 ((u32)0x00000030)  /* Pause time minus 256 slot times */
#define ETH_MACFCR_UPFD   ((u32)0x00000008)  /* Unicast pause frame detect */
#define ETH_MACFCR_RFCE   ((u32)0x00000004)  /* Receive flow control enable */
#define ETH_MACFCR_TFCE   ((u32)0x00000002)  /* Transmit flow control enable */
#define ETH_MACFCR_FCBBPA ((u32)0x00000001)  /* Flow control busy/backpressure activate */

/* Bit definition for Ethernet MAC VLAN Tag Register */
#define ETH_MACVLANTR_VLANTC ((u32)0x00010000)  /* 12-bit VLAN tag comparison */
#define ETH_MACVLANTR_VLANTI ((u32)0x0000FFFF)  /* VLAN tag identifier (for receive frames) */

/* Bit definition for Ethernet MAC Remote Wake-UpFrame Filter Register */
#define ETH_MACRWUFFR_D   ((u32)0xFFFFFFFF)  /* Wake-up frame filter register data */
/* Eight sequential Writes to this address (offset 0x28) will write all Wake-UpFrame Filter Registers.
   Eight sequential Reads from this address (offset 0x28) will read all Wake-UpFrame Filter Registers. */
/* Wake-UpFrame Filter Reg0 : Filter 0 Byte Mask
   Wake-UpFrame Filter Reg1 : Filter 1 Byte Mask
   Wake-UpFrame Filter Reg2 : Filter 2 Byte Mask
   Wake-UpFrame Filter Reg3 : Filter 3 Byte Mask
   Wake-UpFrame Filter Reg4 : RSVD - Filter3 Command - RSVD - Filter2 Command -
                              RSVD - Filter1 Command - RSVD - Filter0 Command
   Wake-UpFrame Filter Re5 : Filter3 Offset - Filter2 Offset - Filter1 Offset - Filter0 Offset
   Wake-UpFrame Filter Re6 : Filter1 CRC16 - Filter0 CRC16
   Wake-UpFrame Filter Re7 : Filter3 CRC16 - Filter2 CRC16 */

/* Bit definition for Ethernet MAC PMT Control and Status Register */
#define ETH_MACPMTCSR_WFFRPR ((u32)0x80000000)  /* Wake-Up Frame Filter Register Pointer Reset */
#define ETH_MACPMTCSR_GU     ((u32)0x00000200)  /* Global Unicast */
#define ETH_MACPMTCSR_WFR    ((u32)0x00000040)  /* Wake-Up Frame Received */
#define ETH_MACPMTCSR_MPR    ((u32)0x00000020)  /* Magic Packet Received */
#define ETH_MACPMTCSR_WFE    ((u32)0x00000004)  /* Wake-Up Frame Enable */
#define ETH_MACPMTCSR_MPE    ((u32)0x00000002)  /* Magic Packet Enable */
#define ETH_MACPMTCSR_PD     ((u32)0x00000001)  /* Power Down */

/* Bit definition for Ethernet MAC Status Register */
#define ETH_MACSR_TSTS      ((u32)0x00000200)  /* Time stamp trigger status */
#define ETH_MACSR_MMCTS     ((u32)0x00000040)  /* MMC transmit status */
#define ETH_MACSR_MMMCRS    ((u32)0x00000020)  /* MMC receive status */
#define ETH_MACSR_MMCS      ((u32)0x00000010)  /* MMC status */
#define ETH_MACSR_PMTS      ((u32)0x00000008)  /* PMT status */

/* Bit definition for Ethernet MAC Interrupt Mask Register */
#define ETH_MACIMR_TSTIM     ((u32)0x00000200)  /* Time stamp trigger interrupt mask */
#define ETH_MACIMR_PMTIM     ((u32)0x00000008)  /* PMT interrupt mask */

/* Bit definition for Ethernet MAC Address0 High Register */
#define ETH_MACA0HR_MACA0H   ((u32)0x0000FFFF)  /* MAC address0 high */

/* Bit definition for Ethernet MAC Address0 Low Register */
#define ETH_MACA0LR_MACA0L   ((u32)0xFFFFFFFF)  /* MAC address0 low */

/* Bit definition for Ethernet MAC Address1 High Register */
#define ETH_MACA1HR_AE       ((u32)0x80000000)  /* Address enable */
#define ETH_MACA1HR_SA       ((u32)0x40000000)  /* Source address */
#define ETH_MACA1HR_MBC      ((u32)0x3F000000)  /* Mask byte control: bits to mask for comparison of the MAC Address bytes */
  #define ETH_MACA1HR_MBC_HBits15_8    ((u32)0x20000000)  /* Mask MAC Address high reg bits [15:8] */
  #define ETH_MACA1HR_MBC_HBits7_0     ((u32)0x10000000)  /* Mask MAC Address high reg bits [7:0] */
  #define ETH_MACA1HR_MBC_LBits31_24   ((u32)0x08000000)  /* Mask MAC Address low reg bits [31:24] */
  #define ETH_MACA1HR_MBC_LBits23_16   ((u32)0x04000000)  /* Mask MAC Address low reg bits [23:16] */
  #define ETH_MACA1HR_MBC_LBits15_8    ((u32)0x02000000)  /* Mask MAC Address low reg bits [15:8] */
  #define ETH_MACA1HR_MBC_LBits7_0     ((u32)0x01000000)  /* Mask MAC Address low reg bits [7:0] */
#define ETH_MACA1HR_MACA1H   ((u32)0x0000FFFF)  /* MAC address1 high */

/* Bit definition for Ethernet MAC Address1 Low Register */
#define ETH_MACA1LR_MACA1L   ((u32)0xFFFFFFFF)  /* MAC address1 low */

/* Bit definition for Ethernet MAC Address2 High Register */
#define ETH_MACA2HR_AE       ((u32)0x80000000)  /* Address enable */
#define ETH_MACA2HR_SA       ((u32)0x40000000)  /* Source address */
#define ETH_MACA2HR_MBC      ((u32)0x3F000000)  /* Mask byte control */
  #define ETH_MACA2HR_MBC_HBits15_8    ((u32)0x20000000)  /* Mask MAC Address high reg bits [15:8] */
  #define ETH_MACA2HR_MBC_HBits7_0     ((u32)0x10000000)  /* Mask MAC Address high reg bits [7:0] */
  #define ETH_MACA2HR_MBC_LBits31_24   ((u32)0x08000000)  /* Mask MAC Address low reg bits [31:24] */
  #define ETH_MACA2HR_MBC_LBits23_16   ((u32)0x04000000)  /* Mask MAC Address low reg bits [23:16] */
  #define ETH_MACA2HR_MBC_LBits15_8    ((u32)0x02000000)  /* Mask MAC Address low reg bits [15:8] */
  #define ETH_MACA2HR_MBC_LBits7_0     ((u32)0x01000000)  /* Mask MAC Address low reg bits [70] */
#define ETH_MACA2HR_MACA2H   ((u32)0x0000FFFF)  /* MAC address1 high */

/* Bit definition for Ethernet MAC Address2 Low Register */
#define ETH_MACA2LR_MACA2L   ((u32)0xFFFFFFFF)  /* MAC address2 low */

/* Bit definition for Ethernet MAC Address3 High Register */
#define ETH_MACA3HR_AE       ((u32)0x80000000)  /* Address enable */
#define ETH_MACA3HR_SA       ((u32)0x40000000)  /* Source address */
#define ETH_MACA3HR_MBC      ((u32)0x3F000000)  /* Mask byte control */
  #define ETH_MACA2HR_MBC_HBits15_8    ((u32)0x20000000)  /* Mask MAC Address high reg bits [15:8] */
  #define ETH_MACA2HR_MBC_HBits7_0     ((u32)0x10000000)  /* Mask MAC Address high reg bits [7:0] */
  #define ETH_MACA2HR_MBC_LBits31_24   ((u32)0x08000000)  /* Mask MAC Address low reg bits [31:24] */
  #define ETH_MACA2HR_MBC_LBits23_16   ((u32)0x04000000)  /* Mask MAC Address low reg bits [23:16] */
  #define ETH_MACA2HR_MBC_LBits15_8    ((u32)0x02000000)  /* Mask MAC Address low reg bits [15:8] */
  #define ETH_MACA2HR_MBC_LBits7_0     ((u32)0x01000000)  /* Mask MAC Address low reg bits [70] */
#define ETH_MACA3HR_MACA3H   ((u32)0x0000FFFF)  /* MAC address3 high */

/* Bit definition for Ethernet MAC Address3 Low Register */
#define ETH_MACA3LR_MACA3L   ((u32)0xFFFFFFFF)  /* MAC address3 low */

/******************************************************************************/
/*                Ethernet MMC Registers bits definition                      */
/******************************************************************************/

/* Bit definition for Ethernet MMC Contol Register */
#define ETH_MMCCR_MCF        ((u32)0x00000008)  /* MMC Counter Freeze */
#define ETH_MMCCR_ROR        ((u32)0x00000004)  /* Reset on Read */
#define ETH_MMCCR_CSR        ((u32)0x00000002)  /* Counter Stop Rollover */
#define ETH_MMCCR_CR         ((u32)0x00000001)  /* Counters Reset */

/* Bit definition for Ethernet MMC Receive Interrupt Register */
#define ETH_MMCRIR_RGUFS     ((u32)0x00020000)  /* Set when Rx good unicast frames counter reaches half the maximum value */
#define ETH_MMCRIR_RFAES     ((u32)0x00000040)  /* Set when Rx alignment error counter reaches half the maximum value */
#define ETH_MMCRIR_RFCES     ((u32)0x00000020)  /* Set when Rx crc error counter reaches half the maximum value */

/* Bit definition for Ethernet MMC Transmit Interrupt Register */
#define ETH_MMCTIR_TGFS      ((u32)0x00200000)  /* Set when Tx good frame count counter reaches half the maximum value */
#define ETH_MMCTIR_TGFMSCS   ((u32)0x00008000)  /* Set when Tx good multi col counter reaches half the maximum value */
#define ETH_MMCTIR_TGFSCS    ((u32)0x00004000)  /* Set when Tx good single col counter reaches half the maximum value */

/* Bit definition for Ethernet MMC Receive Interrupt Mask Register */
#define ETH_MMCRIMR_RGUFM    ((u32)0x00020000)  /* Mask the interrupt when Rx good unicast frames counter reaches half the maximum value */
#define ETH_MMCRIMR_RFAEM    ((u32)0x00000040)  /* Mask the interrupt when when Rx alignment error counter reaches half the maximum value */
#define ETH_MMCRIMR_RFCEM    ((u32)0x00000020)  /* Mask the interrupt when Rx crc error counter reaches half the maximum value */

/* Bit definition for Ethernet MMC Transmit Interrupt Mask Register */
#define ETH_MMCTIMR_TGFM     ((u32)0x00200000)  /* Mask the interrupt when Tx good frame count counter reaches half the maximum value */
#define ETH_MMCTIMR_TGFMSCM  ((u32)0x00008000)  /* Mask the interrupt when Tx good multi col counter reaches half the maximum value */
#define ETH_MMCTIMR_TGFSCM   ((u32)0x00004000)  /* Mask the interrupt when Tx good single col counter reaches half the maximum value */

/* Bit definition for Ethernet MMC Transmitted Good Frames after Single Collision Counter Register */
#define ETH_MMCTGFSCCR_TGFSCC     ((u32)0xFFFFFFFF)  /* Number of successfully transmitted frames after a single collision in Half-duplex mode. */

/* Bit definition for Ethernet MMC Transmitted Good Frames after More than a Single Collision Counter Register */
#define ETH_MMCTGFMSCCR_TGFMSCC   ((u32)0xFFFFFFFF)  /* Number of successfully transmitted frames after more than a single collision in Half-duplex mode. */

/* Bit definition for Ethernet MMC Transmitted Good Frames Counter Register */
#define ETH_MMCTGFCR_TGFC    ((u32)0xFFFFFFFF)  /* Number of good frames transmitted. */

/* Bit definition for Ethernet MMC Received Frames with CRC Error Counter Register */
#define ETH_MMCRFCECR_RFCEC  ((u32)0xFFFFFFFF)  /* Number of frames received with CRC error. */

/* Bit definition for Ethernet MMC Received Frames with Alignement Error Counter Register */
#define ETH_MMCRFAECR_RFAEC  ((u32)0xFFFFFFFF)  /* Number of frames received with alignment (dribble) error */

/* Bit definition for Ethernet MMC Received Good Unicast Frames Counter Register */
#define ETH_MMCRGUFCR_RGUFC  ((u32)0xFFFFFFFF)  /* Number of good unicast frames received. */

/******************************************************************************/
/*               Ethernet PTP Registers bits definition                       */
/******************************************************************************/

/* Bit definition for Ethernet PTP Time Stamp Contol Register */
#define ETH_PTPTSCR_TSARU    ((u32)0x00000020)  /* Addend register update */
#define ETH_PTPTSCR_TSITE    ((u32)0x00000010)  /* Time stamp interrupt trigger enable */
#define ETH_PTPTSCR_TSSTU    ((u32)0x00000008)  /* Time stamp update */
#define ETH_PTPTSCR_TSSTI    ((u32)0x00000004)  /* Time stamp initialize */
#define ETH_PTPTSCR_TSFCU    ((u32)0x00000002)  /* Time stamp fine or coarse update */
#define ETH_PTPTSCR_TSE      ((u32)0x00000001)  /* Time stamp enable */

/* Bit definition for Ethernet PTP Sub-Second Increment Register */
#define ETH_PTPSSIR_STSSI    ((u32)0x000000FF)  /* System time Sub-second increment value */

/* Bit definition for Ethernet PTP Time Stamp High Register */
#define ETH_PTPTSHR_STS      ((u32)0xFFFFFFFF)  /* System Time second */

/* Bit definition for Ethernet PTP Time Stamp Low Register */
#define ETH_PTPTSLR_STPNS    ((u32)0x80000000)  /* System Time Positive or negative time */
#define ETH_PTPTSLR_STSS     ((u32)0x7FFFFFFF)  /* System Time sub-seconds */

/* Bit definition for Ethernet PTP Time Stamp High Update Register */
#define ETH_PTPTSHUR_TSUS    ((u32)0xFFFFFFFF)  /* Time stamp update seconds */

/* Bit definition for Ethernet PTP Time Stamp Low Update Register */
#define ETH_PTPTSLUR_TSUPNS  ((u32)0x80000000)  /* Time stamp update Positive or negative time */
#define ETH_PTPTSLUR_TSUSS   ((u32)0x7FFFFFFF)  /* Time stamp update sub-seconds */

/* Bit definition for Ethernet PTP Time Stamp Addend Register */
#define ETH_PTPTSAR_TSA      ((u32)0xFFFFFFFF)  /* Time stamp addend */

/* Bit definition for Ethernet PTP Target Time High Register */
#define ETH_PTPTTHR_TTSH     ((u32)0xFFFFFFFF)  /* Target time stamp high */

/* Bit definition for Ethernet PTP Target Time Low Register */
#define ETH_PTPTTLR_TTSL     ((u32)0xFFFFFFFF)  /* Target time stamp low */

/******************************************************************************/
/*                 Ethernet DMA Registers bits definition                     */
/******************************************************************************/

/* Bit definition for Ethernet DMA Bus Mode Register */
#define ETH_DMABMR_AAB       ((u32)0x02000000)  /* Address-Aligned beats */
#define ETH_DMABMR_FPM        ((u32)0x01000000)  /* 4xPBL mode */
#define ETH_DMABMR_USP       ((u32)0x00800000)  /* Use separate PBL */
#define ETH_DMABMR_RDP       ((u32)0x007E0000)  /* RxDMA PBL */
  /* Values to be confirmed: maybe they are inversed */
  #define ETH_DMABMR_RDP_1Beat    ((u32)0x00020000)  /* maximum number of beats to be transferred in one RxDMA transaction is 1 */
  #define ETH_DMABMR_RDP_2Beat    ((u32)0x00040000)  /* maximum number of beats to be transferred in one RxDMA transaction is 2 */
  #define ETH_DMABMR_RDP_4Beat    ((u32)0x00080000)  /* maximum number of beats to be transferred in one RxDMA transaction is 4 */
  #define ETH_DMABMR_RDP_8Beat    ((u32)0x00100000)  /* maximum number of beats to be transferred in one RxDMA transaction is 8 */
  #define ETH_DMABMR_RDP_16Beat   ((u32)0x00200000)  /* maximum number of beats to be transferred in one RxDMA transaction is 16 */
  #define ETH_DMABMR_RDP_32Beat   ((u32)0x00400000)  /* maximum number of beats to be transferred in one RxDMA transaction is 32 */
  #define ETH_DMABMR_RDP_4xPBL_4Beat   ((u32)0x01020000)  /* maximum number of beats to be transferred in one RxDMA transaction is 4 */
  #define ETH_DMABMR_RDP_4xPBL_8Beat   ((u32)0x01040000)  /* maximum number of beats to be transferred in one RxDMA transaction is 8 */
  #define ETH_DMABMR_RDP_4xPBL_16Beat  ((u32)0x01080000)  /* maximum number of beats to be transferred in one RxDMA transaction is 16 */
  #define ETH_DMABMR_RDP_4xPBL_32Beat  ((u32)0x01100000)  /* maximum number of beats to be transferred in one RxDMA transaction is 32 */
  #define ETH_DMABMR_RDP_4xPBL_64Beat  ((u32)0x01200000)  /* maximum number of beats to be transferred in one RxDMA transaction is 64 */
  #define ETH_DMABMR_RDP_4xPBL_128Beat ((u32)0x01400000)  /* maximum number of beats to be transferred in one RxDMA transaction is 128 */
#define ETH_DMABMR_FB        ((u32)0x00010000)  /* Fixed Burst */
#define ETH_DMABMR_RTPR      ((u32)0x0000C000)  /* Rx Tx priority ratio */
  #define ETH_DMABMR_RTPR_1_1     ((u32)0x00000000)  /* Rx Tx priority ratio */
  #define ETH_DMABMR_RTPR_2_1     ((u32)0x00004000)  /* Rx Tx priority ratio */
  #define ETH_DMABMR_RTPR_3_1     ((u32)0x00008000)  /* Rx Tx priority ratio */
  #define ETH_DMABMR_RTPR_4_1     ((u32)0x0000C000)  /* Rx Tx priority ratio */
#define ETH_DMABMR_PBL    ((u32)0x00003F00)  /* Programmable burst length */
  /* Values to be confirmed: maybe they are inversed */
  #define ETH_DMABMR_PBL_1Beat    ((u32)0x00000100)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 1 */
  #define ETH_DMABMR_PBL_2Beat    ((u32)0x00000200)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 2 */
  #define ETH_DMABMR_PBL_4Beat    ((u32)0x00000400)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 4 */
  #define ETH_DMABMR_PBL_8Beat    ((u32)0x00000800)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 8 */
  #define ETH_DMABMR_PBL_16Beat   ((u32)0x00001000)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 16 */
  #define ETH_DMABMR_PBL_32Beat   ((u32)0x00002000)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 32 */
  #define ETH_DMABMR_PBL_4xPBL_4Beat   ((u32)0x01000100)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 4 */
  #define ETH_DMABMR_PBL_4xPBL_8Beat   ((u32)0x01000200)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 8 */
  #define ETH_DMABMR_PBL_4xPBL_16Beat  ((u32)0x01000400)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 16 */
  #define ETH_DMABMR_PBL_4xPBL_32Beat  ((u32)0x01000800)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 32 */
  #define ETH_DMABMR_PBL_4xPBL_64Beat  ((u32)0x01001000)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 64 */
  #define ETH_DMABMR_PBL_4xPBL_128Beat ((u32)0x01002000)  /* maximum number of beats to be transferred in one TxDMA (or both) transaction is 128 */
#define ETH_DMABMR_DSL       ((u32)0x0000007C)  /* Descriptor Skip Length */
#define ETH_DMABMR_DA        ((u32)0x00000002)  /* DMA arbitration scheme */
#define ETH_DMABMR_SR        ((u32)0x00000001)  /* Software reset */

/* Bit definition for Ethernet DMA Transmit Poll Demand Register */
#define ETH_DMATPDR_TPD      ((u32)0xFFFFFFFF)  /* Transmit poll demand */

/* Bit definition for Ethernet DMA Receive Poll Demand Register */
#define ETH_DMARPDR_RPD      ((u32)0xFFFFFFFF)  /* Receive poll demand  */

/* Bit definition for Ethernet DMA Receive Descriptor List Address Register */
#define ETH_DMARDLAR_SRL     ((u32)0xFFFFFFFF)  /* Start of receive list */

/* Bit definition for Ethernet DMA Transmit Descriptor List Address Register */
#define ETH_DMATDLAR_STL     ((u32)0xFFFFFFFF)  /* Start of transmit list */

/* Bit definition for Ethernet DMA Status Register */
#define ETH_DMASR_TSTS       ((u32)0x20000000)  /* Time-stamp trigger status */
#define ETH_DMASR_PMTS       ((u32)0x10000000)  /* PMT status */
#define ETH_DMASR_MMCS       ((u32)0x08000000)  /* MMC status */
#define ETH_DMASR_EBS        ((u32)0x03800000)  /* Error bits status */
  /* combination with EBS[2:0] for GetFlagStatus function */
  #define ETH_DMASR_EBS_DescAccess      ((u32)0x02000000)  /* Error bits 0-data buffer, 1-desc. access */
  #define ETH_DMASR_EBS_ReadTransf      ((u32)0x01000000)  /* Error bits 0-write trnsf, 1-read transfr */
  #define ETH_DMASR_EBS_DataTransfTx    ((u32)0x00800000)  /* Error bits 0-Rx DMA, 1-Tx DMA */
#define ETH_DMASR_TPS         ((u32)0x00700000)  /* Transmit process state */
  #define ETH_DMASR_TPS_Stopped         ((u32)0x00000000)  /* Stopped - Reset or Stop Tx Command issued  */
  #define ETH_DMASR_TPS_Fetching        ((u32)0x00100000)  /* Running - fetching the Tx descriptor */
  #define ETH_DMASR_TPS_Waiting         ((u32)0x00200000)  /* Running - waiting for status */
  #define ETH_DMASR_TPS_Reading         ((u32)0x00300000)  /* Running - reading the data from host memory */
  #define ETH_DMASR_TPS_Suspended       ((u32)0x00600000)  /* Suspended - Tx Descriptor unavailabe */
  #define ETH_DMASR_TPS_Closing         ((u32)0x00700000)  /* Running - closing Rx descriptor */
#define ETH_DMASR_RPS         ((u32)0x000E0000)  /* Receive process state */
  #define ETH_DMASR_RPS_Stopped         ((u32)0x00000000)  /* Stopped - Reset or Stop Rx Command issued */
  #define ETH_DMASR_RPS_Fetching        ((u32)0x00020000)  /* Running - fetching the Rx descriptor */
  #define ETH_DMASR_RPS_Waiting         ((u32)0x00060000)  /* Running - waiting for packet */
  #define ETH_DMASR_RPS_Suspended       ((u32)0x00080000)  /* Suspended - Rx Descriptor unavailable */
  #define ETH_DMASR_RPS_Closing         ((u32)0x000A0000)  /* Running - closing descriptor */
  #define ETH_DMASR_RPS_Queuing         ((u32)0x000E0000)  /* Running - queuing the recieve frame into host memory */
#define ETH_DMASR_NIS        ((u32)0x00010000)  /* Normal interrupt summary */
#define ETH_DMASR_AIS        ((u32)0x00008000)  /* Abnormal interrupt summary */
#define ETH_DMASR_ERS        ((u32)0x00004000)  /* Early receive status */
#define ETH_DMASR_FBES       ((u32)0x00002000)  /* Fatal bus error status */
#define ETH_DMASR_ETS        ((u32)0x00000400)  /* Early transmit status */
#define ETH_DMASR_RWTS       ((u32)0x00000200)  /* Receive watchdog timeout status */
#define ETH_DMASR_RPSS       ((u32)0x00000100)  /* Receive process stopped status */
#define ETH_DMASR_RBUS       ((u32)0x00000080)  /* Receive buffer unavailable status */
#define ETH_DMASR_RS         ((u32)0x00000040)  /* Receive status */
#define ETH_DMASR_TUS        ((u32)0x00000020)  /* Transmit underflow status */
#define ETH_DMASR_ROS        ((u32)0x00000010)  /* Receive overflow status */
#define ETH_DMASR_TJTS       ((u32)0x00000008)  /* Transmit jabber timeout status */
#define ETH_DMASR_TBUS       ((u32)0x00000004)  /* Transmit buffer unavailable status */
#define ETH_DMASR_TPSS       ((u32)0x00000002)  /* Transmit process stopped status */
#define ETH_DMASR_TS         ((u32)0x00000001)  /* Transmit status */

/* Bit definition for Ethernet DMA Operation Mode Register */
#define ETH_DMAOMR_DTCEFD    ((u32)0x04000000)  /* Disable Dropping of TCP/IP checksum error frames */
#define ETH_DMAOMR_RSF       ((u32)0x02000000)  /* Receive store and forward */
#define ETH_DMAOMR_DFRF      ((u32)0x01000000)  /* Disable flushing of received frames */
#define ETH_DMAOMR_TSF       ((u32)0x00200000)  /* Transmit store and forward */
#define ETH_DMAOMR_FTF       ((u32)0x00100000)  /* Flush transmit FIFO */
#define ETH_DMAOMR_TTC       ((u32)0x0001C000)  /* Transmit threshold control */
  #define ETH_DMAOMR_TTC_64Bytes       ((u32)0x00000000)  /* threshold level of the MTL Transmit FIFO is 64 Bytes */
  #define ETH_DMAOMR_TTC_128Bytes      ((u32)0x00004000)  /* threshold level of the MTL Transmit FIFO is 128 Bytes */
  #define ETH_DMAOMR_TTC_192Bytes      ((u32)0x00008000)  /* threshold level of the MTL Transmit FIFO is 192 Bytes */
  #define ETH_DMAOMR_TTC_256Bytes      ((u32)0x0000C000)  /* threshold level of the MTL Transmit FIFO is 256 Bytes */
  #define ETH_DMAOMR_TTC_40Bytes       ((u32)0x00010000)  /* threshold level of the MTL Transmit FIFO is 40 Bytes */
  #define ETH_DMAOMR_TTC_32Bytes       ((u32)0x00014000)  /* threshold level of the MTL Transmit FIFO is 32 Bytes */
  #define ETH_DMAOMR_TTC_24Bytes       ((u32)0x00018000)  /* threshold level of the MTL Transmit FIFO is 24 Bytes */
  #define ETH_DMAOMR_TTC_16Bytes       ((u32)0x0001C000)  /* threshold level of the MTL Transmit FIFO is 16 Bytes */
#define ETH_DMAOMR_ST        ((u32)0x00002000)  /* Start/stop transmission command */
#define ETH_DMAOMR_FEF       ((u32)0x00000080)  /* Forward error frames */
#define ETH_DMAOMR_FUGF      ((u32)0x00000040)  /* Forward undersized good frames */
#define ETH_DMAOMR_RTC       ((u32)0x00000018)  /* receive threshold control */
  #define ETH_DMAOMR_RTC_64Bytes       ((u32)0x00000000)  /* threshold level of the MTL Receive FIFO is 64 Bytes */
  #define ETH_DMAOMR_RTC_32Bytes       ((u32)0x00000008)  /* threshold level of the MTL Receive FIFO is 32 Bytes */
  #define ETH_DMAOMR_RTC_96Bytes       ((u32)0x00000010)  /* threshold level of the MTL Receive FIFO is 96 Bytes */
  #define ETH_DMAOMR_RTC_128Bytes      ((u32)0x00000018)  /* threshold level of the MTL Receive FIFO is 128 Bytes */
#define ETH_DMAOMR_OSF       ((u32)0x00000004)  /* operate on second frame */
#define ETH_DMAOMR_SR        ((u32)0x00000002)  /* Start/stop receive */

/* Bit definition for Ethernet DMA Interrupt Enable Register */
#define ETH_DMAIER_NISE      ((u32)0x00010000)  /* Normal interrupt summary enable */
#define ETH_DMAIER_AISE      ((u32)0x00008000)  /* Abnormal interrupt summary enable */
#define ETH_DMAIER_ERIE      ((u32)0x00004000)  /* Early receive interrupt enable */
#define ETH_DMAIER_FBEIE     ((u32)0x00002000)  /* Fatal bus error interrupt enable */
#define ETH_DMAIER_ETIE      ((u32)0x00000400)  /* Early transmit interrupt enable */
#define ETH_DMAIER_RWTIE     ((u32)0x00000200)  /* Receive watchdog timeout interrupt enable */
#define ETH_DMAIER_RPSIE     ((u32)0x00000100)  /* Receive process stopped interrupt enable */
#define ETH_DMAIER_RBUIE     ((u32)0x00000080)  /* Receive buffer unavailable interrupt enable */
#define ETH_DMAIER_RIE       ((u32)0x00000040)  /* Receive interrupt enable */
#define ETH_DMAIER_TUIE      ((u32)0x00000020)  /* Transmit Underflow interrupt enable */
#define ETH_DMAIER_ROIE      ((u32)0x00000010)  /* Receive Overflow interrupt enable */
#define ETH_DMAIER_TJTIE     ((u32)0x00000008)  /* Transmit jabber timeout interrupt enable */
#define ETH_DMAIER_TBUIE     ((u32)0x00000004)  /* Transmit buffer unavailable interrupt enable */
#define ETH_DMAIER_TPSIE     ((u32)0x00000002)  /* Transmit process stopped interrupt enable */
#define ETH_DMAIER_TIE       ((u32)0x00000001)  /* Transmit interrupt enable */

/* Bit definition for Ethernet DMA Missed Frame and Buffer Overflow Counter Register */
#define ETH_DMAMFBOCR_OFOC   ((u32)0x10000000)  /* Overflow bit for FIFO overflow counter */
#define ETH_DMAMFBOCR_MFA    ((u32)0x0FFE0000)  /* Number of frames missed by the application */
#define ETH_DMAMFBOCR_OMFC   ((u32)0x00010000)  /* Overflow bit for missed frame counter */
#define ETH_DMAMFBOCR_MFC    ((u32)0x0000FFFF)  /* Number of frames missed by the controller */

/* Bit definition for Ethernet DMA Current Host Transmit Descriptor Register */
#define ETH_DMACHTDR_HTDAP   ((u32)0xFFFFFFFF)  /* Host transmit descriptor address pointer */

/* Bit definition for Ethernet DMA Current Host Receive Descriptor Register */
#define ETH_DMACHRDR_HRDAP   ((u32)0xFFFFFFFF)  /* Host receive descriptor address pointer */

/* Bit definition for Ethernet DMA Current Host Transmit Buffer Address Register */
#define ETH_DMACHTBAR_HTBAP  ((u32)0xFFFFFFFF)  /* Host transmit buffer address pointer */

/* Bit definition for Ethernet DMA Current Host Receive Buffer Address Register */
#define ETH_DMACHRBAR_HRBAP  ((u32)0xFFFFFFFF)  /* Host receive buffer address pointer */

/******************************************************************************/
/*                                      Macros                                */
/******************************************************************************/
#define  SET_BIT(REG, BIT)   ((REG) |= (BIT))
#define  CLEAR_BIT(REG, BIT) ((REG) &= ~(BIT))
#define  READ_BIT(REG, BIT)  ((REG) & (BIT))

/******************************************************************************/
/*                         Peripheral memory map                              */
/******************************************************************************/
/* ETHERNET registers base address */
#define ETH_BASE             ((u32)0x40028000)
#define ETH_MAC_BASE         (ETH_BASE)
#define ETH_MMC_BASE         (ETH_BASE + 0x0100)
#define ETH_PTP_BASE         (ETH_BASE + 0x0700)
#define ETH_DMA_BASE         (ETH_BASE + 0x1000)

/******************************************************************************/
/*                         Peripheral declaration                             */
/******************************************************************************/

/*------------------------ Non Debug Mode ------------------------------------*/
#ifndef ETH_DEBUG
#ifdef _ETH_MAC
  #define ETH_MAC            ((ETH_MAC_TypeDef *) ETH_MAC_BASE)
#endif /*_ETH_MAC */

#ifdef _ETH_MMC
  #define ETH_MMC            ((ETH_MMC_TypeDef *) ETH_MMC_BASE)
#endif /*_ETH_MMC */

#ifdef _ETH_PTP
  #define ETH_PTP            ((ETH_PTP_TypeDef *) ETH_PTP_BASE)
#endif /*_ETH_PTP */

#ifdef _ETH_DMA
  #define ETH_DMA            ((ETH_DMA_TypeDef *) ETH_DMA_BASE)
#endif /*_ETH_DMA */

/*------------------------ Debug Mode ----------------------------------------*/
#else   /* ETH_DEBUG */
#ifdef _ETH_MAC
  EXT ETH_MAC_TypeDef        *ETH_MAC;
#endif /*_ETH_MAC */

#ifdef _ETH_MMC
  EXT ETH_MMC_TypeDef        *ETH_MMC;
#endif /*_ETH_MMC */

#ifdef _ETH_PTP
  EXT ETH_PTP_TypeDef        *ETH_PTP;
#endif /*_ETH_PTP */

#ifdef _ETH_DMA
  EXT ETH_DMA_TypeDef        *ETH_DMA;
#endif /*_ETH_DMA */

#endif  /* ETH_DEBUG */

/* Exported constants --------------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

#endif /* __STM32FXXX_ETH_MAP_H */

/******************* (C) COPYRIGHT 2008 STMicroelectronics *****END OF FILE****/
