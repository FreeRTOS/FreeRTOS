/*
 * @brief CAN registers and control functions
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __CAN_001_H_
#define __CAN_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_CAN_001 IP: CAN register block and driver
 * @ingroup IP_Drivers
 * Controller Area Network
 * @{
 */

/** The number of entry in AF RAM region */
#define CANAF_RAM_ENTRY_NUM        512

/**
 * @brief CAN AF RAM section definitions
 */
typedef enum IP_CAN_AF_RAM_SECTION {
	CANAF_RAM_FULLCAN_SEC,	/*!<FullCAN Section*/
	CANAF_RAM_SFF_SEC,		/*!<Standard ID Section*/
	CANAF_RAM_SFF_GRP_SEC,	/*!<Group Standard ID Section*/
	CANAF_RAM_EFF_SEC,		/*!<Extended ID Section*/
	CANAF_RAM_EFF_GRP_SEC,	/*!<Group Extended ID Section*/
	CANAF_RAM_SECTION_NUM,
} IP_CAN_AF_RAM_SECTION_T;

/**
 * @brief CAN acceptance filter RAM register block structure
 */
typedef struct							/*!< AF RAM Mask Table        */
{
	__IO uint32_t MASK[CANAF_RAM_ENTRY_NUM];	/*!< Acceptance Filter RAM ID mask register */
} IP_CAN_001_AF_RAM_T;

/**
 * @brief CAN acceptance filter register block structure
 */
typedef struct							/*!< CAN AF structure        */
{
	__IO uint32_t AFMR;						/*!< Acceptance Filter Register */
	__IO uint32_t ENDADDR[CANAF_RAM_SECTION_NUM];				/*!< Start/End Address Registers */
	__I  uint32_t LUTERRAD;					/*!< LUT Error Address Register */
	__I  uint32_t LUTERR;					/*!< LUT Error Register */
	__IO uint32_t FCANIE;					/*!< Global FullCANInterrupt Enable Register */
	__IO uint32_t FCANIC[2];				/*!< FullCAN Interrupt and Capture Registers */
} IP_CAN_001_AF_T;

/**
 * @brief Central CAN register block structure
 */
typedef struct							/*!< Central CAN structure                  */
{
	__I  uint32_t TXSR;						/*!< CAN Central Transmit Status Register */
	__I  uint32_t RXSR;						/*!< CAN Central Receive Status Register */
	__I  uint32_t MSR;						/*!< CAN Central Miscellaneous Register */
} IP_CAN_001_CR_T;

/**
 * @brief CAN Transmit register block structure
 */
typedef struct							/*!< CAN Transmit structure                  */
{
	__IO uint32_t TFI;					/*!< CAN Transmit Frame Information register*/
	__IO uint32_t TID;					/*!< CAN Transfer Identifier register*/
	__IO uint32_t TD[2];				/*!<CAN Transmit Data register*/
} IP_CAN_001_TX_T;

/**
 * @brief CAN Receive register block structure
 */
typedef struct				/*!< CAN Receive Frame structure                  */
{
	__IO uint32_t RFS;		/*!< Characteristic of the received frame. It includes the following characteristics:
							   CAN_RFS_BP: indicate that the current message is received in Bypass mode.
							 *							CAN_RFS_RTR: indicate the value of Remote Transmission Request bit in the current message.
							 *							CAN_RFS_FF: indicate that the identifier in the current message is 11-bit or 29-bit identifier.
							   Use CAN_RFS_ID_INDEX(RFS value) to get the ID Index of the matched entry in the Lookup Table RAM.
							   Use CAN_RFS_DLC(RFS value) to get the Data Length Code field of the current received message.
							 */
	__IO uint32_t RID;		/*!<Identifier in the received message. Use RFS field to determine if it is 11-bit or 29-bit identifier.*/
	__IO uint32_t RD[2];	/*!< Data bytes of the received message. Use DLC value in RFS fied to determine the number of data bytes.*/
} IP_CAN_001_RX_T;

/**
 * @brief CAN register block structure
 */
typedef struct							/*!< CANn structure               */
{
	__IO uint32_t MOD;					/*!< CAN Mode Register */
	__O  uint32_t CMR;					/*!< CAN Command Register */
	__IO uint32_t GSR;					/*!< CAN Global Status Register */
	__I  uint32_t ICR;					/*!< CAN Interrupt and Capture Register */
	__IO uint32_t IER;					/*!< CAN Interrupt Enable Register*/
	__IO uint32_t BTR;					/*!< CAN Bus Timing Register*/
	__IO uint32_t EWL;					/*!< CAN Error Warning Limit Register*/
	__I  uint32_t SR;					/*!< CAN Status Register*/
	__IO IP_CAN_001_RX_T RX;			/*!< CAN Receive Registers*/
	__IO IP_CAN_001_TX_T TX[3];		/*!< CAN Transmit Registers*/
} IP_CAN_001_T;

/**
 * @brief CAN Mode  register definitions
 */
/** CAN Mode Register Bitmask */
#define CAN_MOD_BITMASK     (0xBF)

/** CAN Operationg Mode */
#define CAN_MOD_OPERATION   ((uint32_t) 0)

/** CAN Reset mode */
#define CAN_MOD_RM          ((uint32_t) (1 << 0))

/** CAN Listen Only Mode (Don't send ACK/Message)*/
#define CAN_MOD_LOM         ((uint32_t) (1 << 1))

/** CAN Self Test mode (Don't care ACK after sending message)*/
#define CAN_MOD_STM         ((uint32_t) (1 << 2))

/** CAN Transmit Priority mode (Determine the transmit priority basing on Tx Priority Register)*/
#define CAN_MOD_TPM         ((uint32_t) (1 << 3))

/** CAN Sleep mode */
#define CAN_MOD_SM          ((uint32_t) (1 << 4))

/** CAN Receive Polarity mode (Determine RD is active Low or High).*/
#define CAN_MOD_RPM         ((uint32_t) (1 << 5))

/** CAN Test mode (TD pin will reflects the bit detected on RD pin)*/
#define CAN_MOD_TM          ((uint32_t) (1 << 7))

/**
 * @brief CAN Command  register definitions
 */
/** CAN Command Register Bitmask */
#define CAN_CMR_BITMASK     (0xFF)

/** Request to Send message which is available in selected Transmit Buffer*/
#define CAN_CMR_TR          ((uint32_t) (1))

/** Cancel the current transmission or the pending transmission request*/
#define CAN_CMR_AT          ((uint32_t) (1 << 1))

/** Release the information in Receive Buffer */
#define CAN_CMR_RRB         ((uint32_t) (1 << 2))

/** Clear the Data Overrun bit in Status Register(s)*/
#define CAN_CMR_CDO         ((uint32_t) (1 << 3))

/** Self Reception Request.The message sent is received simultaneously. */
#define CAN_CMR_SRR         ((uint32_t) (1 << 4))

/** Select one or multi transmit buffer(s).( n = 0/1/2) */
#define CAN_CMR_STB(n)       ((uint32_t) (1 << (n + 5)))

/**
 * @brief CAN Global Status register definitions
 */
/** CAN Global Status Register Bitmask */
#define CAN_GSR_BITMASK     (0xFFFF00FF)

/** CAN Receive Buffer Status (At least one complete message is received) */
#define CAN_GSR_RBS         ((uint32_t) (1))

/** CAN Data Overrun Status */
#define CAN_GSR_DOS         ((uint32_t) (1 << 1))

/** CAN Transmit Buffer Status  (All 3 Transmit Buffers are available)*/
#define CAN_GSR_TBS         ((uint32_t) (1 << 2))

/** CAN Transmit Complete Status (All requested transmission(s) has (have) been successfully completed)*/
#define CAN_GSR_TCS         ((uint32_t) (1 << 3))

/** CAN Receive Status (The CAN controller is receiving a message)*/
#define CAN_GSR_RS          ((uint32_t) (1 << 4))

/** CAN Transmit Status (The CAN controller is sending a message)*/
#define CAN_GSR_TS          ((uint32_t) (1 << 5))

/** CAN Error Status */
#define CAN_GSR_ES          ((uint32_t) (1 << 6))

/** CAN Bus Status (CAN Controller is involed in bus activity or not*/
#define CAN_GSR_BS          ((uint32_t) (1 << 7))

/** CAN Current value of the Rx Error Counter */
#define CAN_GSR_RXERR(n)    ((uint32_t) ((n >> 16) & 0xFF)

/** CAN Current value of the Tx Error Counter */
#define CAN_GSR_TXERR(n)    ((uint32_t) ((n >> 24) & 0xFF)

/**
 * @brief CAN Interrupt and Capture  register definitions
 */
/** CAN Interrupt and Capture Registe Bitmask */
#define CAN_ICR_BITMASK     (0xFFFF07FF)

/** CAN Receive Interrupt  (A new message was received)*/
#define CAN_ICR_RI          ((uint32_t) (1))

/** CAN Transmit Interrupt (Transmit buffer 1 is available) */
#define CAN_ICR_TI1         ((uint32_t) (1 << 1))

/** CAN Error Warning Interrupt */
#define CAN_ICR_EI          ((uint32_t) (1 << 2))

/** CAN Data Overrun Interrupt */
#define CAN_ICR_DOI         ((uint32_t) (1 << 3))

/** CAN Wake-Up Interrupt */
#define CAN_ICR_WUI         ((uint32_t) (1 << 4))

/** CAN Error Passive Interrupt */
#define CAN_ICR_EPI         ((uint32_t) (1 << 5))

/** CAN Arbitration Lost Interrupt */
#define CAN_ICR_ALI         ((uint32_t) (1 << 6))

/** CAN Bus Error Interrupt */
#define CAN_ICR_BEI         ((uint32_t) (1 << 7))

/** CAN ID Ready Interrupt */
#define CAN_ICR_IDI         ((uint32_t) (1 << 8))

/** CAN Transmit Interrupt 2 (Transmit buffer 2 is available) */
#define CAN_ICR_TI2         ((uint32_t) (1 << 9))

/** CAN Transmit Interrupt 3 (Transmit buffer 3 is available)*/
#define CAN_ICR_TI3         ((uint32_t) (1 << 10))

/** CAN Error Code Capture (Error Location)*/
#define CAN_ICR_ERRBIT_VAL(n)   ((uint32_t) (((n) >> 16) & 0x1F))
/** Start of Frame error value */
#define CAN_ICR_ERR_SOF             (3)
/** ID28...ID21 Error value */
#define CAN_ICR_ERR_ID28_ID21       (2)
/** ID28...ID21 Error value */
#define CAN_ICR_ERR_ID20_ID18       (6)
/**SRTR Bit Error value */
#define CAN_ICR_ERR_SRTR        (4)
/**IDE Bit Error value */
#define CAN_ICR_ERR_IDE     (5)
/** ID17...ID13 Error value */
#define CAN_ICR_ERR_ID17_ID13       (7)
/** ID12...ID15 Error value */
#define CAN_ICR_ERR_ID12_ID5        (0x0F)
/** ID4...ID0 Error value */
#define CAN_ICR_ERR_ID4_ID0     (0x0E)
/**RTR Bit Error value */
#define CAN_ICR_ERR_RTR     (0x0C)
/**Reserved Bit 1 Error value */
#define CAN_ICR_ERR_ReservedBit_1       (0x0D)
/**Reserved Bit 0 Error value */
#define CAN_ICR_ERR_ReservedBit_0       (0x09)
/** DLC Error value */
#define CAN_ICR_ERR_DLC     (0x0B)
/** Data Field Error value */
#define CAN_ICR_ERR_DATA_FIELD      (0x0A)
/** CRC Sequence Error value */
#define CAN_ICR_ERR_CRC_SEQ     (0x08)
/** CRC Delimiter Error value */
#define CAN_ICR_ERR_CRC_DELIMITER       (0x18)
/** ACK Error value */
#define CAN_ICR_ERR_ACK     (0x19)
/** ACK Delimiter Error value */
#define CAN_ICR_ERR_ACK_DELIMITER       (0x1B)
/** EOF Error value */
#define CAN_ICR_ERR_EOF     (0x1A)
/** Intermission Error value */
#define CAN_ICR_ERR_INTERMISSION        (0x12)

/** CAN Error Direction */
#define CAN_ICR_ERRDIR_RECEIVE      ((uint32_t) (1 << 21))

/** CAN Error Type Capture */
#define CAN_ICR_ERRC_VAL(n)     ((uint32_t) (((n) >> 22) & 0x3))
#define CAN_ICR_BIT_ERROR       (0)
#define CAN_ICR_FORM_ERROR      (1)
#define CAN_ICR_STUFF_ERROR     (2)
#define CAN_ICR_OTHER_ERROR     (3)

/** CAN Arbitration Lost Capture */
#define CAN_ICR_ALCBIT_VAL(n)       ((uint32_t) (((n) >> 24) & 0xFF))

/**
 * @brief CAN Interrupt Enable  register definitions
 */
/** CAN Interrupt Enable  Register Bitmask */
#define CAN_IER_BITMASK     (0x7FF)

/** CAN Receive Interrupt Enable */
#define CAN_IER_RIE         ((uint32_t) (1))

/** CAN Transmit Interrupt Enable for buffer 1 */
#define CAN_IER_TIE1        ((uint32_t) (1 << 1))

/** CAN Error Warning Interrupt Enable */
#define CAN_IER_EIE         ((uint32_t) (1 << 2))

/** CAN Data Overrun Interrupt Enable */
#define CAN_IER_DOIE        ((uint32_t) (1 << 3))

/** CAN Wake-Up Interrupt Enable */
#define CAN_IER_WUIE        ((uint32_t) (1 << 4))

/** CAN Error Passive Interrupt Enable */
#define CAN_IER_EPIE        ((uint32_t) (1 << 5))

/** CAN Arbitration Lost Interrupt Enable */
#define CAN_IER_ALIE        ((uint32_t) (1 << 6))

/** CAN Bus Error Interrupt Enable */
#define CAN_IER_BEIE        ((uint32_t) (1 << 7))

/** CAN ID Ready Interrupt Enable */
#define CAN_IER_IDIE        ((uint32_t) (1 << 8))

/** CAN Transmit Enable Interrupt for Buffer 2 */
#define CAN_IER_TIE2        ((uint32_t) (1 << 9))

/** CAN Transmit Enable Interrupt for Buffer 3 */
#define CAN_IER_TIE3        ((uint32_t) (1 << 10))

/**
 * @brief CAN Bus Timing  register definitions
 */
/** CAN Bus Timing  Register Bitmask */
#define CAN_BTR_BITMASK     (0xFFC3FF)

/** CAN Baudrate Prescaler */
#define CAN_BTR_BRP(n)      ((uint32_t) ((n) & 0x3FF))

/** CAN Synchronization Jump Width */
#define CAN_BTR_SJW(n)      ((uint32_t) (((n) & 0x3) << 14))

/** CAN Time Segment 1 */
#define CAN_BTR_TESG1(n)    ((uint32_t) (((n) & 0xF) << 16))

/** CAN Time Segment 2 */
#define CAN_BTR_TESG2(n)    ((uint32_t) (((n) & 0xF) << 20))

/** CAN Sampling */
#define CAN_BTR_SAM         ((uint32_t) (1 << 23))

/**
 * @brief CAN Error Warning Limit  register definitions
 */
/** CAN Error Warning Limit  Register Bitmask */
#define CAN_EWL_BITMASK     (0xFF)

/** CAN Error Warning Limit */
#define CAN_EWL_VAL(n)      ((uint32_t) ((n) & 0xFF))

/**
 * @brief CAN Status  Registe definitions
 */
/** CAN Status  Registe Bitmask */
#define CAN_SR_BITMASK     (0xFFFFFF)

/** CAN Receive Buffer Status (Bit 0, 8, 16 are the same)*/
#define CAN_SR_RBS(n)     ((uint32_t) (1 << ((n) * 8)))

/** CAN Data Overrun Status (Bit 1, 9, 17 are the same)*/
#define CAN_SR_DOS(n)     ((uint32_t) (1 << (1 + (n) * 8)))

/** CAN Transmit Buffer Status (Tx Buffer n=0/1/2  is available)*/
#define CAN_SR_TBS(n)     ((uint32_t) (1 << (2 + (n) * 8)))

/** CAN Transmission Complete Status (The request on Tx Buffer n=0/1/2 has been completed) */
#define CAN_SR_TCS(n)     ((uint32_t) (1 << (3 + (n) * 8)))

/** CAN Receive Status (Bit 4, 12, 20 are the same)*/
#define CAN_SR_RS(n)      ((uint32_t) (1 << (4 + (n) * 8)))

/** CAN Transmit Status (The CAN controller is sending a message in Tx Buffer n=0/1/2) */
#define CAN_SR_TS(n)      ((uint32_t) (1 << (5 + (n) * 8)))

/** CAN Error Status (Bit 6, 14, 22 are the same)*/
#define CAN_SR_ES(n)      ((uint32_t) (1 << (6 + (n) * 8)))

/** CAN Bus Status (Bit 7, 15, 23 are the same)*/
#define CAN_SR_BS(n)      ((uint32_t) (1 << (7 + (n) * 8)))

/**
 * @brief CAN Receive Frame Status  register definitions
 */
/** CAN Receive Frame Status Register  Bitmask */
#define CAN_RFS_BITMASK     (0xC00F07FF)

/** CAN ID Index */
#define CAN_RFS_ID_INDEX(n) ((uint32_t) ((n) & 0x3FF))

/** CAN Bypass */
#define CAN_RFS_BP          ((uint32_t) (1 << 10))

/** CAN Data Length Code */
#define CAN_RFS_DLC(n)      ((uint32_t) ((n >> 16) & 0x0F))

/** CAN Remote Transmission Request */
#define CAN_RFS_RTR         ((uint32_t) (1 << 30))

/** CAN control 11 bit or 29 bit Identifier */
#define CAN_RFS_FF          ((uint32_t) ((uint32_t) 1 << 31))

/**
 * @brief CAN Receive Identifier Register definitions
 */
/** CAN 11 bit Identifier */
#define CAN_RID_ID_11(n)        ((uint32_t) ((n) & 0x7FF))

/** CAN 29 bit Identifier */
#define CAN_RID_ID_29(n)        ((uint32_t) ((n) & 0x1FFFFFFF))

/**
 * @brief CAN Transmit Frame Information register definitions
 */
/** CAN Transmit Frame Information  Register  Bitmask */
#define CAN_TFI_BITMASK     (0xC00F00FF)

/** CAN Priority */
#define CAN_TFI_PRIO(n)         ((uint32_t) ((n) & 0xFF))

/** CAN Data Length Code */
#define CAN_TFI_DLC(n)          ((uint32_t) (((n) & 0xF) << 16))

/** CAN Remote Frame Transmission */
#define CAN_TFI_RTR             ((uint32_t) (1 << 30))

/** CAN control 11-bit or 29-bit Identifier */
#define CAN_TFI_FF              ((uint32_t) ((uint32_t) 1 << 31))

/**
 * @brief CAN Transfer Identifier register definitions
 */
/** CAN 11-bit Identifier */
#define CAN_TID_ID11(n)         ((uint32_t) ((n) & 0x7FF))

/** CAN 11-bit Identifier */
#define CAN_TID_ID29(n)         ((uint32_t) ((n) & 0x1FFFFFFF))

/**
 * @brief CAN Central transmit Status register definitions
 */
/** CAN Central transmit Status Register  Bitmask */
#define CAN_TSR_BITMASK     (0x30303)

/** Bit indicate CAN n (0/1) is sending a message */
#define CAN_TSR_TS(n)         ((uint32_t) (1 << (n + 0)))

/** Bit indicate all 3 Tx buffer of CAN n (0/1) are available */
#define CAN_TSR_TBS(n)        ((uint32_t) (1 << (n + 8)))

/** Bit indicate all requested transmissions have been completed successfully by the CAN n(0/1) */
#define CAN_TSR_TCS(n)        ((uint32_t) (1 << (n + 16)))

/**
 * @brief CAN Central Receive Status register definitions
 */
/** CAN Central Receive Status Register  Bitmask */
#define CAN_RSR_BITMASK     (0x30303)

/** Bit indicate CAN n (0/1) is receiving a message */
#define CAN_RSR_RS(n)         ((uint32_t) (1 << (n + 0)))

/** Bit indicate a received message is available in CAN n (0/1) */
#define CAN_RSR_RBS(n)        ((uint32_t) (1 << (n + 8)))

/** Bit indicate a message was lost because the preceding message to CAN n(0/1) controller was not
   read out quickly enough*/
#define CAN_RSR_DOS(n)        ((uint32_t) (1 << (n + 16)))

/**
 * @brief CAN Central Miscellaneous Status register definitions
 */
/** CAN Central Receive Status Register  Bitmask */
#define CAN_MSR_BITMASK     (0x303)

/** Bit indicate Tx/Rx Error Counter has reached the limit set in CAN n (0/1) */
#define CAN_MSR_E(n)      ((uint32_t) (1 << (n + 0)))

/** Bit indicate CAN n (0/1) is currently involved in bus activities*/
#define CAN_MSR_BS(n)     ((uint32_t) (1 << (n + 8)))

/**
 * @brief Acceptance Filter Mode register definitions
 */
/** CAN Acceptance Filter Operation mode */
#define CANAF_AFMR_OPERATION     ((uint32_t) (0))

/** CAN Acceptance Filter Off mode */
#define CANAF_AFMR_ACCOFF     ((uint32_t) (1))

/** CAN Acceptance File Bypass mode */
#define CANAF_AFMR_ACCBP      ((uint32_t) (1 << 1))

/** FullCAN Mode Enhancements */
#define CANAF_AFMR_EFCAN      ((uint32_t) (1 << 2))

/**
 * @brief Extended Frame Group Start Address register definitions
 */
/** The start address of the table of grouped Extended Identifier */
#define CANAF_ENDADDR(n)       ((uint32_t) (((n) & 0x3FF) << 2))
#define CANAF_ENDADDR_VAL(n)   ((uint32_t) ((n >> 2) & 0x3FF))

/**
 * @brief LUT Error Address register definitions
 */
/** CAN Look-Up Table Error Address */
#define CANAF_LUTERRAD(n)     ((uint32_t) (((n) & 0x1FF) << 2))

/**
 * @brief LUT Error register definitions
 */
/** CAN Look-Up Table Error */
#define CANAF_LUTERR      ((uint32_t) (1))

/**
 * @brief Global FullCANInterrupt Enable register definitions
 */
/** Global FullCANInterrupt Enable Register  Bitmask */
#define CANAF_FCANIE_BITMASK     (0x01)

/** Global FullCANInterrupt Enable */
#define CANAF_FCANIE      ((uint32_t) (1))

/**
 * @brief FullCAN Message Layout definitions
 */

/** FF Bit Position*/
#define CANAF_FULLCAN_MSG_FF_POS    (31)
/** RTR Bit Position*/
#define CANAF_FULLCAN_MSG_RTR_POS   (30)
/** Message Lost Bit Position*/
#define CANAF_FULLCAN_MSG_LOST_POS  (26)
/** SEM Bit Position*/
#define CANAF_FULLCAN_MSG_SEM_POS   (24)
/** SEM Bit Mask*/
#define CANAF_FULLCAN_MSG_SEM_BITMASK   (0x03)
/** DLC Bit Position*/
#define CANAF_FULLCAN_MSG_DLC_POS   (16)
/** DLC Bit Mask*/
#define CANAF_FULLCAN_MSG_DLC_BITMASK   (0x0F)
/** SCC Bit Position*/
#define CANAF_FULLCAN_MSG_SCC_POS   (13)
/** SCC Bit Mask*/
#define CANAF_FULLCAN_MSG_SCC_BITMASK   (0x07)
/** 11bit-ID Bit Position*/
#define CANAF_FULLCAN_MSG_ID11_POS  (0)
/** 11bit-ID Bit Mask*/
#define CANAF_FULLCAN_MSG_ID11_BITMASK  (0x7FF)

/**
 * @brief FullCAN Message Status
 */
/** AF is updating FullCAN Message*/
#define CANAF_FULCAN_MSG_AF_UPDATING        (0x01)
/** AF has finished updating FullCAN Message*/
#define CANAF_FULCAN_MSG_AF_FINISHED        (0x03)
/** CPU is in process of reading FullCAN Message*/
#define CANAF_FULCAN_MSG_CPU_READING        (0x0)

/**
 * @brief FullCAN Interrupt and Capture register definitions
 */
/** FullCAN Interrupt and Capture (0-31)*/
#define CANAF_FCAN_IC_INTPND(n)   ((n >= 32) ? ((uint32_t) (1 << (n - 32))) : ((uint32_t) (1 << n)))

/**
 * @brief Standard ID Entry definitions
 */
/** Start position of Controller Number Bits */
#define CAN_STD_ENTRY_CTRL_NO_POS       (13 )
/** Mask of Controller Number Bits */
#define CAN_STD_ENTRY_CTRL_NO_MASK      (0x07)
/** Start position of Disable bit */
#define CAN_STD_ENTRY_DISABLE_POS       (12 )
/** Mask of Disable Bit */
#define CAN_STD_ENTRY_DISABLE_MASK      (0x01)
/** Start position of Interrupt Enable bit (FullCAN entry only)*/
#define CAN_STD_ENTRY_IE_POS            (11 )
/** Mask of Interrupt Enable bit (FullCAN entry only)*/
#define CAN_STD_ENTRY_IE_MASK           (0x01)
/** Start position of ID bit */
#define CAN_STD_ENTRY_ID_POS            (0  )
/** Mask of ID Bit */
#define CAN_STD_ENTRY_ID_MASK           (0x7FF)

/**
 * @brief Extended ID Entry definitions
 */
/** Start position of Controller Number Bits */
#define CAN_EXT_ENTRY_CTRL_NO_POS       (29 )
/** Mask of Controller Number Bits */
#define CAN_EXT_ENTRY_CTRL_NO_MASK      (0x07)
/** Start position of ID bit */
#define CAN_EXT_ENTRY_ID_POS            (0  )
/** Mask of ID Bit */
#define CAN_EXT_ENTRY_ID_MASK           (0x1FFFFFFF)

/**
 * @brief CAN Message Type definitions
 */

/** Remote Message */
#define CAN_REMOTE_MSG         ((uint32_t) (1 << 0))

/** Message use Extend ID*/
#define CAN_EXTEND_ID_USAGE     ((uint32_t) (1 << 30))

/** The maximum data length in CAN Message */
#define CAN_MSG_MAX_DATA_LEN       (8)

/**
 * @brief CAN Buffer ID definition
 */
typedef enum IP_CAN_BUFFER_ID {
	CAN_BUFFER_1 = 0,	/*!< Buffer 1 */
	CAN_BUFFER_2,		/*!< Buffer 2 */
	CAN_BUFFER_3,		/*!< Buffer 3 */
	CAN_BUFFER_LAST,	/*!< Last Buffer */
} IP_CAN_BUFFER_ID_T;

/**
 * @brief CAN Message Object Structure
 */
typedef struct						/*!< Message structure */
{
	uint32_t ID;					/*!< Message Identifier. If 30th-bit is set, this is 29-bit ID, othewise 11-bit ID */
	uint32_t Type;					/*!< Message Type. which can include: - CAN_REMOTE_MSG type*/
	uint32_t DLC;					/*!< Message Data Length: 0~8 */
	uint8_t  Data[CAN_MSG_MAX_DATA_LEN];/*!< Message Data */
} IP_CAN_MSG_T;

/**
 * @brief CAN Bus Timing Structure
 */
typedef struct						/*!< Bus Timing structure */
{
	uint16_t BRP;					/*!< Baud Rate Prescaler */
	uint8_t SJW;					/*!< SJW value*/
	uint8_t TESG1;					/*!< TESG1 value */
	uint8_t TESG2;					/*!< TESG2 value */
	uint8_t SAM;					/*!<0: The bus is sampled once, 1: sampled 3 times */
} IP_CAN_BUS_TIMING_T;

/**
 * @brief Standard ID Entry structure
 */
typedef struct {
	uint8_t CtrlNo;				/*!<Controller Number: 0 for CAN1 and 1 for CAN2*/
	uint8_t Disable;			/*!< 0(ENABLE)/1(DISABLE): Response On/Off dynamically*/
	uint16_t ID_11;				/*!< Standard ID, should be 11-bit value */
} IP_CAN_STD_ID_Entry_T;

/**
 * @brief Standard ID Range structure
 */
typedef struct {
	IP_CAN_STD_ID_Entry_T LowerID;	/*!< Lower ID Bound, should be in 11-bit value*/
	IP_CAN_STD_ID_Entry_T UpperID;	/*!< Upper ID Bound, should be in 11-bit value*/
} IP_CAN_STD_ID_RANGE_Entry_T;

/**
 * @brief Extended ID  Entry structure
 */
typedef struct {
	uint8_t CtrlNo;			/*!<Controller Number: 0 for CAN1 and 1 for CAN2*/
	uint32_t ID_29;			/*!< Extend ID, shoud be 29-bit value */
} IP_CAN_EXT_ID_Entry_T;

/**
 * @brief Extended ID Range structure
 */
typedef struct {
	IP_CAN_EXT_ID_Entry_T LowerID;	/*!< Lower ID Bound, should be in 29-bit value*/
	IP_CAN_EXT_ID_Entry_T UpperID;	/*!< Upper ID Bound, should be in 29-bit value*/
} IP_CAN_EXT_ID_RANGE_Entry_T;

/**
 * @brief Acceptance Filter Section Table structure
 */
typedef struct {
	IP_CAN_STD_ID_Entry_T *FullCANSec;		/*!< The pointer to fullCAN section */
	uint16_t FullCANEntryNum;					/*!< FullCAN Entry Number */
	IP_CAN_STD_ID_Entry_T *SffSec;			/*!< The pointer to individual Standard ID Section */
	uint16_t SffEntryNum;						/*!< Standard ID Entry Number */
	IP_CAN_STD_ID_RANGE_Entry_T *SffGrpSec;	/*!< The pointer to  Group Standard ID  Section */
	uint16_t SffGrpEntryNum;					/*!< Group Standard ID Entry Number */
	IP_CAN_EXT_ID_Entry_T *EffSec;			/*!< The pointer to Extended ID Section */
	uint16_t EffEntryNum;						/*!< Extended ID Entry Number */
	IP_CAN_EXT_ID_RANGE_Entry_T *EffGrpSec;	/*!< The pointer to Group Extended ID Section */
	uint16_t EffGrpEntryNum;					/*!< Group Extended ID Entry Number */
} IP_CAN_AF_LUT_T;

/**
 * @brief	De-initialize the CAN peripheral
 * @param	pCAN	: Pointer to CAN peripheral block
 * @return	None
 */
STATIC INLINE void IP_CAN_DeInit(IP_CAN_001_T *pCAN)
{}

/**
 * @brief	Get current mode register settings of the CAN controller
 * @param	pCAN	: Pointer to CAN peripheral block
 * @return	Current Mode register value of the CAN Controller (Bit values of CAN_MOD_*)
 */
STATIC INLINE uint32_t IP_CAN_GetMode(IP_CAN_001_T *pCAN)
{
	return pCAN->MOD & CAN_MOD_BITMASK;
}

/**
 * @brief	Set the CAN command request
 * @param	pCAN	: Pointer to CAN peripheral block
 * @param	command	: Command request (Or'ed bit values of CAN_CMR_*).
 * @return	None
 */
STATIC INLINE void IP_CAN_SetCmd(IP_CAN_001_T *pCAN, uint32_t command)
{
	pCAN->CMR = command;
}

/**
 * @brief	Set Error Warning Limit for the CAN Controller
 * @param	pCAN	: Pointer to CAN peripheral block
 * @param	ewl		: expected limit
 * @return	None
 */
STATIC INLINE void IP_CAN_SetEWL(IP_CAN_001_T *pCAN, uint32_t ewl)
{
	pCAN->EWL = ewl & CAN_EWL_BITMASK;
}

/**
 * @brief	Get Error Warning Limit of the CAN Controller
 * @param	pCAN	: Pointer to CAN peripheral block
 * @return	Error warning limit value
 */
STATIC INLINE uint8_t IP_CAN_GetEWL(IP_CAN_001_T *pCAN)
{
	return CAN_EWL_VAL(pCAN->EWL);
}

/**
 * @brief	Get global status register contents of the CAN Controller
 * @param	pCAN	: Pointer to CAN peripheral block
 * @return	Gloabl Status register contents (Or'ed bit values of CAN_GSR_*)
 */
STATIC INLINE uint32_t IP_CAN_GetGlobalStatus(IP_CAN_001_T *pCAN)
{
	return pCAN->GSR;
}

/**
 * @brief	Get the status of the CAN Controller
 * @param	pCAN	: Pointer to CAN peripheral block
 * @return	Status (Or'ed bit values of CAN_SR_*(n) with n = CAN_BUFFER_1/2/3).
 */
STATIC INLINE uint32_t IP_CAN_GetStatus(IP_CAN_001_T *pCAN)
{
	return pCAN->SR;
}

/**
 * @brief	Enable the given interrupt of the CAN Controller
 * @param	pCAN	    : Pointer to CAN peripheral block
 * @param	IntMask	    : Interrupt Mask value (Or'ed bit values of CAN_IER_*).
 * @return	Nothing
 */
STATIC INLINE void IP_CAN_IntEnable(IP_CAN_001_T *pCAN, uint32_t IntMask) {
	pCAN->IER |= IntMask;
}

/**
 * @brief	Disable the given interrupt of the CAN Controller
 * @param	pCAN	    : Pointer to CAN peripheral block
 * @param	IntMask	    : Interrupt Mask value (Or'ed bit values of CAN_IER_*).
 * @return	Nothing
 */
STATIC INLINE void IP_CAN_IntDisable(IP_CAN_001_T *pCAN, uint32_t IntMask) {
	pCAN->IER &= (~IntMask) & CAN_IER_BITMASK;
}

/**
 * @brief	Get the interrupt status of the CAN Controller
 * @param	pCAN	: Pointer to CAN peripheral block
 * @return	Interrupt status (Or'ed bit values of CAN_ICR_* )
 */
STATIC INLINE uint32_t IP_CAN_GetIntStatus(IP_CAN_001_T *pCAN)
{
	return pCAN->ICR;
}

/**
 * @brief	Set CAN AF Mode
 * @param	pCanAF	: Pointer to CAN AF Register block
 * @param	AFMode	: Mode selected (Bit values of CANAF_AFMR_*)
 * @return	None
 */
STATIC INLINE void IP_CAN_AF_SetMode(IP_CAN_001_AF_T *pCanAF, uint32_t AFMode)
{
	pCanAF->AFMR = AFMode;
}

/**
 * @brief	Get CAN AF Mode
 * @param	pCanAF	: Pointer to CAN AF Register block
 * @return	Mode
 */
STATIC INLINE uint32_t IP_CAN_AF_GetMode(IP_CAN_001_AF_T *pCanAF)
{
	return pCanAF->AFMR;
}

/**
 * @brief	Initialize the CAN peripheral
 * @param	pCAN	: Pointer to CAN peripheral block
 * @return	None
 */
void IP_CAN_Init(IP_CAN_001_T *pCAN);

/**
 * @brief	Enable/Disable the specified mode in CAN controller
 * @param	pCAN	    : Pointer to CAN peripheral block
 * @param	Mode	    : Mode selected (Bit values of CAN_MOD_*)
 * @param	NewState	: ENABLE: Enable, DISABLE: Disable
 * @return	None
 */
void IP_CAN_SetMode(IP_CAN_001_T *pCAN, uint32_t Mode, FunctionalState NewState);

/**
 * @brief	Set Bus Timing for the CAN Controller
 * @param	pCAN	    : Pointer to CAN peripheral block
 * @param	pBusTiming	: Bus Timing information
 * @return	None
 */
void IP_CAN_SetBusTiming(IP_CAN_001_T *pCAN, IP_CAN_BUS_TIMING_T *pBusTiming);

/**
 * @brief	Get message received by the CAN Controller
 * @param	pCAN	: Pointer to CAN peripheral block
 * @param	pMsg    : Pointer to the buffer to store the received message
 * @return	SUCCESS (message information saved) or ERROR (no message received)
 */
Status IP_CAN_Receive(IP_CAN_001_T *pCAN, IP_CAN_MSG_T *pMsg);

/**
 * @brief	Request the CAN Controller to send message
 * @param	pCAN	: Pointer to CAN peripheral block
 * @param   TxBufID	: ID of buffer which will be used for transmit
 * @param	pMsg    : Pointer to the buffer of message which will be sent
 * @return	SUCCESS (message information saved) or ERROR (no message received)
 */
Status IP_CAN_Send(IP_CAN_001_T *pCAN, IP_CAN_BUFFER_ID_T TxBufID, IP_CAN_MSG_T *pMsg);

/**
 * @brief	Initialize CAN Acceptance Filter
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param	pCanAFRam	: Pointer to CAN AF RAM Register block
 * @return	Nothing
 */
void IP_CAN_AF_Init(IP_CAN_001_AF_T *pCanAF, IP_CAN_001_AF_RAM_T *pCanAFRam);

/**
 * @brief	Enable/Disable the interrupts of the CAN Controller in FullCAN Mode
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param	NewState	: ENABLE to enable/DISABLE to Disable
 * @return  Nothing
 */
void IP_CAN_FullCANIntConfig(IP_CAN_001_AF_T *pCanAF, FunctionalState NewState);

/**
 * @brief	Get FullCAN interrupt status of the object
 * @param	pCanAF	: Pointer to CAN AF Register block
 * @param	ObjID	: Object ID
 * @return  Interrupt Status
 */
uint32_t IP_CAN_GetFullCANIntStatus(IP_CAN_001_AF_T *pCanAF, uint8_t ObjID);

/**
 * @brief	Get FULLCANmessage automatically received by the AF
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param	ObjID	    : Object ID
 * @param	pMsg        : Pointer to the buffer storing the received message
 * @param	pSCC        : Pointer to the buffer storing the controller ID of the received message
 * @return	SUCCESS (message information saved) or ERROR (no message received)
 */
Status IP_CAN_FullCANReceive(IP_CAN_001_AF_T *pCanAF, IP_CAN_001_AF_RAM_T *pCanAFRam,
							 uint8_t ObjID, IP_CAN_MSG_T *pMsg, uint8_t *pSCC);

/**
 * @brief	Clear CAN AF LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @return	None
 */
void IP_CAN_ClearAFLUT(IP_CAN_001_AF_T *pCanAF, IP_CAN_001_AF_RAM_T *pCanAFRam);

/**
 * @brief	Set CAN AF LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   pAFSections : Pointer to buffer storing AF Section Data
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_SetAFLUT(IP_CAN_001_AF_T *pCanAF, IP_CAN_001_AF_RAM_T *pCanAFRam, IP_CAN_AF_LUT_T *pAFSections);

/**
 * @brief	Insert a FullCAN Entry into the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   pEntry      : Pointer to the entry which will be inserted
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_InsertFullCANEntry(IP_CAN_001_AF_T *pCanAF,
								 IP_CAN_001_AF_RAM_T *pCanAFRam,
								 IP_CAN_STD_ID_Entry_T *pEntry);

/**
 * @brief	Insert an individual Standard  Entry into the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   pEntry      : Pointer to the entry which will be inserted
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_InsertIndividualSTDEntry(IP_CAN_001_AF_T *pCanAF,
									   IP_CAN_001_AF_RAM_T *pCanAFRam,
									   IP_CAN_STD_ID_Entry_T *pEntry);

/**
 * @brief	Insert an Group Standard  Entry into the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   pEntry      : Pointer to the entry which will be inserted
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_InsertGroupSTDEntry(IP_CAN_001_AF_T *pCanAF,
								  IP_CAN_001_AF_RAM_T *pCanAFRam,
								  IP_CAN_STD_ID_RANGE_Entry_T *pEntry);

/**
 * @brief	Insert an individual Extended  Entry into the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   pEntry      : Pointer to the entry which will be inserted
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_InsertIndividualEXTEntry(IP_CAN_001_AF_T *pCanAF,
									   IP_CAN_001_AF_RAM_T *pCanAFRam,
									   IP_CAN_EXT_ID_Entry_T *pEntry);

/**
 * @brief	Insert an Group Extended  Entry into the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   pEntry      : Pointer to the entry which will be inserted
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_InsertGroupEXTEntry(IP_CAN_001_AF_T *pCanAF,
								  IP_CAN_001_AF_RAM_T *pCanAFRam,
								  IP_CAN_EXT_ID_RANGE_Entry_T *pEntry);

/**
 * @brief	Remove a FullCAN Entry from the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   Position    : Position of the entry in the Full CAN section (started from 0)
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_RemoveFullCANEntry(IP_CAN_001_AF_T *pCanAF,
								 IP_CAN_001_AF_RAM_T *pCanAFRam,
								 int16_t Position);

/**
 * @brief	Remove an individual Standard Entry from the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   Position    : Position of the entry in the Individual STD section (started from 0)
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_RemoveIndividualSTDEntry(IP_CAN_001_AF_T *pCanAF,
									   IP_CAN_001_AF_RAM_T *pCanAFRam,
									   int16_t Position);

/**
 * @brief	Remove an Group Standard Entry from the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   Position    : Position of the entry in the Group STD section (started from 0)
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_RemoveGroupSTDEntry(IP_CAN_001_AF_T *pCanAF,
								  IP_CAN_001_AF_RAM_T *pCanAFRam,
								  int16_t Position);

/**
 * @brief	Remove an individual Extended Entry from the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   Position    : Position of the entry in the Individual EXT section (started from 0)
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_RemoveIndividualEXTEntry(IP_CAN_001_AF_T *pCanAF,
									   IP_CAN_001_AF_RAM_T *pCanAFRam,
									   int16_t Position);

/**
 * @brief	Remove an Group Extended  Entry from the current LUT
 * @param	pCanAF      : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   Position    : Position of the entry in the Group EXT section (started from 0)
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_RemoveGroupEXTEntry(IP_CAN_001_AF_T *pCanAF,
								  IP_CAN_001_AF_RAM_T *pCanAFRam,
								  int16_t Position);

/**
 * @brief	Get the number of entries of the given section
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   SectionID	: Section ID
 * @return	Number of entries
 */
uint16_t IP_CAN_GetEntriesNum(IP_CAN_001_AF_T *pCanAF,
							  IP_CAN_001_AF_RAM_T *pCanAFRam,
							  IP_CAN_AF_RAM_SECTION_T SectionID);

/**
 * @brief	Read a FullCAN Entry into from current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   Position    : Position of the entry in the given section (started from 0)
 * @param   pEntry      : Pointer to the entry which will be inserted
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_ReadFullCANEntry(IP_CAN_001_AF_T *pCanAF,
							   IP_CAN_001_AF_RAM_T *pCanAFRam,
							   uint16_t Position,
							   IP_CAN_STD_ID_Entry_T *pEntry);

/**
 * @brief	Read an individual Standard  Entry from the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   Position    : Position of the entry in the given section (started from 0)
 * @param   pEntry      : Pointer to the entry which will be inserted
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_ReadIndividualSTDEntry(IP_CAN_001_AF_T *pCanAF,
									 IP_CAN_001_AF_RAM_T *pCanAFRam,
									 uint16_t Position,
									 IP_CAN_STD_ID_Entry_T *pEntry);

/**
 * @brief	Read an Group Standard  Entry from the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   Position    : Position of the entry in the given section (started from 0)
 * @param   pEntry      : Pointer to the entry which will be inserted
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_ReadGroupSTDEntry(IP_CAN_001_AF_T *pCanAF,
								IP_CAN_001_AF_RAM_T *pCanAFRam,
								uint16_t Position,
								IP_CAN_STD_ID_RANGE_Entry_T *pEntry);

/**
 * @brief	Read an individual Extended  Entry from the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   Position    : Position of the entry in the given section (started from 0)
 * @param   pEntry      : Pointer to the entry which will be inserted
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_ReadIndividualEXTEntry(IP_CAN_001_AF_T *pCanAF,
									 IP_CAN_001_AF_RAM_T *pCanAFRam,
									 uint16_t Position,
									 IP_CAN_EXT_ID_Entry_T *pEntry);

/**
 * @brief	Read an Group Extended  Entry from the current LUT
 * @param	pCanAF	    : Pointer to CAN AF Register block
 * @param   pCanAFRam   : Pointer to CAN AF RAM Register block
 * @param   Position    : Position of the entry in the given section (started from 0)
 * @param   pEntry      : Pointer to the entry which will be inserted
 * @return	SUCCESS/ERROR
 */
Status IP_CAN_ReadGroupEXTEntry(IP_CAN_001_AF_T *pCanAF,
								IP_CAN_001_AF_RAM_T *pCanAFRam,
								uint16_t Position,
								IP_CAN_EXT_ID_RANGE_Entry_T *pEntry);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __CAN_001_H_ */
