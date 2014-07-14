/******************************************************************************
*
* (c) Copyright 2010-2013 Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xcanps_hw.h
*
* This header file contains the identifiers and basic driver functions (or
* macros) that can be used to access the device. Other driver functions
* are defined in xcanps.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- -----  -------- -----------------------------------------------
* 1.00a xd/sv  01/12/10 First release
* 1.01a sbs    12/27/11 Updated the Register/bit definitions
*                       Changed XCANPS_RXFWIR_RXFLL_MASK to XCANPS_WIR_FW_MASK
*                       Changed XCANPS_RXWIR_OFFSET to XCANPS_WIR_OFFSET
*			Added XCANPS_IXR_TXFEMP_MASK for Tx Fifo Empty
*			Changed XCANPS_IXR_RXFLL_MASK to
*			XCANPS_IXR_RXFWMFLL_MASK
* 			Changed
*			XCANPS_TXBUF_ID_OFFSET to XCANPS_TXHPB_ID_OFFSET
* 			XCANPS_TXBUF_DLC_OFFSET to XCANPS_TXHPB_DLC_OFFSET
*			XCANPS_TXBUF_DW1_OFFSET  to XCANPS_TXHPB_DW1_OFFSET
*			XCANPS_TXBUF_DW2_OFFSET  to XCANPS_TXHPB_DW2_OFFSET
* 1.02a adk   08/08/13  Updated for inclding the function prototype
* </pre>
*
******************************************************************************/

#ifndef XCANPS_HW_H		/* prevent circular inclusions */
#define XCANPS_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif


/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

/** @name Register offsets for the CAN. Each register is 32 bits.
 *  @{
 */
#define XCANPS_SRR_OFFSET	  	0x00 /**< Software Reset Register */
#define XCANPS_MSR_OFFSET	  	0x04 /**< Mode Select Register */
#define XCANPS_BRPR_OFFSET	  	0x08 /**< Baud Rate Prescaler */
#define XCANPS_BTR_OFFSET	  	0x0C /**< Bit Timing Register */
#define XCANPS_ECR_OFFSET	  	0x10 /**< Error Counter Register */
#define XCANPS_ESR_OFFSET	  	0x14 /**< Error Status Register */
#define XCANPS_SR_OFFSET	  	0x18 /**< Status Register */

#define XCANPS_ISR_OFFSET	  	0x1C /**< Interrupt Status Register */
#define XCANPS_IER_OFFSET	  	0x20 /**< Interrupt Enable Register */
#define XCANPS_ICR_OFFSET	  	0x24 /**< Interrupt Clear Register */
#define XCANPS_TCR_OFFSET	  	0x28 /**< Timestamp Control Register */
#define XCANPS_WIR_OFFSET	  	0x2C /**< Watermark Interrupt Reg */

#define XCANPS_TXFIFO_ID_OFFSET  	0x30 /**< TX FIFO ID */
#define XCANPS_TXFIFO_DLC_OFFSET 	0x34 /**< TX FIFO DLC */
#define XCANPS_TXFIFO_DW1_OFFSET	0x38 /**< TX FIFO Data Word 1 */
#define XCANPS_TXFIFO_DW2_OFFSET 	0x3C /**< TX FIFO Data Word 2 */

#define XCANPS_TXHPB_ID_OFFSET   	0x40 /**< TX High Priority Buffer ID */
#define XCANPS_TXHPB_DLC_OFFSET  	0x44 /**< TX High Priority Buffer DLC */
#define XCANPS_TXHPB_DW1_OFFSET  	0x48 /**< TX High Priority Buf Data 1 */
#define XCANPS_TXHPB_DW2_OFFSET  	0x4C /**< TX High Priority Buf Data Word 2 */

#define XCANPS_RXFIFO_ID_OFFSET  	0x50 /**< RX FIFO ID */
#define XCANPS_RXFIFO_DLC_OFFSET 	0x54 /**< RX FIFO DLC */
#define XCANPS_RXFIFO_DW1_OFFSET 	0x58 /**< RX FIFO Data Word 1 */
#define XCANPS_RXFIFO_DW2_OFFSET 	0x5C /**< RX FIFO Data Word 2 */

#define XCANPS_AFR_OFFSET	  	0x60 /**< Acceptance Filter Register */
#define XCANPS_AFMR1_OFFSET	  	0x64 /**< Acceptance Filter Mask 1 */
#define XCANPS_AFIR1_OFFSET	  	0x68 /**< Acceptance Filter ID  1 */
#define XCANPS_AFMR2_OFFSET	  	0x6C /**< Acceptance Filter Mask  2 */
#define XCANPS_AFIR2_OFFSET	  	0x70 /**< Acceptance Filter ID 2 */
#define XCANPS_AFMR3_OFFSET	  	0x74 /**< Acceptance Filter Mask 3 */
#define XCANPS_AFIR3_OFFSET	  	0x78 /**< Acceptance Filter ID 3 */
#define XCANPS_AFMR4_OFFSET	  	0x7C /**< Acceptance Filter Mask  4 */
#define XCANPS_AFIR4_OFFSET	  	0x80 /**< Acceptance Filter ID 4 */
/* @} */

/** @name Software Reset Register (SRR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_SRR_CEN_MASK	0x00000002  /**< Can Enable */
#define XCANPS_SRR_SRST_MASK	0x00000001  /**< Reset */
/* @} */

/** @name Mode Select Register (MSR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_MSR_SNOOP_MASK	0x00000004 /**< Snoop Mode Select */
#define XCANPS_MSR_LBACK_MASK	0x00000002 /**< Loop Back Mode Select */
#define XCANPS_MSR_SLEEP_MASK	0x00000001 /**< Sleep Mode Select */
/* @} */

/** @name Baud Rate Prescaler register (BRPR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_BRPR_BRP_MASK	0x000000FF /**< Baud Rate Prescaler */
/* @} */

/** @name Bit Timing Register (BTR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_BTR_SJW_MASK	0x00000180 /**< Synchronization Jump Width */
#define XCANPS_BTR_SJW_SHIFT	7
#define XCANPS_BTR_TS2_MASK	0x00000070 /**< Time Segment 2 */
#define XCANPS_BTR_TS2_SHIFT	4
#define XCANPS_BTR_TS1_MASK	0x0000000F /**< Time Segment 1 */
/* @} */

/** @name Error Counter Register (ECR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_ECR_REC_MASK	0x0000FF00 /**< Receive Error Counter */
#define XCANPS_ECR_REC_SHIFT	8
#define XCANPS_ECR_TEC_MASK	0x000000FF /**< Transmit Error Counter */
/* @} */

/** @name Error Status Register (ESR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_ESR_ACKER_MASK	0x00000010 /**< ACK Error */
#define XCANPS_ESR_BERR_MASK	0x00000008 /**< Bit Error */
#define XCANPS_ESR_STER_MASK	0x00000004 /**< Stuff Error */
#define XCANPS_ESR_FMER_MASK	0x00000002 /**< Form Error */
#define XCANPS_ESR_CRCER_MASK	0x00000001 /**< CRC Error */
/* @} */

/** @name Status Register (SR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_SR_SNOOP_MASK	0x00001000 /**< Snoop Mask */
#define XCANPS_SR_ACFBSY_MASK	0x00000800 /**< Acceptance Filter busy */
#define XCANPS_SR_TXFLL_MASK	0x00000400 /**< TX FIFO is full */
#define XCANPS_SR_TXBFLL_MASK	0x00000200 /**< TX High Priority Buffer full */
#define XCANPS_SR_ESTAT_MASK	0x00000180 /**< Error Status */
#define XCANPS_SR_ESTAT_SHIFT	7
#define XCANPS_SR_ERRWRN_MASK	0x00000040 /**< Error Warning */
#define XCANPS_SR_BBSY_MASK	0x00000020 /**< Bus Busy */
#define XCANPS_SR_BIDLE_MASK	0x00000010 /**< Bus Idle */
#define XCANPS_SR_NORMAL_MASK	0x00000008 /**< Normal Mode */
#define XCANPS_SR_SLEEP_MASK	0x00000004 /**< Sleep Mode */
#define XCANPS_SR_LBACK_MASK	0x00000002 /**< Loop Back Mode */
#define XCANPS_SR_CONFIG_MASK	0x00000001 /**< Configuration Mode */
/* @} */

/** @name Interrupt Status/Enable/Clear Register Bit Definitions and Masks
 *  @{
 */
#define XCANPS_IXR_TXFEMP_MASK   0x00004000 /**< Tx Fifo Empty Interrupt */
#define XCANPS_IXR_TXFWMEMP_MASK 0x00002000 /**< Tx Fifo Watermark Empty */
#define XCANPS_IXR_RXFWMFLL_MASK 0x00001000 /**< Rx FIFO Watermark Full */
#define XCANPS_IXR_WKUP_MASK	0x00000800 /**< Wake up Interrupt */
#define XCANPS_IXR_SLP_MASK	0x00000400 /**< Sleep Interrupt */
#define XCANPS_IXR_BSOFF_MASK	0x00000200 /**< Bus Off Interrupt */
#define XCANPS_IXR_ERROR_MASK	0x00000100 /**< Error Interrupt */
#define XCANPS_IXR_RXNEMP_MASK	0x00000080 /**< RX FIFO Not Empty Interrupt */
#define XCANPS_IXR_RXOFLW_MASK	0x00000040 /**< RX FIFO Overflow Interrupt */
#define XCANPS_IXR_RXUFLW_MASK	0x00000020 /**< RX FIFO Underflow Interrupt */
#define XCANPS_IXR_RXOK_MASK	0x00000010 /**< New Message Received Intr */
#define XCANPS_IXR_TXBFLL_MASK	0x00000008 /**< TX High Priority Buf Full */
#define XCANPS_IXR_TXFLL_MASK	0x00000004 /**< TX FIFO Full Interrupt */
#define XCANPS_IXR_TXOK_MASK	0x00000002 /**< TX Successful Interrupt */
#define XCANPS_IXR_ARBLST_MASK	0x00000001 /**< Arbitration Lost Interrupt */
#define XCANPS_IXR_ALL		(XCANPS_IXR_RXFWMFLL_MASK | \
				XCANPS_IXR_WKUP_MASK   | \
				XCANPS_IXR_SLP_MASK	| \
				XCANPS_IXR_BSOFF_MASK  | \
				XCANPS_IXR_ERROR_MASK  | \
				XCANPS_IXR_RXNEMP_MASK | \
 				XCANPS_IXR_RXOFLW_MASK | \
				XCANPS_IXR_RXUFLW_MASK | \
	 			XCANPS_IXR_RXOK_MASK   | \
				XCANPS_IXR_TXBFLL_MASK | \
				XCANPS_IXR_TXFLL_MASK  | \
				XCANPS_IXR_TXOK_MASK   | \
				XCANPS_IXR_ARBLST_MASK)
/* @} */

/** @name CAN Timestamp Control Register (TCR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_TCR_CTS_MASK	0x00000001 /**< Clear Timestamp counter mask */
/* @} */

/** @name CAN Watermark Register (WIR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_WIR_FW_MASK   	0x0000003F /**< Rx Full Threshold mask */
#define XCANPS_WIR_EW_MASK 	0x00003F00 /**< Tx Empty Threshold mask */
#define XCANPS_WIR_EW_SHIFT 	0x00000008 /**< Tx Empty Threshold shift */

/* @} */

/** @name CAN Frame Identifier (TX High Priority Buffer/TX/RX/Acceptance Filter
				Mask/Acceptance Filter ID)
 *  @{
 */
#define XCANPS_IDR_ID1_MASK	0xFFE00000 /**< Standard Messg Identifier */
#define XCANPS_IDR_ID1_SHIFT	21
#define XCANPS_IDR_SRR_MASK	0x00100000 /**< Substitute Remote TX Req */
#define XCANPS_IDR_SRR_SHIFT	20
#define XCANPS_IDR_IDE_MASK	0x00080000 /**< Identifier Extension */
#define XCANPS_IDR_IDE_SHIFT	19
#define XCANPS_IDR_ID2_MASK	0x0007FFFE /**< Extended Message Ident */
#define XCANPS_IDR_ID2_SHIFT	1
#define XCANPS_IDR_RTR_MASK	0x00000001 /**< Remote TX Request */
/* @} */

/** @name CAN Frame Data Length Code (TX High Priority Buffer/TX/RX)
 *  @{
 */
#define XCANPS_DLCR_DLC_MASK	 0xF0000000	/**< Data Length Code */
#define XCANPS_DLCR_DLC_SHIFT	 28
#define XCANPS_DLCR_TIMESTAMP_MASK 0x0000FFFF	/**< Timestamp Mask (Rx only) */

/* @} */

/** @name CAN Frame Data Word 1 (TX High Priority Buffer/TX/RX)
 *  @{
 */
#define XCANPS_DW1R_DB0_MASK	0xFF000000 /**< Data Byte 0 */
#define XCANPS_DW1R_DB0_SHIFT	24
#define XCANPS_DW1R_DB1_MASK	0x00FF0000 /**< Data Byte 1 */
#define XCANPS_DW1R_DB1_SHIFT	16
#define XCANPS_DW1R_DB2_MASK	0x0000FF00 /**< Data Byte 2 */
#define XCANPS_DW1R_DB2_SHIFT	8
#define XCANPS_DW1R_DB3_MASK	0x000000FF /**< Data Byte 3 */
/* @} */

/** @name CAN Frame Data Word 2 (TX High Priority Buffer/TX/RX)
 *  @{
 */
#define XCANPS_DW2R_DB4_MASK	0xFF000000 /**< Data Byte 4 */
#define XCANPS_DW2R_DB4_SHIFT	24
#define XCANPS_DW2R_DB5_MASK	0x00FF0000 /**< Data Byte 5 */
#define XCANPS_DW2R_DB5_SHIFT	16
#define XCANPS_DW2R_DB6_MASK	0x0000FF00 /**< Data Byte 6 */
#define XCANPS_DW2R_DB6_SHIFT	8
#define XCANPS_DW2R_DB7_MASK	0x000000FF /**< Data Byte 7 */
/* @} */

/** @name Acceptance Filter Register (AFR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_AFR_UAF4_MASK	0x00000008 /**< Use Acceptance Filter No.4 */
#define XCANPS_AFR_UAF3_MASK	0x00000004 /**< Use Acceptance Filter No.3 */
#define XCANPS_AFR_UAF2_MASK	0x00000002 /**< Use Acceptance Filter No.2 */
#define XCANPS_AFR_UAF1_MASK	0x00000001 /**< Use Acceptance Filter No.1 */
#define XCANPS_AFR_UAF_ALL_MASK	(XCANPS_AFR_UAF4_MASK | \
					XCANPS_AFR_UAF3_MASK | \
					XCANPS_AFR_UAF2_MASK | \
					XCANPS_AFR_UAF1_MASK)
/* @} */

/** @name CAN frame length constants
 *  @{
 */
#define XCANPS_MAX_FRAME_SIZE 16 /**< Maximum CAN frame length in bytes */
/* @} */

/* For backwards compatibilty */
#define XCANPS_TXBUF_ID_OFFSET   XCANPS_TXHPB_ID_OFFSET
#define XCANPS_TXBUF_DLC_OFFSET  XCANPS_TXHPB_DLC_OFFSET
#define XCANPS_TXBUF_DW1_OFFSET  XCANPS_TXHPB_DW1_OFFSET
#define XCANPS_TXBUF_DW2_OFFSET  XCANPS_TXHPB_DW2_OFFSET

#define XCANPS_RXFWIR_RXFLL_MASK XCANPS_WIR_FW_MASK
#define XCANPS_RXWIR_OFFSET 	 XCANPS_WIR_OFFSET
#define XCANPS_IXR_RXFLL_MASK 	 XCANPS_IXR_RXFWMFLL_MASK




/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* This macro reads the given register.
*
* @param	BaseAddr is the base address of the device.
* @param	RegOffset is the register offset to be read.
*
* @return	The 32-bit value of the register
*
* @note		None.
*
*****************************************************************************/
#define XCanPs_ReadReg(BaseAddr, RegOffset) \
		Xil_In32((BaseAddr) + (RegOffset))


/****************************************************************************/
/**
*
* This macro writes the given register.
*
* @param	BaseAddr is the base address of the device.
* @param	RegOffset is the register offset to be written.
* @param	Data is the 32-bit value to write to the register.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
#define XCanPs_WriteReg(BaseAddr, RegOffset, Data) \
		Xil_Out32((BaseAddr) + (RegOffset), (Data))

/************************** Function Prototypes ******************************/
/*
 * Perform reset operation to the CanPs interface
 */
void XCanPs_ResetHw(u32 BaseAddr);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */

