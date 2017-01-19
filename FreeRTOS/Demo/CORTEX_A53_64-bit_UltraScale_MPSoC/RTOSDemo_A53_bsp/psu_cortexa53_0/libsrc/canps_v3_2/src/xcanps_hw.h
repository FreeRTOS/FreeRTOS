/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xcanps_hw.h
* @addtogroup canps_v3_0
* @{
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
* 3.00  kvn   02/13/15  Modified code for MISRA-C:2012 compliance.
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
#define XCANPS_SRR_OFFSET	  	0x00000000U /**< Software Reset Register */
#define XCANPS_MSR_OFFSET	  	0x00000004U /**< Mode Select Register */
#define XCANPS_BRPR_OFFSET	  	0x00000008U /**< Baud Rate Prescaler */
#define XCANPS_BTR_OFFSET	  	0x0000000CU /**< Bit Timing Register */
#define XCANPS_ECR_OFFSET	  	0x00000010U /**< Error Counter Register */
#define XCANPS_ESR_OFFSET	  	0x00000014U /**< Error Status Register */
#define XCANPS_SR_OFFSET	  	0x00000018U /**< Status Register */

#define XCANPS_ISR_OFFSET	  	0x0000001CU /**< Interrupt Status Register */
#define XCANPS_IER_OFFSET	  	0x00000020U /**< Interrupt Enable Register */
#define XCANPS_ICR_OFFSET	  	0x00000024U /**< Interrupt Clear Register */
#define XCANPS_TCR_OFFSET	  	0x00000028U /**< Timestamp Control Register */
#define XCANPS_WIR_OFFSET	  	0x0000002CU /**< Watermark Interrupt Reg */

#define XCANPS_TXFIFO_ID_OFFSET  	0x00000030U /**< TX FIFO ID */
#define XCANPS_TXFIFO_DLC_OFFSET 	0x00000034U /**< TX FIFO DLC */
#define XCANPS_TXFIFO_DW1_OFFSET	0x00000038U /**< TX FIFO Data Word 1 */
#define XCANPS_TXFIFO_DW2_OFFSET 	0x0000003CU /**< TX FIFO Data Word 2 */

#define XCANPS_TXHPB_ID_OFFSET   	0x00000040U /**< TX High Priority Buffer ID */
#define XCANPS_TXHPB_DLC_OFFSET  	0x00000044U /**< TX High Priority Buffer DLC */
#define XCANPS_TXHPB_DW1_OFFSET  	0x00000048U /**< TX High Priority Buf Data 1 */
#define XCANPS_TXHPB_DW2_OFFSET  	0x0000004CU /**< TX High Priority Buf Data Word 2 */

#define XCANPS_RXFIFO_ID_OFFSET  	0x00000050U /**< RX FIFO ID */
#define XCANPS_RXFIFO_DLC_OFFSET 	0x00000054U /**< RX FIFO DLC */
#define XCANPS_RXFIFO_DW1_OFFSET 	0x00000058U /**< RX FIFO Data Word 1 */
#define XCANPS_RXFIFO_DW2_OFFSET 	0x0000005CU /**< RX FIFO Data Word 2 */

#define XCANPS_AFR_OFFSET	  	0x00000060U /**< Acceptance Filter Register */
#define XCANPS_AFMR1_OFFSET	  	0x00000064U /**< Acceptance Filter Mask 1 */
#define XCANPS_AFIR1_OFFSET	  	0x00000068U /**< Acceptance Filter ID  1 */
#define XCANPS_AFMR2_OFFSET	  	0x0000006CU /**< Acceptance Filter Mask  2 */
#define XCANPS_AFIR2_OFFSET	  	0x00000070U /**< Acceptance Filter ID 2 */
#define XCANPS_AFMR3_OFFSET	  	0x00000074U /**< Acceptance Filter Mask 3 */
#define XCANPS_AFIR3_OFFSET	  	0x00000078U /**< Acceptance Filter ID 3 */
#define XCANPS_AFMR4_OFFSET	  	0x0000007CU /**< Acceptance Filter Mask  4 */
#define XCANPS_AFIR4_OFFSET	  	0x00000080U /**< Acceptance Filter ID 4 */
/* @} */

/** @name Software Reset Register (SRR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_SRR_CEN_MASK		0x00000002U  /**< Can Enable */
#define XCANPS_SRR_SRST_MASK	0x00000001U  /**< Reset */
/* @} */

/** @name Mode Select Register (MSR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_MSR_SNOOP_MASK	0x00000004U /**< Snoop Mode Select */
#define XCANPS_MSR_LBACK_MASK	0x00000002U /**< Loop Back Mode Select */
#define XCANPS_MSR_SLEEP_MASK	0x00000001U /**< Sleep Mode Select */
/* @} */

/** @name Baud Rate Prescaler register (BRPR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_BRPR_BRP_MASK	0x000000FFU /**< Baud Rate Prescaler */
/* @} */

/** @name Bit Timing Register (BTR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_BTR_SJW_MASK	0x00000180U /**< Synchronization Jump Width */
#define XCANPS_BTR_SJW_SHIFT	7U
#define XCANPS_BTR_TS2_MASK	0x00000070U /**< Time Segment 2 */
#define XCANPS_BTR_TS2_SHIFT	4U
#define XCANPS_BTR_TS1_MASK	0x0000000FU /**< Time Segment 1 */
/* @} */

/** @name Error Counter Register (ECR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_ECR_REC_MASK	0x0000FF00U /**< Receive Error Counter */
#define XCANPS_ECR_REC_SHIFT		 8U
#define XCANPS_ECR_TEC_MASK	0x000000FFU /**< Transmit Error Counter */
/* @} */

/** @name Error Status Register (ESR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_ESR_ACKER_MASK	0x00000010U /**< ACK Error */
#define XCANPS_ESR_BERR_MASK	0x00000008U /**< Bit Error */
#define XCANPS_ESR_STER_MASK	0x00000004U /**< Stuff Error */
#define XCANPS_ESR_FMER_MASK	0x00000002U /**< Form Error */
#define XCANPS_ESR_CRCER_MASK	0x00000001U /**< CRC Error */
/* @} */

/** @name Status Register (SR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_SR_SNOOP_MASK	0x00001000U /**< Snoop Mask */
#define XCANPS_SR_ACFBSY_MASK	0x00000800U /**< Acceptance Filter busy */
#define XCANPS_SR_TXFLL_MASK	0x00000400U /**< TX FIFO is full */
#define XCANPS_SR_TXBFLL_MASK	0x00000200U /**< TX High Priority Buffer full */
#define XCANPS_SR_ESTAT_MASK	0x00000180U /**< Error Status */
#define XCANPS_SR_ESTAT_SHIFT			 7U
#define XCANPS_SR_ERRWRN_MASK	0x00000040U /**< Error Warning */
#define XCANPS_SR_BBSY_MASK		0x00000020U /**< Bus Busy */
#define XCANPS_SR_BIDLE_MASK	0x00000010U /**< Bus Idle */
#define XCANPS_SR_NORMAL_MASK	0x00000008U /**< Normal Mode */
#define XCANPS_SR_SLEEP_MASK	0x00000004U /**< Sleep Mode */
#define XCANPS_SR_LBACK_MASK	0x00000002U /**< Loop Back Mode */
#define XCANPS_SR_CONFIG_MASK	0x00000001U /**< Configuration Mode */
/* @} */

/** @name Interrupt Status/Enable/Clear Register Bit Definitions and Masks
 *  @{
 */
#define XCANPS_IXR_TXFEMP_MASK   0x00004000U /**< Tx Fifo Empty Interrupt */
#define XCANPS_IXR_TXFWMEMP_MASK 0x00002000U /**< Tx Fifo Watermark Empty */
#define XCANPS_IXR_RXFWMFLL_MASK 0x00001000U /**< Rx FIFO Watermark Full */
#define XCANPS_IXR_WKUP_MASK	 0x00000800U /**< Wake up Interrupt */
#define XCANPS_IXR_SLP_MASK		0x00000400U /**< Sleep Interrupt */
#define XCANPS_IXR_BSOFF_MASK	0x00000200U /**< Bus Off Interrupt */
#define XCANPS_IXR_ERROR_MASK	0x00000100U /**< Error Interrupt */
#define XCANPS_IXR_RXNEMP_MASK	0x00000080U /**< RX FIFO Not Empty Interrupt */
#define XCANPS_IXR_RXOFLW_MASK	0x00000040U /**< RX FIFO Overflow Interrupt */
#define XCANPS_IXR_RXUFLW_MASK	0x00000020U /**< RX FIFO Underflow Interrupt */
#define XCANPS_IXR_RXOK_MASK	0x00000010U /**< New Message Received Intr */
#define XCANPS_IXR_TXBFLL_MASK	0x00000008U /**< TX High Priority Buf Full */
#define XCANPS_IXR_TXFLL_MASK	0x00000004U /**< TX FIFO Full Interrupt */
#define XCANPS_IXR_TXOK_MASK	0x00000002U /**< TX Successful Interrupt */
#define XCANPS_IXR_ARBLST_MASK	0x00000001U /**< Arbitration Lost Interrupt */
#define XCANPS_IXR_ALL		((u32)XCANPS_IXR_RXFWMFLL_MASK | \
				(u32)XCANPS_IXR_WKUP_MASK   | \
				(u32)XCANPS_IXR_SLP_MASK	| \
				(u32)XCANPS_IXR_BSOFF_MASK  | \
				(u32)XCANPS_IXR_ERROR_MASK  | \
				(u32)XCANPS_IXR_RXNEMP_MASK | \
				(u32)XCANPS_IXR_RXOFLW_MASK | \
				(u32)XCANPS_IXR_RXUFLW_MASK | \
				(u32)XCANPS_IXR_RXOK_MASK   | \
				(u32)XCANPS_IXR_TXBFLL_MASK | \
				(u32)XCANPS_IXR_TXFLL_MASK  | \
				(u32)XCANPS_IXR_TXOK_MASK   | \
				(u32)XCANPS_IXR_ARBLST_MASK)
/* @} */

/** @name CAN Timestamp Control Register (TCR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_TCR_CTS_MASK	0x00000001U /**< Clear Timestamp counter mask */
/* @} */

/** @name CAN Watermark Register (WIR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_WIR_FW_MASK   	0x0000003FU /**< Rx Full Threshold mask */
#define XCANPS_WIR_EW_MASK 	0x00003F00U /**< Tx Empty Threshold mask */
#define XCANPS_WIR_EW_SHIFT 	0x00000008U /**< Tx Empty Threshold shift */

/* @} */

/** @name CAN Frame Identifier (TX High Priority Buffer/TX/RX/Acceptance Filter
				Mask/Acceptance Filter ID)
 *  @{
 */
#define XCANPS_IDR_ID1_MASK	0xFFE00000U /**< Standard Messg Identifier */
#define XCANPS_IDR_ID1_SHIFT	21U
#define XCANPS_IDR_SRR_MASK	0x00100000U /**< Substitute Remote TX Req */
#define XCANPS_IDR_SRR_SHIFT	20U
#define XCANPS_IDR_IDE_MASK	0x00080000U /**< Identifier Extension */
#define XCANPS_IDR_IDE_SHIFT	19U
#define XCANPS_IDR_ID2_MASK	0x0007FFFEU /**< Extended Message Ident */
#define XCANPS_IDR_ID2_SHIFT	1U
#define XCANPS_IDR_RTR_MASK	0x00000001U /**< Remote TX Request */
/* @} */

/** @name CAN Frame Data Length Code (TX High Priority Buffer/TX/RX)
 *  @{
 */
#define XCANPS_DLCR_DLC_MASK	 0xF0000000U	/**< Data Length Code */
#define XCANPS_DLCR_DLC_SHIFT	 28U
#define XCANPS_DLCR_TIMESTAMP_MASK 0x0000FFFFU	/**< Timestamp Mask (Rx only) */

/* @} */

/** @name CAN Frame Data Word 1 (TX High Priority Buffer/TX/RX)
 *  @{
 */
#define XCANPS_DW1R_DB0_MASK	0xFF000000U /**< Data Byte 0 */
#define XCANPS_DW1R_DB0_SHIFT	24U
#define XCANPS_DW1R_DB1_MASK	0x00FF0000U /**< Data Byte 1 */
#define XCANPS_DW1R_DB1_SHIFT	16U
#define XCANPS_DW1R_DB2_MASK	0x0000FF00U /**< Data Byte 2 */
#define XCANPS_DW1R_DB2_SHIFT	8U
#define XCANPS_DW1R_DB3_MASK	0x000000FFU /**< Data Byte 3 */
/* @} */

/** @name CAN Frame Data Word 2 (TX High Priority Buffer/TX/RX)
 *  @{
 */
#define XCANPS_DW2R_DB4_MASK	0xFF000000U /**< Data Byte 4 */
#define XCANPS_DW2R_DB4_SHIFT	24U
#define XCANPS_DW2R_DB5_MASK	0x00FF0000U /**< Data Byte 5 */
#define XCANPS_DW2R_DB5_SHIFT	16U
#define XCANPS_DW2R_DB6_MASK	0x0000FF00U /**< Data Byte 6 */
#define XCANPS_DW2R_DB6_SHIFT	8U
#define XCANPS_DW2R_DB7_MASK	0x000000FFU /**< Data Byte 7 */
/* @} */

/** @name Acceptance Filter Register (AFR) Bit Definitions and Masks
 *  @{
 */
#define XCANPS_AFR_UAF4_MASK	0x00000008U /**< Use Acceptance Filter No.4 */
#define XCANPS_AFR_UAF3_MASK	0x00000004U /**< Use Acceptance Filter No.3 */
#define XCANPS_AFR_UAF2_MASK	0x00000002U /**< Use Acceptance Filter No.2 */
#define XCANPS_AFR_UAF1_MASK	0x00000001U /**< Use Acceptance Filter No.1 */
#define XCANPS_AFR_UAF_ALL_MASK	((u32)XCANPS_AFR_UAF4_MASK | \
					(u32)XCANPS_AFR_UAF3_MASK | \
					(u32)XCANPS_AFR_UAF2_MASK | \
					(u32)XCANPS_AFR_UAF1_MASK)
/* @} */

/** @name CAN frame length constants
 *  @{
 */
#define XCANPS_MAX_FRAME_SIZE sizeof(u32)*16U /**< Maximum CAN frame length in bytes */
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
		Xil_In32((BaseAddr) + (u32)(RegOffset))


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
		Xil_Out32((BaseAddr) + (u32)(RegOffset), (u32)(Data))

/************************** Function Prototypes ******************************/
/*
 * Perform reset operation to the CanPs interface
 */
void XCanPs_ResetHw(u32 BaseAddr);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
/** @} */
