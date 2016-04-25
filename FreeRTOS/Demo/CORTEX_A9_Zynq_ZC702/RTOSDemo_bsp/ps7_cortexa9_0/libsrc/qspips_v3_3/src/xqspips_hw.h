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
* @file xqspips_hw.h
* @addtogroup qspips_v3_2
* @{
*
* This header file contains the identifiers and basic HW access driver
* functions (or  macros) that can be used to access the device. Other driver
* functions are defined in xqspips.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- -----------------------------------------------
* 1.00  sdm 11/25/10 First release
* 2.00a ka  07/25/12 Added a few register defines for CR 670297
*		     and removed some defines of reserved fields for
*		     CR 671468
*		     Added define XQSPIPS_CR_HOLD_B_MASK for Holdb_dr
*		     bit in Configuration register.
* 2.01a sg  02/03/13 Added defines for DelayNss,Rx Watermark,Interrupts
*		     which need write to clear. Removed Read zeros mask from
*		     LQSPI Config register.
* 2.03a hk  08/22/13 Added prototypes of API's for QSPI reset and
*                    linear mode initialization for boot. Added related
*                    constant definitions.
* 3.1   hk  08/13/14 Changed definition of CR reset value masks to set/reset
*                    required bits leaving reserved bits untouched. CR# 796813.
* 3.2	sk	02/05/15 Add SLCR reset in abort function as a workaround because
* 					 controller does not update FIFO status flags as expected
* 					 when thresholds are used.
*
* </pre>
*
******************************************************************************/
#ifndef XQSPIPS_HW_H		/* prevent circular inclusions */
#define XQSPIPS_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"
#include "xparameters.h"

/************************** Constant Definitions *****************************/

/** @name Register Map
 *
 * Register offsets from the base address of an QSPI device.
 * @{
 */
#define XQSPIPS_CR_OFFSET	 	0x00 /**< Configuration Register */
#define XQSPIPS_SR_OFFSET	 	0x04 /**< Interrupt Status */
#define XQSPIPS_IER_OFFSET	 	0x08 /**< Interrupt Enable */
#define XQSPIPS_IDR_OFFSET	 	0x0c /**< Interrupt Disable */
#define XQSPIPS_IMR_OFFSET	 	0x10 /**< Interrupt Enabled Mask */
#define XQSPIPS_ER_OFFSET	 	0x14 /**< Enable/Disable Register */
#define XQSPIPS_DR_OFFSET	 	0x18 /**< Delay Register */
#define XQSPIPS_TXD_00_OFFSET	 	0x1C /**< Transmit 4-byte inst/data */
#define XQSPIPS_RXD_OFFSET	 	0x20 /**< Data Receive Register */
#define XQSPIPS_SICR_OFFSET	 	0x24 /**< Slave Idle Count */
#define XQSPIPS_TXWR_OFFSET	 	0x28 /**< Transmit FIFO Watermark */
#define XQSPIPS_RXWR_OFFSET	 	0x2C /**< Receive FIFO Watermark */
#define XQSPIPS_GPIO_OFFSET	 	0x30 /**< GPIO Register */
#define XQSPIPS_LPBK_DLY_ADJ_OFFSET	0x38 /**< Loopback Delay Adjust Reg */
#define XQSPIPS_TXD_01_OFFSET	 	0x80 /**< Transmit 1-byte inst */
#define XQSPIPS_TXD_10_OFFSET	 	0x84 /**< Transmit 2-byte inst */
#define XQSPIPS_TXD_11_OFFSET	 	0x88 /**< Transmit 3-byte inst */
#define XQSPIPS_LQSPI_CR_OFFSET  	0xA0 /**< Linear QSPI config register */
#define XQSPIPS_LQSPI_SR_OFFSET  	0xA4 /**< Linear QSPI status register */
#define XQSPIPS_MOD_ID_OFFSET  		0xFC /**< Module ID register */

/* @} */

/** @name Configuration Register
 *
 * This register contains various control bits that
 * affect the operation of the QSPI device. Read/Write.
 * @{
 */

#define XQSPIPS_CR_IFMODE_MASK    0x80000000 /**< Flash mem interface mode */
#define XQSPIPS_CR_ENDIAN_MASK    0x04000000 /**< Tx/Rx FIFO endianness */
#define XQSPIPS_CR_MANSTRT_MASK   0x00010000 /**< Manual Transmission Start */
#define XQSPIPS_CR_MANSTRTEN_MASK 0x00008000 /**< Manual Transmission Start
						   Enable */
#define XQSPIPS_CR_SSFORCE_MASK   0x00004000 /**< Force Slave Select */
#define XQSPIPS_CR_SSCTRL_MASK    0x00000400 /**< Slave Select Decode */
#define XQSPIPS_CR_SSCTRL_SHIFT   10	      /**< Slave Select Decode shift */
#define XQSPIPS_CR_DATA_SZ_MASK   0x000000C0 /**< Size of word to be
						   transferred */
#define XQSPIPS_CR_PRESC_MASK     0x00000038 /**< Prescaler Setting */
#define XQSPIPS_CR_PRESC_SHIFT    3	      /**< Prescaler shift */
#define XQSPIPS_CR_PRESC_MAXIMUM  0x07	      /**< Prescaler maximum value */

#define XQSPIPS_CR_CPHA_MASK      0x00000004 /**< Phase Configuration */
#define XQSPIPS_CR_CPOL_MASK      0x00000002 /**< Polarity Configuration */

#define XQSPIPS_CR_MSTREN_MASK    0x00000001 /**< Master Mode Enable */

#define XQSPIPS_CR_HOLD_B_MASK    0x00080000 /**< HOLD_B Pin Drive Enable */

#define XQSPIPS_CR_REF_CLK_MASK   0x00000100 /**< Ref clk bit - should be 0 */

/* Deselect the Slave select line and set the transfer size to 32 at reset */
#define XQSPIPS_CR_RESET_MASK_SET  XQSPIPS_CR_IFMODE_MASK | \
				   XQSPIPS_CR_SSCTRL_MASK | \
				   XQSPIPS_CR_DATA_SZ_MASK | \
				   XQSPIPS_CR_MSTREN_MASK | \
				   XQSPIPS_CR_SSFORCE_MASK | \
				   XQSPIPS_CR_HOLD_B_MASK
#define XQSPIPS_CR_RESET_MASK_CLR  XQSPIPS_CR_CPOL_MASK | \
				   XQSPIPS_CR_CPHA_MASK | \
				   XQSPIPS_CR_PRESC_MASK | \
				   XQSPIPS_CR_MANSTRTEN_MASK | \
				   XQSPIPS_CR_MANSTRT_MASK | \
				   XQSPIPS_CR_ENDIAN_MASK | \
				   XQSPIPS_CR_REF_CLK_MASK
/* @} */


/** @name QSPI Interrupt Registers
 *
 * <b>QSPI Status Register</b>
 *
 * This register holds the interrupt status flags for an QSPI device. Some
 * of the flags are level triggered, which means that they are set as long
 * as the interrupt condition exists. Other flags are edge triggered,
 * which means they are set once the interrupt condition occurs and remain
 * set until they are cleared by software. The interrupts are cleared by
 * writing a '1' to the interrupt bit position in the Status Register.
 * Read/Write.
 *
 * <b>QSPI Interrupt Enable Register</b>
 *
 * This register is used to enable chosen interrupts for an QSPI device.
 * Writing a '1' to a bit in this register sets the corresponding bit in the
 * QSPI Interrupt Mask register.  Write only.
 *
 * <b>QSPI Interrupt Disable Register </b>
 *
 * This register is used to disable chosen interrupts for an QSPI device.
 * Writing a '1' to a bit in this register clears the corresponding bit in the
 * QSPI Interrupt Mask register. Write only.
 *
 * <b>QSPI Interrupt Mask Register</b>
 *
 * This register shows the enabled/disabled interrupts of an QSPI device.
 * Read only.
 *
 * All four registers have the same bit definitions. They are only defined once
 * for each of the Interrupt Enable Register, Interrupt Disable Register,
 * Interrupt Mask Register, and Channel Interrupt Status Register
 * @{
 */

#define XQSPIPS_IXR_TXUF_MASK	   0x00000040  /**< QSPI Tx FIFO Underflow */
#define XQSPIPS_IXR_RXFULL_MASK    0x00000020  /**< QSPI Rx FIFO Full */
#define XQSPIPS_IXR_RXNEMPTY_MASK  0x00000010  /**< QSPI Rx FIFO Not Empty */
#define XQSPIPS_IXR_TXFULL_MASK    0x00000008  /**< QSPI Tx FIFO Full */
#define XQSPIPS_IXR_TXOW_MASK	   0x00000004  /**< QSPI Tx FIFO Overwater */
#define XQSPIPS_IXR_RXOVR_MASK	   0x00000001  /**< QSPI Rx FIFO Overrun */
#define XQSPIPS_IXR_DFLT_MASK	   0x00000025  /**< QSPI default interrupts
						    mask */
#define XQSPIPS_IXR_WR_TO_CLR_MASK 0x00000041  /**< Interrupts which
						    need write to clear */
#define XQSPIPS_ISR_RESET_STATE    0x00000004  /**< Default to tx/rx empty */
#define XQSPIPS_IXR_DISABLE_ALL    0x0000007D  /**< Disable all interrupts */
/* @} */


/** @name Enable Register
 *
 * This register is used to enable or disable an QSPI device.
 * Read/Write
 * @{
 */
#define XQSPIPS_ER_ENABLE_MASK    0x00000001 /**< QSPI Enable Bit Mask */
/* @} */


/** @name Delay Register
 *
 * This register is used to program timing delays in
 * slave mode. Read/Write
 * @{
 */
#define XQSPIPS_DR_NSS_MASK	0xFF000000 /**< Delay to de-assert slave select
						between two words mask */
#define XQSPIPS_DR_NSS_SHIFT	24	   /**< Delay to de-assert slave select
						between two words shift */
#define XQSPIPS_DR_BTWN_MASK	0x00FF0000 /**< Delay Between Transfers
						mask */
#define XQSPIPS_DR_BTWN_SHIFT	16	   /**< Delay Between Transfers shift */
#define XQSPIPS_DR_AFTER_MASK	0x0000FF00 /**< Delay After Transfers mask */
#define XQSPIPS_DR_AFTER_SHIFT	8 	   /**< Delay After Transfers shift */
#define XQSPIPS_DR_INIT_MASK	0x000000FF /**< Delay Initially mask */
/* @} */

/** @name Slave Idle Count Registers
 *
 * This register defines the number of pclk cycles the slave waits for a the
 * QSPI clock to become stable in quiescent state before it can detect the start
 * of the next transfer in CPHA = 1 mode.
 * Read/Write
 *
 * @{
 */
#define XQSPIPS_SICR_MASK	0x000000FF /**< Slave Idle Count Mask */
/* @} */


/** @name Transmit FIFO Watermark Register
 *
 * This register defines the watermark setting for the Transmit FIFO.
 *
 * @{
 */
#define XQSPIPS_TXWR_MASK           0x0000003F /**< Transmit Watermark Mask */
#define XQSPIPS_TXWR_RESET_VALUE    0x00000001 /**< Transmit Watermark
						  * register reset value */

/* @} */

/** @name Receive FIFO Watermark Register
 *
 * This register defines the watermark setting for the Receive FIFO.
 *
 * @{
 */
#define XQSPIPS_RXWR_MASK	    0x0000003F /**< Receive Watermark Mask */
#define XQSPIPS_RXWR_RESET_VALUE    0x00000001 /**< Receive Watermark
						  * register reset value */

/* @} */

/** @name FIFO Depth
 *
 * This macro provides the depth of transmit FIFO and receive FIFO.
 *
 * @{
 */
#define XQSPIPS_FIFO_DEPTH	63	/**< FIFO depth (words) */
/* @} */


/** @name Linear QSPI Configuration Register
 *
 * This register contains various control bits that
 * affect the operation of the Linear QSPI controller. Read/Write.
 *
 * @{
 */
#define XQSPIPS_LQSPI_CR_LINEAR_MASK	 0x80000000 /**< LQSPI mode enable */
#define XQSPIPS_LQSPI_CR_TWO_MEM_MASK	 0x40000000 /**< Both memories or one */
#define XQSPIPS_LQSPI_CR_SEP_BUS_MASK	 0x20000000 /**< Seperate memory bus */
#define XQSPIPS_LQSPI_CR_U_PAGE_MASK	 0x10000000 /**< Upper memory page */
#define XQSPIPS_LQSPI_CR_MODE_EN_MASK	 0x02000000 /**< Enable mode bits */
#define XQSPIPS_LQSPI_CR_MODE_ON_MASK	 0x01000000 /**< Mode on */
#define XQSPIPS_LQSPI_CR_MODE_BITS_MASK  0x00FF0000 /**< Mode value for dual I/O
							 or quad I/O */
#define XQSPIPS_LQSPI_CR_DUMMY_MASK	 0x00000700 /**< Number of dummy bytes
							 between addr and return
							 read data */
#define XQSPIPS_LQSPI_CR_INST_MASK	 0x000000FF /**< Read instr code */
#define XQSPIPS_LQSPI_CR_RST_STATE	 0x8000016B /**< Default CR value */
/* @} */

/** @name Linear QSPI Status Register
 *
 * This register contains various status bits of the Linear QSPI controller.
 * Read/Write.
 *
 * @{
 */
#define XQSPIPS_LQSPI_SR_D_FSM_ERR_MASK	  0x00000004 /**< AXI Data FSM Error
							  received */
#define XQSPIPS_LQSPI_SR_WR_RECVD_MASK	  0x00000002 /**< AXI write command
							  received */
/* @} */


/** @name Loopback Delay Adjust Register
 *
 * This register contains various bit masks of Loopback Delay Adjust Register.
 *
 * @{
 */

#define XQSPIPS_LPBK_DLY_ADJ_USE_LPBK_MASK 0x00000020 /**< Loopback Bit */

/* @} */


/** @name SLCR Register
 *
 * Register offsets from SLCR base address.
 *
 * @{
 */

#define SLCR_LOCK 0x00000004 /**< SLCR Write Protection Lock */
#define SLCR_UNLOCK 0x00000008 /**< SLCR Write Protection Unlock */
#define LQSPI_RST_CTRL 0x00000230 /**< Quad SPI Software Reset Control */
#define SLCR_LOCKSTA 0x0000000C /**< SLCR Write Protection status */

/* @} */


/** @name SLCR Register
 *
 * Bit Masks of above SLCR Registers .
 *
 * @{
 */

#ifndef XPAR_XSLCR_0_BASEADDR
#define XPAR_XSLCR_0_BASEADDR 0xF8000000
#endif
#define SLCR_LOCK_MASK 0x767B /**< Write Protection Lock mask*/
#define SLCR_UNLOCK_MASK 0xDF0D /**< SLCR Write Protection Unlock */
#define LQSPI_RST_CTRL_MASK 0x3 /**< Quad SPI Software Reset Control */

/* @} */


/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

#define XQspiPs_In32 Xil_In32
#define XQspiPs_Out32 Xil_Out32

/****************************************************************************/
/**
* Read a register.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset contains the offset from the 1st register of the
*		device to the target register.
*
* @return	The value read from the register.
*
* @note		C-Style signature:
*		u32 XQspiPs_ReadReg(u32 BaseAddress. int RegOffset)
*
******************************************************************************/
#define XQspiPs_ReadReg(BaseAddress, RegOffset) \
	XQspiPs_In32((BaseAddress) + (RegOffset))

/***************************************************************************/
/**
* Write to a register.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset contains the offset from the 1st register of the
*		device to target register.
* @param	RegisterValue is the value to be written to the register.
*
* @return	None.
*
* @note		C-Style signature:
*		void XQspiPs_WriteReg(u32 BaseAddress, int RegOffset,
*		u32 RegisterValue)
*
******************************************************************************/
#define XQspiPs_WriteReg(BaseAddress, RegOffset, RegisterValue) \
	XQspiPs_Out32((BaseAddress) + (RegOffset), (RegisterValue))

/************************** Function Prototypes ******************************/

/*
 * Functions implemented in xqspips_hw.c
 */
void XQspiPs_ResetHw(u32 BaseAddress);
void XQspiPs_LinearInit(u32 BaseAddress);

/************************** Variable Definitions *****************************/

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
/** @} */
