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
* @file xspips_hw.h
*
* This header file contains the identifiers and basic driver functions (or
* macros) that can be used to access the device. Other driver functions
* are defined in xspips.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- -----------------------------------------------
* 1.00   drg/jz 01/25/10 First release
* 1.02a  sg     05/31/12 Updated XSPIPS_FIFO_DEPTH to 128 from 32 to match HW
*			 for CR 658289
* 1.04a	 sg     01/30/13 Created XSPIPS_CR_MODF_GEN_EN_MASK macro and added it
*			 to XSPIPS_CR_RESET_STATE. Created
* 			 XSPIPS_IXR_WR_TO_CLR_MASK for interrupts which need
*			 write-to-clear. Added shift and mask macros for d_nss
*			 parameter. Added Rx Watermark mask.
* 1.06a hk      08/22/13 Added prototypes of reset API and related constant
*                        definitions.
* 3.00  kvn     02/13/15 Modified code for MISRA-C:2012 compliance.
*
* </pre>
*
******************************************************************************/

#ifndef XSPIPS_HW_H		/* prevent circular inclusions */
#define XSPIPS_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

/** @name Register Map
 *
 * Register offsets from the base address of an SPI device.
 * @{
 */
#define XSPIPS_CR_OFFSET	0x00U  /**< Configuration */
#define XSPIPS_SR_OFFSET	0x04U  /**< Interrupt Status */
#define XSPIPS_IER_OFFSET	0x08U  /**< Interrupt Enable */
#define XSPIPS_IDR_OFFSET	0x0CU  /**< Interrupt Disable */
#define XSPIPS_IMR_OFFSET	0x10U  /**< Interrupt Enabled Mask */
#define XSPIPS_ER_OFFSET	0x14U  /**< Enable/Disable Register */
#define XSPIPS_DR_OFFSET	0x18U  /**< Delay Register */
#define XSPIPS_TXD_OFFSET	0x1CU  /**< Data Transmit Register */
#define XSPIPS_RXD_OFFSET	0x20U  /**< Data Receive Register */
#define XSPIPS_SICR_OFFSET	0x24U  /**< Slave Idle Count */
#define XSPIPS_TXWR_OFFSET	0x28U  /**< Transmit FIFO Watermark */
#define XSPIPS_RXWR_OFFSET	0x2CU  /**< Receive FIFO Watermark */
/* @} */

/** @name Configuration Register
 *
 * This register contains various control bits that
 * affects the operation of an SPI device. Read/Write.
 * @{
 */
#define XSPIPS_CR_MODF_GEN_EN_MASK 0x00020000U /**< Modefail Generation
						 Enable */
#define XSPIPS_CR_MANSTRT_MASK   0x00010000U /**< Manual Transmission Start */
#define XSPIPS_CR_MANSTRTEN_MASK 0x00008000U /**< Manual Transmission Start
						 Enable */
#define XSPIPS_CR_SSFORCE_MASK   0x00004000U /**< Force Slave Select */
#define XSPIPS_CR_SSCTRL_MASK    0x00003C00U /**< Slave Select Decode */
#define XSPIPS_CR_SSCTRL_SHIFT   10U	    /**< Slave Select Decode shift */
#define XSPIPS_CR_SSCTRL_MAXIMUM 0xFU	    /**< Slave Select maximum value */
#define XSPIPS_CR_SSDECEN_MASK   0x00000200U /**< Slave Select Decode Enable */

#define XSPIPS_CR_PRESC_MASK     0x00000038U /**< Prescaler Setting */
#define XSPIPS_CR_PRESC_SHIFT    3U	    /**< Prescaler shift */
#define XSPIPS_CR_PRESC_MAXIMUM  0x07U	    /**< Prescaler maximum value */

#define XSPIPS_CR_CPHA_MASK      0x00000004U /**< Phase Configuration */
#define XSPIPS_CR_CPOL_MASK      0x00000002U /**< Polarity Configuration */

#define XSPIPS_CR_MSTREN_MASK    0x00000001U /**< Master Mode Enable */
#define XSPIPS_CR_RESET_STATE    0x00020000U /**< Mode Fail Generation Enable */
/* @} */


/** @name SPI Interrupt Registers
 *
 * <b>SPI Status Register</b>
 *
 * This register holds the interrupt status flags for an SPI device. Some
 * of the flags are level triggered, which means that they are set as long
 * as the interrupt condition exists. Other flags are edge triggered,
 * which means they are set once the interrupt condition occurs and remain
 * set until they are cleared by software. The interrupts are cleared by
 * writing a '1' to the interrupt bit position in the Status Register.
 * Read/Write.
 *
 * <b>SPI Interrupt Enable Register</b>
 *
 * This register is used to enable chosen interrupts for an SPI device.
 * Writing a '1' to a bit in this register sets the corresponding bit in the
 * SPI Interrupt Mask register.  Write only.
 *
 * <b>SPI Interrupt Disable Register </b>
 *
 * This register is used to disable chosen interrupts for an SPI device.
 * Writing a '1' to a bit in this register clears the corresponding bit in the
 * SPI Interrupt Mask register. Write only.
 *
 * <b>SPI Interrupt Mask Register</b>
 *
 * This register shows the enabled/disabled interrupts of an SPI device.
 * Read only.
 *
 * All four registers have the same bit definitions. They are only defined once
 * for each of the Interrupt Enable Register, Interrupt Disable Register,
 * Interrupt Mask Register, and Channel Interrupt Status Register
 * @{
 */

#define XSPIPS_IXR_TXUF_MASK		0x00000040U  /**< Tx FIFO Underflow */
#define XSPIPS_IXR_RXFULL_MASK		0x00000020U  /**< Rx FIFO Full */
#define XSPIPS_IXR_RXNEMPTY_MASK	0x00000010U  /**< Rx FIFO Not Empty */
#define XSPIPS_IXR_TXFULL_MASK		0x00000008U  /**< Tx FIFO Full */
#define XSPIPS_IXR_TXOW_MASK		0x00000004U  /**< Tx FIFO Overwater */
#define XSPIPS_IXR_MODF_MASK		0x00000002U  /**< Mode Fault */
#define XSPIPS_IXR_RXOVR_MASK		0x00000001U  /**< Rx FIFO Overrun */
#define XSPIPS_IXR_DFLT_MASK		0x00000027U  /**< Default interrupts
							 mask */
#define XSPIPS_IXR_WR_TO_CLR_MASK	0x00000043U  /**< Interrupts which
							 need write to clear */
#define XSPIPS_ISR_RESET_STATE		0x04U	    /**< Default to tx/rx
						       * reg empty */
#define XSPIPS_IXR_DISABLE_ALL_MASK	0x00000043U  /**< Disable all
						       * interrupts */
/* @} */


/** @name Enable Register
 *
 * This register is used to enable or disable an SPI device.
 * Read/Write
 * @{
 */
#define XSPIPS_ER_ENABLE_MASK	0x00000001U /**< SPI Enable Bit Mask */
/* @} */


/** @name Delay Register
 *
 * This register is used to program timing delays in
 * slave mode. Read/Write
 * @{
 */
#define XSPIPS_DR_NSS_MASK	0xFF000000U /**< Delay for slave select
					      * de-assertion between
					      * word transfers mask */
#define XSPIPS_DR_NSS_SHIFT	24U	   /**< Delay for slave select
					      * de-assertion between
					      * word transfers shift */
#define XSPIPS_DR_BTWN_MASK	0x00FF0000U /**< Delay Between Transfers	mask */
#define XSPIPS_DR_BTWN_SHIFT	16U	   /**< Delay Between Transfers shift */
#define XSPIPS_DR_AFTER_MASK	0x0000FF00U /**< Delay After Transfers mask */
#define XSPIPS_DR_AFTER_SHIFT	8U 	   /**< Delay After Transfers shift */
#define XSPIPS_DR_INIT_MASK	0x000000FFU /**< Delay Initially mask */
/* @} */


/** @name Slave Idle Count Registers
 *
 * This register defines the number of pclk cycles the slave waits for a the
 * SPI clock to become stable in quiescent state before it can detect the start
 * of the next transfer in CPHA = 1 mode.
 * Read/Write
 *
 * @{
 */
#define XSPIPS_SICR_MASK	0x000000FFU /**< Slave Idle Count Mask */
/* @} */



/** @name Transmit FIFO Watermark Register
 *
 * This register defines the watermark setting for the Transmit FIFO. The
 * transmit FIFO is 128 bytes deep, so the register is 7 bits. Valid values
 * are 1 to 128.
 *
 * @{
 */
#define XSPIPS_TXWR_MASK	0x0000007FU /**< Transmit Watermark Mask */
#define XSPIPS_TXWR_RESET_VALUE	0x00000001U /**< Transmit Watermark
					      * register reset value */
/* @} */

/** @name Receive FIFO Watermark Register
 *
 * This register defines the watermark setting for the Receive FIFO. The
 * receive FIFO is 128 bytes deep, so the register is 7 bits. Valid values
 * are 1 to 128.
 *
 * @{
 */
#define XSPIPS_RXWR_MASK	0x0000007FU /**< Receive Watermark Mask */
#define XSPIPS_RXWR_RESET_VALUE	0x00000001U /**< Receive Watermark
					      * register reset value */
/* @} */

/** @name FIFO Depth
 *
 * This macro provides the depth of transmit FIFO and receive FIFO.
 *
 * @{
 */
#define XSPIPS_FIFO_DEPTH	128U /**< FIFO depth of Tx and Rx */
/* @} */

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

#define XSpiPs_In32 Xil_In32
#define XSpiPs_Out32 Xil_Out32

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
*		u32 XSpiPs_ReadReg(u32 BaseAddress. int RegOffset)
*
******************************************************************************/
#define XSpiPs_ReadReg(BaseAddress, RegOffset) \
	XSpiPs_In32((BaseAddress) + (RegOffset))

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
*		void XSpiPs_WriteReg(u32 BaseAddress, int RegOffset,
*		u32 RegisterValue)
*
******************************************************************************/
#define XSpiPs_WriteReg(BaseAddress, RegOffset, RegisterValue) \
    XSpiPs_Out32((BaseAddress) + (RegOffset), (RegisterValue))

/************************** Function Prototypes ******************************/

void XSpiPs_ResetHw(u32 BaseAddress);

/************************** Variable Definitions *****************************/

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
