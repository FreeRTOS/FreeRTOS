/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc.  All rights reserved.
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
* @file xzdma_hw.h
*
* This header file contains identifiers and register-level driver functions (or
* macros) that can be used to access the Xilinx ZDMA core.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- ------------------------------------------------------
* 1.0   vns     2/27/15  First release
* </pre>
*
******************************************************************************/
#ifndef XZDMA_HW_H_
#define XZDMA_HW_H_		/**< Prevent circular inclusions
				  *  by using protection macros	*/
#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_io.h"

/************************** Constant Definitions *****************************/

/** @name Registers offsets
 * @{
 */
#define XZDMA_ERR_CTRL				(0x000U)
#define XZDMA_CH_ECO				(0x004U)
#define XZDMA_CH_ISR_OFFSET			(0x100U)
#define XZDMA_CH_IMR_OFFSET			(0x104U)
#define XZDMA_CH_IEN_OFFSET			(0x108U)
#define XZDMA_CH_IDS_OFFSET			(0x10CU)
#define XZDMA_CH_CTRL0_OFFSET			(0x110U)
#define XZDMA_CH_CTRL1_OFFSET			(0x114U)
#define XZDMA_CH_PERIF_OFFSET			(0x118U)
#define XZDMA_CH_STS_OFFSET			(0x11CU)
#define XZDMA_CH_DATA_ATTR_OFFSET		(0x120U)
#define XZDMA_CH_DSCR_ATTR_OFFSET		(0x124U)
#define XZDMA_CH_SRC_DSCR_WORD0_OFFSET		(0x128U)
#define XZDMA_CH_SRC_DSCR_WORD1_OFFSET		(0x12CU)
#define XZDMA_CH_SRC_DSCR_WORD2_OFFSET		(0x130U)
#define XZDMA_CH_SRC_DSCR_WORD3_OFFSET		(0x134U)
#define XZDMA_CH_DST_DSCR_WORD0_OFFSET		(0x138U)
#define XZDMA_CH_DST_DSCR_WORD1_OFFSET		(0x13CU)
#define XZDMA_CH_DST_DSCR_WORD2_OFFSET		(0x140U)
#define XZDMA_CH_DST_DSCR_WORD3_OFFSET		(0x144U)
#define XZDMA_CH_WR_ONLY_WORD0_OFFSET		(0x148U)
#define XZDMA_CH_WR_ONLY_WORD1_OFFSET		(0x14CU)
#define XZDMA_CH_WR_ONLY_WORD2_OFFSET		(0x150U)
#define XZDMA_CH_WR_ONLY_WORD3_OFFSET		(0x154U)
#define XZDMA_CH_SRC_START_LSB_OFFSET		(0x158U)
#define XZDMA_CH_SRC_START_MSB_OFFSET		(0x15CU)
#define XZDMA_CH_DST_START_LSB_OFFSET		(0x160U)
#define XZDMA_CH_DST_START_MSB_OFFSET		(0x164U)
#define XZDMA_CH_SRC_CUR_PYLD_LSB_OFFSET	(0x168U)
#define XZDMA_CH_SRC_CUR_PYLD_MSB_OFFSET	(0x16CU)
#define XZDMA_CH_DST_CUR_PYLD_LSB_OFFSET	(0x170U)
#define XZDMA_CH_DST_CUR_PYLD_MSB_OFFSET	(0x174U)
#define XZDMA_CH_SRC_CUR_DSCR_LSB_OFFSET	(0x178U)
#define XZDMA_CH_SRC_CUR_DSCR_MSB_OFFSET	(0x17CU)
#define XZDMA_CH_DST_CUR_DSCR_LSB_OFFSET	(0x180U)
#define XZDMA_CH_DST_CUR_DSCR_MSB_OFFSET	(0x184U)
#define XZDMA_CH_TOTAL_BYTE_OFFSET		(0x188U)
#define XZDMA_CH_RATE_CNTL_OFFSET		(0x18CU)
#define XZDMA_CH_IRQ_SRC_ACCT_OFFSET		(0x190U)
#define XZDMA_CH_IRQ_DST_ACCT_OFFSET		(0x194U)
#define XZDMA_CH_CTRL2_OFFSET			(0x200U)
/*@}*/

/** @name Interrupt Enable/Disable/Mask/Status registers bit masks and shifts
 * @{
 */
#define XZDMA_IXR_DMA_PAUSE_MASK	(0x00000800U) /**< IXR pause mask */
#define XZDMA_IXR_DMA_DONE_MASK		(0x00000400U) /**< IXR done mask */
#define XZDMA_IXR_AXI_WR_DATA_MASK	(0x00000200U) /**< IXR AXI write data
							*  error mask */
#define XZDMA_IXR_AXI_RD_DATA_MASK	(0x00000100U) /**< IXR AXI read data
							*  error mask */
#define XZDMA_IXR_AXI_RD_DST_DSCR_MASK	(0x00000080U) /**< IXR AXI read
							*  descriptor error
							*  mask */
#define XZDMA_IXR_AXI_RD_SRC_DSCR_MASK	(0x00000040U) /**< IXR AXI write
							*  descriptor error
							*  mask */
#define XZDMA_IXR_DST_ACCT_ERR_MASK	(0x00000020U) /**< IXR DST interrupt
							*  count overflow
							*  mask */
#define XZDMA_IXR_SRC_ACCT_ERR_MASK	(0x00000010U) /**< IXR SRC interrupt
							*  count overflow
							*  mask */
#define XZDMA_IXR_BYTE_CNT_OVRFL_MASK	(0x00000008U) /**< IXR byte count over
							* flow mask */
#define XZDMA_IXR_DST_DSCR_DONE_MASK	(0x00000004U) /**< IXR destination
							*  descriptor done
							*  mask */
#define XZDMA_IXR_SRC_DSCR_DONE_MASK	(0x00000002U) /**< IXR source
							*  descriptor done
							*  mask */
#define XZDMA_IXR_INV_APB_MASK		(0x00000001U) /**< IXR invalid APB
							*  access mask */
#define XZDMA_IXR_ALL_INTR_MASK		(0x00000FFFU) /**< IXR OR of all the
							*  interrupts mask */
#define XZDMA_IXR_DONE_MASK		(0x00000400U) /**< IXR All done mask */

#define XZDMA_IXR_ERR_MASK		(0x00000BF9U) /**< IXR all Error mask*/
					/**< Or of XZDMA_IXR_AXI_WR_DATA_MASK,
					  * XZDMA_IXR_AXI_RD_DATA_MASK,
					  * XZDMA_IXR_AXI_RD_DST_DSCR_MASK,
					  * XZDMA_IXR_AXI_RD_SRC_DSCR_MASK,
					  * XZDMA_IXR_INV_APB_MASK,
					  * XZDMA_IXR_DMA_PAUSE_MASK,
					  * XZDMA_IXR_BYTE_CNT_OVRFL_MASK,
					  * XZDMA_IXR_SRC_ACCT_ERR_MASK,
					  *  XZDMA_IXR_DST_ACCT_ERR_MASK */
/*@}*/

/** @name Channel Control0 register bit masks and shifts
 * @{
 */
#define XZDMA_CTRL0_OVR_FETCH_MASK	(0x00000080U) /**< Over fetch mask */
#define XZDMA_CTRL0_POINT_TYPE_MASK	(0x00000040U) /**< Pointer type mask */
#define XZDMA_CTRL0_MODE_MASK		(0x00000030U) /**< Mode mask */
#define XZDMA_CTRL0_WRONLY_MASK		(0x00000010U) /**< Write only mask */
#define XZDMA_CTRL0_RDONLY_MASK		(0x00000020U) /**< Read only mask */
#define XZDMA_CTRL0_RATE_CNTL_MASK	(0x00000008U) /**< Rate control mask */
#define XZDMA_CTRL0_CONT_ADDR_MASK	(0x00000004U) /**< Continue address
							*  specified mask */
#define XZDMA_CTRL0_CONT_MASK		(0x00000002U) /**< Continue mask */

#define XZDMA_CTRL0_OVR_FETCH_SHIFT	(7U)	/**< Over fetch shift */
#define XZDMA_CTRL0_POINT_TYPE_SHIFT	(6U)	/**< Pointer type shift */
#define XZDMA_CTRL0_MODE_SHIFT		(4U)	/**< Mode type shift */
#define XZDMA_CTRL0_RESET_VALUE		(0x00000080U) /**< CTRL0 reset value */

/*@}*/

/** @name Channel Control1 register bit masks and shifts
 * @{
 */
#define XZDMA_CTRL1_SRC_ISSUE_MASK	(0x0000001FU) /**< Source issue mask */
#define XZDMA_CTRL1_RESET_VALUE		(0x000003FFU) /**< CTRL1 reset value */
/*@}*/

/** @name Channel Peripheral register bit masks and shifts
 * @{
 */
#define XZDMA_PERIF_PROG_CELL_CNT_MASK	(0x0000003EU) /**< Peripheral program
							*  cell count */
#define XZDMA_PERIF_SIDE_MASK		(0x00000002U) /**< Interface attached
							* the side mask */
#define XZDMA_PERIF_EN_MASK		(0x00000001U) /**< Peripheral flow
							* control mask */
/*@}*/

/** @name Channel Status register bit masks and shifts
 * @{
 */
#define XZDMA_STS_DONE_ERR_MASK	(0x00000003U) /**< Done with errors mask */
#define XZDMA_STS_BUSY_MASK	(0x00000002U) /**< ZDMA is busy in transfer
						*  mask */
#define XZDMA_STS_PAUSE_MASK	(0x00000001U) /**< ZDMA is in Pause state
						*  mask */
#define XZDMA_STS_DONE_MASK	(0x00000000U) /**< ZDMA done mask */
#define XZDMA_STS_ALL_MASK	(0x00000003U) /**< ZDMA status mask */

/*@}*/

/** @name Channel Data Attribute register bit masks and shifts
 * @{
 */
#define XZDMA_DATA_ATTR_ARBURST_MASK	(0x0C000000U) /**< Data ArBurst mask */
#define XZDMA_DATA_ATTR_ARCACHE_MASK	(0x03C00000U) /**< Data ArCache mask */
#define XZDMA_DATA_ATTR_ARQOS_MASK	(0x003C0000U) /**< Data ARQos masks */
#define XZDMA_DATA_ATTR_ARLEN_MASK	(0x0003C000U) /**< Data Arlen mask */
#define XZDMA_DATA_ATTR_AWBURST_MASK	(0x00003000U) /**< Data Awburst mask */
#define XZDMA_DATA_ATTR_AWCACHE_MASK	(0x00000F00U) /**< Data AwCache mask */
#define XZDMA_DATA_ATTR_AWQOS_MASK	(0x000000F0U) /**< Data AwQos mask */
#define XZDMA_DATA_ATTR_AWLEN_MASK	(0x0000000FU) /**< Data Awlen mask */

#define XZDMA_DATA_ATTR_ARBURST_SHIFT	(26U) /**< Data Arburst shift */
#define XZDMA_DATA_ATTR_ARCACHE_SHIFT	(22U) /**< Data ArCache shift */
#define XZDMA_DATA_ATTR_ARQOS_SHIFT	(18U) /**< Data ARQos shift */
#define XZDMA_DATA_ATTR_ARLEN_SHIFT	(14U) /**< Data Arlen shift */
#define XZDMA_DATA_ATTR_AWBURST_SHIFT	(12U) /**< Data Awburst shift  */
#define XZDMA_DATA_ATTR_AWCACHE_SHIFT	(8U)  /**< Data Awcache shift */
#define XZDMA_DATA_ATTR_AWQOS_SHIFT	(4U)  /**< Data Awqos shift */
#define XZDMA_DATA_ATTR_RESET_VALUE	(0x0483D20FU) /**< Data Attributes
							*  reset value */

/*@}*/

/** @name Channel DSCR Attribute register bit masks and shifts
 * @{
 */
#define XZDMA_DSCR_ATTR_AXCOHRNT_MASK	(0x00000100U) /**< Descriptor coherent
							*  mask */
#define XZDMA_DSCR_ATTR_AXCACHE_MASK	(0x000000F0U) /**< Descriptor cache
							* mask */
#define XZDMA_DSCR_ATTR_AXQOS_MASK	(0x0000000FU) /**< Descriptor AxQos
							*  mask */

#define XZDMA_DSCR_ATTR_AXCOHRNT_SHIFT	(8U) /**< Descriptor coherent shift */
#define XZDMA_DSCR_ATTR_AXCACHE_SHIFT	(7U) /**< Descriptor cache shift */
#define XZDMA_DSCR_ATTR_RESET_VALUE	(0x00000000U) /**< Dscr Attributes
							*  reset value */

/*@}*/

/** @name Channel Source/Destination Word0 register bit mask
 * @{
 */
#define XZDMA_WORD0_LSB_MASK	(0xFFFFFFFFU)	/**< LSB Address mask */
/*@}*/

/** @name Channel Source/Destination Word1 register bit mask
 * @{
 */
#define XZDMA_WORD1_MSB_MASK	(0x0001FFFFU)	/**< MSB Address mask */
#define XZDMA_WORD1_MSB_SHIFT	(32U)		/**< MSB Address shift */
/*@}*/

/** @name Channel Source/Destination Word2 register bit mask
 * @{
 */
#define XZDMA_WORD2_SIZE_MASK	(0x3FFFFFFFU) /**< Size mask */
/*@}*/

/** @name Channel Source/Destination Word3 register bit masks and shifts
 * @{
 */
#define XZDMA_WORD3_CMD_MASK		(0x00000018U)	/**< Cmd mask */
#define XZDMA_WORD3_CMD_SHIFT		(3U)		/**< Cmd shift */
#define XZDMA_WORD3_CMD_NXTVALID_MASK	(0x00000000U)	/**< Next Dscr is valid
							  *  mask */
#define XZDMA_WORD3_CMD_PAUSE_MASK	(0x00000008U)	/**< Pause after this
							  * dscr mask */
#define XZDMA_WORD3_CMD_STOP_MASK	(0x00000010U)	/**< Stop after this
							..*  dscr mask */
#define XZDMA_WORD3_INTR_MASK		(0x00000004U)	/**< Interrupt
							  *  enable or disable
							  *  mask */
#define XZDMA_WORD3_INTR_SHIFT		(2U)		/**< Interrupt enable
							  *  disable
							  *  shift */
#define XZDMA_WORD3_TYPE_MASK		(0x00000002U)	/**< Type of Descriptor
							  *  mask */
#define XZDMA_WORD3_TYPE_SHIFT		(1U)		/**< Type of Descriptor
							  *  Shift */
#define XZDMA_WORD3_COHRNT_MASK		(0x00000001U)	/**< Coherence mask */
/*@}*/

/** @name Channel Source/Destination start address or current payload
 *  MSB register bit mask
 * @{
 */
#define XZDMA_START_MSB_ADDR_MASK	(0x0001FFFFU)	/**< Start msb address
							  *  mask */
/*@}*/

/** @name Channel Rate control count register bit mask
 * @{
 */
#define XZDMA_CH_RATE_CNTL_MASK		(0x00000FFFU) /**< Channel rate control
							*  mask */
/*@}*/

/** @name Channel Source/Destination Interrupt account count register bit mask
 * @{
 */
#define XZDMA_CH_IRQ_ACCT_MASK		(0x000000FFU) /**< Interrupt count
							*  mask */
/*@}*/

/** @name Channel debug register 0/1 bit mask
 * @{
 */
#define XZDMA_CH_DBG_CMN_BUF_MASK	(0x000001FFU) /**< Common buffer count
							* mask */
/*@}*/

/** @name Channel control2 register bit mask
 * @{
 */
#define XZDMA_CH_CTRL2_EN_MASK		(0x00000001U) /**< Channel enable
							*  mask */
#define XZDMA_CH_CTRL2_DIS_MASK		(0x00000000U) /**< Channel disable
							*  mask */
/*@}*/

/** @name Channel control2 register bit mask
 * @{
 */
 #define XZDMA_WRITE_TO_CLEAR_MASK	(0x00000000U) /**< Write to clear
							*  mask */
 /*@}*/

/***************** Macros (Inline Functions) Definitions *********************/

#define XZDma_In32		Xil_In32	/**< Input operation */
#define XZDma_Out32		Xil_Out32	/**< Output operation */

/*****************************************************************************/
/**
*
* This macro reads the given register.
*
* @param	BaseAddress is the Xilinx base address of the ZDMA core.
* @param	RegOffset is the register offset of the register.
*
* @return	The 32-bit value of the register.
*
* @note		C-style signature:
*		u32 XZDma_ReadReg(u32 BaseAddress, u32 RegOffset)
*
******************************************************************************/
#define XZDma_ReadReg(BaseAddress, RegOffset) \
		XZDma_In32((BaseAddress) + (u32)(RegOffset))

/*****************************************************************************/
/**
*
* This macro writes the value into the given register.
*
* @param	BaseAddress is the Xilinx base address of the ZDMA core.
* @param	RegOffset is the register offset of the register.
* @param	Data is the 32-bit value to write to the register.
*
* @return	None.
*
* @note		C-style signature:
*		void XZDma_WriteReg(u32 BaseAddress, u32 RegOffset, u32 Data)
*
******************************************************************************/
#define XZDma_WriteReg(BaseAddress, RegOffset, Data) \
		XZDma_Out32(((BaseAddress) + (u32)(RegOffset)), (u32)(Data))

#ifdef __cplusplus
}

#endif

#endif /* XZDMA_HW_H_ */
