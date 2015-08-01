/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
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
/****************************************************************************/
/**
*
* @file xdevcfg_hw.h
*
* This file contains the hardware interface to the Device Config Interface.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a hvm 02/07/11 First release
* 2.01a nm  08/01/12 Added defines for the PS Version bits,
*	             removed the FIFO Flush bits from the
*		     Miscellaneous Control Reg
* 2.03a nm  04/19/13 Fixed CR# 703728.
*		     Updated the register definitions as per the latest TRM
*		     version UG585 (v1.4) November 16, 2012.
* 2.04a	kpc	10/07/13 Added function prototype.	
* 3.00a	kpc	25/02/14 Corrected the XDCFG_BASE_ADDRESS macro value.
* </pre>
*
******************************************************************************/
#ifndef XDCFG_HW_H		/* prevent circular inclusions */
#define XDCFG_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

/** @name Register Map
 * Offsets of registers from the start of the device
 * @{
 */

#define XDCFG_CTRL_OFFSET		0x00 /**< Control Register */
#define XDCFG_LOCK_OFFSET		0x04 /**< Lock Register */
#define XDCFG_CFG_OFFSET		0x08 /**< Configuration Register */
#define XDCFG_INT_STS_OFFSET		0x0C /**< Interrupt Status Register */
#define XDCFG_INT_MASK_OFFSET		0x10 /**< Interrupt Mask Register */
#define XDCFG_STATUS_OFFSET		0x14 /**< Status Register */
#define XDCFG_DMA_SRC_ADDR_OFFSET	0x18 /**< DMA Source Address Register */
#define XDCFG_DMA_DEST_ADDR_OFFSET	0x1C /**< DMA Destination Address Reg */
#define XDCFG_DMA_SRC_LEN_OFFSET	0x20 /**< DMA Source Transfer Length */
#define XDCFG_DMA_DEST_LEN_OFFSET	0x24 /**< DMA Destination Transfer */
#define XDCFG_ROM_SHADOW_OFFSET		0x28 /**< DMA ROM Shadow Register */
#define XDCFG_MULTIBOOT_ADDR_OFFSET	0x2C /**< Multi BootAddress Pointer */
#define XDCFG_SW_ID_OFFSET		0x30 /**< Software ID Register */
#define XDCFG_UNLOCK_OFFSET		0x34 /**< Unlock Register */
#define XDCFG_MCTRL_OFFSET		0x80 /**< Miscellaneous Control Reg */

/* @} */

/** @name Control Register Bit definitions
  * @{
 */

#define XDCFG_CTRL_FORCE_RST_MASK	0x80000000 /**< Force  into
						     * Secure Reset
						     */
#define XDCFG_CTRL_PCFG_PROG_B_MASK	0x40000000 /**< Program signal to
						     *  Reset FPGA
						     */
#define XDCFG_CTRL_PCFG_POR_CNT_4K_MASK	0x20000000 /**< Control PL POR timer */
#define XDCFG_CTRL_PCAP_PR_MASK	  	0x08000000 /**< Enable PCAP for PR */
#define XDCFG_CTRL_PCAP_MODE_MASK	0x04000000 /**< Enable PCAP */
#define XDCFG_CTRL_PCAP_RATE_EN_MASK	0x02000000 /**< Enable PCAP send data
						     *  to FPGA every 4 PCAP
						     *  cycles
						     */
#define XDCFG_CTRL_MULTIBOOT_EN_MASK	0x01000000 /**< Multiboot Enable */
#define XDCFG_CTRL_JTAG_CHAIN_DIS_MASK	0x00800000 /**< JTAG Chain Disable */
#define XDCFG_CTRL_USER_MODE_MASK	0x00008000 /**< User Mode Mask */
#define XDCFG_CTRL_PCFG_AES_FUSE_MASK	0x00001000 /**< AES key source */
#define XDCFG_CTRL_PCFG_AES_EN_MASK	0x00000E00 /**< AES Enable Mask */
#define XDCFG_CTRL_SEU_EN_MASK		0x00000100 /**< SEU Enable Mask */
#define XDCFG_CTRL_SEC_EN_MASK		0x00000080 /**< Secure/Non Secure
						     *  Status mask
						     */
#define XDCFG_CTRL_SPNIDEN_MASK		0x00000040 /**< Secure Non Invasive
						     *  Debug Enable
						     */
#define XDCFG_CTRL_SPIDEN_MASK		0x00000020 /**< Secure Invasive
						     *  Debug Enable
						     */
#define XDCFG_CTRL_NIDEN_MASK		0x00000010 /**< Non-Invasive Debug
						     *  Enable
						     */
#define XDCFG_CTRL_DBGEN_MASK		0x00000008 /**< Invasive Debug
						     *  Enable
						     */
#define XDCFG_CTRL_DAP_EN_MASK		0x00000007 /**< DAP Enable Mask */

/* @} */

/** @name Lock register bit definitions
  * @{
 */

#define XDCFG_LOCK_AES_EFUSE_MASK	0x00000010 /**< Lock AES Efuse bit */
#define XDCFG_LOCK_AES_EN_MASK		0x00000008 /**< Lock AES_EN update */
#define XDCFG_LOCK_SEU_MASK		0x00000004 /**< Lock SEU_En update */
#define XDCFG_LOCK_SEC_MASK		0x00000002 /**< Lock SEC_EN and
						     *  USER_MODE
						     */
#define XDCFG_LOCK_DBG_MASK		0x00000001 /**< This bit locks
						     *  security config
						     *  including: DAP_En,
						     *  DBGEN,,
						     *  NIDEN, SPNIEN
						     */
/*@}*/



/** @name Config Register Bit definitions
  * @{
 */
#define XDCFG_CFG_RFIFO_TH_MASK	  	0x00000C00 /**< Read FIFO
						     *  Threshold Mask
						     */
#define XDCFG_CFG_WFIFO_TH_MASK	  	0x00000300 /**< Write FIFO Threshold
						     *  Mask
						     */
#define XDCFG_CFG_RCLK_EDGE_MASK	0x00000080 /**< Read data active
						     *  clock edge
						     */
#define XDCFG_CFG_WCLK_EDGE_MASK	0x00000040 /**< Write data active
						     *  clock edge
						     */
#define XDCFG_CFG_DISABLE_SRC_INC_MASK	0x00000020 /**< Disable Source address
						     *  increment mask
						     */
#define XDCFG_CFG_DISABLE_DST_INC_MASK	0x00000010 /**< Disable Destination
						     *  address increment
						     *  mask
						     */
/* @} */


/** @name Interrupt Status/Mask Register Bit definitions
  * @{
 */
#define XDCFG_IXR_PSS_GTS_USR_B_MASK	0x80000000 /**< Tri-state IO during
						     *  HIZ
						     */
#define XDCFG_IXR_PSS_FST_CFG_B_MASK	0x40000000 /**< First configuration
						     *  done
						     */
#define XDCFG_IXR_PSS_GPWRDWN_B_MASK	0x20000000 /**< Global power down */
#define XDCFG_IXR_PSS_GTS_CFG_B_MASK	0x10000000 /**< Tri-state IO during
						     *  configuration
						     */
#define XDCFG_IXR_PSS_CFG_RESET_B_MASK	0x08000000 /**< PL configuration
						     *  reset
						     */
#define XDCFG_IXR_AXI_WTO_MASK		0x00800000 /**< AXI Write Address
						     *  or Data or response
						     *  timeout
						     */
#define XDCFG_IXR_AXI_WERR_MASK		0x00400000 /**< AXI Write response
						     *  error
						     */
#define XDCFG_IXR_AXI_RTO_MASK		0x00200000 /**< AXI Read Address or
						     *  response timeout
						     */
#define XDCFG_IXR_AXI_RERR_MASK		0x00100000 /**< AXI Read response
						     *  error
						     */
#define XDCFG_IXR_RX_FIFO_OV_MASK	0x00040000 /**< Rx FIFO Overflow */
#define XDCFG_IXR_WR_FIFO_LVL_MASK	0x00020000 /**< Tx FIFO less than
						     *  threshold */
#define XDCFG_IXR_RD_FIFO_LVL_MASK	0x00010000 /**< Rx FIFO greater than
						     *  threshold */
#define XDCFG_IXR_DMA_CMD_ERR_MASK	0x00008000 /**< Illegal DMA command */
#define XDCFG_IXR_DMA_Q_OV_MASK		0x00004000 /**< DMA command queue
						     *  overflow
						     */
#define XDCFG_IXR_DMA_DONE_MASK		0x00002000 /**< DMA Command Done */
#define XDCFG_IXR_D_P_DONE_MASK		0x00001000 /**< DMA and PCAP
						     *  transfers Done
						     */
#define XDCFG_IXR_P2D_LEN_ERR_MASK	0x00000800 /**< PCAP to DMA transfer
						     *  length error
						     */
#define XDCFG_IXR_PCFG_HMAC_ERR_MASK	0x00000040 /**< HMAC error mask */
#define XDCFG_IXR_PCFG_SEU_ERR_MASK	0x00000020 /**< SEU Error mask */
#define XDCFG_IXR_PCFG_POR_B_MASK	0x00000010 /**< FPGA POR mask */
#define XDCFG_IXR_PCFG_CFG_RST_MASK	0x00000008 /**< FPGA Reset mask */
#define XDCFG_IXR_PCFG_DONE_MASK	0x00000004 /**< Done Signal  Mask */
#define XDCFG_IXR_PCFG_INIT_PE_MASK	0x00000002 /**< Detect Positive edge
						     *  of Init Signal
						     */
#define XDCFG_IXR_PCFG_INIT_NE_MASK  	0x00000001 /**< Detect Negative edge
						     *  of Init Signal
						     */
#define XDCFG_IXR_ERROR_FLAGS_MASK		(XDCFG_IXR_AXI_WTO_MASK | \
						XDCFG_IXR_AXI_WERR_MASK | \
						XDCFG_IXR_AXI_RTO_MASK |  \
						XDCFG_IXR_AXI_RERR_MASK | \
						XDCFG_IXR_RX_FIFO_OV_MASK | \
						XDCFG_IXR_DMA_CMD_ERR_MASK |\
						XDCFG_IXR_DMA_Q_OV_MASK |   \
						XDCFG_IXR_P2D_LEN_ERR_MASK |\
						XDCFG_IXR_PCFG_HMAC_ERR_MASK)


#define XDCFG_IXR_ALL_MASK			0x00F7F8EF



/* @} */


/** @name Status Register Bit definitions
  * @{
 */
#define XDCFG_STATUS_DMA_CMD_Q_F_MASK	0x80000000 /**< DMA command
						     *  Queue full
						     */
#define XDCFG_STATUS_DMA_CMD_Q_E_MASK	0x40000000 /**< DMA command
						     *  Queue empty
						     */
#define XDCFG_STATUS_DMA_DONE_CNT_MASK	0x30000000 /**< Number of
						     *  completed DMA
						     *  transfers
						     */
#define XDCFG_STATUS_RX_FIFO_LVL_MASK	0x01F000000 /**< Rx FIFO level */
#define XDCFG_STATUS_TX_FIFO_LVL_MASK	0x0007F000  /**< Tx FIFO level */

#define XDCFG_STATUS_PSS_GTS_USR_B	0x00000800  /**< Tri-state IO
						      *  during HIZ
						      */
#define XDCFG_STATUS_PSS_FST_CFG_B	0x00000400  /**< First PL config
						      *  done
						      */
#define XDCFG_STATUS_PSS_GPWRDWN_B	0x00000200  /**< Global power down */
#define XDCFG_STATUS_PSS_GTS_CFG_B	0x00000100  /**< Tri-state IO during
						      *  config
						      */
#define XDCFG_STATUS_SECURE_RST_MASK	0x00000080  /**< Secure Reset
						      *  POR Status
						      */
#define XDCFG_STATUS_ILLEGAL_APB_ACCESS_MASK 	0x00000040 /**< Illegal APB
							     *  access
						  	     */
#define XDCFG_STATUS_PSS_CFG_RESET_B		0x00000020 /**< PL config
							     *  reset status
							     */
#define XDCFG_STATUS_PCFG_INIT_MASK		0x00000010 /**< FPGA Init
							     *  Status
							     */
#define XDCFG_STATUS_EFUSE_BBRAM_KEY_DISABLE_MASK	0x00000008
							   /**< BBRAM key
							     *  disable
							     */
#define XDCFG_STATUS_EFUSE_SEC_EN_MASK		0x00000004 /**< Efuse Security
						     	     *  Enable Status
						     	     */
#define XDCFG_STATUS_EFUSE_JTAG_DIS_MASK	0x00000002 /**< EFuse JTAG
							     *  Disable
							     *  status
							     */
/* @} */


/** @name DMA Source/Destination Transfer Length Register Bit definitions
 * @{
 */
#define XDCFG_DMA_LEN_MASK		0x7FFFFFF /**< Length Mask */
/*@}*/




/** @name Miscellaneous Control  Register Bit definitions
  * @{
 */
#define XDCFG_MCTRL_PCAP_PS_VERSION_MASK  0xF0000000 /**< PS Version Mask */
#define XDCFG_MCTRL_PCAP_PS_VERSION_SHIFT 28	     /**< PS Version Shift */
#define XDCFG_MCTRL_PCAP_LPBK_MASK	  0x00000010 /**< PCAP loopback mask */
/* @} */

/** @name FIFO Threshold Bit definitions
  * @{
 */

#define XDCFG_CFG_FIFO_QUARTER		0x0	 /**< Quarter empty */
#define XDCFG_CFG_FIFO_HALF		0x1	 /**< Half empty */
#define XDCFG_CFG_FIFO_3QUARTER		0x2	 /**< 3/4 empty */
#define XDCFG_CFG_FIFO_EMPTY		0x4	 /**< Empty */
/* @}*/


/* Miscellaneous constant values */
#define XDCFG_DMA_INVALID_ADDRESS	0xFFFFFFFF  /**< Invalid DMA address */
#define XDCFG_UNLOCK_DATA		0x757BDF0D  /**< First APB access data*/
#define XDCFG_BASE_ADDRESS		0xF8007000  /**< Device Config base
						      * address
						      */
#define XDCFG_CONFIG_RESET_VALUE	0x508	/**< Config reg reset value */							  

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* Read the given register.
*
* @param	BaseAddr is the base address of the device
* @param	RegOffset is the register offset to be read
*
* @return	The 32-bit value of the register
*
* @note		C-style signature:
*		u32 XDcfg_ReadReg(u32 BaseAddr, u32 RegOffset)
*
*****************************************************************************/
#define XDcfg_ReadReg(BaseAddr, RegOffset)		\
	Xil_In32((BaseAddr) + (RegOffset))

/****************************************************************************/
/**
*
* Write to the given register.
*
* @param	BaseAddr is the base address of the device
* @param	RegOffset is the register offset to be written
* @param	Data is the 32-bit value to write to the register
*
* @return	None.
*
* @note		C-style signature:
*		void XDcfg_WriteReg(u32 BaseAddr, u32 RegOffset, u32 Data)
*
*****************************************************************************/
#define XDcfg_WriteReg(BaseAddr, RegOffset, Data)	\
	Xil_Out32((BaseAddr) + (RegOffset), (Data))

/************************** Function Prototypes ******************************/
/*
 * Perform reset operation to the devcfg interface
 */
void XDcfg_ResetHw(u32 BaseAddr);
/************************** Variable Definitions *****************************/

#ifdef __cplusplus
}
#endif

#endif	/* end of protection macro */
