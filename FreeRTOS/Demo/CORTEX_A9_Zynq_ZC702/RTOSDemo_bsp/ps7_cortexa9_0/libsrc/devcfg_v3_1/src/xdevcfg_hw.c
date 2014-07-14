/******************************************************************************
*
* (c) Copyright 2010-14 Xilinx, Inc. All rights reserved.
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
/****************************************************************************/
/**
*
* @file xdevcfg_hw.c
*
* This file contains the implementation of the interface reset functionality
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 2.04a kpc 10/07/13 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xdevcfg_hw.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/*****************************************************************************/
/**
* This function perform the reset sequence to the given devcfg interface by 
* configuring the appropriate control bits in the devcfg specifc registers
* the devcfg reset squence involves the following steps
*	Disable all the interuupts 
*	Clear the status
*	Update relevant config registers with reset values
*	Disbale the looopback mode and pcap rate enable
*
* @param   BaseAddress of the interface
*
* @return N/A
*
* @note 
* This function will not modify the slcr registers that are relavant for 
* devcfg controller
******************************************************************************/
void XDcfg_ResetHw(u32 BaseAddr)
{
	u32 Regval = 0;

	/* Mask the interrupts  */
	XDcfg_WriteReg(BaseAddr, XDCFG_INT_MASK_OFFSET,
			XDCFG_IXR_ALL_MASK);
	/* Clear the interuupt status */			
	Regval = XDcfg_ReadReg(BaseAddr, XDCFG_INT_STS_OFFSET);		
	XDcfg_WriteReg(BaseAddr, XDCFG_INT_STS_OFFSET, Regval);
	/* Clear the source address register */						
	XDcfg_WriteReg(BaseAddr, XDCFG_DMA_SRC_ADDR_OFFSET, 0x0);
	/* Clear the destination address register */									
	XDcfg_WriteReg(BaseAddr, XDCFG_DMA_DEST_ADDR_OFFSET, 0x0);
	/* Clear the source length register */												
	XDcfg_WriteReg(BaseAddr, XDCFG_DMA_SRC_LEN_OFFSET, 0x0);
	/* Clear the destination length register */															
	XDcfg_WriteReg(BaseAddr, XDCFG_DMA_DEST_LEN_OFFSET, 0x0);
	/* Clear the loopback enable bit */				
	Regval = XDcfg_ReadReg(BaseAddr, XDCFG_MCTRL_OFFSET);	
	Regval = Regval & ~XDCFG_MCTRL_PCAP_LPBK_MASK;				
	XDcfg_WriteReg(BaseAddr, XDCFG_MCTRL_OFFSET, Regval);	
	/*Reset the configuration register to reset value */							
	XDcfg_WriteReg(BaseAddr, XDCFG_CFG_OFFSET,
				XDCFG_CONFIG_RESET_VALUE);		
	/*Disable the PCAP rate enable bit */										
	Regval = XDcfg_ReadReg(BaseAddr, XDCFG_CTRL_OFFSET);	
	Regval = Regval & ~XDCFG_CTRL_PCAP_RATE_EN_MASK;				
	XDcfg_WriteReg(BaseAddr, XDCFG_CTRL_OFFSET, Regval);
				
}
