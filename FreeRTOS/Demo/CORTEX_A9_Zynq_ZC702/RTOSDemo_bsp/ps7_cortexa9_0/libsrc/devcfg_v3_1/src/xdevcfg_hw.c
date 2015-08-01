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
