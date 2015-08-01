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
/*****************************************************************************/
/**
*
* @file xemacps_hw.c
*
* This file contains the implementation of the ethernet interface reset sequence
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.05a kpc  28/06/13 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xparameters.h"
#include "xemacps_hw.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

/*****************************************************************************/
/**
* This function perform the reset sequence to the given emacps interface by 
* configuring the appropriate control bits in the emacps specifc registers.
* the emacps reset squence involves the following steps
*	Disable all the interuupts 
*	Clear the status registers
*	Disable Rx and Tx engines
*	Update the Tx and Rx descriptor queue registers with reset values
*	Update the other relevant control registers with reset value
*
* @param   BaseAddress of the interface
*
* @return N/A
*
* @note 
* This function will not modify the slcr registers that are relavant for 
* emacps controller
******************************************************************************/
void XEmacPs_ResetHw(u32 BaseAddr)
{
	u32 RegVal = 0;

	/* Disable the interrupts  */
	XEmacPs_WriteReg(BaseAddr,XEMACPS_IDR_OFFSET,0x0);

	/* Stop transmission,disable loopback and Stop tx and Rx engines */
	RegVal = XEmacPs_ReadReg(BaseAddr,XEMACPS_NWCTRL_OFFSET);
	RegVal &= ~(XEMACPS_NWCTRL_TXEN_MASK|
				XEMACPS_NWCTRL_RXEN_MASK|
				XEMACPS_NWCTRL_HALTTX_MASK|
				XEMACPS_NWCTRL_LOOPEN_MASK);
	/* Clear the statistic registers, flush the packets in DPRAM*/				
	RegVal |= (XEMACPS_NWCTRL_STATCLR_MASK|
				XEMACPS_NWCTRL_FLUSH_DPRAM_MASK);
	XEmacPs_WriteReg(BaseAddr,XEMACPS_NWCTRL_OFFSET,RegVal);
	/* Clear the interrupt status */					
	XEmacPs_WriteReg(BaseAddr,XEMACPS_ISR_OFFSET,XEMACPS_IXR_ALL_MASK);
	/* Clear the tx status */						
	XEmacPs_WriteReg(BaseAddr,XEMACPS_TXSR_OFFSET,XEMACPS_TXSR_ERROR_MASK|
									XEMACPS_TXSR_TXCOMPL_MASK|
									XEMACPS_TXSR_TXGO_MASK);
	/* Clear the rx status */							
	XEmacPs_WriteReg(BaseAddr,XEMACPS_RXSR_OFFSET,
								XEMACPS_RXSR_FRAMERX_MASK);	
	/* Clear the tx base address */							
	XEmacPs_WriteReg(BaseAddr,XEMACPS_TXQBASE_OFFSET,0x0);		
	/* Clear the rx base address */						
	XEmacPs_WriteReg(BaseAddr,XEMACPS_RXQBASE_OFFSET,0x0);	
	/* Update the network config register with reset value */						
	XEmacPs_WriteReg(BaseAddr,XEMACPS_NWCFG_OFFSET,XEMACPS_NWCFG_RESET_MASK);
	/* Update the hash address registers with reset value */	
	XEmacPs_WriteReg(BaseAddr,XEMACPS_HASHL_OFFSET,0x0);			
	XEmacPs_WriteReg(BaseAddr,XEMACPS_HASHH_OFFSET,0x0);
}




