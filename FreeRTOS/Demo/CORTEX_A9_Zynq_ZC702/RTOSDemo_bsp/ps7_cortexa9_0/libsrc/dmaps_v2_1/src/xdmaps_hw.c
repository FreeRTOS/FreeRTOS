/******************************************************************************
*
* Copyright (C) 2009 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xdmaps_hw.c
* @addtogroup dmaps_v2_1
* @{
*
* This file contains the implementation of the interface reset functionality 
*	for XDmaPs driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  	Date     Changes
* ----- ------ -------- ----------------------------------------------
* 1.06a kpc 10/07/13 First release
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/
#include "xdmaps_hw.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/
#ifndef XDMAPS_MAX_WAIT
#define XDMAPS_MAX_WAIT 4000
#endif
/************************** Function Prototypes *****************************/

/************************** Variable Definitions ****************************/

/*****************************************************************************/
/**
* This function perform the reset sequence to the given dmaps interface by 
* configuring the appropriate control bits in the dmaps specifc registers
* the dmaps reset squence involves the following steps
*	Disable all the interuupts 
*	Clear the pending interrupts
*	Kill all the active channel threads
*	Kill the manager thread
*
* @param   BaseAddress of the interface
*
* @return N/A
*
* @note 
* This function will not modify the slcr registers that are relavant for 
* dmaps controller
******************************************************************************/
void XDmaPs_ResetHw(u32 BaseAddress)
{
	u32 DbgInst;
	u32 WaitCount = 0;
	u32 ChanIndex;

	/* Disable all the interrupts */
	XDmaPs_WriteReg(BaseAddress, XDMAPS_INTEN_OFFSET, 0x00);
	/* Clear the interrupts */
	XDmaPs_WriteReg(BaseAddress, XDMAPS_INTCLR_OFFSET, XDMAPS_INTCLR_ALL_MASK);
	/* Kill the dma channel threads */
	for (ChanIndex=0; ChanIndex < XDMAPS_CHANNELS_PER_DEV; ChanIndex++) {
		while ((XDmaPs_ReadReg(BaseAddress, XDMAPS_DBGSTATUS_OFFSET)
				& XDMAPS_DBGSTATUS_BUSY)
				&& (WaitCount < XDMAPS_MAX_WAIT))
				WaitCount++;

		DbgInst = XDmaPs_DBGINST0(0, 0x01, ChanIndex, 1);	
		XDmaPs_WriteReg(BaseAddress, XDMAPS_DBGINST0_OFFSET, DbgInst);
		XDmaPs_WriteReg(BaseAddress, XDMAPS_DBGINST1_OFFSET, 0x0);	
		XDmaPs_WriteReg(BaseAddress, XDMAPS_DBGCMD_OFFSET, 0x0);
	}	
	/* Kill the manager thread	*/
	DbgInst = XDmaPs_DBGINST0(0, 0x01, 0, 0);	
	XDmaPs_WriteReg(BaseAddress, XDMAPS_DBGINST0_OFFSET, DbgInst);
	XDmaPs_WriteReg(BaseAddress, XDMAPS_DBGINST1_OFFSET, 0x0);	
	XDmaPs_WriteReg(BaseAddress, XDMAPS_DBGCMD_OFFSET, 0x0);	
}



/** @} */
