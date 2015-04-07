/*****************************************************************************
*
* (c) Copyright 2009-2013 Xilinx, Inc. All rights reserved.
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
*****************************************************************************/
/****************************************************************************/
/**
*
* @file xdmaps_hw.c
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



