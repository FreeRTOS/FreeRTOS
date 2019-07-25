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
* @file xdmaps_selftest.c
* @addtogroup dmaps_v2_3
* @{
*
* This file contains the self-test functions for the XDmaPs driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------ -------- -----------------------------------------------
* 1.00	hbm 	03/29/2010 First Release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xdmaps.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Variable Definitions *****************************/


/************************** Function Prototypes ******************************/


/****************************************************************************/
/**
*
* This function runs a self-test on the driver and hardware device. This self
* test performs a local loopback and verifies data can be sent and received.
*
* The time for this test is proportional to the baud rate that has been set
* prior to calling this function.
*
* The mode and control registers are restored before return.
*
* @param	InstPtr is a pointer to the XDmaPs instance
*
* @return
*
*		- XST_SUCCESS if the test was successful
*		- XST_FAILURE if the test failed
*
* @note
*
* This function can hang if the hardware is not functioning properly.
*
******************************************************************************/
int XDmaPs_SelfTest(XDmaPs *InstPtr)
{
	u32 BaseAddr = InstPtr->Config.BaseAddress;
	int i;

	if (XDmaPs_ReadReg(BaseAddr, XDMAPS_DBGSTATUS_OFFSET)
	    & XDMAPS_DBGSTATUS_BUSY)
		return XST_FAILURE;

	for (i = 0; i < XDMAPS_CHANNELS_PER_DEV; i++) {
		if (XDmaPs_ReadReg(BaseAddr,
				    XDmaPs_CSn_OFFSET(i)))
			return XST_FAILURE;
	}
	return XST_SUCCESS;
}
/** @} */
