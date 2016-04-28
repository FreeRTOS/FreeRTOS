/******************************************************************************
*
* Copyright (C) 2015 Xilinx, Inc.  All rights reserved.
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
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* XILINX CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
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
* @file xrtcpsu_selftest.c
* @addtogroup rtcpsu_v1_0
* @{
*
* This file contains the self-test functions for the XRtcPsu driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- ------ -------- -----------------------------------------------
* 1.00  kvn    04/21/15 First release.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xrtcpsu.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Variable Definitions *****************************/


/************************** Function Prototypes ******************************/


/****************************************************************************/
/**
*
* This function runs a self-test on the driver and hardware device. This self
* test writes reset value into safety check register and read backs the same.
* If mismatch offers, returns the failure.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance
*
* @return
*		 - XST_SUCCESS if the test was successful
*
* @note
*
* This function can hang if the hardware is not functioning properly.
*
******************************************************************************/
s32 XRtcPsu_SelfTest(XRtcPsu *InstancePtr)
{
	s32 Status = XST_SUCCESS;
	u32 SafetyCheck;

	/* Assert validates the input arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Write the reset value in safety check register and
	 * try reading back. If mismatch happens, return failure.
	 */
	XRtcPsu_WriteReg(InstancePtr->RtcConfig.BaseAddr + XRTC_SFTY_CHK_OFFSET,
			XRTC_SFTY_CHK_RSTVAL);
	SafetyCheck = XRtcPsu_ReadReg(InstancePtr->RtcConfig.BaseAddr +
			XRTC_SFTY_CHK_OFFSET);

	if (SafetyCheck != XRTC_SFTY_CHK_RSTVAL) {
		Status = XST_FAILURE;
	}

	return Status;
}
/** @} */
