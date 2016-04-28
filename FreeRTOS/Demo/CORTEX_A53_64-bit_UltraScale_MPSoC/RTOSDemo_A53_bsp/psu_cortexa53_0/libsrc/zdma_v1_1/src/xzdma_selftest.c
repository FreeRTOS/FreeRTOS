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
* @file xzdma_selftest.c
* @addtogroup zdma_v1_0
* @{
*
* This file contains the self-test function for the ZDMA core.
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

/***************************** Include Files *********************************/

#include "xzdma.h"

/************************** Constant Definitions *****************************/


/***************** Macros (Inline Functions) Definitions *********************/


/**************************** Type Definitions *******************************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/************************** Function Definitions *****************************/

/*****************************************************************************/
/**
*
* This file contains a diagnostic self-test function for the ZDMA driver.
* Refer to the header file xzdma.h for more detailed information.
*
* @param	InstancePtr is a pointer to XZDma instance.
*
* @return
*		- XST_SUCCESS if the test is successful.
*		- XST_FAILURE if the test is failed.
*
* @note		None.
*
******************************************************************************/
s32 XZDma_SelfTest(XZDma *InstancePtr)
{

	u32 Data;
	s32 Status;

	Xil_AssertNonvoid(InstancePtr != NULL);

	Data = XZDma_ReadReg(InstancePtr->Config.BaseAddress,
				XZDMA_CH_CTRL0_OFFSET);

	/* Changing DMA channel to over fetch */

	XZDma_WriteReg(InstancePtr->Config.BaseAddress, XZDMA_CH_CTRL0_OFFSET,
			(Data | XZDMA_CTRL0_OVR_FETCH_MASK));

	if (((u32)XZDma_ReadReg(InstancePtr->Config.BaseAddress,
		XZDMA_CH_CTRL0_OFFSET) & XZDMA_CTRL0_OVR_FETCH_MASK) !=
						XZDMA_CTRL0_OVR_FETCH_MASK) {
		Status = (s32)XST_FAILURE;
	}
	else {
		Status = (s32)XST_SUCCESS;
	}

	/* Retrieving the change settings */
	XZDma_WriteReg(InstancePtr->Config.BaseAddress, XZDMA_CH_CTRL0_OFFSET,
				Data);

	return Status;

}
/** @} */
