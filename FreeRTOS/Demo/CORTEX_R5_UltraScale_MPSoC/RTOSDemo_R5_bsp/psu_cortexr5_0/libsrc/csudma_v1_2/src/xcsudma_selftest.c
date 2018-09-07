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
* @file xcsudma_selftest.c
* @addtogroup csudma_v1_2
* @{
*
* This file contains a diagnostic self-test function for the CSU_DMA driver.
* Refer to the header file xcsudma.h for more detailed information.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- ---------------------------------------------------
* 1.0   vnsld   22/10/14 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xcsudma.h"

/************************** Constant Definitions ****************************/


/**************************** Type Definitions ******************************/


/***************** Macros (Inline Functions) Definitions ********************/


/************************** Variable Definitions ****************************/


/************************** Function Prototypes *****************************/


/************************** Function Definitions *****************************/


/*****************************************************************************/
/**
*
* This function runs a self-test on the driver and hardware device. Performs
* reset of both source and destination channels and checks if reset is working
* properly or not.
*
* @param	InstancePtr is a pointer to the XCsuDma instance.
*
* @return
*		- XST_SUCCESS if the self-test passed.
* 		- XST_FAILURE otherwise.
*
* @note		None.
*
******************************************************************************/
s32 XCsuDma_SelfTest(XCsuDma *InstancePtr)
{
	u32 Data;
	s32 Status;

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);

	Data = XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
					(u32)(XCSUDMA_CTRL_OFFSET));

	/* Changing Endianess of Source channel */

	XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
			(u32)(XCSUDMA_CTRL_OFFSET),
			((Data) | (u32)(XCSUDMA_CTRL_ENDIAN_MASK)));

	if ((XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
		(u32)(XCSUDMA_CTRL_OFFSET)) &
			(u32)(XCSUDMA_CTRL_ENDIAN_MASK)) ==
				(XCSUDMA_CTRL_ENDIAN_MASK)) {
		Status = (s32)(XST_SUCCESS);
	}
	else {
		Status = (s32)(XST_FAILURE);
	}

	/* Changes made are being reverted back */
	XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
				(u32)(XCSUDMA_CTRL_OFFSET), Data);

	return Status;

}
/** @} */
