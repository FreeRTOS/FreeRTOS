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
* @file xiicps_selftest.c
*
* This component contains the implementation of selftest functions for the
* XIicPs driver component.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------
* 1.00a drg/jz 01/30/10 First release
* 1.00a sdm    09/22/11 Removed unused code
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xiicps.h"

/************************** Constant Definitions *****************************/

#define REG_TEST_VALUE    0x00000005

/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Runs a self-test on the driver/device. The self-test is destructive in that
* a reset of the device is performed in order to check the reset values of
* the registers and to get the device into a known state.
*
* Upon successful return from the self-test, the device is reset.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_REGISTER_ERROR indicates a register did not read or write
*		correctly
*
* @note		None.
*
******************************************************************************/
int XIicPs_SelfTest(XIicPs *InstancePtr)
{

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * All the IIC registers should be in their default state right now.
	 */
	if ((XIICPS_CR_RESET_VALUE !=
		 XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				  XIICPS_CR_OFFSET)) ||
		(XIICPS_TO_RESET_VALUE !=
		 XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				  XIICPS_TIME_OUT_OFFSET)) ||
		(XIICPS_IXR_ALL_INTR_MASK !=
		 XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				  XIICPS_IMR_OFFSET))) {
		return XST_FAILURE;
	}

	XIicPs_Reset(InstancePtr);

	/*
	 * Write, Read then write a register
	 */
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XIICPS_SLV_PAUSE_OFFSET, REG_TEST_VALUE);

	if (REG_TEST_VALUE != XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
						   XIICPS_SLV_PAUSE_OFFSET)) {
		return XST_FAILURE;
	}

	XIicPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XIICPS_SLV_PAUSE_OFFSET, 0);

	XIicPs_Reset(InstancePtr);

	return XST_SUCCESS;
}

