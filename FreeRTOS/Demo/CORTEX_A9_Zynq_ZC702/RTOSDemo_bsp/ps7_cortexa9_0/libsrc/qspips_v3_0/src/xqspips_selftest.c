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
* @file xqspips_selftest.c
* @addtogroup qspips_v3_0
* @{
*
* This file contains the implementation of selftest function for the QSPI
* device.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- -----------------------------------------------
* 1.00  sdm 11/25/10 First release
* 2.01a sg  02/03/13 Delay Register test is added with DelayNss parameter.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xqspips.h"

/************************** Constant Definitions *****************************/

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
* @param	InstancePtr is a pointer to the XQspiPs instance.
*
* @return
* 		- XST_SUCCESS if successful
*		- XST_REGISTER_ERROR indicates a register did not read or write
*		correctly.
*
* @note		None.
*
******************************************************************************/
int XQspiPs_SelfTest(XQspiPs *InstancePtr)
{
	int Status;
	u32 Register;
	u8 DelayTestNss;
	u8 DelayTestBtwn;
	u8 DelayTestAfter;
	u8 DelayTestInit;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Reset the QSPI device to leave it in a known good state
	 */
	XQspiPs_Reset(InstancePtr);

	/*
	 * All the QSPI registers should be in their default state right now.
	 */
	Register = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XQSPIPS_CR_OFFSET);
	if (Register != XQSPIPS_CR_RESET_STATE) {
		return XST_REGISTER_ERROR;
	}

	Register = XQspiPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XQSPIPS_SR_OFFSET);
	if (Register != XQSPIPS_ISR_RESET_STATE) {
		return XST_REGISTER_ERROR;
	}

	DelayTestNss = 0x5A;
	DelayTestBtwn = 0xA5;
	DelayTestAfter = 0xAA;
	DelayTestInit = 0x55;

	/*
	 * Write and read the delay register, just to be sure there is some
	 * hardware out there.
	 */
	Status = XQspiPs_SetDelays(InstancePtr, DelayTestNss, DelayTestBtwn,
				DelayTestAfter, DelayTestInit);
	if (Status != XST_SUCCESS) {
		return Status;
	}

	XQspiPs_GetDelays(InstancePtr, &DelayTestNss, &DelayTestBtwn,
				&DelayTestAfter, &DelayTestInit);
	if ((0x5A != DelayTestNss) || (0xA5 != DelayTestBtwn) ||
		(0xAA != DelayTestAfter) || (0x55 != DelayTestInit)) {
		return XST_REGISTER_ERROR;
	}

	Status = XQspiPs_SetDelays(InstancePtr, 0, 0, 0, 0);
	if (Status != XST_SUCCESS) {
		return Status;
	}

	/*
	 * Reset the QSPI device to leave it in a known good state
	 */
	XQspiPs_Reset(InstancePtr);

	return XST_SUCCESS;
}
/** @} */
