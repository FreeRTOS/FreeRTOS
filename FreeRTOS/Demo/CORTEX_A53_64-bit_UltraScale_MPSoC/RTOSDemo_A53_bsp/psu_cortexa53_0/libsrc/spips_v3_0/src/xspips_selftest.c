/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xspips_selftest.c
*
* This component contains the implementation of selftest functions for an SPI
* device.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ----------------------------------------------
* 1.00  drg/jz 01/25/10 First release
* 1.04a	sg     01/30/13 SetDelays test includes DelayTestNss parameter.
* 3.00  kvn    02/13/15 Modified code for MISRA-C:2012 compliance.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xspips.h"

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
* @param	InstancePtr is a pointer to the XSpiPs instance.
*
* @return
* 		- XST_SUCCESS if successful
*		- XST_REGISTER_ERROR indicates a register did not read or write
*		correctly.
*
* @note		None.
*
******************************************************************************/
s32 XSpiPs_SelfTest(XSpiPs *InstancePtr)
{
	s32 Status;
	u32 Register;
	u8 DelayTestNss;
	u8 DelayTestBtwn;
	u8 DelayTestAfter;
	u8 DelayTestInit;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Reset the SPI device to leave it in a known good state
	 */
	XSpiPs_Reset(InstancePtr);

	/*
	 * All the SPI registers should be in their default state right now.
	 */
	Register = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
				 XSPIPS_CR_OFFSET);
	if (Register != XSPIPS_CR_RESET_STATE) {
		return (s32)XST_REGISTER_ERROR;
	}

	Register = XSpiPs_ReadReg(InstancePtr->Config.BaseAddress,
				 XSPIPS_SR_OFFSET);
	if (Register != XSPIPS_ISR_RESET_STATE) {
		return (s32)XST_REGISTER_ERROR;
	}

	DelayTestNss = 0x5AU;
	DelayTestBtwn = 0xA5U;
	DelayTestAfter = 0xAAU;
	DelayTestInit = 0x55U;

	/*
	 * Write and read the delay register, just to be sure there is some
	 * hardware out there.
	 */
	Status = XSpiPs_SetDelays(InstancePtr, DelayTestNss, DelayTestBtwn,
				   DelayTestAfter, DelayTestInit);
	if (Status != (s32)XST_SUCCESS) {
		return Status;
	}

	XSpiPs_GetDelays(InstancePtr, &DelayTestNss, &DelayTestBtwn,
			&DelayTestAfter, &DelayTestInit);
	if ((0x5AU != DelayTestNss) || (0xA5U != DelayTestBtwn) ||
		(0xAAU != DelayTestAfter) || (0x55U != DelayTestInit)) {
		return (s32)XST_REGISTER_ERROR;
	}

	Status = XSpiPs_SetDelays(InstancePtr, 0U, 0U, 0U, 0U);
	if (Status != (s32)XST_SUCCESS) {
		return Status;
	}

	/*
	 * Reset the SPI device to leave it in a known good state
	 */
	XSpiPs_Reset(InstancePtr);

	return (s32)XST_SUCCESS;
}
