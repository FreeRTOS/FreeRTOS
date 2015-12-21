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
/****************************************************************************/
/**
*
* @file xscutimer_selftest.c
* @addtogroup scutimer_v2_0
* @{
*
* Contains diagnostic self-test functions for the XScuTimer driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a nm  03/10/10 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xscutimer.h"

/************************** Constant Definitions *****************************/

#define XSCUTIMER_SELFTEST_VALUE	0xA55AF00F

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/****************************************************************************/
/**
*
* Run a self-test on the timer. This test clears the timer enable bit in
* the control register, writes to the timer load register and verifies the
* value read back matches the value written and restores the control register
* and the timer load register.
*
* @param	InstancePtr is a pointer to the XScuTimer instance.
*
* @return
*		- XST_SUCCESS if self-test was successful.
*		- XST_FAILURE if self test was not successful.
*
* @note		None.
*
******************************************************************************/
int XScuTimer_SelfTest(XScuTimer *InstancePtr)
{
	u32 Register;
	u32 CtrlOrig;
	u32 LoadOrig;

	/*
	 * Assert to ensure the inputs are valid and the instance has been
	 * initialized.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Save the contents of the Control Register and stop the timer.
	 */
	CtrlOrig = XScuTimer_ReadReg(InstancePtr->Config.BaseAddr,
				  XSCUTIMER_CONTROL_OFFSET);
	Register = CtrlOrig & ~XSCUTIMER_CONTROL_ENABLE_MASK;
	XScuTimer_WriteReg(InstancePtr->Config.BaseAddr,
			XSCUTIMER_CONTROL_OFFSET, Register);

	/*
	 * Save the contents of the Load Register.
	 * Load a new test value in the Load Register, read it back and
	 * compare it with the written value.
	 */
	LoadOrig = XScuTimer_ReadReg((InstancePtr)->Config.BaseAddr,
				  XSCUTIMER_LOAD_OFFSET);
	XScuTimer_LoadTimer(InstancePtr, XSCUTIMER_SELFTEST_VALUE);
	Register = XScuTimer_ReadReg((InstancePtr)->Config.BaseAddr,
				  XSCUTIMER_LOAD_OFFSET);

	/*
	 * Restore the contents of the Load Register and Control Register.
	 */
	XScuTimer_LoadTimer(InstancePtr, LoadOrig);
	XScuTimer_WriteReg(InstancePtr->Config.BaseAddr,
			XSCUTIMER_CONTROL_OFFSET, CtrlOrig);

	/*
	 * Return a Failure if the contents of the Load Register do not
	 * match with the value written to it.
	 */
	if (Register != XSCUTIMER_SELFTEST_VALUE) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}
/** @} */
