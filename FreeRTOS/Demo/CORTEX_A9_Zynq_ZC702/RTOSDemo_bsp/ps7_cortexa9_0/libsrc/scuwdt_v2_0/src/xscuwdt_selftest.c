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
* @file xscuwdt_selftest.c
* @addtogroup scuwdt_v2_0
* @{
*
* Contains diagnostic self-test functions for the XScuWdt driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a sdm 01/15/10 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xscuwdt.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/****************************************************************************/
/**
*
* Run a self-test on the WDT. This test stops the watchdog, writes a value to
* the watchdog load register, starts the watchdog and verifies that the value
* read from the counter register is less that the value written to the load
* register. It then restores the control register and the watchdog load
* register.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
*
* @return
*		- XST_SUCCESS if self-test was successful.
*		- XST_FAILURE if the WDT is not decrementing.
*
* @note		None.
*
******************************************************************************/
int XScuWdt_SelfTest(XScuWdt *InstancePtr)
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
	 * Stop the watchdog timer.
	 */
	CtrlOrig = XScuWdt_GetControlReg(InstancePtr);
	XScuWdt_SetControlReg(InstancePtr,
			      CtrlOrig & ~XSCUWDT_CONTROL_WD_ENABLE_MASK);

	LoadOrig = XScuWdt_ReadReg((InstancePtr)->Config.BaseAddr,
				   XSCUWDT_LOAD_OFFSET);
	XScuWdt_LoadWdt(InstancePtr, 0xFFFFFFFF);

	/*
	 * Start the watchdog timer and check if the watchdog counter is
	 * decrementing.
	 */
	XScuWdt_SetControlReg(InstancePtr,
			      CtrlOrig | XSCUWDT_CONTROL_WD_ENABLE_MASK);

	Register = XScuWdt_ReadReg((InstancePtr)->Config.BaseAddr,
				   XSCUWDT_COUNTER_OFFSET);

	XScuWdt_LoadWdt(InstancePtr, LoadOrig);
	XScuWdt_SetControlReg(InstancePtr, CtrlOrig);

	if (Register == 0xFFFFFFFF) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}
/** @} */
