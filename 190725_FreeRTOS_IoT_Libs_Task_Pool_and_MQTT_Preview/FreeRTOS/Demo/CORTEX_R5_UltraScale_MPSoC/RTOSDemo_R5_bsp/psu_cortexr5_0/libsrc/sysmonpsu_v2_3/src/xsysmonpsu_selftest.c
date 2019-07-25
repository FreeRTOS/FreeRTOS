/******************************************************************************
*
* Copyright (C) 2016 Xilinx, Inc.  All rights reserved.
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
* XILINX BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
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
* @file xsysmon_selftest.c
*
* This file contains a diagnostic self test function for the XSysMon driver.
* The self test function does a simple read/write test of the Alarm Threshold
* Register.
*
* See xsysmonpsu.h for more information.
*
* @note	None.
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.0   kvn   12/15/15  First release
*
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xsysmonpsu.h"

/************************** Constant Definitions ****************************/

/*
 * The following constant defines the test value to be written
 * to the Alarm Threshold Register
 */
#define XSM_ATR_TEST_VALUE 		0x55U

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/

/*****************************************************************************/
/**
*
* Run a self-test on the driver/device. The test
*	- Resets the device,
*	- Writes a value into the Alarm Threshold register and reads it back
*	for comparison.
*	- Resets the device again.
*
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
*
* @return
*		- XST_SUCCESS if the value read from the Alarm Threshold
*		register is the same as the value written.
*		- XST_FAILURE Otherwise
*
* @note		This is a destructive test in that resets of the device are
*		performed. Refer to the device specification for the
*		device status after the reset operation.
*
******************************************************************************/
s32 XSysMonPsu_SelfTest(XSysMonPsu *InstancePtr)
{
	s32 Status;
	u32 RegValue;

	/* Assert the argument */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Reset the device to get it back to its default state */
	XSysMonPsu_Reset(InstancePtr);

	/*
	 * Write a value into the Alarm Threshold registers, read it back, and
	 * do the comparison
	 */
	XSysMonPsu_SetAlarmThreshold(InstancePtr, XSM_ATR_SUP1_UPPER,
				  XSM_ATR_TEST_VALUE, XSYSMON_PS);
	RegValue = (u32)XSysMonPsu_GetAlarmThreshold(InstancePtr,
					XSM_ATR_SUP1_UPPER, XSYSMON_PS);

	if (RegValue == XSM_ATR_TEST_VALUE) {
		Status = XST_SUCCESS;
	} else {
		Status = XST_FAILURE;
	}

	/* Reset the device again to its default state. */
	XSysMonPsu_Reset(InstancePtr);

	/* Return the test result. */
	return Status;
}
/** @} */
