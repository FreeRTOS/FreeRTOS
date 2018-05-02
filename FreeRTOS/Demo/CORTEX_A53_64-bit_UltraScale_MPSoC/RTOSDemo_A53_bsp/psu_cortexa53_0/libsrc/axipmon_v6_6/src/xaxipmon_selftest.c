/******************************************************************************
*
* Copyright (C) 2012 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xaxipmon_selftest.c
* @addtogroup axipmon_v6_6
* @{
*
* This file contains a diagnostic self test function for the XAxiPmon driver.
* The self test function does a simple read/write test of the Alarm Threshold
* Register.
*
* See XAxiPmon.h for more information.
*
* @note	None.
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.00a bss  02/24/12 First release
* 2.00a bss  06/23/12 Updated to support v2_00a version of IP.
* 6.3   kvn  07/02/15 Modified code according to MISRA-C:2012 guidelines.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xaxipmon.h"

/************************** Constant Definitions ****************************/

/*
 * The following constant defines the test value to be written
 * to the Range Registers of Incrementers
 */

#define XAPM_TEST_RANGEUPPER_VALUE	16U /**< Test Value for Upper Range */
#define XAPM_TEST_RANGELOWER_VALUE	 8U /**< Test Value for Lower Range */

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/

/*****************************************************************************/
/**
*
* Run a self-test on the driver/device. The test
*	- Resets the device,
*	- Writes a value into the Range Registers of Incrementer 0 and reads
*	  it back for comparison.
*	- Resets the device again.
*
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return
*		- XST_SUCCESS if the value read from the Range Register of
*		  Incrementer 0 is the same as the value written.
*		- XST_FAILURE Otherwise
*
* @note		This is a destructive test in that resets of the device are
*		performed. Refer to the device specification for the
*		device status after the reset operation.
*
******************************************************************************/
s32 XAxiPmon_SelfTest(XAxiPmon *InstancePtr)
{
	s32 Status;
	u16 RangeUpper = 0U;
	u16 RangeLower = 0U;

	/*
	 * Assert the argument
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	/*
	 * Reset the device to get it back to its default state
	 */
	(void)XAxiPmon_ResetMetricCounter(InstancePtr);
	XAxiPmon_ResetGlobalClkCounter(InstancePtr);

	/*
	 * Write a value into the Incrementer register and
	 * read it back, and do the comparison
	 */
	XAxiPmon_SetIncrementerRange(InstancePtr, XAPM_INCREMENTER_0,
					XAPM_TEST_RANGEUPPER_VALUE,
					XAPM_TEST_RANGELOWER_VALUE);

	XAxiPmon_GetIncrementerRange(InstancePtr, XAPM_INCREMENTER_0,
					&RangeUpper, &RangeLower);

	if ((RangeUpper == XAPM_TEST_RANGEUPPER_VALUE) &&
			(RangeLower == XAPM_TEST_RANGELOWER_VALUE)) {
		Status = XST_SUCCESS;
	} else {
		Status = XST_FAILURE;
	}

	/*
	 * Reset the device again to its default state.
	 */
	(void)XAxiPmon_ResetMetricCounter(InstancePtr);
	XAxiPmon_ResetGlobalClkCounter(InstancePtr);

	/*
	 * Return the test result.
	 */
	return Status;
}
/** @} */
