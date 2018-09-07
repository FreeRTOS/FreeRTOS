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
* @file xgpiops_selftest.c
* @addtogroup gpiops_v3_3
* @{
*
* This file contains a diagnostic self-test function for the XGpioPs driver.
*
* Read xgpiops.h file for more information.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sv   01/18/10 First Release
* 3.00  kvn  02/13/15 Modified code for MISRA-C:2012 compliance.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xstatus.h"
#include "xgpiops.h"

/************************** Constant Definitions ****************************/


/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/

/*****************************************************************************/
/**
*
* This function runs a self-test on the GPIO driver/device. This function
* does a register read/write test on some of the Interrupt Registers.
*
* @param	InstancePtr is a pointer to the XGpioPs instance.
*
* @return
*		- XST_SUCCESS if the self-test passed.
* 		- XST_FAILURE otherwise.
*
*
******************************************************************************/
s32 XGpioPs_SelfTest(XGpioPs *InstancePtr)
{
	s32 Status = XST_SUCCESS;
	u32 IntrEnabled;
	u32 CurrentIntrType = 0U;
	u32 CurrentIntrPolarity = 0U;
	u32 CurrentIntrOnAny = 0U;
	u32 IntrType = 0U;
	u32 IntrPolarity = 0U;
	u32 IntrOnAny = 0U;
	u32 IntrTestValue = 0x22U;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Disable the Interrupts for Bank 0 . */
	IntrEnabled = XGpioPs_IntrGetEnabled(InstancePtr, XGPIOPS_BANK0);
	XGpioPs_IntrDisable(InstancePtr, XGPIOPS_BANK0, IntrEnabled);

	/*
	 * Get the Current Interrupt properties for Bank 0.
	 * Set them to a known value, read it back and compare.
	 */
	XGpioPs_GetIntrType(InstancePtr, XGPIOPS_BANK0, &CurrentIntrType,
			     &CurrentIntrPolarity, &CurrentIntrOnAny);

	XGpioPs_SetIntrType(InstancePtr, XGPIOPS_BANK0, IntrTestValue,
			     IntrTestValue, IntrTestValue);

	XGpioPs_GetIntrType(InstancePtr, XGPIOPS_BANK0, &IntrType,
			     &IntrPolarity, &IntrOnAny);

	if ((IntrType != IntrTestValue) && (IntrPolarity != IntrTestValue) &&
	    (IntrOnAny != IntrTestValue)) {

		Status = XST_FAILURE;
	}

	/*
	 * Restore the contents of all the interrupt registers modified in this
	 * test.
	 */
	XGpioPs_SetIntrType(InstancePtr, XGPIOPS_BANK0, CurrentIntrType,
			     CurrentIntrPolarity, CurrentIntrOnAny);

	XGpioPs_IntrEnable(InstancePtr, XGPIOPS_BANK0, IntrEnabled);

	return Status;
}
/** @} */
