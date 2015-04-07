/******************************************************************************
*
* (c) Copyright 2010-14 Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xgpiops_selftest.c
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
int XGpioPs_SelfTest(XGpioPs *InstancePtr)
{
	int Status = XST_SUCCESS;
	u32 IntrEnabled;
	u32 CurrentIntrType;
	u32 CurrentIntrPolarity;
	u32 CurrentIntrOnAny;
	u32 IntrType;
	u32 IntrPolarity;
	u32 IntrOnAny;
	u32 IntrTestValue = 0x22;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Disable the Interrupts for Bank 0 .
	 */
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
