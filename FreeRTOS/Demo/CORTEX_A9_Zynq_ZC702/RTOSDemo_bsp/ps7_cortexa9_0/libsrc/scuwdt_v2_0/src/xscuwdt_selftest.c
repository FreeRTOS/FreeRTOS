/******************************************************************************
*
* (c) Copyright 2010-12 Xilinx, Inc. All rights reserved.
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
/****************************************************************************/
/**
*
* @file xscuwdt_selftest.c
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
