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
* @file xscugic_selftest.c
* @addtogroup scugic_v2_1
* @{
*
* Contains diagnostic self-test functions for the XScuGic driver.
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a drg  01/19/10 First release
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xscugic.h"

/************************** Constant Definitions *****************************/

#define	XSCUGIC_PCELL_ID	0xB105F00D

/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/*****************************************************************************/
/**
*
* Run a self-test on the driver/device. This test reads the ID registers and
* compares them.
*
* @param	InstancePtr is a pointer to the XScuGic instance.
*
* @return
*
* 		- XST_SUCCESS if self-test is successful.
* 		- XST_FAILURE if the self-test is not successful.
*
* @note		None.
*
******************************************************************************/
int  XScuGic_SelfTest(XScuGic *InstancePtr)
{
	u32 RegValue1 =0;
	int Index;

	/*
	 * Assert the arguments
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the ID registers.
	 */
	for(Index=0; Index<=3; Index++) {
		RegValue1 |= XScuGic_DistReadReg(InstancePtr,
			(XSCUGIC_PCELLID_OFFSET + (Index * 4))) << (Index * 8);
	}

	if(XSCUGIC_PCELL_ID != RegValue1){
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}

/** @} */
