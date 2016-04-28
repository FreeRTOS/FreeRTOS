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
/****************************************************************************/
/**
*
* @file xwdtps_selftest.c
* @addtogroup wdtps_v3_0
* @{
*
* Contains diagnostic self-test functions for the XWdtPs driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- --------------------------------------------
* 1.00a ecm/jz 01/15/10 First release
* 1.02a sg     08/01/12 Modified it use the Reset Length mask for the self
*		        test for CR 658287
* 3.00  kvn    02/13/15 Modified code for MISRA-C:2012 compliance.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xwdtps.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/****************************************************************************/
/**
*
* Run a self-test on the timebase. This test verifies that the register access
* locking functions. This is tested by trying to alter a register without
* setting the key value and verifying that the register contents did not
* change.
*
* @param	InstancePtr is a pointer to the XWdtPs instance.
*
* @return
*		- XST_SUCCESS if self-test was successful.
*		- XST_FAILURE if self-test was not successful.
*
* @note		None.
*
******************************************************************************/
s32 XWdtPs_SelfTest(XWdtPs *InstancePtr)
{
	u32 ZmrOrig;
	u32 ZmrValue1;
	u32 ZmrValue2;
	s32 Status;

	/*
	 * Assert to ensure the inputs are valid and the instance has been
	 * initialized.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the ZMR register at start the test.
	 */
	ZmrOrig = XWdtPs_ReadReg(InstancePtr->Config.BaseAddress,
				 XWDTPS_ZMR_OFFSET);

	/*
	 * EX-OR in the length of the interrupt pulse,
	 * do not set the key value.
	 */
	ZmrValue1 = ZmrOrig ^ (u32)XWDTPS_ZMR_RSTLN_MASK;


	/*
	 * Try to write to register w/o key value then read back.
	 */
	XWdtPs_WriteReg(InstancePtr->Config.BaseAddress, XWDTPS_ZMR_OFFSET,
			  ZmrValue1);

	ZmrValue2 =	XWdtPs_ReadReg(InstancePtr->Config.BaseAddress,
				 XWDTPS_ZMR_OFFSET);

	if (ZmrValue1 == ZmrValue2) {
		/*
		 * If the values match, the hw failed the test,
		 * return orig register value.
		 */
		XWdtPs_WriteReg(InstancePtr->Config.BaseAddress,
				  XWDTPS_ZMR_OFFSET,
				  (ZmrOrig | (u32)XWDTPS_ZMR_ZKEY_VAL));
		Status = XST_FAILURE;
	} else {


		/*
		 * Try to write to register with key value then read back.
		 */
		XWdtPs_WriteReg(InstancePtr->Config.BaseAddress, XWDTPS_ZMR_OFFSET,
				  (ZmrValue1 | XWDTPS_ZMR_ZKEY_VAL));

		ZmrValue2 =	XWdtPs_ReadReg(InstancePtr->Config.BaseAddress,
					 XWDTPS_ZMR_OFFSET);

		if (ZmrValue1 != ZmrValue2) {
			/*
			 * If the values do not match, the hw failed the test,
			 * return orig register value.
			 */
			XWdtPs_WriteReg(InstancePtr->Config.BaseAddress,
					  XWDTPS_ZMR_OFFSET,
					  ZmrOrig | XWDTPS_ZMR_ZKEY_VAL);
			Status = XST_FAILURE;

		} else {

			/*
			 * The hardware locking feature is functional, return the original value
			 * and return success.
			 */
			XWdtPs_WriteReg(InstancePtr->Config.BaseAddress, XWDTPS_ZMR_OFFSET,
					  ZmrOrig | XWDTPS_ZMR_ZKEY_VAL);

			Status = XST_SUCCESS;
		}
	}
	return Status;
}
/** @} */
