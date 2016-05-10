/******************************************************************************
*
* Copyright (C) 2002 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xtmrctr_selftest.c
* @addtogroup tmrctr_v4_0
* @{
*
* Contains diagnostic/self-test functions for the XTmrCtr component.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00b jhl  02/06/02 First release
* 1.10b mta  03/21/07 Updated to new coding style
* 2.00a ktn  10/30/09 Updated to use HAL API's. _m is removed from all the macro
*		      definitions.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_io.h"
#include "xtmrctr.h"
#include "xtmrctr_i.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Runs a self-test on the driver/device. This test verifies that the specified
* timer counter of the device can be enabled and increments.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	TmrCtrNumber is the timer counter of the device to operate on.
*		Each device may contain multiple timer counters. The timer
*		number is a  zero based number with a range of
*		0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return
* 		- XST_SUCCESS if self-test was successful
*		- XST_FAILURE if the timer is not incrementing.
*
* @note
*
* This is a destructive test using the provided timer. The current settings
* of the timer are returned to the initialized values and all settings at the
* time this function is called are overwritten.
*
******************************************************************************/
int XTmrCtr_SelfTest(XTmrCtr * InstancePtr, u8 TmrCtrNumber)
{
	u32 TimerCount1 = 0;
	u32 TimerCount2 = 0;
	u16 Count = 0;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(TmrCtrNumber < XTC_DEVICE_TIMER_COUNT);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Set the Capture register to 0
	 */
	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TLR_OFFSET, 0);

	/*
	 * Reset the timer and the interrupt
	 */
	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TCSR_OFFSET,
			  XTC_CSR_INT_OCCURED_MASK | XTC_CSR_LOAD_MASK);

	/*
	 * Set the control/status register to enable timer
	 */
	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TCSR_OFFSET, XTC_CSR_ENABLE_TMR_MASK);

	/*
	 * Read the timer
	 */
	TimerCount1 = XTmrCtr_ReadReg(InstancePtr->BaseAddress,
					 TmrCtrNumber, XTC_TCR_OFFSET);
	/*
	 * Make sure timer is incrementing if the Count rolls over to zero
	 * and the timer still has not incremented an error is returned
	 */

	do {
		TimerCount2 = XTmrCtr_ReadReg(InstancePtr->BaseAddress,
						 TmrCtrNumber, XTC_TCR_OFFSET);
		Count++;
	}
	while ((TimerCount1 == TimerCount2) && (Count != 0));

	/*
	 * Reset the timer and the interrupt
	 */
	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TCSR_OFFSET,
			  XTC_CSR_INT_OCCURED_MASK | XTC_CSR_LOAD_MASK);

	/*
	 * Set the control/status register to 0 to complete initialization
	 * this disables the timer completely and allows it to be used again
	 */

	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TCSR_OFFSET, 0);

	if (TimerCount1 == TimerCount2) {
		return XST_FAILURE;
	}
	else {
		return XST_SUCCESS;
	}
}
/** @} */
