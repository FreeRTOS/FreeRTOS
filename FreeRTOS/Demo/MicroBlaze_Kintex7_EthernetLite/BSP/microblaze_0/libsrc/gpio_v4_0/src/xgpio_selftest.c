/******************************************************************************
*
* Copyright (C) 2002 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xgpio_selftest.c
*
* The implementation of the XGpio driver's self test function.
* See xgpio.h for more information about the driver.
*
* @note
*
* None
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a rmm  02/04/02 First release
* 2.00a jhl  01/13/04 Addition of dual channels and interrupts.
* 2.11a mta  03/21/07 Updated to new coding style
* 3.00a sv   11/21/09 Updated to use HAL Processor APIs.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/
#include "xgpio.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/


/******************************************************************************/
/**
* Run a self-test on the driver/device. This function does a minimal test
* in which the data register is read. It only does a read without any kind
* of test because the hardware has been parameterized such that it may be only
* an input such that the state of the inputs won't be known.
*
* All other hardware features of the device are not guaranteed to be in the
* hardware since they are parameterizable.
*
*
* @param	InstancePtr is a pointer to the XGpio instance to be worked on.
*		This parameter must have been previously initialized with
*		XGpio_Initialize().
*
* @return 	XST_SUCCESS always. If the GPIO device was not present in the
*		hardware a bus error could be generated. Other indicators of a
*		bus error, such as registers in bridges or buses, may be
*		necessary to determine if this function caused a bus error.
*
* @note		None.
*
******************************************************************************/
int XGpio_SelfTest(XGpio * InstancePtr)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read from the data register of channel 1 which is always guaranteed
	 * to be in the hardware device. Since the data may be configured as
	 * all inputs, there is not way to guarantee the value read so don't
	 * test it.
	 */
	(void) XGpio_DiscreteRead(InstancePtr, 1);

	return (XST_SUCCESS);
}
