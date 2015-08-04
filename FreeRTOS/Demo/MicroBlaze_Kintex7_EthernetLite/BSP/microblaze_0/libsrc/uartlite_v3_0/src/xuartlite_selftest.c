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
/****************************************************************************/
/**
*
* @file xuartlite_selftest.c
*
* This file contains the self-test functions for the UART Lite component
* (XUartLite).
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a ecm  08/31/01 First release
* 1.00b jhl  02/21/02 Repartitioned the driver for smaller files
* 2.00a ktn  10/20/09 Updated to use HAL Processor APIs. The macros have been
*		      renamed to remove _m from the name.
* 3.0 adk 17/12/13  Fixed CR:741186,761863 Reset the FIFO's before reading 
*		      the status register We don't know the status of the Status
* 		      Register in case of if there is more than one uartlite IP
*		      instance in the h/w design.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xuartlite.h"
#include "xuartlite_i.h"
#include "xil_io.h"

/************************** Constant Definitions ****************************/


/**************************** Type Definitions ******************************/


/***************** Macros (Inline Functions) Definitions ********************/


/************************** Variable Definitions ****************************/


/************************** Function Prototypes *****************************/


/****************************************************************************/
/**
*
* Runs a self-test on the device hardware. Since there is no way to perform a
* loopback in the hardware, this test can only check the state of the status
* register to verify it is correct. This test assumes that the hardware
* device is still in its reset state, but has been initialized with the
* Initialize function.
*
* @param	InstancePtr is a pointer to the XUartLite instance.
*
* @return
* 		- XST_SUCCESS if the self-test was successful.
* 		- XST_FAILURE if the self-test failed, the status register
*			value was not correct
*
* @note		None.
*
******************************************************************************/
int XUartLite_SelfTest(XUartLite *InstancePtr)
{
	u32 StatusRegister;

	/*
	 * Assert validates the input arguments
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Reset the FIFO's before reading the status register.
	 * It is likely that the Uartlite IP may not always have an 
	 * empty Tx and Rx FIFO when a selftest is performed if more than one 
	 * uartlite instance is present in the h/w design.
	 */
	 	XUartLite_ResetFifos(InstancePtr);
		
	/*
	 * Read the Status register value to check if it is the correct value
	 * after a reset
	 */
	StatusRegister = XUartLite_ReadReg(InstancePtr->RegBaseAddress,
					XUL_STATUS_REG_OFFSET);

	/*
	 * If the status register is any other value other than
	 * XUL_SR_TX_FIFO_EMPTY then the test is a failure since this is
	 * the not the value after reset
	 */
	if (StatusRegister != XUL_SR_TX_FIFO_EMPTY) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}


