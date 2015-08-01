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
/****************************************************************************/
/**
*
* @file xuartps_selftest.c
*
* This file contains the self-test functions for the XUartPs driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- ------ -------- -----------------------------------------------
* 1.00	drg/jz 01/13/108First Release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xuartps.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/

#define XUARTPS_TOTAL_BYTES 32

/************************** Variable Definitions *****************************/

static u8 TestString[XUARTPS_TOTAL_BYTES]="abcdefghABCDEFGH012345677654321";
static u8 ReturnString[XUARTPS_TOTAL_BYTES];

/************************** Function Prototypes ******************************/


/****************************************************************************/
/**
*
* This function runs a self-test on the driver and hardware device. This self
* test performs a local loopback and verifies data can be sent and received.
*
* The time for this test is proportional to the baud rate that has been set
* prior to calling this function.
*
* The mode and control registers are restored before return.
*
* @param	InstancePtr is a pointer to the XUartPs instance
*
* @return
*		 - XST_SUCCESS if the test was successful
*		- XST_UART_TEST_FAIL if the test failed looping back the data
*
* @note
*
* This function can hang if the hardware is not functioning properly.
*
******************************************************************************/
int XUartPs_SelfTest(XUartPs *InstancePtr)
{
	int Status = XST_SUCCESS;
	u32 IntrRegister;
	u32 ModeRegister;
	u8 Index;

	/*
	 * Assert validates the input arguments
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Disable all interrupts in the interrupt disable register
	 */
	IntrRegister = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
				   XUARTPS_IMR_OFFSET);
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress, XUARTPS_IDR_OFFSET,
		XUARTPS_IXR_MASK);

	/*
	 * Setup for local loopback
	 */
	ModeRegister = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
				   XUARTPS_MR_OFFSET);
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress, XUARTPS_MR_OFFSET,
			   ((ModeRegister & (~XUARTPS_MR_CHMODE_MASK)) |
				XUARTPS_MR_CHMODE_L_LOOP));

	/*
	 * Send a number of bytes and receive them, one at a time.
	 */
	for (Index = 0; Index < XUARTPS_TOTAL_BYTES; Index++) {
		/*
		 * Send out the byte and if it was not sent then the failure
		 * will be caught in the comparison at the end
		 */
		XUartPs_Send(InstancePtr, &TestString[Index], 1);

		/*
		 * Wait until the byte is received. This can hang if the HW
		 * is broken. Watch for the FIFO empty flag to be false.
		 */
		while (!(XUartPs_IsReceiveData(InstancePtr->Config.
						BaseAddress)));

		/*
		 * Receive the byte
		 */
		XUartPs_Recv(InstancePtr, &ReturnString[Index], 1);
	}

	/*
	 * Compare the bytes received to the bytes sent to verify the exact data
	 * was received
	 */
	for (Index = 0; Index < XUARTPS_TOTAL_BYTES; Index++) {
		if (TestString[Index] != ReturnString[Index]) {
			Status = XST_UART_TEST_FAIL;
		}
	}

	/*
	 * Restore the registers which were altered to put into polling and
	 * loopback modes so that this test is not destructive
	 */
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress, XUARTPS_IER_OFFSET,
			   IntrRegister);
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress, XUARTPS_MR_OFFSET,
			   ModeRegister);

	return Status;
}
