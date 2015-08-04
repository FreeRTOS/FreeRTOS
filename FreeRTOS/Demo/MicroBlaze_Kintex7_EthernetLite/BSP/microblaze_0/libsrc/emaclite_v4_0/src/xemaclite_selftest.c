/******************************************************************************
*
* Copyright (C) 2004 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xemaclite_selftest.c
*
* Function(s) in this file are the required functions for the EMAC Lite
* driver sefftest for the hardware.
* See xemaclite.h for a detailed description of the driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- --------------------------------------------------------
* 1.01a ecm  01/31/04 First release
* 1.11a mta  03/21/07 Updated to new coding style
* 3.00a ktn  10/22/09 Updated driver to use the HAL Processor APIs/macros.
* </pre>
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_io.h"
#include "xemaclite.h"
#include "xemaclite_i.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/*****************************************************************************/
/**
*
* Performs a SelfTest on the EmacLite device as follows:
*   - Writes to the mandatory TX buffer and reads back to verify.
*   - If configured, writes to the secondary TX buffer and reads back to verify.
*   - Writes to the mandatory RX buffer and reads back to verify.
*   - If configured, writes to the secondary RX buffer and reads back to verify.
*
*
* @param	InstancePtr is a pointer to the XEmacLite instance .
*
* @return
*		- XST_SUCCESS if the device Passed the Self Test.
* 		- XST_FAILURE if any of the data read backs fail.
*
* @note		None.
*
******************************************************************************/
int XEmacLite_SelfTest(XEmacLite * InstancePtr)
{
	u32 BaseAddress;
	u8 Index;
	u8 TestString[4] = { 0xDE, 0xAD, 0xBE, 0xEF };
	u8 ReturnString[4] = { 0x0, 0x0, 0x0, 0x0 };

	/*
	 * Verify that each of the inputs are valid.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);

	/*
	 * Determine the TX buffer address
	 */
	BaseAddress = InstancePtr->EmacLiteConfig.BaseAddress +
			XEL_TXBUFF_OFFSET;

	/*
	 * Write the TestString to the TX buffer in EMAC Lite then
	 * back from the EMAC Lite and verify
	 */
	XEmacLite_AlignedWrite(TestString, (u32 *) BaseAddress,
			       sizeof(TestString));
	XEmacLite_AlignedRead((u32 *) BaseAddress, ReturnString,
			      sizeof(ReturnString));

	for (Index = 0; Index < 4; Index++) {

		if (ReturnString[Index] != TestString[Index]) {
			return XST_FAILURE;
		}

		/*
		 * Zero the return string for the next test
		 */
		ReturnString[Index] = 0;
	}

	/*
	 * If the second buffer is configured, test it also
	 */
	if (InstancePtr->EmacLiteConfig.TxPingPong != 0) {
		BaseAddress += XEL_BUFFER_OFFSET;
		/*
		 * Write the TestString to the optional TX buffer in EMAC Lite
		 * then back from the EMAC Lite and verify
		 */
		XEmacLite_AlignedWrite(TestString, (u32 *) BaseAddress,
				       sizeof(TestString));
		XEmacLite_AlignedRead((u32 *) BaseAddress, ReturnString,
				      sizeof(ReturnString));

		for (Index = 0; Index < 4; Index++) {

			if (ReturnString[Index] != TestString[Index]) {
				return XST_FAILURE;
			}

			/*
			 * Zero the return string for the next test
			 */
			ReturnString[Index] = 0;
		}
	}

	/*
	 * Determine the RX buffer address
	 */
	BaseAddress = InstancePtr->EmacLiteConfig.BaseAddress +
				XEL_RXBUFF_OFFSET;

	/*
	 * Write the TestString to the RX buffer in EMAC Lite then
	 * back from the EMAC Lite and verify
	 */
	XEmacLite_AlignedWrite(TestString, (u32 *) (BaseAddress),
			       sizeof(TestString));
	XEmacLite_AlignedRead((u32 *) (BaseAddress), ReturnString,
			      sizeof(ReturnString));

	for (Index = 0; Index < 4; Index++) {

		if (ReturnString[Index] != TestString[Index]) {
			return XST_FAILURE;
		}

		/*
		 * Zero the return string for the next test
		 */
		ReturnString[Index] = 0;
	}

	/*
	 * If the second buffer is configured, test it also
	 */
	if (InstancePtr->EmacLiteConfig.RxPingPong != 0) {
		BaseAddress += XEL_BUFFER_OFFSET;
		/*
		 * Write the TestString to the optional RX buffer in EMAC Lite
		 * then back from the EMAC Lite and verify
		 */
		XEmacLite_AlignedWrite(TestString, (u32 *) BaseAddress,
				       sizeof(TestString));
		XEmacLite_AlignedRead((u32 *) BaseAddress, ReturnString,
				      sizeof(ReturnString));

		for (Index = 0; Index < 4; Index++) {

			if (ReturnString[Index] != TestString[Index]) {
				return XST_FAILURE;
			}

			/*
			 * Zero the return string for the next test
			 */
			ReturnString[Index] = 0;
		}
	}

	return XST_SUCCESS;
}
