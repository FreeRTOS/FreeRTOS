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
* @file xcanps_selftest.c
*
* This file contains a diagnostic self-test function for the XCanPs driver.
*
* Read xcanps.h file for more information.
*
* @note
* The  Baud Rate Prescaler Register (BRPR) and Bit Timing Register(BTR)
* are setup such that CAN baud rate equals 40Kbps, given the CAN clock
* equal to 24MHz. These need to be changed based on the desired baudrate
* and CAN clock frequency.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- -----  -------- -----------------------------------------------
* 1.00a xd/sv  01/12/10 First release
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xstatus.h"
#include "xcanps.h"

/************************** Constant Definitions ****************************/

#define XCANPS_MAX_FRAME_SIZE_IN_WORDS (XCANPS_MAX_FRAME_SIZE / sizeof(u32))

#define FRAME_DATA_LENGTH	8 /* Frame Data field length */

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/

/*
 * Buffers to hold frames to send and receive. These are declared as global so
 * that they are not on the stack.
 */
static u32 TxFrame[XCANPS_MAX_FRAME_SIZE_IN_WORDS];
static u32 RxFrame[XCANPS_MAX_FRAME_SIZE_IN_WORDS];

/************************** Function Prototypes *****************************/

/*****************************************************************************/
/**
*
* This function runs a self-test on the CAN driver/device. The test resets
* the device, sets up the Loop Back mode, sends a standard frame, receives the
* frame, verifies the contents, and resets the device again.
*
* Note that this is a destructive test in that resets of the device are
* performed. Refer the device specification for the device status after
* the reset operation.
*
*
* @param	InstancePtr is a pointer to the XCanPs instance.
*
* @return
*		- XST_SUCCESS if the self-test passed. i.e., the frame
*		  received via the internal loop back has the same contents as
*		  the frame sent.
* 		- XST_FAILURE   Otherwise.
*
* @note
*
* If the CAN device does not work properly, this function may enter an
* infinite loop and will never return to the caller.
* <br><br>
* If XST_FAILURE is returned, the device is not reset so that the caller could
* have a chance to check reason(s) causing the failure.
*
******************************************************************************/
int XCanPs_SelfTest(XCanPs *InstancePtr)
{
	u8 *FramePtr;
	u32 Status;
	u32 Index;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	XCanPs_Reset(InstancePtr);

	/*
	 * The device should enter Configuration Mode immediately after
	 * reset above is finished. Now check the mode and return error code if
	 * it is not Configuration Mode.
	 */
	if (XCanPs_GetMode(InstancePtr) != XCANPS_MODE_CONFIG) {
		return XST_FAILURE;
	}

	/*
	 * Setup Baud Rate Prescaler Register (BRPR) and Bit Timing Register
	 * (BTR) such that CAN baud rate equals 40Kbps, given the CAN clock
	 * equal to 24MHz. For more information see the CAN 2.0A, CAN 2.0B,
	 * ISO 11898-1 specifications.
	 */
	XCanPs_SetBaudRatePrescaler(InstancePtr, 1);
	XCanPs_SetBitTiming(InstancePtr, 1, 3, 8);

	/*
	 * Enter the loop back mode.
	 */
	XCanPs_EnterMode(InstancePtr, XCANPS_MODE_LOOPBACK);
	while (XCanPs_GetMode(InstancePtr) != XCANPS_MODE_LOOPBACK);

	/*
	 * Create a frame to send with known values so we can verify them
	 * on receive.
	 */
	TxFrame[0] = (u32)XCanPs_CreateIdValue((u32)2000, 0, 0, 0, 0);
	TxFrame[1] = (u32)XCanPs_CreateDlcValue((u32)8);

	FramePtr = (u8 *) (&TxFrame[2]);
	for (Index = 0; Index < 8; Index++) {
		*FramePtr++ = (u8) Index;
	}

	/*
	 * Send the frame.
	 */
	Status = XCanPs_Send(InstancePtr, TxFrame);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/*
	 * Wait until the frame arrives RX FIFO via internal loop back.
	 */
	while (XCanPs_IsRxEmpty(InstancePtr) == TRUE);

	/*
	 * Receive the frame.
	 */
	Status = XCanPs_Recv(InstancePtr, RxFrame);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/*
	 * Verify Identifier and Data Length Code.
	 */
	if (RxFrame[0] !=
		(u32)XCanPs_CreateIdValue((u32)2000, 0, 0, 0, 0)) {
		return XST_FAILURE;
	}

	if ((RxFrame[1] & ~XCANPS_DLCR_TIMESTAMP_MASK) != TxFrame[1]) {
		return XST_FAILURE;
	}


	for (Index = 2; Index < XCANPS_MAX_FRAME_SIZE_IN_WORDS; Index++) {
		if (RxFrame[Index] != TxFrame[Index]) {
			return XST_FAILURE;
		}
	}

	/*
	 * Reset device again before returning to the caller.
	 */
	XCanPs_Reset(InstancePtr);

	return XST_SUCCESS;
}


