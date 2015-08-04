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
*
* @file xintc_selftest.c
*
* Contains diagnostic self-test functions for the XIntc component. This file
* requires other files of the component to be linked in also.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00b jhl  02/21/02 First release
* 1.10c mta  03/21/07 Updated to new coding style
* 2.00a ktn  10/20/09 Updated to use HAL Processor APIs
* 2.04a bss  01/16/12 Removed CurrentMIE variable and reading of the
*                     MER register to remove warnings
* 2.06a bss  01/28/13 To support Cascade mode:
*		      Modified XIntc_SimulateIntr API.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xintc.h"
#include "xintc_i.h"

/************************** Constant Definitions *****************************/

#define XIN_TEST_MASK 1

/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Run a self-test on the driver/device. This is a destructive test.
*
* This involves forcing interrupts into the controller and verifying that they
* are recognized and can be acknowledged. This test will not succeed if the
* interrupt controller has been started in real mode such that interrupts
* cannot be forced.
*
* @param	InstancePtr is a pointer to the XIntc instance to be worked on.
*
* @return
* 		- XST_SUCCESS if self-test is successful.
* 		- XST_INTC_FAIL_SELFTEST if the Interrupt controller fails the
*		self-test. It will fail the self test if the device has
*		previously been started in real mode.
*
* @note		None.
*
******************************************************************************/
int XIntc_SelfTest(XIntc * InstancePtr)
{
	u32 CurrentISR;
	u32 Temp;

	/*
	 * Assert the arguments
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	/*
	 * Acknowledge all pending interrupts by reading the interrupt status
	 * register and writing the value to the acknowledge register
	 */
	Temp = XIntc_In32(InstancePtr->BaseAddress + XIN_ISR_OFFSET);

	XIntc_Out32(InstancePtr->BaseAddress + XIN_IAR_OFFSET, Temp);

	/*
	 * Verify that there are no interrupts by reading the interrupt status
	 */
	CurrentISR = XIntc_In32(InstancePtr->BaseAddress + XIN_ISR_OFFSET);

	/*
	 * ISR should be zero after all interrupts are acknowledged
	 */
	if (CurrentISR != 0) {
		return XST_INTC_FAIL_SELFTEST;
	}

	/*
	 * Set a bit in the ISR which simulates an interrupt
	 */
	XIntc_Out32(InstancePtr->BaseAddress + XIN_ISR_OFFSET, XIN_TEST_MASK);

	/*
	 * Verify that it was set
	 */
	CurrentISR = XIntc_In32(InstancePtr->BaseAddress + XIN_ISR_OFFSET);

	if (CurrentISR != XIN_TEST_MASK) {
		return XST_INTC_FAIL_SELFTEST;
	}

	/*
	 * Acknowledge the interrupt
	 */
	XIntc_Out32(InstancePtr->BaseAddress + XIN_IAR_OFFSET, XIN_TEST_MASK);

	/*
	 * Read back the ISR to verify that the interrupt is gone
	 */
	CurrentISR = XIntc_In32(InstancePtr->BaseAddress + XIN_ISR_OFFSET);

	if (CurrentISR != 0) {
		return XST_INTC_FAIL_SELFTEST;
	}

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* Allows software to simulate an interrupt in the interrupt controller. This
* function will only be successful when the interrupt controller has been
* started in simulation mode. Once it has been started in real mode,
* interrupts cannot be simulated. A simulated interrupt allows the interrupt
* controller to be tested without any device to drive an interrupt input
* signal into it. In Cascade mode writes to ISR of appropraite Slave
* controller depending on Id.
*
* @param	InstancePtr is a pointer to the XIntc instance to be worked on.
* @param	Id is the interrupt ID for which to simulate an interrupt.
*
* @return
* 		- XST_SUCCESS if successful
*		- XST_FAILURE if the interrupt could not be
* 		simulated because the interrupt controller is or
*		has previously been in real mode.
*
* @note		None.
*
******************************************************************************/
int XIntc_SimulateIntr(XIntc * InstancePtr, u8 Id)
{
	u32 Mask;
	u32 MasterEnable;
	XIntc_Config *CfgPtr;
	int Index;
	int DeviceId;

	/*
	 * Assert the arguments
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(Id < XPAR_INTC_MAX_NUM_INTR_INPUTS);


	/* Get the contents of the master enable register and determine if
	 * hardware interrupts have already been enabled, if so, this is a write
	 * once bit such that simulation can't be done at this point because
	 * the ISR register is no longer writable by software
	 */
	MasterEnable = XIntc_In32(InstancePtr->BaseAddress + XIN_MER_OFFSET);
	if (MasterEnable & XIN_INT_HARDWARE_ENABLE_MASK) {
		return XST_FAILURE;
	}


	if (Id > 31) {

		DeviceId = Id/32;

		CfgPtr = XIntc_LookupConfig(Id/32);
		Mask = XIntc_BitPosMask[Id%32];
		XIntc_Out32(CfgPtr->BaseAddress + XIN_ISR_OFFSET, Mask);

		/* Generate interrupt for 31 by writing to Interrupt Status
		 * register of parent controllers. Primary controller ISR
		 * will be written last in the loop
		 */
		Mask = XIntc_BitPosMask[31];
		for (Index = DeviceId - 1; Index >= 0; Index--)
		{
			CfgPtr = XIntc_LookupConfig(Index);

			XIntc_Out32(CfgPtr->BaseAddress + XIN_ISR_OFFSET,
									Mask);
		}
	}
	else {
		/*
		 * The Id is used to create the appropriate mask for the
		 * desired bit position.
		 */
		Mask = XIntc_BitPosMask[Id];

		/*
		 * Enable the selected interrupt source by reading the interrupt
		 * enable register and then modifying only the specified
		 * interrupt id enable
		 */
		XIntc_Out32(InstancePtr->BaseAddress + XIN_ISR_OFFSET, Mask);

	}
	/* indicate the interrupt was successfully simulated */

	return XST_SUCCESS;
}
