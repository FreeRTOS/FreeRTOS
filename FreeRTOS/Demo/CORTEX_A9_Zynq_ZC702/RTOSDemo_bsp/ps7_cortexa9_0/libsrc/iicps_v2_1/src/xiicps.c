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
* @file xiicps.c
*
* Contains implementation of required functions for the XIicPs driver.
* See xiicps.h for detailed description of the device and driver.
*
* <pre> MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- --------------------------------------------
* 1.00a drg/jz  01/30/10 First release
* 1.00a sdm     09/21/11 Updated the InstancePtr->Options in the
*			 XIicPs_CfgInitialize by calling XIicPs_GetOptions.
* 2.1   hk      04/25/14 Explicitly reset CR and clear FIFO in Abort function
*                        and state the same in the comments. CR# 784254.
*                        Fix for CR# 761060 - provision for repeated start.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xiicps.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

static void StubHandler(void *CallBackRef, u32 StatusEvent);

/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Initializes a specific XIicPs instance such that the driver is ready to use.
*
* The state of the device after initialization is:
*   - Device is disabled
*   - Slave mode
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	ConfigPtr is a reference to a structure containing information
*		about a specific IIC device. This function initializes an
*		InstancePtr object for a specific device specified by the
*		contents of Config.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. The caller is responsible for keeping the address
*		mapping from EffectiveAddr to the device physical base address
*		unchanged once this function is invoked. Unexpected errors may
*		occur if the address mapping changes after this function is
*		called. If address translation is not used, use
*		ConfigPtr->BaseAddress for this parameter, passing the physical
*		address instead.
*
* @return	The return value is XST_SUCCESS if successful.
*
* @note		None.
*
******************************************************************************/
int XIicPs_CfgInitialize(XIicPs *InstancePtr, XIicPs_Config *ConfigPtr,
				  u32 EffectiveAddr)
{
	/*
	 * Assert validates the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/*
	 * Set some default values.
	 */
	InstancePtr->Config.DeviceId = ConfigPtr->DeviceId;
	InstancePtr->Config.BaseAddress = EffectiveAddr;
	InstancePtr->Config.InputClockHz = ConfigPtr->InputClockHz;
	InstancePtr->StatusHandler = StubHandler;
	InstancePtr->CallBackRef = NULL;

	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	/*
	 * Reset the IIC device to get it into its initial state. It is expected
	 * that device configuration will take place after this initialization
	 * is done, but before the device is started.
	 */
	XIicPs_Reset(InstancePtr);

	/*
	 * Keep a copy of what options this instance has.
	 */
	InstancePtr->Options = XIicPs_GetOptions(InstancePtr);

	/* Initialize repeated start flag to 0 */
	InstancePtr->IsRepeatedStart = 0;

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* Check whether the I2C bus is busy
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return
* 		- TRUE if the bus is busy.
*		- FALSE if the bus is not busy.
*
* @note		None.
*
******************************************************************************/
int XIicPs_BusIsBusy(XIicPs *InstancePtr)
{
	u32 StatusReg;

	StatusReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
					   XIICPS_SR_OFFSET);
	if (StatusReg & XIICPS_SR_BA_MASK) {
		return TRUE;
	}else {
		return FALSE;
	}
}

/*****************************************************************************/
/**
*
* This is a stub for the status callback. The stub is here in case the upper
* layers forget to set the handler.
*
* @param	CallBackRef is a pointer to the upper layer callback reference.
* @param	StatusEvent is the event that just occurred.
* @param	ByteCount is the number of bytes transferred up until the event
*		occurred.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void StubHandler(void *CallBackRef, u32 StatusEvent)
{
	(void) CallBackRef;
	(void) StatusEvent;
	Xil_AssertVoidAlways();
}


/*****************************************************************************/
/**
*
* Aborts a transfer in progress by resetting the FIFOs. The byte counts are
* cleared.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XIicPs_Abort(XIicPs *InstancePtr)
{
	u32 IntrMaskReg;
	u32 IntrStatusReg;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Enter a critical section, so disable the interrupts while we clear
	 * the FIFO and the status register.
	 */
	IntrMaskReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
					   XIICPS_IMR_OFFSET);
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XIICPS_IDR_OFFSET, XIICPS_IXR_ALL_INTR_MASK);

	/*
	 * Reset the settings in config register and clear the FIFOs.
	 */
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress, XIICPS_CR_OFFSET,
			  XIICPS_CR_RESET_VALUE | XIICPS_CR_CLR_FIFO_MASK);

	/*
	 * Read, then write the interrupt status to make sure there are no
	 * pending interrupts.
	 */
	IntrStatusReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
					 XIICPS_ISR_OFFSET);
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XIICPS_ISR_OFFSET, IntrStatusReg);

	/*
	 * Restore the interrupt state.
	 */
	IntrMaskReg = XIICPS_IXR_ALL_INTR_MASK & (~IntrMaskReg);
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XIICPS_IER_OFFSET, IntrMaskReg);

}

/*****************************************************************************/
/**
*
* Resets the IIC device. Reset must only be called after the driver has been
* initialized. The configuration of the device after reset is the same as its
* configuration after initialization.  Any data transfer that is in progress is
* aborted.
*
* The upper layer software is responsible for re-configuring (if necessary)
* and reenabling interrupts for the IIC device after the reset.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XIicPs_Reset(XIicPs *InstancePtr)
{

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Abort any transfer that is in progress.
	 */
	XIicPs_Abort(InstancePtr);

	/*
	 * Reset any values so the software state matches the hardware device.
	 */
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress, XIICPS_CR_OFFSET,
			  XIICPS_CR_RESET_VALUE);
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XIICPS_TIME_OUT_OFFSET, XIICPS_TO_RESET_VALUE);
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress, XIICPS_IDR_OFFSET,
			  XIICPS_IXR_ALL_INTR_MASK);

}
/*****************************************************************************/
/**
* Put more data into the transmit FIFO, number of bytes is ether expected
* number of bytes for this transfer or available space in FIFO, which ever
* is less.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return	Number of bytes left for this instance.
*
* @note		This is function is shared by master and slave.
*
******************************************************************************/
int TransmitFifoFill(XIicPs *InstancePtr)
{
	u8 AvailBytes;
	int LoopCnt;
	int NumBytesToSend;

	/*
	 * Determine number of bytes to write to FIFO.
	 */
	AvailBytes = XIICPS_FIFO_DEPTH -
		XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
					   XIICPS_TRANS_SIZE_OFFSET);

	if (InstancePtr->SendByteCount > AvailBytes) {
		NumBytesToSend = AvailBytes;
	} else {
		NumBytesToSend = InstancePtr->SendByteCount;
	}

	/*
	 * Fill FIFO with amount determined above.
	 */
	for (LoopCnt = 0; LoopCnt < NumBytesToSend; LoopCnt++) {
		XIicPs_SendByte(InstancePtr);
	}

	return InstancePtr->SendByteCount;
}
