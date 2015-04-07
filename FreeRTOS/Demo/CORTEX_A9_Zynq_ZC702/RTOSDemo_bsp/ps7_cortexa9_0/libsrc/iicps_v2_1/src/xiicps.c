/******************************************************************************
*
* (c) Copyright 2010-14 Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
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
