/******************************************************************************
*
* (c) Copyright 2010-12 Xilinx, Inc. All rights reserved.
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

/****************************************************************************/
/**
*
* @file xscutimer.c
*
* Contains the implementation of interface functions of the SCU Timer driver.
* See xscutimer.h for a description of the driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a nm  03/10/10 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xscutimer.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/****************************************************************************/
/**
*
* Initialize a specific timer instance/driver. This function  must be called
* before other functions of the driver are called.
*
* @param	InstancePtr is a pointer to the XScuTimer instance.
* @param	ConfigPtr points to the XScuTimer configuration structure.
* @param	EffectiveAddress is the base address for the device. It could be
*		a virtual address if address translation is supported in the
*		system, otherwise it is the physical address.
*
* @return
*		- XST_SUCCESS if initialization was successful.
*		- XST_DEVICE_IS_STARTED if the device has already been started.
*
* @note		None.
*
******************************************************************************/
int XScuTimer_CfgInitialize(XScuTimer *InstancePtr,
			 XScuTimer_Config *ConfigPtr, u32 EffectiveAddress)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/*
	 * If the device is started, disallow the initialize and return a
	 * status indicating it is started. This allows the user to stop the
	 * device and reinitialize, but prevents a user from inadvertently
	 * initializing.
	 */
	if (InstancePtr->IsStarted == XIL_COMPONENT_IS_STARTED) {
		return XST_DEVICE_IS_STARTED;
	}

	/*
	 * Copy configuration into the instance structure.
	 */
	InstancePtr->Config.DeviceId = ConfigPtr->DeviceId;

	/*
	 * Save the base address pointer such that the registers of the block
	 * can be accessed and indicate it has not been started yet.
	 */
	InstancePtr->Config.BaseAddr = EffectiveAddress;

	InstancePtr->IsStarted = 0;

	/*
	 * Indicate the instance is ready to use, successfully initialized.
	 */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* Start the timer.
*
* @param	InstancePtr is a pointer to the XScuTimer instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XScuTimer_Start(XScuTimer *InstancePtr)
{
	u32 Register;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the contents of the Control register.
	 */
	Register = XScuTimer_ReadReg(InstancePtr->Config.BaseAddr,
				  XSCUTIMER_CONTROL_OFFSET);

	/*
	 * Set the 'timer enable' bit in the register.
	 */
	Register |= XSCUTIMER_CONTROL_ENABLE_MASK;

	/*
	 * Update the Control register with the new value.
	 */
	XScuTimer_WriteReg(InstancePtr->Config.BaseAddr,
			XSCUTIMER_CONTROL_OFFSET, Register);

	/*
	 * Indicate that the device is started.
	 */
	InstancePtr->IsStarted = XIL_COMPONENT_IS_STARTED;
}

/****************************************************************************/
/**
*
* Stop the timer.
*
* @param	InstancePtr is a pointer to the XScuTimer instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XScuTimer_Stop(XScuTimer *InstancePtr)
{
	u32 Register;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the contents of the Control register.
	 */
	Register = XScuTimer_ReadReg(InstancePtr->Config.BaseAddr,
				  XSCUTIMER_CONTROL_OFFSET);

	/*
	 * Clear the 'timer enable' bit in the register.
	 */
	Register &= ~XSCUTIMER_CONTROL_ENABLE_MASK;

	/*
	 * Update the Control register with the new value.
	 */
	XScuTimer_WriteReg(InstancePtr->Config.BaseAddr,
			XSCUTIMER_CONTROL_OFFSET, Register);

	/*
	 * Indicate that the device is stopped.
	 */
	InstancePtr->IsStarted = 0;
}

/*****************************************************************************/
/**
*
* This function sets the prescaler bits in the timer control register.
*
* @param	InstancePtr is a pointer to the XScuTimer instance.
* @param	PrescalerValue is a 8 bit value that sets the prescaler to use.
*
* @return	None
*
* @note		None
*
****************************************************************************/
void XScuTimer_SetPrescaler(XScuTimer *InstancePtr, u8 PrescalerValue)
{
	u32 ControlReg;

	/*
	 * Assert to validate input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	/*
	 * Read the Timer control register.
	 */
	ControlReg = XScuTimer_ReadReg(InstancePtr->Config.BaseAddr,
					XSCUTIMER_CONTROL_OFFSET);

	/*
	 * Clear all of the prescaler control bits in the register.
	 */
	ControlReg &= ~XSCUTIMER_CONTROL_PRESCALER_MASK;

	/*
	 * Set the prescaler value.
	 */
	ControlReg |= (PrescalerValue << XSCUTIMER_CONTROL_PRESCALER_SHIFT);

	/*
	 * Write the register with the new values.
	 */
	XScuTimer_WriteReg(InstancePtr->Config.BaseAddr,
			  XSCUTIMER_CONTROL_OFFSET, ControlReg);
}

/*****************************************************************************/
/**
*
* This function returns the current prescaler value.
*
* @param	InstancePtr is a pointer to the XScuTimer instance.
*
* @return	The prescaler value.
*
* @note		None.
*
****************************************************************************/
u8 XScuTimer_GetPrescaler(XScuTimer *InstancePtr)
{
	u32 ControlReg;

	/*
	 * Assert to validate input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Timer control register.
	 */
	ControlReg = XScuTimer_ReadReg(InstancePtr->Config.BaseAddr,
				    XSCUTIMER_CONTROL_OFFSET);
	ControlReg &= XSCUTIMER_CONTROL_PRESCALER_MASK;

	return (ControlReg >> XSCUTIMER_CONTROL_PRESCALER_SHIFT);
}
