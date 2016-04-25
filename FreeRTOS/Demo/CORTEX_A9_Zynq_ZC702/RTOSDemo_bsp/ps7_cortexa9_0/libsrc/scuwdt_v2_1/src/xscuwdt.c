/* $Id: xscuwdt.c,v 1.1.2.1 2011/01/20 04:04:40 sadanan Exp $ */
/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xscuwdt.c
* @addtogroup scuwdt_v2_1
* @{
*
* Contains the implementation of interface functions of the XScuWdt driver.
* See xscuwdt.h for a description of the driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a sdm 01/15/10 First release
* 2.1 	sk  02/26/15 Modified the code for MISRA-C:2012 compliance.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xscuwdt.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/****************************************************************************/
/**
*
* Initialize a specific watchdog timer instance/driver. This function
* must be called before other functions of the driver are called.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
* @param	ConfigPtr is the config structure.
* @param	EffectiveAddress is the base address for the device. It could be
*		a virtual address if address translation is supported in the
*		system, otherwise it is the physical address.
*
* @return
*		- XST_SUCCESS if initialization was successful.
*		- XST_DEVICE_IS_STARTED if the device has already been started.
*
* @note		This function enables the watchdog mode.
*
******************************************************************************/
s32 XScuWdt_CfgInitialize(XScuWdt *InstancePtr,
			 XScuWdt_Config *ConfigPtr, u32 EffectiveAddress)
{
	s32 CfgStatus;
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);
	Xil_AssertNonvoid(EffectiveAddress != 0x00U);

	/*
	 * If the device is started, disallow the initialize and return a
	 * status indicating it is started. This allows the user to stop the
	 * device and reinitialize, but prevents a user from inadvertently
	 * initializing.
	 */
	if (InstancePtr->IsStarted == XIL_COMPONENT_IS_STARTED) {
		CfgStatus = (s32)XST_DEVICE_IS_STARTED;
	}
	else {
		/*
		 * Copy configuration into instance.
		 */
		InstancePtr->Config.DeviceId = ConfigPtr->DeviceId;

		/*
		 * Save the base address pointer such that the registers of the block
		 * can be accessed and indicate it has not been started yet.
		 */
		InstancePtr->Config.BaseAddr = EffectiveAddress;
		InstancePtr->IsStarted = 0U;

		/*
		 * Put the watchdog timer in Watchdog mode.
		 */
		XScuWdt_SetWdMode(InstancePtr);

		/*
		 * Indicate the instance is ready to use, successfully initialized.
		 */
		InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

		CfgStatus =(s32)XST_SUCCESS;
	}
	return CfgStatus;
}

/****************************************************************************/
/**
*
* Start the watchdog counter of the device.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
*
* @return	None.
*
* @note		User needs to select the appropriate mode (watchdog/timer)
*		before using this API.
*		See XScuWdt_SetWdMode/XScuWdt_SetTimerMode macros in
*		xscuwdt.h.
*
******************************************************************************/
void XScuWdt_Start(XScuWdt *InstancePtr)
{
	u32 Register;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the contents of the Control register.
	 */
	Register = XScuWdt_ReadReg(InstancePtr->Config.BaseAddr,
				  XSCUWDT_CONTROL_OFFSET);

	/*
	 * Set the 'watchdog enable' bit in the register.
	 */
	Register |= XSCUWDT_CONTROL_WD_ENABLE_MASK;

	/*
	 * Update the Control register with the new value.
	 */
	XScuWdt_WriteReg(InstancePtr->Config.BaseAddr,
			XSCUWDT_CONTROL_OFFSET, Register);

	/*
	 * Indicate that the device is started.
	 */
	InstancePtr->IsStarted = XIL_COMPONENT_IS_STARTED;
}

/****************************************************************************/
/**
*
* Stop the watchdog timer.
*
* @param	InstancePtr is a pointer to the XScuWdt instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XScuWdt_Stop(XScuWdt *InstancePtr)
{
	u32 Register;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the contents of the Control register.
	 */
	Register = XScuWdt_ReadReg(InstancePtr->Config.BaseAddr,
				  XSCUWDT_CONTROL_OFFSET);

	/*
	 * Clear the 'watchdog enable' bit in the register.
	 */
	Register &= (u32)(~XSCUWDT_CONTROL_WD_ENABLE_MASK);

	/*
	 * Update the Control register with the new value.
	 */
	XScuWdt_WriteReg(InstancePtr->Config.BaseAddr,
			XSCUWDT_CONTROL_OFFSET, Register);

	/*
	 * Indicate that the device is stopped.
	 */
	InstancePtr->IsStarted = 0U;
}
/** @} */
