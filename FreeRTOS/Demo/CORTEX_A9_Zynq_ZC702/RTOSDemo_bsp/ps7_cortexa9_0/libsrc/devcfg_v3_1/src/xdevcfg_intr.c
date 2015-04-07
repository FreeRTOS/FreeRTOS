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
/****************************************************************************/
/**
*
* @file xdevcfg_intr.c
*
* Contains the implementation of interrupt related functions of the XDcfg
* driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a hvm 02/07/11 First release
* 2.01a nm  07/07/12 Updated the XDcfg_IntrClear function to directly
*		     set the mask instead of oring it with the
*		     value read from the interrupt status register
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xdevcfg.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/****************************************************************************/
/**
*
* This function enables the specified interrupts in the device.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	Mask is the bit-mask of the interrupts to be enabled.
*		Bit positions of 1 will be enabled. Bit positions of 0 will
*		keep the previous setting. This mask is formed by OR'ing
*		XDCFG_INT_* bits defined in xdevcfg_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XDcfg_IntrEnable(XDcfg *InstancePtr, u32 Mask)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Enable the specified interrupts in the Interrupt Mask Register.
	 */
	RegValue = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
				    XDCFG_INT_MASK_OFFSET);
	RegValue &= ~(Mask & XDCFG_IXR_ALL_MASK);
	XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
				XDCFG_INT_MASK_OFFSET,
			  	RegValue);
}


/****************************************************************************/
/**
*
* This function disables the specified interrupts in the device.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	Mask is the bit-mask of the interrupts to be disabled.
*		Bit positions of 1 will be disabled. Bit positions of 0 will
*		keep the previous setting. This mask is formed by OR'ing
*		XDCFG_INT_* bits defined in xdevcfg_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XDcfg_IntrDisable(XDcfg *InstancePtr, u32 Mask)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Disable the specified interrupts in the Interrupt Mask Register.
	 */
	RegValue = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
				    XDCFG_INT_MASK_OFFSET);
	RegValue |= (Mask & XDCFG_IXR_ALL_MASK);
	XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
				XDCFG_INT_MASK_OFFSET,
			  	RegValue);
}
/****************************************************************************/
/**
*
* This function returns the enabled interrupts read from the Interrupt Mask
* Register. Use the XDCFG_INT_* constants defined in xdevcfg_hw.h
* to interpret the returned value.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	A 32-bit value representing the contents of the IMR.
*
* @note		None.
*
*****************************************************************************/
u32 XDcfg_IntrGetEnabled(XDcfg *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Return the value read from the Interrupt Mask Register.
	 */
	return (~ XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
				XDCFG_INT_MASK_OFFSET));
}

/****************************************************************************/
/**
*
* This function returns the interrupt status read from Interrupt Status
* Register. Use the XDCFG_INT_* constants defined in xdevcfg_hw.h
* to interpret the returned value.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	A 32-bit value representing the contents of the Interrupt
*		Status register.
*
* @note		None.
*
*****************************************************************************/
u32 XDcfg_IntrGetStatus(XDcfg *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Return the value read from the Interrupt Status register.
	 */
	return XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
				XDCFG_INT_STS_OFFSET);
}

/****************************************************************************/
/**
*
* This function clears the specified interrupts in the Interrupt Status
* Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	Mask is the bit-mask of the interrupts to be cleared.
*		Bit positions of 1 will be cleared. Bit positions of 0 will not
* 		change the previous interrupt status. This mask is formed by
* 		OR'ing XDCFG_INT_* bits which are defined in xdevcfg_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XDcfg_IntrClear(XDcfg *InstancePtr, u32 Mask)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
				XDCFG_INT_STS_OFFSET,
			  	Mask);

}

/*****************************************************************************/
/**
* The interrupt handler for the Device Config Interface.
*
* Events are signaled to upper layer for proper handling.
*
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	None.
*
* @note 	None.
*
****************************************************************************/
void XDcfg_InterruptHandler(XDcfg *InstancePtr)
{
	u32 IntrStatusReg;

	/*
	 * Assert validates the input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Interrupt status register.
	 */
	IntrStatusReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
					 XDCFG_INT_STS_OFFSET);

	/*
	 * Write the status back to clear the interrupts so that no
	 * subsequent interrupts are missed while processing this interrupt.
	 * This also does the DMA acknowledgment automatically.
	 */
	XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
				XDCFG_INT_STS_OFFSET, IntrStatusReg);

	/*
	 * Signal application that there are events to handle.
	 */
	InstancePtr->StatusHandler(InstancePtr->CallBackRef,
					   IntrStatusReg);

}

/****************************************************************************/
/**
*
* This function sets the handler that will be called when an event (interrupt)
* occurs that needs application's attention.
*
* @param	InstancePtr is a pointer to the XDcfg instance
* @param	CallBackFunc is the address of the callback function.
* @param	CallBackRef is a user data item that will be passed to the
*		callback function when it is invoked.
*
* @return	None.
*
* @note		None.
*
*
*****************************************************************************/
void XDcfg_SetHandler(XDcfg *InstancePtr, void *CallBackFunc,
				void *CallBackRef)
{
	/*
	 * Asserts validate the input arguments
	 * CallBackRef not checked, no way to know what is valid
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(CallBackFunc != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->StatusHandler = (XDcfg_IntrHandler) CallBackFunc;
	InstancePtr->CallBackRef = CallBackRef;
}
