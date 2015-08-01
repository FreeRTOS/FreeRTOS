/******************************************************************************
*
* Copyright (C) 2011 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xadcps_intr.c
*
* This file contains interrupt handling API functions of the XADC
* device.
*
* The device must be configured at hardware build time to support interrupt
* for all the functions in this file to work.
*
* Refer to xadcps.h header file and device specification for more information.
*
* @note
*
* Calling the interrupt functions without including the interrupt component will
* result in asserts if asserts are enabled, and will result in a unpredictable
* behavior if the asserts are not enabled.
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.00a ssb    12/22/11 First release based on the XPS/AXI xadc driver
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xadcps.h"

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
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Mask is the bit-mask of the interrupts to be enabled.
*		Bit positions of 1 will be enabled. Bit positions of 0 will
*		keep the previous setting. This mask is formed by OR'ing
*		XADCPS_INTX_* bits defined in xadcps_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_IntrEnable(XAdcPs *InstancePtr, u32 Mask)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Disable the specified interrupts in the IPIER.
	 */
	RegValue = XAdcPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XADCPS_INT_MASK_OFFSET);
	RegValue &= ~(Mask & XADCPS_INTX_ALL_MASK);
	XAdcPs_WriteReg(InstancePtr->Config.BaseAddress,
				XADCPS_INT_MASK_OFFSET,
			  	RegValue);
}


/****************************************************************************/
/**
*
* This function disables the specified interrupts in the device.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Mask is the bit-mask of the interrupts to be disabled.
*		Bit positions of 1 will be disabled. Bit positions of 0 will
*		keep the previous setting. This mask is formed by OR'ing
*		XADCPS_INTX_* bits defined in xadcps_hw.h.
*
* @return	None.
*
* @note		None
*
*****************************************************************************/
void XAdcPs_IntrDisable(XAdcPs *InstancePtr, u32 Mask)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Enable the specified interrupts in the IPIER.
	 */
	RegValue = XAdcPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XADCPS_INT_MASK_OFFSET);
	RegValue |= (Mask & XADCPS_INTX_ALL_MASK);
	XAdcPs_WriteReg(InstancePtr->Config.BaseAddress,
				XADCPS_INT_MASK_OFFSET,
			  	RegValue);
}
/****************************************************************************/
/**
*
* This function returns the enabled interrupts read from the Interrupt Mask
* Register (IPIER). Use the XADCPS_IPIXR_* constants defined in xadcps_hw.h to
* interpret the returned value.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	A 32-bit value representing the contents of the I.
*
* @note		None.
*
*****************************************************************************/
u32 XAdcPs_IntrGetEnabled(XAdcPs *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Return the value read from the Interrupt Enable Register.
	 */
	return (~ XAdcPs_ReadReg(InstancePtr->Config.BaseAddress,
				XADCPS_INT_MASK_OFFSET) & XADCPS_INTX_ALL_MASK);
}

/****************************************************************************/
/**
*
* This function returns the interrupt status read from Interrupt Status
* Register(IPISR). Use the XADCPS_IPIXR_* constants defined in xadcps_hw.h
* to interpret the returned value.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	A 32-bit value representing the contents of the IPISR.
*
* @note		The device must be configured at hardware build time to include
*		interrupt component for this function to work.
*
*****************************************************************************/
u32 XAdcPs_IntrGetStatus(XAdcPs *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Return the value read from the Interrupt Status register.
	 */
	return XAdcPs_ReadReg(InstancePtr->Config.BaseAddress,
				XADCPS_INT_STS_OFFSET) & XADCPS_INTX_ALL_MASK;
}

/****************************************************************************/
/**
*
* This function clears the specified interrupts in the Interrupt Status
* Register (IPISR).
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Mask is the bit-mask of the interrupts to be cleared.
*		Bit positions of 1 will be cleared. Bit positions of 0 will not
* 		change the previous interrupt status. This mask is formed by
* 		OR'ing XADCPS_IPIXR_* bits which are defined in xadcps_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_IntrClear(XAdcPs *InstancePtr, u32 Mask)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Clear the specified interrupts in the Interrupt Status register.
	 */
	RegValue = XAdcPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XADCPS_INT_STS_OFFSET);
	RegValue &= (Mask & XADCPS_INTX_ALL_MASK);
	XAdcPs_WriteReg(InstancePtr->Config.BaseAddress, XADCPS_INT_STS_OFFSET,
			  RegValue);

}
