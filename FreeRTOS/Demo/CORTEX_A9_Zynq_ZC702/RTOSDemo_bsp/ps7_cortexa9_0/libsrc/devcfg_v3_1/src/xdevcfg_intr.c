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
* @file xdevcfg_intr.c
* @addtogroup devcfg_v3_1
* @{
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
/** @} */
