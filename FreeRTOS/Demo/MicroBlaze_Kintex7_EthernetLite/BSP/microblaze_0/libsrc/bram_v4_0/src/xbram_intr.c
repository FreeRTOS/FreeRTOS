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
* @file xbram_intr.c
*
* Implements BRAM interrupt processing functions for the
* XBram driver. See xbram.h for more information
* about the driver.
*
* The functions in this file require the hardware device to be built with
* interrupt capabilities. The functions will assert if called using hardware
* that does not have interrupt capabilities.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sa   05/11/10 Initial release
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/
#include "xbram.h"


/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/


/****************************************************************************/
/**
* Enable interrupts. This function will assert if the hardware device has not
* been built with interrupt capabilities.
*
* @param	InstancePtr is the BRAM instance to operate on.
* @param	Mask is the mask to enable. Bit positions of 1 are enabled.
*		This mask is formed by OR'ing bits from XBRAM_IR*
*		bits which are contained in xbram_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XBram_InterruptEnable(XBram *InstancePtr, u32 Mask)
{
	u32 Register;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Config.CtrlBaseAddress != 0);

	/*
	 * Read the interrupt enable register and only enable the specified
	 * interrupts without disabling or enabling any others.
	 */
	Register = XBram_ReadReg(InstancePtr->Config.CtrlBaseAddress,
					XBRAM_ECC_EN_IRQ_OFFSET);
	XBram_WriteReg(InstancePtr->Config.CtrlBaseAddress,
					XBRAM_ECC_EN_IRQ_OFFSET,
					Register | Mask);
}


/****************************************************************************/
/**
* Disable interrupts. This function allows each specific interrupt to be
* disabled. This function will assert if the hardware device has not been
* built with interrupt capabilities.
*
* @param	InstancePtr is the BRAM instance to operate on.
* @param 	Mask is the mask to disable. Bits set to 1 are disabled. This
*		mask is formed by OR'ing bits from XBRAM_IR* bits
*		which are contained in xbram_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XBram_InterruptDisable(XBram *InstancePtr, u32 Mask)
{
	u32 Register;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Config.CtrlBaseAddress != 0);

	/*
	 * Read the interrupt enable register and only disable the specified
	 * interrupts without enabling or disabling any others.
	 */
	Register = XBram_ReadReg(InstancePtr->Config.CtrlBaseAddress,
					XBRAM_ECC_EN_IRQ_OFFSET);
	XBram_WriteReg(InstancePtr->Config.CtrlBaseAddress,
				XBRAM_ECC_EN_IRQ_OFFSET,
				Register & (~Mask));
}

/****************************************************************************/
/**
* Clear pending interrupts with the provided mask. This function should be
* called after the software has serviced the interrupts that are pending.
* This function will assert if the hardware device has not been built with
* interrupt capabilities.
*
* @param 	InstancePtr is the BRAM instance to operate on.
* @param 	Mask is the mask to clear pending interrupts for. Bit positions
*		of 1 are cleared. This mask is formed by OR'ing bits from
*		XBRAM_IR* bits which are contained in
*		xbram_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XBram_InterruptClear(XBram *InstancePtr, u32 Mask)
{
	u32 Register;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Config.CtrlBaseAddress != 0);

	/*
	 * Read the interrupt status register and only clear the interrupts
	 * that are specified without affecting any others.  Since the register
	 * is a toggle on write, make sure any bits to be written are already
	 * set.
	 */
	Register = XBram_ReadReg(InstancePtr->Config.CtrlBaseAddress,
					XBRAM_ECC_STATUS_OFFSET);
	XBram_WriteReg(InstancePtr->Config.CtrlBaseAddress,
				XBRAM_ECC_STATUS_OFFSET,
				Register & Mask);


}


/****************************************************************************/
/**
* Returns the interrupt enable mask. This function will assert if the
* hardware device has not been built with interrupt capabilities.
*
* @param	InstancePtr is the BRAM instance to operate on.
*
* @return	A mask of bits made from XBRAM_IR* bits which
*		are contained in xbram_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
u32 XBram_InterruptGetEnabled(XBram * InstancePtr)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Config.CtrlBaseAddress != 0);

	return XBram_ReadReg(InstancePtr->Config.CtrlBaseAddress,
				XBRAM_ECC_EN_IRQ_OFFSET);
}


/****************************************************************************/
/**
* Returns the status of interrupt signals. Any bit in the mask set to 1
* indicates that the channel associated with the bit has asserted an interrupt
* condition. This function will assert if the hardware device has not been
* built with interrupt capabilities.
*
* @param	InstancePtr is the BRAM instance to operate on.
*
* @return	A pointer to a mask of bits made from XBRAM_IR*
*		bits which are contained in xbram_hw.h.
*
* @note
*
* The interrupt status indicates the status of the device irregardless if
* the interrupts from the devices have been enabled or not through
* XBram_InterruptEnable().
*
*****************************************************************************/
u32 XBram_InterruptGetStatus(XBram * InstancePtr)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Config.CtrlBaseAddress != 0);

	return XBram_ReadReg(InstancePtr->Config.CtrlBaseAddress,
				XBRAM_ECC_EN_IRQ_OFFSET);
}
