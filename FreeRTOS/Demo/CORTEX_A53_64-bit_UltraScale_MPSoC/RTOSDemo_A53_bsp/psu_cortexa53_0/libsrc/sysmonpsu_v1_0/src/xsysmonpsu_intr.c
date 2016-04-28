/******************************************************************************
*
* Copyright (C) 2016 Xilinx, Inc.  All rights reserved.
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
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* XILINX CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
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
* @file xsysmonpsu_intr.c
*
* This file contains functions related to SYSMONPSU interrupt handling.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- -----  -------- -----------------------------------------------
* 1.0   kvn    12/15/15 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xsysmonpsu.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions ****************************/

/****************************************************************************/
/**
*
* This function enables the specified interrupts in the device.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	Mask is the 64 bit-mask of the interrupts to be enabled.
*		Bit positions of 1 will be enabled. Bit positions of 0 will
*		keep the previous setting. This mask is formed by OR'ing
*		XSYSMONPSU_IER_0_* and XSYSMONPSU_IER_1_* bits defined in
*		xsysmonpsu_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XSysMonPsu_IntrEnable(XSysMonPsu *InstancePtr, u64 Mask)
{
	u32 RegValue;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Enable the specified interrupts in the AMS Interrupt Enable Register. */
	RegValue = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
					XSYSMONPSU_IER_0_OFFSET);
	RegValue |= (u32)(Mask & (u64)XSYSMONPSU_IXR_0_MASK);
	XSysmonPsu_WriteReg(InstancePtr->Config.BaseAddress + XSYSMONPSU_IER_0_OFFSET,
			  RegValue);

	RegValue = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
					XSYSMONPSU_IER_1_OFFSET);
	RegValue |= (u32)((Mask >> XSYSMONPSU_IXR_1_SHIFT) & XSYSMONPSU_IXR_1_MASK);
	XSysmonPsu_WriteReg(InstancePtr->Config.BaseAddress + XSYSMONPSU_IER_1_OFFSET,
			  RegValue);
}

/****************************************************************************/
/**
*
* This function disables the specified interrupts in the device.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	Mask is the 64 bit-mask of the interrupts to be disabled.
*		Bit positions of 1 will be disabled. Bit positions of 0 will
*		keep the previous setting. This mask is formed by OR'ing
*		XSYSMONPSU_IDR_0_* and XSYSMONPSU_IDR_1_* bits defined in
*		xsysmonpsu_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XSysMonPsu_IntrDisable(XSysMonPsu *InstancePtr, u64 Mask)
{
	u32 RegValue;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Disable the specified interrupts in the AMS Interrupt Disable Register. */
	RegValue = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
					XSYSMONPSU_IDR_0_OFFSET);
	RegValue |= (u32)(Mask & (u64)XSYSMONPSU_IXR_0_MASK);
	XSysmonPsu_WriteReg(InstancePtr->Config.BaseAddress + XSYSMONPSU_IDR_0_OFFSET,
			  RegValue);

	RegValue = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
					XSYSMONPSU_IDR_1_OFFSET);
	RegValue |= (u32)((Mask >> XSYSMONPSU_IXR_1_SHIFT) & XSYSMONPSU_IXR_1_MASK);
	XSysmonPsu_WriteReg(InstancePtr->Config.BaseAddress + XSYSMONPSU_IDR_1_OFFSET,
			  RegValue);
}

/****************************************************************************/
/**
*
* This function returns the enabled interrupts read from the Interrupt Enable
* Register (IER). Use the XSYSMONPSU_IER_0_* and XSYSMONPSU_IER_1_* constants
* defined in xsysmonpsu_hw.h to interpret the returned value.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
*
* @return	A 64-bit value representing the contents of the Interrupt Mask
* 			Registers (IMR1 IMR0).
*
* @note		None.
*
*****************************************************************************/
u64 XSysMonPsu_IntrGetEnabled(XSysMonPsu *InstancePtr)
{
	u64 MaskedInterrupts;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Return the value read from the AMS Interrupt Mask Register. */
	MaskedInterrupts = (u64)XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
                         XSYSMONPSU_IMR_0_OFFSET) & (u64)XSYSMONPSU_IXR_0_MASK;
	MaskedInterrupts |= ((u64)XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
                         XSYSMONPSU_IMR_1_OFFSET) & (u64)XSYSMONPSU_IXR_1_MASK)
                          << XSYSMONPSU_IXR_1_SHIFT;

	return (~MaskedInterrupts);
}

/****************************************************************************/
/**
*
* This function returns the interrupt status read from Interrupt Status
* Register(ISR). Use the XSYSMONPSU_ISR_0_* and XSYSMONPSU_ISR_1_ constants
* defined in xsysmonpsu_hw.h to interpret the returned value.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
*
* @return	A 64-bit value representing the contents of the Interrupt Status
* 			Registers (ISR1 ISR0).
*
* @note		None.
*
*****************************************************************************/
u64 XSysMonPsu_IntrGetStatus(XSysMonPsu *InstancePtr)
{
	u64 IntrStatusRegister;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Return the value read from the AMS ISR. */
	IntrStatusRegister = (u64)XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
                           XSYSMONPSU_ISR_0_OFFSET) & (u64)XSYSMONPSU_IXR_0_MASK;
	IntrStatusRegister |= ((u64)XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
                           XSYSMONPSU_ISR_1_OFFSET) & (u64)XSYSMONPSU_IXR_1_MASK)
                           << XSYSMONPSU_IXR_1_SHIFT;

	return IntrStatusRegister;
}

/****************************************************************************/
/**
*
* This function clears the specified interrupts in the Interrupt Status
* Register (ISR).
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	Mask is the 64 bit-mask of the interrupts to be cleared.
*		Bit positions of 1 will be cleared. Bit positions of 0 will not
* 		change the previous interrupt status. This mask is formed by
* 		OR'ing the XSYSMONPSU_ISR_0_* and XSYSMONPSU_ISR_1_* bits
* 		which are defined in xsysmonpsu_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XSysMonPsu_IntrClear(XSysMonPsu *InstancePtr, u64 Mask)
{
	u32 RegValue;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Clear the specified interrupts in the Interrupt Status register. */
	RegValue = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
					XSYSMONPSU_ISR_0_OFFSET);
	RegValue &= (u32)(Mask & (u64)XSYSMONPSU_IXR_0_MASK);
	XSysmonPsu_WriteReg(InstancePtr->Config.BaseAddress + XSYSMONPSU_ISR_0_OFFSET,
			  RegValue);

	RegValue = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
					XSYSMONPSU_ISR_1_OFFSET);
	RegValue &= (u32)((Mask >> XSYSMONPSU_IXR_1_SHIFT) & XSYSMONPSU_IXR_1_MASK);
	XSysmonPsu_WriteReg(InstancePtr->Config.BaseAddress + XSYSMONPSU_ISR_1_OFFSET,
			  RegValue);
}


/** @} */
