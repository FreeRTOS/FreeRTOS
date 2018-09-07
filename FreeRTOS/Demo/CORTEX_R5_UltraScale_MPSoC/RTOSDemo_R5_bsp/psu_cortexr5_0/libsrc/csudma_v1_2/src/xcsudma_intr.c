/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc.  All rights reserved.
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
* @file xcsudma_intr.c
* @addtogroup csudma_v1_2
* @{
*
* This file contains interrupt related functions of Xilinx CSU_DMA core.
* Please see xcsudma.h for more details of the driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- ---------------------------------------------------
* 1.0   vnsld  22/10/14  First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xcsudma.h"

/************************** Function Prototypes ******************************/


/************************** Function Definitions *****************************/


/*****************************************************************************/
/**
*
* This function returns interrupt status read from Interrupt Status Register.
* Use the XCSUDMA_IXR_*_MASK constants defined in xcsudma_hw.h to interpret the
* returned value.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
*		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
*
* @return	The pending interrupts of the CSU_DMA. Use th following masks
*		to interpret the returned value.
*		XCSUDMA_IXR_SRC_MASK   - For Source channel
*		XCSUDMA_IXR_DST_MASK   - For Destination channel
*
* @note		None.
*
******************************************************************************/
u32 XCsuDma_IntrGetStatus(XCsuDma *InstancePtr, XCsuDma_Channel Channel)
{
	u32 Data;

	/* Verify arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
				(Channel == (XCSUDMA_DST_CHANNEL)));

	Data = XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
				(u32)(XCSUDMA_I_STS_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF)));

	return Data;

}

/*****************************************************************************/
/**
*
* This function clears interrupt(s). Every bit set in Interrupt Status
* Register indicates that a specific type of interrupt is occurring, and this
* function clears one or more interrupts by writing a bit mask to Interrupt
* Clear Register.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
*		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
* @param	Mask is the mask to clear. Bit positions of 1 will be cleared.
*		Bit positions of 0 will not change the previous interrupt
*		status. This mask is formed by OR'ing XCSUDMA_IXR_* bits
*		defined in xcsudma_hw.h.
*
* @note		None.
*
******************************************************************************/
void XCsuDma_IntrClear(XCsuDma *InstancePtr, XCsuDma_Channel Channel, u32 Mask)
{


	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
				(Channel == (XCSUDMA_DST_CHANNEL)));
	if (Channel == (XCSUDMA_SRC_CHANNEL)) {
		XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
			(u32)(XCSUDMA_I_STS_OFFSET),
				(Mask & (u32)(XCSUDMA_IXR_SRC_MASK)));
	}
	else {
		XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_I_STS_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))),
				(Mask & (u32)(XCSUDMA_IXR_DST_MASK)));
	}
}

/*****************************************************************************/
/**
*
* This function enables the interrupt(s). Use the XCSUDMA_IXR_*_MASK constants
* defined in xcsudma_hw.h to create the bit-mask to enable interrupts.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
*		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
* @param	Mask contains interrupts to be enabled.
*		- Bit positions of 1 will be enabled.
*		This mask is formed by OR'ing XCSUDMA_IXR_*_MASK bits defined
*		in xcsudma_hw.h.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XCsuDma_EnableIntr(XCsuDma *InstancePtr, XCsuDma_Channel Channel,
							u32 Mask)
{
	u32 Data;

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
				(Channel == (XCSUDMA_DST_CHANNEL)));

	if (Channel == (XCSUDMA_SRC_CHANNEL)) {
		Data = Mask & (u32)(XCSUDMA_IXR_SRC_MASK);
	}
	else {
		Data = Mask & (u32)(XCSUDMA_IXR_DST_MASK);
	}
	/*
	 * Write the mask to the IER Register
	 */
	XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
		((u32)(XCSUDMA_I_EN_OFFSET) +
		((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))), Data);

}

/*****************************************************************************/
/**
*
* This function disables the interrupt(s). Use the XCSUDMA_IXR_*_MASK constants
* defined in xcsudma_hw.h to create the bit-mask to disable interrupts.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
*		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
* @param	Mask contains interrupts to be disabled.
*		- Bit positions of 1 will be disabled.
*		This mask is formed by OR'ing XCSUDMA_IXR_*_MASK bits defined
*		in xcsudma_hw.h.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XCsuDma_DisableIntr(XCsuDma *InstancePtr, XCsuDma_Channel Channel,
								u32 Mask)
{
	u32 Data;

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
			(Channel == (XCSUDMA_DST_CHANNEL)));

	if (Channel == XCSUDMA_SRC_CHANNEL) {
		Data = (Mask) & (u32)(XCSUDMA_IXR_SRC_MASK);
	}
	else {
		Data = (Mask) & (u32)(XCSUDMA_IXR_DST_MASK);
	}

	/*
	 * Write the mask to the IDR Register
	 */
	XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
		((u32)(XCSUDMA_I_DIS_OFFSET) +
		((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))), Data);

}

/*****************************************************************************/
/**
*
* This function returns the interrupt mask to know which interrupts are
* enabled and which of them were disaled.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
*		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
*
* @return	The current interrupt mask. The mask indicates which interrupts
*		are enabled/disabled.
*		0 bit represents .....corresponding interrupt is enabled.
*		1 bit represents .....Corresponding interrupt is disabled.
*		To interpret returned mask use
*		XCSUDMA_IXR_SRC_MASK........For source channel
*		XCSUDMA_IXR_DST_MASK........For destination channel
*
* @note		None.
*
******************************************************************************/
u32 XCsuDma_GetIntrMask(XCsuDma *InstancePtr, XCsuDma_Channel Channel)
{

	/* Verify arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
					(Channel == (XCSUDMA_DST_CHANNEL)));

	/*
	 * Read the Interrupt Mask register
	 */
	return (XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_I_MASK_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF)))));
}
/** @} */
