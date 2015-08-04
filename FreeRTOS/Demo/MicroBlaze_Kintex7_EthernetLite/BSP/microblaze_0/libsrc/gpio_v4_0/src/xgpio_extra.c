/******************************************************************************
*
* Copyright (C) 2002 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xgpio_extra.c
*
* The implementation of the XGpio driver's advanced discrete functions.
* See xgpio.h for more information about the driver.
*
* @note
*
* These APIs can only be used if the GPIO_IO ports in the IP are used for
* connecting to the external output ports.
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a rmm  02/04/02 First release
* 2.00a jhl  12/16/02 Update for dual channel and interrupt support
* 2.11a mta  03/21/07 Updated to new coding style
* 3.00a sv   11/21/09 Updated to use HAL Processor APIs. Renamed the macros
*		      XGpio_mWriteReg to XGpio_WriteReg, and XGpio_mReadReg
*		      to XGpio_ReadReg.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xgpio.h"
#include "xgpio_i.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/


/****************************************************************************/
/**
* Set output discrete(s) to logic 1 for the specified GPIO channel.
*
* @param	InstancePtr is a pointer to an XGpio instance to be worked on.
* @param	Channel contains the channel of the GPIO (1 or 2) to operate on.
* @param	Mask is the set of bits that will be set to 1 in the discrete
*		data register. All other bits in the data register are
*		unaffected.
*
* @return	None.
*
* @note
*
* The hardware must be built for dual channels if this function is used
* with any channel other than 1.  If it is not, this function will assert.
*
* This API can only be used if the GPIO_IO ports in the IP are used for
* connecting to the external output ports.
*
*****************************************************************************/
void XGpio_DiscreteSet(XGpio * InstancePtr, unsigned Channel, u32 Mask)
{
	u32 Current;
	unsigned DataOffset;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((Channel == 1) ||
		     ((Channel == 2) && (InstancePtr->IsDual == TRUE)));

	/*
	 * Calculate the offset to the data register of the GPIO once
	 */
	DataOffset = ((Channel - 1) * XGPIO_CHAN_OFFSET) + XGPIO_DATA_OFFSET;

	/*
	 * Read the contents of the data register, merge in Mask and write
	 * back results
	 */
	Current = XGpio_ReadReg(InstancePtr->BaseAddress, DataOffset);
	Current |= Mask;
	XGpio_WriteReg(InstancePtr->BaseAddress, DataOffset, Current);
}


/****************************************************************************/
/**
* Set output discrete(s) to logic 0 for the specified GPIO channel.
*
* @param	InstancePtr is a pointer to an XGpio instance to be worked on.
* @param	Channel contains the channel of the GPIO (1 or 2) to operate on.
* @param	Mask is the set of bits that will be set to 0 in the discrete
*		data register. All other bits in the data register are
*		unaffected.
*
* @return	None.
*
* @note
*
* The hardware must be built for dual channels if this function is used
* with any channel other than 1.  If it is not, this function will assert.
*
* This API can only be used if the GPIO_IO ports in the IP are used for
* connecting to the external output ports.
*
*****************************************************************************/
void XGpio_DiscreteClear(XGpio * InstancePtr, unsigned Channel, u32 Mask)
{
	u32 Current;
	unsigned DataOffset;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((Channel == 1) ||
		     ((Channel == 2) && (InstancePtr->IsDual == TRUE)));

	/*
	 * Calculate the offset to the data register of the GPIO once
	 */
	DataOffset = ((Channel - 1) * XGPIO_CHAN_OFFSET) + XGPIO_DATA_OFFSET;

	/*
	 * Read the contents of the data register, merge in Mask and write
	 * back results
	 */
	Current = XGpio_ReadReg(InstancePtr->BaseAddress, DataOffset);
	Current &= ~Mask;
	XGpio_WriteReg(InstancePtr->BaseAddress, DataOffset, Current);
}
