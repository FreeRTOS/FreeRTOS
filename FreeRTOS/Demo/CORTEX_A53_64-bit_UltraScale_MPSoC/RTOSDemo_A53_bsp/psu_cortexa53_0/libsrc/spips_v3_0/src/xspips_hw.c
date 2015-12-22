/******************************************************************************
*
* Copyright (C) 2013 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xspips_hw.c
*
* Contains the reset and post boot rom state initialization.
* Function prototypes in xspips_hw.h
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- -----------------------------------------------
* 1.06a hk     08/22/13 First release.
* 3.00  kvn    02/13/15 Modified code for MISRA-C:2012 compliance.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xspips_hw.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Resets the spi module
*
* @param    BaseAddress is the base address of the device.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
void XSpiPs_ResetHw(u32 BaseAddress)
{
	u32 Check;
	/*
	 * Disable Interrupts
	 */
	XSpiPs_WriteReg(BaseAddress, XSPIPS_IDR_OFFSET,
			XSPIPS_IXR_DISABLE_ALL_MASK);

	/*
	 * Disable device
	 */
	XSpiPs_WriteReg(BaseAddress, XSPIPS_ER_OFFSET,
				0U);
	/*
	 * Write default value to RX and TX threshold registers
	 * RX threshold should be set to 1 here as the corresponding
	 * status bit is used to clear the FIFO next
	 */
	XSpiPs_WriteReg(BaseAddress, XSPIPS_TXWR_OFFSET,
			(XSPIPS_TXWR_RESET_VALUE & XSPIPS_TXWR_MASK));
	XSpiPs_WriteReg(BaseAddress, XSPIPS_RXWR_OFFSET,
			(XSPIPS_RXWR_RESET_VALUE & XSPIPS_RXWR_MASK));

	/*
	 * Clear RXFIFO
	 */
	Check = (XSpiPs_ReadReg(BaseAddress,XSPIPS_SR_OFFSET) &
		XSPIPS_IXR_RXNEMPTY_MASK);
	while (Check != 0U) {
		(void)XSpiPs_ReadReg(BaseAddress, XSPIPS_RXD_OFFSET);
		Check = (XSpiPs_ReadReg(BaseAddress,XSPIPS_SR_OFFSET) &
			XSPIPS_IXR_RXNEMPTY_MASK);
	}

	/*
	 * Clear status register by writing 1 to the write to clear bits
	 */
	XSpiPs_WriteReg(BaseAddress, XSPIPS_SR_OFFSET,
				XSPIPS_IXR_WR_TO_CLR_MASK);

	/*
	 * Write default value to configuration register
	 * De-select all slaves
	 */
	XSpiPs_WriteReg(BaseAddress, XSPIPS_CR_OFFSET,
				XSPIPS_CR_RESET_STATE |
				XSPIPS_CR_SSCTRL_MASK);

}
