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
* @file xuartps_hw.c
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- ------ -------- ----------------------------------------------
* 1.00	drg/jz 01/12/10 First Release
* 1.05a hk     08/22/13 Added reset function
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/
#include "xuartps_hw.h"

/************************** Constant Definitions ****************************/


/***************** Macros (Inline Functions) Definitions ********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/

/****************************************************************************/
/**
*
* This function sends one byte using the device. This function operates in
* polled mode and blocks until the data has been put into the TX FIFO register.
*
* @param	BaseAddress contains the base address of the device.
* @param	Data contains the byte to be sent.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUartPs_SendByte(u32 BaseAddress, u8 Data)
{
		/*
		 * Wait until there is space in TX FIFO
		 */
		while (XUartPs_IsTransmitFull(BaseAddress));

		/*
		 * Write the byte into the TX FIFO
		 */
		XUartPs_WriteReg(BaseAddress, XUARTPS_FIFO_OFFSET, Data);
}

/****************************************************************************/
/**
*
* This function receives a byte from the device. It operates in polled mode
* and blocks until a byte has received.
*
* @param	BaseAddress contains the base address of the device.
*
* @return	The data byte received.
*
* @note		None.
*
*****************************************************************************/
u8 XUartPs_RecvByte(u32 BaseAddress)
{
		/*
		 * Wait until there is data
		 */
		while (!XUartPs_IsReceiveData(BaseAddress));

		/*
		 * Return the byte received
		 */
		return (XUartPs_ReadReg(BaseAddress, XUARTPS_FIFO_OFFSET));
}

/****************************************************************************/
/**
*
* This function resets UART
*
* @param	BaseAddress contains the base address of the device.
*
* @return	None
*
* @note		None.
*
*****************************************************************************/
void XUartPs_ResetHw(u32 BaseAddress)
{

	/*
	 * Disable interrupts
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_IDR_OFFSET, XUARTPS_IXR_MASK);

	/*
	 * Disable receive and transmit
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_CR_OFFSET,
				XUARTPS_CR_RX_DIS | XUARTPS_CR_TX_DIS);

	/*
	 * Software reset of receive and transmit
	 * This clears the FIFO.
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_CR_OFFSET,
				XUARTPS_CR_TXRST | XUARTPS_CR_RXRST);

	/*
	 * Clear status flags - SW reset wont clear sticky flags.
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_ISR_OFFSET, XUARTPS_IXR_MASK);

	/*
	 * Mode register reset value : All zeroes
	 * Normal mode, even parity, 1 stop bit
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_MR_OFFSET,
				XUARTPS_MR_CHMODE_NORM);

	/*
	 * Rx and TX trigger register reset values
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_RXWM_OFFSET,
				XUARTPS_RXWM_RESET_VAL);
	XUartPs_WriteReg(BaseAddress, XUARTPS_TXWM_OFFSET,
				XUARTPS_TXWM_RESET_VAL);

	/*
	 * Rx timeout disabled by default
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_RXTOUT_OFFSET,
				XUARTPS_RXTOUT_DISABLE);

	/*
	 * Baud rate generator and dividor reset values
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_BAUDGEN_OFFSET,
				XUARTPS_BAUDGEN_RESET_VAL);
	XUartPs_WriteReg(BaseAddress, XUARTPS_BAUDDIV_OFFSET,
				XUARTPS_BAUDDIV_RESET_VAL);

	/*
	 * Control register reset value -
	 * RX and TX are disable by default
	 */
	XUartPs_WriteReg(BaseAddress, XUARTPS_CR_OFFSET,
				XUARTPS_CR_RX_DIS | XUARTPS_CR_TX_DIS |
				XUARTPS_CR_STOPBRK);

}

