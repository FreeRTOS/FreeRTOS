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
/****************************************************************************/
/**
*
* @file xuartlite_l.c
*
* This file contains low-level driver functions that can be used to access the
* device.  The user should refer to the hardware device specification for more
* details of the device operation.

* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00b rpm  04/25/02 First release
* 1.12a rpm  07/16/07 Fixed arg type for RecvByte
* 2.00a ktn  10/20/09 The macros have been renamed to remove _m from the name.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xuartlite_l.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Prototypes ******************************/


/****************************************************************************/
/**
*
* This functions sends a single byte using the UART. It is blocking in that it
* waits for the transmitter to become non-full before it writes the byte to
* the transmit register.
*
* @param	BaseAddress is the base address of the device
* @param	Data is the byte of data to send
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XUartLite_SendByte(u32 BaseAddress, u8 Data)
{
	while (XUartLite_IsTransmitFull(BaseAddress));

	XUartLite_WriteReg(BaseAddress, XUL_TX_FIFO_OFFSET, Data);
}


/****************************************************************************/
/**
*
* This functions receives a single byte using the UART. It is blocking in that
* it waits for the receiver to become non-empty before it reads from the
* receive register.
*
* @param	BaseAddress is the base address of the device
*
* @return	The byte of data received.
*
* @note		None.
*
******************************************************************************/
u8 XUartLite_RecvByte(u32 BaseAddress)
{
	while (XUartLite_IsReceiveEmpty(BaseAddress));

	return (u8)XUartLite_ReadReg(BaseAddress, XUL_RX_FIFO_OFFSET);
}

