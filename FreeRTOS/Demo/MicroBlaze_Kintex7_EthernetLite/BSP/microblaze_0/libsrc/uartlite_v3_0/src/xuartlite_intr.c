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
* @file xuartlite_intr.c
*
* This file contains interrupt-related functions for the UART Lite component
* (XUartLite).
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a ecm  08/31/01 First release
* 1.00b jhl  02/21/02 Repartitioned the driver for smaller files
* 1.02a rpm  02/14/07 Added check for outstanding transmission before
*			calling the send callback (avoids extraneous
*			callback invocations)
* 2.00a ktn  10/20/09 Updated to use HAL Processor APIs. The macros have been
*		      renamed to remove _m from the name.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xuartlite.h"
#include "xuartlite_i.h"
#include "xil_io.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Function Prototypes *****************************/

static void ReceiveDataHandler(XUartLite *InstancePtr);
static void SendDataHandler(XUartLite *InstancePtr);

/************************** Variable Definitions ****************************/

typedef void (*Handler)(XUartLite *InstancePtr);

/****************************************************************************/
/**
*
* This function sets the handler that will be called when an event (interrupt)
* occurs in the driver. The purpose of the handler is to allow application
* specific processing to be performed.
*
* @param	InstancePtr is a pointer to the XUartLite instance.
* @param	FuncPtr is the pointer to the callback function.
* @param	CallBackRef is the upper layer callback reference passed back
*		when the callback function is invoked.
*
* @return	None.
*
* @note		There is no assert on the CallBackRef since the driver doesn't
*		know what it is (nor should it)
*
*****************************************************************************/
void XUartLite_SetRecvHandler(XUartLite *InstancePtr,
				XUartLite_Handler FuncPtr, void *CallBackRef)
{
	/*
	 * Assert validates the input arguments
	 * CallBackRef not checked, no way to know what is valid
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(FuncPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->RecvHandler = FuncPtr;
	InstancePtr->RecvCallBackRef = CallBackRef;
}

/****************************************************************************/
/**
*
* This function sets the handler that will be called when an event (interrupt)
* occurs in the driver. The purpose of the handler is to allow application
* specific processing to be performed.
*
* @param	InstancePtr is a pointer to the XUartLite instance .
* @param	FuncPtr is the pointer to the callback function.
* @param	CallBackRef is the upper layer callback reference passed back
*		when the callback function is invoked.
*
* @return 	None.
*
* @note		There is no assert on the CallBackRef since the driver doesn't
*		know what it is (nor should it)
*
*****************************************************************************/
void XUartLite_SetSendHandler(XUartLite *InstancePtr,
				XUartLite_Handler FuncPtr, void *CallBackRef)
{
	/*
	 * Assert validates the input arguments
	 * CallBackRef not checked, no way to know what is valid
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(FuncPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->SendHandler = FuncPtr;
	InstancePtr->SendCallBackRef = CallBackRef;
}

/****************************************************************************/
/**
*
* This function is the interrupt handler for the UART lite driver.
* It must be connected to an interrupt system by the user such that it is
* called when an interrupt for any UART lite occurs. This function
* does not save or restore the processor context such that the user must
* ensure this occurs.
*
* @param	InstancePtr contains a pointer to the instance of the UART that
*		the interrupt is for.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XUartLite_InterruptHandler(XUartLite *InstancePtr)
{
	u32 IsrStatus;

	Xil_AssertVoid(InstancePtr != NULL);

	/*
	 * Read the status register to determine which, coulb be both
	 * interrupt is active
	 */
	IsrStatus = XUartLite_ReadReg(InstancePtr->RegBaseAddress,
					XUL_STATUS_REG_OFFSET);

	if ((IsrStatus & (XUL_SR_RX_FIFO_FULL |
		XUL_SR_RX_FIFO_VALID_DATA)) != 0) {
		ReceiveDataHandler(InstancePtr);
	}

	if (((IsrStatus & XUL_SR_TX_FIFO_EMPTY) != 0) &&
		(InstancePtr->SendBuffer.RequestedBytes > 0)) {
		SendDataHandler(InstancePtr);
	}
}

/****************************************************************************/
/**
*
* This function handles the interrupt when data is received, either a single
* byte when FIFOs are not enabled, or multiple bytes with the FIFO.
*
* @param	InstancePtr is a pointer to the XUartLite instance.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
static void ReceiveDataHandler(XUartLite *InstancePtr)
{
	/*
	 * If there are bytes still to be received in the specified buffer
	 * go ahead and receive them
	 */
	if (InstancePtr->ReceiveBuffer.RemainingBytes != 0) {
		XUartLite_ReceiveBuffer(InstancePtr);
	}

	/*
	 * If the last byte of a message was received then call the application
	 * handler, this code should not use an else from the previous check of
	 * the number of bytes to receive because the call to receive the buffer
	 * updates the bytes to receive
	 */
	if (InstancePtr->ReceiveBuffer.RemainingBytes == 0) {
		InstancePtr->RecvHandler(InstancePtr->RecvCallBackRef,
		InstancePtr->ReceiveBuffer.RequestedBytes -
		InstancePtr->ReceiveBuffer.RemainingBytes);
	}

	/*
	 * Update the receive stats to reflect the receive interrupt
	 */
	InstancePtr->Stats.ReceiveInterrupts++;
}

/****************************************************************************/
/**
*
* This function handles the interrupt when data has been sent, the transmit
* FIFO is empty (transmitter holding register).
*
* @param	InstancePtr is a pointer to the XUartLite instance .
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
static void SendDataHandler(XUartLite *InstancePtr)
{
	/*
	 * If there are not bytes to be sent from the specified buffer,
	 * call the callback function
	 */
	if (InstancePtr->SendBuffer.RemainingBytes == 0) {
		int SaveReq;

		/*
		 * Save and zero the requested bytes since transmission
		 * is complete
		 */
		SaveReq = InstancePtr->SendBuffer.RequestedBytes;
		InstancePtr->SendBuffer.RequestedBytes = 0;

		/*
		 * Call the application handler to indicate
		 * the data has been sent
		 */
		InstancePtr->SendHandler(InstancePtr->SendCallBackRef, SaveReq);
	}
	/*
	 * Otherwise there is still more data to send in the specified buffer
	 * so go ahead and send it
	 */
	else {
		XUartLite_SendBuffer(InstancePtr);
	}

	/*
	 * Update the transmit stats to reflect the transmit interrupt
	 */
	InstancePtr->Stats.TransmitInterrupts++;
}


/*****************************************************************************/
/**
*
* This function disables the UART interrupt. After calling this function,
* data may still be received by the UART but no interrupt will be generated
* since the hardware device has no way to disable the receiver.
*
* @param	InstancePtr is a pointer to the XUartLite instance.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUartLite_DisableInterrupt(XUartLite *InstancePtr)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Write to the control register to disable the interrupts, the only
	 * other bits in this register are the FIFO reset bits such that
	 * writing them to zero will not affect them.
	 */
	XUartLite_WriteReg(InstancePtr->RegBaseAddress,
				XUL_CONTROL_REG_OFFSET, 0);
}

/*****************************************************************************/
/**
*
* This function enables the UART interrupt such that an interrupt will occur
* when data is received or data has been transmitted. The device contains
* 16 byte receive and transmit FIFOs such that an interrupt is generated
* anytime there is data in the receive FIFO and when the transmit FIFO
* transitions from not empty to empty.
*
* @param	InstancePtr is a pointer to the XUartLite instance.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUartLite_EnableInterrupt(XUartLite *InstancePtr)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Write to the control register to enable the interrupts, the only
	 * other bits in this register are the FIFO reset bits such that
	 * writing them to zero will not affect them.
	 */
	XUartLite_WriteReg(InstancePtr->RegBaseAddress,
				XUL_CONTROL_REG_OFFSET, XUL_CR_ENABLE_INTR);
}

