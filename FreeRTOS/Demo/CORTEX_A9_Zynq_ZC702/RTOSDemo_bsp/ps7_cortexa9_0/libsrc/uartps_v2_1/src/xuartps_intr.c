/*****************************************************************************
*
* (c) Copyright 2010-13 Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
*
*****************************************************************************/
/****************************************************************************/
/**
*
* @file xuartps_intr.c
*
* This file contains the functions for interrupt handling
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- ------ -------- -----------------------------------------------
* 1.00  drg/jz 01/13/10 First Release
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xuartps.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Function Prototypes *****************************/

static void ReceiveDataHandler(XUartPs *InstancePtr);
static void SendDataHandler(XUartPs *InstancePtr, u32 isrstatus);
static void ReceiveErrorHandler(XUartPs *InstancePtr);
static void ReceiveTimeoutHandler(XUartPs *InstancePtr);
static void ModemHandler(XUartPs *InstancePtr);


/* Internal function prototypes implemented in xuartps.c */
extern unsigned int XUartPs_ReceiveBuffer(XUartPs *InstancePtr);
extern unsigned int XUartPs_SendBuffer(XUartPs *InstancePtr);

/************************** Variable Definitions ****************************/

typedef void (*Handler)(XUartPs *InstancePtr);

/****************************************************************************/
/**
*
* This function gets the interrupt mask
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return
*		The current interrupt mask. The mask indicates which interupts
*		are enabled.
*
* @note		None.
*
*****************************************************************************/
u32 XUartPs_GetInterruptMask(XUartPs *InstancePtr)
{
	/*
	 * Assert validates the input argument
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);

	/*
	 * Read the Interrupt Mask register
	 */
	return (XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
			 XUARTPS_IMR_OFFSET));
}

/****************************************************************************/
/**
*
* This function sets the interrupt mask.
*
* @param	InstancePtr is a pointer to the XUartPs instance
* @param	Mask contains the interrupts to be enabled or disabled.
*		A '1' enables an interupt, and a '0' disables.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XUartPs_SetInterruptMask(XUartPs *InstancePtr, u32 Mask)
{
	/*
	 * Assert validates the input arguments
	 */
	Xil_AssertVoid(InstancePtr != NULL);

	Mask &= XUARTPS_IXR_MASK;

	/*
	 * Write the mask to the IER Register
	 */
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress,
		 XUARTPS_IER_OFFSET, Mask);

	/*
	 * Write the inverse of the Mask to the IDR register
	 */
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress,
		 XUARTPS_IDR_OFFSET, (~Mask));

}

/****************************************************************************/
/**
*
* This function sets the handler that will be called when an event (interrupt)
* occurs that needs application's attention.
*
* @param	InstancePtr is a pointer to the XUartPs instance
* @param	FuncPtr is the pointer to the callback function.
* @param	CallBackRef is the upper layer callback reference passed back
*		when the callback function is invoked.
*
* @return	None.
*
* @note
*
* There is no assert on the CallBackRef since the driver doesn't know what it
* is (nor should it)
*
*****************************************************************************/
void XUartPs_SetHandler(XUartPs *InstancePtr, XUartPs_Handler FuncPtr,
		 void *CallBackRef)
{
	/*
	 * Asserts validate the input arguments
	 * CallBackRef not checked, no way to know what is valid
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(FuncPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->Handler = FuncPtr;
	InstancePtr->CallBackRef = CallBackRef;
}

/****************************************************************************/
/**
*
* This function is the interrupt handler for the driver.
* It must be connected to an interrupt system by the application such that it
* can be called when an interrupt occurs.
*
* @param	InstancePtr contains a pointer to the driver instance
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XUartPs_InterruptHandler(XUartPs *InstancePtr)
{
	u32 IsrStatus;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the interrupt ID register to determine which
	 * interrupt is active
	 */
	IsrStatus = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
				   XUARTPS_IMR_OFFSET);

	IsrStatus &= XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
				   XUARTPS_ISR_OFFSET);

	/*
	 * Dispatch an appropiate handler.
	 */
	if(0 != (IsrStatus & (XUARTPS_IXR_RXOVR | XUARTPS_IXR_RXEMPTY |
				 XUARTPS_IXR_RXFULL))) {
		/* Recieved data interrupt */
		ReceiveDataHandler(InstancePtr);
	}

	if(0 != (IsrStatus & (XUARTPS_IXR_TXEMPTY | XUARTPS_IXR_TXFULL))) {
		/* Transmit data interrupt */
		SendDataHandler(InstancePtr, IsrStatus);
	}

	if(0 != (IsrStatus & (XUARTPS_IXR_OVER | XUARTPS_IXR_FRAMING |
				XUARTPS_IXR_PARITY))) {
		/* Recieved Error Status interrupt */
		ReceiveErrorHandler(InstancePtr);
	}

	if(0 != (IsrStatus & XUARTPS_IXR_TOUT )) {
		/* Recieved Timeout interrupt */
		ReceiveTimeoutHandler(InstancePtr);
	}

	if(0 != (IsrStatus & XUARTPS_IXR_DMS)) {
		/* Modem status interrupt */
		ModemHandler(InstancePtr);
	}

	/*
	 * Clear the interrupt status.
	 */
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress, XUARTPS_ISR_OFFSET,
		IsrStatus);

}

/****************************************************************************/
/*
*
* This function handles interrupts for receive errors which include
* overrun errors, framing errors, parity errors, and the break interrupt.
*
* @param	InstancePtr is a pointer to the XUartPs instance.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
static void ReceiveErrorHandler(XUartPs *InstancePtr)
{
	/*
	 * If there are bytes still to be received in the specified buffer
	 * go ahead and receive them. Removing bytes from the RX FIFO will
	 * clear the interrupt.
	 */
	if (InstancePtr->ReceiveBuffer.RemainingBytes != 0) {
		XUartPs_ReceiveBuffer(InstancePtr);
	}

	/*
	 * Call the application handler to indicate that there is a receive
	 * error or a break interrupt, if the application cares about the
	 * error it call a function to get the last errors.
	 */
	InstancePtr->Handler(InstancePtr->CallBackRef,
				XUARTPS_EVENT_RECV_ERROR,
				(InstancePtr->ReceiveBuffer.RequestedBytes -
				InstancePtr->ReceiveBuffer.RemainingBytes));

}
/****************************************************************************/
/**
*
* This function handles the receive timeout interrupt. This interrupt occurs
* whenever a number of bytes have been present in the RX FIFO and the receive
* data line has been idle for at lease 4 or more character times, (the timeout
* is set using XUartPs_SetrecvTimeout() function).
*
* @param	InstancePtr is a pointer to the XUartPs instance
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
static void ReceiveTimeoutHandler(XUartPs *InstancePtr)
{
	u32 Event;

	/*
	 * If there are bytes still to be received in the specified buffer
	 * go ahead and receive them. Removing bytes from the RX FIFO will
	 * clear the interrupt.
	 */
	if (InstancePtr->ReceiveBuffer.RemainingBytes != 0) {
		XUartPs_ReceiveBuffer(InstancePtr);
	}

	/*
	 * If there are no more bytes to receive then indicate that this is
	 * not a receive timeout but the end of the buffer reached, a timeout
	 * normally occurs if # of bytes is not divisible by FIFO threshold,
	 * don't rely on previous test of remaining bytes since receive
	 * function updates it
	 */
	if (InstancePtr->ReceiveBuffer.RemainingBytes != 0) {
		Event = XUARTPS_EVENT_RECV_TOUT;
	} else {
		Event = XUARTPS_EVENT_RECV_DATA;
	}

	/*
	 * Call the application handler to indicate that there is a receive
	 * timeout or data event
	 */
	InstancePtr->Handler(InstancePtr->CallBackRef, Event,
				 InstancePtr->ReceiveBuffer.RequestedBytes -
				 InstancePtr->ReceiveBuffer.RemainingBytes);

}
/****************************************************************************/
/**
*
* This function handles the interrupt when data is in RX FIFO.
*
* @param	InstancePtr is a pointer to the XUartPs instance
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
static void ReceiveDataHandler(XUartPs *InstancePtr)
{
	/*
	 * If there are bytes still to be received in the specified buffer
	 * go ahead and receive them. Removing bytes from the RX FIFO will
	 * clear the interrupt.
	 */
	 if (InstancePtr->ReceiveBuffer.RemainingBytes != 0) {
		XUartPs_ReceiveBuffer(InstancePtr);
	}


	/* If the last byte of a message was received then call the application
	 * handler, this code should not use an else from the previous check of
	 * the number of bytes to receive because the call to receive the buffer
	 * updates the bytes ramained
	 */
	if (InstancePtr->ReceiveBuffer.RemainingBytes == 0) {
		InstancePtr->Handler(InstancePtr->CallBackRef,
				XUARTPS_EVENT_RECV_DATA,
				(InstancePtr->ReceiveBuffer.RequestedBytes -
				InstancePtr->ReceiveBuffer.RemainingBytes));
	}

}

/****************************************************************************/
/**
*
* This function handles the interrupt when data has been sent, the transmit
* FIFO is empty (transmitter holding register).
*
* @param	InstancePtr is a pointer to the XUartPs instance
* @param	IsrStatus is the register value for channel status register
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
static void SendDataHandler(XUartPs *InstancePtr, u32 IsrStatus)
{

	/*
	 * If there are not bytes to be sent from the specified buffer then disable
	 * the transmit interrupt so it will stop interrupting as it interrupts
	 * any time the FIFO is empty
	 */
	if (InstancePtr->SendBuffer.RemainingBytes == 0) {
		XUartPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUARTPS_IDR_OFFSET,
				(XUARTPS_IXR_TXEMPTY | XUARTPS_IXR_TXFULL));

		/* Call the application handler to indicate the sending is done */
		InstancePtr->Handler(InstancePtr->CallBackRef,
					XUARTPS_EVENT_SENT_DATA,
					InstancePtr->SendBuffer.RequestedBytes -
					InstancePtr->SendBuffer.RemainingBytes);
	}

	/*
	 * If TX FIFO is empty, send more.
	 */
	else if(IsrStatus & XUARTPS_IXR_TXEMPTY) {
		XUartPs_SendBuffer(InstancePtr);
	}

}

/****************************************************************************/
/**
*
* This function handles modem interrupts.  It does not do any processing
* except to call the application handler to indicate a modem event.
*
* @param	InstancePtr is a pointer to the XUartPs instance
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
static void ModemHandler(XUartPs *InstancePtr)
{
	u32 MsrRegister;

	/*
	 * Read the modem status register so that the interrupt is acknowledged
	 * and it can be passed to the callback handler with the event
	 */
	MsrRegister = XUartPs_ReadReg(InstancePtr->Config.BaseAddress,
			  XUARTPS_MODEMSR_OFFSET);

	/*
	 * Call the application handler to indicate the modem status changed,
	 * passing the modem status and the event data in the call
	 */
	InstancePtr->Handler(InstancePtr->CallBackRef,
				  XUARTPS_EVENT_MODEM,
				  MsrRegister);

}

