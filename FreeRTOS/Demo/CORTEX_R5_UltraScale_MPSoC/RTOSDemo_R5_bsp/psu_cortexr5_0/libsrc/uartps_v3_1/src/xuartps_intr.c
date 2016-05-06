/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xuartps_intr.c
* @addtogroup uartps_v3_1
* @{
*
* This file contains the functions for interrupt handling
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- ------ -------- -----------------------------------------------
* 1.00  drg/jz 01/13/10 First Release
* 3.00  kvn    02/13/15 Modified code for MISRA-C:2012 compliance.
* 3.1	kvn    04/10/15 Modified code for latest RTL changes.
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
static void SendDataHandler(XUartPs *InstancePtr, u32 IsrStatus);
static void ReceiveErrorHandler(XUartPs *InstancePtr, u32 IsrStatus);
static void ReceiveTimeoutHandler(XUartPs *InstancePtr);
static void ModemHandler(XUartPs *InstancePtr);


/* Internal function prototypes implemented in xuartps.c */
extern u32 XUartPs_ReceiveBuffer(XUartPs *InstancePtr);
extern u32 XUartPs_SendBuffer(XUartPs *InstancePtr);

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
	/* Assert validates the input argument */
	Xil_AssertNonvoid(InstancePtr != NULL);

	/* Read the Interrupt Mask register */
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
	u32 TempMask = Mask;
	/* Assert validates the input arguments */
	Xil_AssertVoid(InstancePtr != NULL);

	TempMask &= (u32)XUARTPS_IXR_MASK;

	/* Write the mask to the IER Register */
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress,
		 XUARTPS_IER_OFFSET, TempMask);

	/* Write the inverse of the Mask to the IDR register */
	XUartPs_WriteReg(InstancePtr->Config.BaseAddress,
		 XUARTPS_IDR_OFFSET, (~TempMask));

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

	/* Dispatch an appropriate handler. */
	if((IsrStatus & ((u32)XUARTPS_IXR_RXOVR | (u32)XUARTPS_IXR_RXEMPTY |
			(u32)XUARTPS_IXR_RXFULL)) != (u32)0) {
		/* Received data interrupt */
		ReceiveDataHandler(InstancePtr);
	}

	if((IsrStatus & ((u32)XUARTPS_IXR_TXEMPTY | (u32)XUARTPS_IXR_TXFULL))
									 != (u32)0) {
		/* Transmit data interrupt */
		SendDataHandler(InstancePtr, IsrStatus);
	}

	/* XUARTPS_IXR_RBRK is applicable only for Zynq Ultrascale+ MP */
	if ((IsrStatus & ((u32)XUARTPS_IXR_OVER | (u32)XUARTPS_IXR_FRAMING |
			(u32)XUARTPS_IXR_PARITY | (u32)XUARTPS_IXR_RBRK)) != (u32)0) {
		/* Received Error Status interrupt */
		ReceiveErrorHandler(InstancePtr, IsrStatus);
	}

	if((IsrStatus & ((u32)XUARTPS_IXR_TOUT)) != (u32)0) {
		/* Received Timeout interrupt */
		ReceiveTimeoutHandler(InstancePtr);
	}

	if((IsrStatus & ((u32)XUARTPS_IXR_DMS)) != (u32)0) {
		/* Modem status interrupt */
		ModemHandler(InstancePtr);
	}

	/* Clear the interrupt status. */
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
static void ReceiveErrorHandler(XUartPs *InstancePtr, u32 IsrStatus)
{
	u32 ByteStatusValue, EventData;
	u32 Event;

	InstancePtr->is_rxbs_error = 0;

	if ((InstancePtr->Platform == XPLAT_ZYNQ_ULTRA_MP) &&
		(IsrStatus & ((u32)XUARTPS_IXR_PARITY | (u32)XUARTPS_IXR_RBRK
					| (u32)XUARTPS_IXR_FRAMING))) {
		InstancePtr->is_rxbs_error = 1;
	}
	/*
	 * If there are bytes still to be received in the specified buffer
	 * go ahead and receive them. Removing bytes from the RX FIFO will
	 * clear the interrupt.
	 */

	(void)XUartPs_ReceiveBuffer(InstancePtr);

	if (!(InstancePtr->is_rxbs_error)) {
		Event = XUARTPS_EVENT_RECV_ERROR;
		EventData = InstancePtr->ReceiveBuffer.RequestedBytes -
			InstancePtr->ReceiveBuffer.RemainingBytes;

		/*
		 * Call the application handler to indicate that there is a receive
		 * error or a break interrupt, if the application cares about the
		 * error it call a function to get the last errors.
		 */
		InstancePtr->Handler(InstancePtr->CallBackRef,
					Event,
					EventData);
	}
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
	if (InstancePtr->ReceiveBuffer.RemainingBytes != (u32)0) {
		(void)XUartPs_ReceiveBuffer(InstancePtr);
	}

	/*
	 * If there are no more bytes to receive then indicate that this is
	 * not a receive timeout but the end of the buffer reached, a timeout
	 * normally occurs if # of bytes is not divisible by FIFO threshold,
	 * don't rely on previous test of remaining bytes since receive
	 * function updates it
	 */
	if (InstancePtr->ReceiveBuffer.RemainingBytes != (u32)0) {
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
	 if (InstancePtr->ReceiveBuffer.RemainingBytes != (u32)0) {
		(void)XUartPs_ReceiveBuffer(InstancePtr);
	}

	 /* If the last byte of a message was received then call the application
	 * handler, this code should not use an else from the previous check of
	 * the number of bytes to receive because the call to receive the buffer
	 * updates the bytes ramained
	 */
	if (InstancePtr->ReceiveBuffer.RemainingBytes == (u32)0) {
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
	if (InstancePtr->SendBuffer.RemainingBytes == (u32)0) {
		XUartPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUARTPS_IDR_OFFSET,
				((u32)XUARTPS_IXR_TXEMPTY | (u32)XUARTPS_IXR_TXFULL));

		/* Call the application handler to indicate the sending is done */
		InstancePtr->Handler(InstancePtr->CallBackRef,
					XUARTPS_EVENT_SENT_DATA,
					InstancePtr->SendBuffer.RequestedBytes -
					InstancePtr->SendBuffer.RemainingBytes);
	}

	/* If TX FIFO is empty, send more. */
	else if((IsrStatus & ((u32)XUARTPS_IXR_TXEMPTY)) != (u32)0) {
		(void)XUartPs_SendBuffer(InstancePtr);
	}
	else {
		/* Else with dummy entry for MISRA-C Compliance.*/
		;
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
/** @} */
