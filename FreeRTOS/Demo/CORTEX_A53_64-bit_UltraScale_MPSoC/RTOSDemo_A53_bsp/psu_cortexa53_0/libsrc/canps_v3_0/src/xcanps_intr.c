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
/*****************************************************************************/
/**
*
* @file xcanps_intr.c
*
* This file contains functions related to CAN interrupt handling.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- -----  -------- -----------------------------------------------
* 1.00a xd/sv  01/12/10 First release
* 3.00  kvn    02/13/15 Modified code for MISRA-C:2012 compliance.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xcanps.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

/****************************************************************************/
/**
*
* This routine enables interrupt(s). Use the XCANPS_IXR_* constants defined in
* xcanps_hw.h to create the bit-mask to enable interrupts.
*
* @param	InstancePtr is a pointer to the XCanPs instance.
* @param	Mask is the mask to enable. Bit positions of 1 will be enabled.
*		Bit positions of 0 will keep the previous setting. This mask is
*		formed by OR'ing XCANPS_IXR_* bits defined in xcanps_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XCanPs_IntrEnable(XCanPs *InstancePtr, u32 Mask)
{
	u32 IntrValue;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Write to the IER to enable the specified interrupts.
	 */
	IntrValue = XCanPs_IntrGetEnabled(InstancePtr);
	IntrValue |= Mask & XCANPS_IXR_ALL;
	XCanPs_WriteReg(InstancePtr->CanConfig.BaseAddr,
			XCANPS_IER_OFFSET, IntrValue);
}

/****************************************************************************/
/**
*
* This routine disables interrupt(s). Use the XCANPS_IXR_* constants defined in
* xcanps_hw.h to create the bit-mask to disable interrupt(s).
*
* @param	InstancePtr is a pointer to the XCanPs instance.
* @param	Mask is the mask to disable. Bit positions of 1 will be
*		disabled. Bit positions of 0 will keep the previous setting.
*		This mask is formed by OR'ing XCANPS_IXR_* bits defined in
*		xcanps_hw.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XCanPs_IntrDisable(XCanPs *InstancePtr, u32 Mask)
{
	u32 IntrValue;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Write to the IER to disable the specified interrupts.
	 */
	IntrValue = XCanPs_IntrGetEnabled(InstancePtr);
	IntrValue &= ~Mask;
	XCanPs_WriteReg(InstancePtr->CanConfig.BaseAddr,
			XCANPS_IER_OFFSET, IntrValue);
}

/****************************************************************************/
/**
*
* This routine returns enabled interrupt(s). Use the XCANPS_IXR_* constants
* defined in xcanps_hw.h to interpret the returned value.
*
* @param	InstancePtr is a pointer to the XCanPs instance.
*
* @return	Enabled interrupt(s) in a 32-bit format.
*
* @note		None.
*
*****************************************************************************/
u32 XCanPs_IntrGetEnabled(XCanPs *InstancePtr)
{

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	return XCanPs_ReadReg(InstancePtr->CanConfig.BaseAddr,
				XCANPS_IER_OFFSET);
}


/****************************************************************************/
/**
*
* This routine returns interrupt status read from Interrupt Status Register.
* Use the XCANPS_IXR_* constants defined in xcanps_hw.h to interpret the
* returned value.
*
* @param	InstancePtr is a pointer to the XCanPs instance.
*
* @return	The value stored in Interrupt Status Register.
*
* @note		None.
*
*****************************************************************************/
u32 XCanPs_IntrGetStatus(XCanPs *InstancePtr)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	return XCanPs_ReadReg(InstancePtr->CanConfig.BaseAddr,
				XCANPS_ISR_OFFSET);
}

/****************************************************************************/
/**
*
* This function clears interrupt(s). Every bit set in Interrupt Status
* Register indicates that a specific type of interrupt is occurring, and this
* function clears one or more interrupts by writing a bit mask to Interrupt
* Clear Register.
*
* @param	InstancePtr is a pointer to the XCanPs instance.
* @param	Mask is the mask to clear. Bit positions of 1 will be cleared.
*		Bit positions of 0 will not change the previous interrupt
*		status. This mask is formed by OR'ing XCANPS_IXR_* bits defined
* 		in xcanps_hw.h.
*
* @note		None.
*
*****************************************************************************/
void XCanPs_IntrClear(XCanPs *InstancePtr, u32 Mask)
{
	u32 IntrValue;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Clear the currently pending interrupts.
	 */
	IntrValue = XCanPs_IntrGetStatus(InstancePtr);
	IntrValue &= Mask;
	XCanPs_WriteReg(InstancePtr->CanConfig.BaseAddr, XCANPS_ICR_OFFSET,
				IntrValue);
}

/*****************************************************************************/
/**
*
* This routine is the interrupt handler for the CAN driver.
*
* This handler reads the interrupt status from the ISR, determines the source of
* the interrupts, calls according callbacks, and finally clears the interrupts.
*
* Application beyond this driver is responsible for providing callbacks to
* handle interrupts and installing the callbacks using XCanPs_SetHandler()
* during initialization phase. An example delivered with this driver
* demonstrates how this could be done.
*
* @param	InstancePtr is a pointer to the XCanPs instance that just
*		interrupted.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XCanPs_IntrHandler(void *InstancePtr)
{
	u32 PendingIntr;
	u32 EventIntr;
	XCanPs *CanPtr = (XCanPs *) ((void *)InstancePtr);

	Xil_AssertVoid(CanPtr != NULL);
	Xil_AssertVoid(CanPtr->IsReady == XIL_COMPONENT_IS_READY);

	PendingIntr = XCanPs_IntrGetStatus(CanPtr);
	PendingIntr &= XCanPs_IntrGetEnabled(CanPtr);

	/*
	 * Clear all pending interrupts.
	 * Rising Edge interrupt
	 */
	XCanPs_IntrClear(CanPtr, PendingIntr);

	/*
	 * An error interrupt is occurring.
	 */
	if (((PendingIntr & XCANPS_IXR_ERROR_MASK) != (u32)0) &&
		(CanPtr->ErrorHandler != NULL)) {
			CanPtr->ErrorHandler(CanPtr->ErrorRef,
					XCanPs_GetBusErrorStatus(CanPtr));
		/*
		 * Clear Error Status Register.
		 */
		XCanPs_ClearBusErrorStatus(CanPtr,
					XCanPs_GetBusErrorStatus(CanPtr));
	}

	/*
	 * Check if any following event interrupt is pending:
	 *	  - RX FIFO Overflow
	 *	  - RX FIFO Underflow
	 *	  - TX High Priority Buffer full
	 *	  - TX FIFO Full
	 *	  - Wake up from sleep mode
	 *	  - Enter sleep mode
	 *	  - Enter Bus off status
	 *	  - Arbitration is lost
	 *
	 * If so, call event callback provided by upper level.
	 */
	EventIntr = PendingIntr & ((u32)XCANPS_IXR_RXOFLW_MASK |
				(u32)XCANPS_IXR_RXUFLW_MASK |
				(u32)XCANPS_IXR_TXBFLL_MASK |
				(u32)XCANPS_IXR_TXFLL_MASK |
				(u32)XCANPS_IXR_WKUP_MASK |
				(u32)XCANPS_IXR_SLP_MASK |
				(u32)XCANPS_IXR_BSOFF_MASK |
				(u32)XCANPS_IXR_ARBLST_MASK);
	if ((EventIntr != (u32)0) && (CanPtr->EventHandler != NULL)) {
		CanPtr->EventHandler(CanPtr->EventRef, EventIntr);

		if ((EventIntr & XCANPS_IXR_BSOFF_MASK) != (u32)0) {
			/*
			 * Event callback should reset whole device if "Enter
			 * Bus Off Status" interrupt occurred. All pending
			 * interrupts are cleared and no further checking and
			 * handling of other interrupts is needed any more.
			 */
			return;
		} else {
			/*This else was made for misra-c compliance*/
			;
		}
	}


	if (((PendingIntr & (XCANPS_IXR_RXFWMFLL_MASK |
			XCANPS_IXR_RXNEMP_MASK)) != (u32)0) &&
		(CanPtr->RecvHandler != NULL)) {

		/*
		 * This case happens when
		 * A number of frames depending on the Rx FIFO Watermark
		 * threshold are received.
		 * And  also when frame was received and is sitting in RX FIFO.
		 *
		 * XCANPS_IXR_RXOK_MASK is not used because the bit is set
		 * just once even if there are multiple frames sitting
		 * in the RX FIFO.
		 *
		 * XCANPS_IXR_RXNEMP_MASK is used because the bit can be
		 * set again and again automatically as long as there is
		 * at least one frame in RX FIFO.
		 */
		CanPtr->RecvHandler(CanPtr->RecvRef);
	}

	/*
	 * A frame was transmitted successfully.
	 */
	if (((PendingIntr & XCANPS_IXR_TXOK_MASK) != (u32)0) &&
		(CanPtr->SendHandler != NULL)) {
		CanPtr->SendHandler(CanPtr->SendRef);
	}
}


/*****************************************************************************/
/**
*
* This routine installs an asynchronous callback function for the given
* HandlerType:
*
* <pre>
* HandlerType			Callback Function Type
* -----------------------	------------------------
* XCANPS_HANDLER_SEND		XCanPs_SendRecvHandler
* XCANPS_HANDLER_RECV		XCanPs_SendRecvHandler
* XCANPS_HANDLER_ERROR		XCanPs_ErrorHandler
* XCANPS_HANDLER_EVENT		XCanPs_EventHandler
*
* HandlerType			Invoked by this driver when:
* -------------------------------------------------------------------------
* XCANPS_HANDLER_SEND		A frame transmitted by a call to
*				XCanPs_Send() has been sent successfully.
*
* XCANPS_HANDLER_RECV		A frame(s) has been received and is sitting in
*				the RX FIFO.
*
* XCANPS_HANDLER_ERROR		An error interrupt is occurring.
*
* XCANPS_HANDLER_EVENT		Any other kind of interrupt is occurring.
* </pre>
*
* @param	InstancePtr is a pointer to the XCanPs instance.
* @param	HandlerType specifies which handler is to be attached.
* @param	CallBackFunc is the address of the callback function.
* @param	CallBackRef is a user data item that will be passed to the
*		callback function when it is invoked.
*
* @return
*		- XST_SUCCESS when handler is installed.
*		- XST_INVALID_PARAM when HandlerType is invalid.
*
* @note
* Invoking this function for a handler that already has been installed replaces
* it with the new handler.
*
******************************************************************************/
s32 XCanPs_SetHandler(XCanPs *InstancePtr, u32 HandlerType,
			void *CallBackFunc, void *CallBackRef)
{
	s32 Status;
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	switch (HandlerType) {
		case XCANPS_HANDLER_SEND:
			InstancePtr->SendHandler =
				(XCanPs_SendRecvHandler) CallBackFunc;
			InstancePtr->SendRef = CallBackRef;
			Status = XST_SUCCESS;
			break;

		case XCANPS_HANDLER_RECV:
			InstancePtr->RecvHandler =
				(XCanPs_SendRecvHandler) CallBackFunc;
			InstancePtr->RecvRef = CallBackRef;
			Status = XST_SUCCESS;
			break;

		case XCANPS_HANDLER_ERROR:
			InstancePtr->ErrorHandler =
				(XCanPs_ErrorHandler) CallBackFunc;
			InstancePtr->ErrorRef = CallBackRef;
			Status = XST_SUCCESS;
			break;

		case XCANPS_HANDLER_EVENT:
			InstancePtr->EventHandler =
				(XCanPs_EventHandler) CallBackFunc;
			InstancePtr->EventRef = CallBackRef;
			Status = XST_SUCCESS;
			break;

		default:
			Status = XST_INVALID_PARAM;
			break;
	}
	return Status;
}

