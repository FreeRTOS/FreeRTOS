/******************************************************************************
*
* (c) Copyright 2010-11 Xilinx, Inc. All rights reserved.
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
	u32 ErrorStatus;
	XCanPs *CanPtr = (XCanPs *) InstancePtr;

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
	if ((PendingIntr & XCANPS_IXR_ERROR_MASK)) {
		ErrorStatus = XCanPs_GetBusErrorStatus(CanPtr);
		CanPtr->ErrorHandler(CanPtr->ErrorRef, ErrorStatus);

		/*
		 * Clear Error Status Register.
		 */
		XCanPs_ClearBusErrorStatus(CanPtr, ErrorStatus);
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
	EventIntr = PendingIntr & (XCANPS_IXR_RXOFLW_MASK |
				XCANPS_IXR_RXUFLW_MASK |
				XCANPS_IXR_TXBFLL_MASK |
				XCANPS_IXR_TXFLL_MASK |
				XCANPS_IXR_WKUP_MASK |
				XCANPS_IXR_SLP_MASK |
				XCANPS_IXR_BSOFF_MASK |
				XCANPS_IXR_ARBLST_MASK);
	if (EventIntr) {
		CanPtr->EventHandler(CanPtr->EventRef, EventIntr);

		if ((EventIntr & XCANPS_IXR_BSOFF_MASK)) {
			/*
			 * Event callback should reset whole device if "Enter
			 * Bus Off Status" interrupt occurred. All pending
			 * interrupts are cleared and no further checking and
			 * handling of other interrupts is needed any more.
			 */
			return;
		}
	}


	if ((PendingIntr & (XCANPS_IXR_RXFWMFLL_MASK |
			XCANPS_IXR_RXNEMP_MASK))) {

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
	if ((PendingIntr & XCANPS_IXR_TXOK_MASK)) {
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
int XCanPs_SetHandler(XCanPs *InstancePtr, u32 HandlerType,
			void *CallBackFunc, void *CallBackRef)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	switch (HandlerType) {
	case XCANPS_HANDLER_SEND:
		InstancePtr->SendHandler =
			(XCanPs_SendRecvHandler) CallBackFunc;
		InstancePtr->SendRef = CallBackRef;
		break;

	case XCANPS_HANDLER_RECV:
		InstancePtr->RecvHandler =
			(XCanPs_SendRecvHandler) CallBackFunc;
		InstancePtr->RecvRef = CallBackRef;
		break;

	case XCANPS_HANDLER_ERROR:
		InstancePtr->ErrorHandler = (XCanPs_ErrorHandler) CallBackFunc;
		InstancePtr->ErrorRef = CallBackRef;
		break;

	case XCANPS_HANDLER_EVENT:
		InstancePtr->EventHandler = (XCanPs_EventHandler) CallBackFunc;
		InstancePtr->EventRef = CallBackRef;
		break;

	default:
		return (XST_INVALID_PARAM);

	}
	return (XST_SUCCESS);
}

