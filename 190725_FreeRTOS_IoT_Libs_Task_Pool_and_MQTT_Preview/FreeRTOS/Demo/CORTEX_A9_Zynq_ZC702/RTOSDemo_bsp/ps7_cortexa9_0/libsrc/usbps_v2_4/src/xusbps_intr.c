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
/******************************************************************************/
/**
 * @file xusbps_intr.c
* @addtogroup usbps_v2_4
* @{
 *
 * This file contains the functions that are related to interrupt processing
 * for the EPB USB driver.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- ----------------------------------------------------------
 * 1.00a jz  10/10/10 First release
 * 1.03a nm  09/21/12 Fixed CR#678977. Added proper sequence for setup packet
 *                    handling.
 * 2.3   bss 01/19/16 Modified XUsbPs_EpQueueRequest function to fix CR#873972
 *            (moving of dTD Head/Tail Pointers properly).
 * </pre>
 ******************************************************************************/

/***************************** Include Files **********************************/

#include "xusbps.h"
#include "xusbps_endpoint.h"

/************************** Constant Definitions ******************************/

/**************************** Type Definitions ********************************/

/***************** Macros (Inline Functions) Definitions **********************/

/************************** Variable Definitions ******************************/

/************************** Function Prototypes *******************************/

static void XUsbPs_IntrHandleTX(XUsbPs *InstancePtr, u32 EpCompl);
static void XUsbPs_IntrHandleRX(XUsbPs *InstancePtr, u32 EpCompl);
static void XUsbPs_IntrHandleReset(XUsbPs *InstancePtr, u32 IrqSts);
static void XUsbPs_IntrHandleEp0Setup(XUsbPs *InstancePtr);

/*****************************************************************************/
/**
* This function is the first-level interrupt handler for the USB core. All USB
* interrupts will be handled here. Depending on the type of the interrupt,
* second level interrupt handler may be called. Second level interrupt
* handlers will be registered by the user using the:
*    XUsbPs_IntrSetHandler()
* and/or
*    XUsbPs_EpSetHandler()
* functions.
*
*
* @param	HandlerRef is a Reference passed to the interrupt register
*		function. In our case this will be a pointer to the XUsbPs
*		instance.
*
* @return	None
*
* @note		None
*
******************************************************************************/
void XUsbPs_IntrHandler(void *HandlerRef)
{
	XUsbPs	*InstancePtr;

	u32	IrqSts;

	Xil_AssertVoid(HandlerRef != NULL);

	InstancePtr = (XUsbPs *) HandlerRef;

	/* Handle controller (non-endpoint) related interrupts. */
	IrqSts = XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
				XUSBPS_ISR_OFFSET);

	/* Clear the interrupt status register. */
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUSBPS_ISR_OFFSET, IrqSts);

	/* Nak interrupt, used to respond to host's IN request */
	if(IrqSts & XUSBPS_IXR_NAK_MASK) {
		/* Ack the hardware	 */
		XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
					XUSBPS_EPNAKISR_OFFSET,
			XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
						XUSBPS_EPNAKISR_OFFSET));
	}


	/***************************************************************
	 *
	 * Handle general interrupts. Endpoint interrupts will be handler
	 * later.
	 *
	 */

	/* RESET interrupt.*/
	if (IrqSts & XUSBPS_IXR_UR_MASK) {
		XUsbPs_IntrHandleReset(InstancePtr, IrqSts);
		return;
	}

	/* Check if we have a user handler that needs to be called. Note that
	 * this is the handler for general interrupts. Endpoint interrupts will
	 * be handled below.
	 */
	if ((IrqSts & InstancePtr->HandlerMask) && InstancePtr->HandlerFunc) {
		(InstancePtr->HandlerFunc)(InstancePtr->HandlerRef, IrqSts);
	}


	/***************************************************************
	 *
	 * Handle Endpoint interrupts.
	 *
	 */
	if (IrqSts & XUSBPS_IXR_UI_MASK) {
		u32	EpStat;
		u32	EpCompl;

		/* ENDPOINT 0 SETUP PACKET HANDLING
		 *
		 * Check if we got a setup packet on endpoint 0. Currently we
		 * only check for setup packets on endpoint 0 as we would not
		 * expect setup packets on any other endpoint (even though it
		 * is possible to send setup packets on other endpoints).
		 */
		EpStat = XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
						XUSBPS_EPSTAT_OFFSET);
		if (EpStat & 0x0001) {
			/* Handle the setup packet */
			XUsbPs_IntrHandleEp0Setup(InstancePtr);

			/* Re-Prime the endpoint.
			 * Endpoint is de-primed if a setup packet comes in.
	 		 */
			XUsbPs_EpPrime(InstancePtr, 0, XUSBPS_EP_DIRECTION_OUT);
		}

		/* Check for RX and TX complete interrupts. */
		EpCompl = XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
						XUSBPS_EPCOMPL_OFFSET);


		/* ACK the complete interrupts. */
		XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
					XUSBPS_EPCOMPL_OFFSET, EpCompl);

		/* Check OUT (RX) endpoints. */
		if (EpCompl & XUSBPS_EP_OUT_MASK) {
			XUsbPs_IntrHandleRX(InstancePtr, EpCompl);
		}

		/* Check IN (TX) endpoints. */
		if (EpCompl & XUSBPS_EP_IN_MASK) {
			XUsbPs_IntrHandleTX(InstancePtr, EpCompl);
		}
	}
}


/*****************************************************************************/
/**
* This function registers the user callback handler for controller
* (non-endpoint) interrupts.
*
* @param	InstancePtr is a pointer to the XUsbPs instance of the
*		controller.
* @param	CallBackFunc is the Callback function to register.
*		CallBackFunc may be NULL to clear the entry.
* @param	CallBackRef is the user data reference passed to the
*		callback function. CallBackRef may be NULL.
* @param	Mask is the User interrupt mask. Defines which interrupts
*		will cause the callback to be called.
*
* @return
*		- XST_SUCCESS: Callback registered successfully.
*		- XST_FAILURE: Callback could not be registered.
*
* @note		None.
*
******************************************************************************/
int XUsbPs_IntrSetHandler(XUsbPs *InstancePtr,
			   XUsbPs_IntrHandlerFunc CallBackFunc,
			   void *CallBackRef, u32 Mask)
{
	Xil_AssertNonvoid(InstancePtr != NULL);

	InstancePtr->HandlerFunc	= CallBackFunc;
	InstancePtr->HandlerRef		= CallBackRef;
	InstancePtr->HandlerMask	= Mask;

	return XST_SUCCESS;
}


/*****************************************************************************/
/**
* This function handles TX buffer interrupts. It is called by the interrupt
* when a transmit complete interrupt occurs. It returns buffers of completed
* descriptors to the caller.
*
* @param	InstancePtr is a pointer to the XUsbPs instance of the
*		controller.
* @param	EpCompl is the Bit mask of endpoints that caused a transmit
*		complete interrupt.
*
* @return	None
*
* @note		None.
*
******************************************************************************/
static void XUsbPs_IntrHandleTX(XUsbPs *InstancePtr, u32 EpCompl)
{
	int Index;
	u32 Mask;
	int NumEp;

	/* Check all endpoints for TX complete bits.
	 */
	Mask	= 0x00010000;
	NumEp	= InstancePtr->DeviceConfig.NumEndpoints;

	/* Check for every endpoint if its TX complete bit is
	 * set.
	 */
	for (Index = 0; Index < NumEp; Index++, Mask <<= 1) {
		XUsbPs_EpIn	*Ep;

		if (!(EpCompl & Mask)) {
			continue;
		}
		/* The TX complete bit for this endpoint is
		 * set. Walk the list of descriptors to see
		 * which ones are completed.
		 */
		Ep = &InstancePtr->DeviceConfig.Ep[Index].In;
		do {

			XUsbPs_dTDInvalidateCache(Ep->dTDTail);

			/* If the descriptor is not active then the buffer has
			 * not been sent yet.
			 */
			if (XUsbPs_dTDIsActive(Ep->dTDTail)) {
				break;
			}

			if (Ep->HandlerFunc) {
				void *BufPtr;

				BufPtr = (void *) XUsbPs_ReaddTD(Ep->dTDTail,
							XUSBPS_dTDUSERDATA);

				Ep->HandlerFunc(Ep->HandlerRef, Index,
						XUSBPS_EP_EVENT_DATA_TX,
								BufPtr);
			}

			Ep->dTDTail = XUsbPs_dTDGetNLP(Ep->dTDTail);
		} while(Ep->dTDTail != Ep->dTDHead);
	}
}


/*****************************************************************************/
/**
 * This function handles RX buffer interrupts. It is called by the interrupt
 * when a receive complete interrupt occurs. It notifies the callback functions
 * that have been registered with the individual endpoints that data has been
 * received.
 *
 * @param	InstancePtr
 * 		Pointer to the XUsbPs instance of the controller.
 *
 * @param	EpCompl
 * 		Bit mask of endpoints that caused a receive complete interrupt.
 * @return
 *		none
 *
 ******************************************************************************/
static void XUsbPs_IntrHandleRX(XUsbPs *InstancePtr, u32 EpCompl)
{
	XUsbPs_EpOut	*Ep;
	int		Index;
	u32		Mask;
	int		NumEp;

	/* Check all endpoints for RX complete bits. */
	Mask	= 0x00000001;
	NumEp	= InstancePtr->DeviceConfig.NumEndpoints;


	/* Check for every endpoint if its RX complete bit is set.*/
	for (Index = 0; Index < NumEp; Index++, Mask <<= 1) {
		int numP = 0;

		if (!(EpCompl & Mask)) {
			continue;
		}
		Ep = &InstancePtr->DeviceConfig.Ep[Index].Out;

		XUsbPs_dTDInvalidateCache(Ep->dTDCurr);

		/* Handle all finished dTDs */
		while (!XUsbPs_dTDIsActive(Ep->dTDCurr)) {
			numP += 1;
			if (Ep->HandlerFunc) {
				Ep->HandlerFunc(Ep->HandlerRef, Index,
						XUSBPS_EP_EVENT_DATA_RX, NULL);
			}

			Ep->dTDCurr = XUsbPs_dTDGetNLP(Ep->dTDCurr);
			XUsbPs_dTDInvalidateCache(Ep->dTDCurr);
		}
		/* Re-Prime the endpoint.*/
		XUsbPs_EpPrime(InstancePtr, Index, XUSBPS_EP_DIRECTION_OUT);
	}
}


/*****************************************************************************/
/**
* This function handles a RESET interrupt. It will notify the interrupt
* handler callback of the RESET condition.
*
* @param	InstancePtr is pointer to the XUsbPs instance of the controller
* @param	IrqSts is the Interrupt status register content.
*		To be passed on to the user.
*
* @return	None
*
* @Note		None.
*
******************************************************************************/
static void XUsbPs_IntrHandleReset(XUsbPs *InstancePtr, u32 IrqSts)
{
	int Timeout;

	/* Clear all setup token semaphores by reading the
	 * XUSBPS_EPSTAT_OFFSET register and writing its value back to
	 * itself.
	 */
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress, XUSBPS_EPSTAT_OFFSET,
		XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
				XUSBPS_EPSTAT_OFFSET));

	/* Clear all the endpoint complete status bits by reading the
	 * XUSBPS_EPCOMPL_OFFSET register and writings its value back
	 * to itself.
	 */
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
			XUSBPS_EPCOMPL_OFFSET,
		XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
				XUSBPS_EPCOMPL_OFFSET));

	/* Cancel all endpoint prime status by waiting until all bits
	 * in XUSBPS_EPPRIME_OFFSET are 0 and then writing 0xFFFFFFFF
	 * to XUSBPS_EPFLUSH_OFFSET.
	 *
	 * Avoid hanging here by using a Timeout counter...
	 */
	Timeout = XUSBPS_TIMEOUT_COUNTER;
	while ((XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
					XUSBPS_EPPRIME_OFFSET) &
					XUSBPS_EP_ALL_MASK) && --Timeout) {
		/* NOP */
	}
	XUsbPs_WriteReg(InstancePtr->Config.BaseAddress,
				XUSBPS_EPFLUSH_OFFSET, 0xFFFFFFFF);

	/* Make sure that the reset bit in XUSBPS_PORTSCR1_OFFSET is
	 * still set at this point. If the code gets to this point and
	 * the reset bit has already been cleared we are in trouble and
	 * hardware reset is necessary.
	 */
	if (!(XUsbPs_ReadReg(InstancePtr->Config.BaseAddress,
				XUSBPS_PORTSCR1_OFFSET) &
				XUSBPS_PORTSCR_PR_MASK)) {
		/* Send a notification to the user that a hardware
		 * RESET is required. At this point we can only hope
		 * that the user registered an interrupt handler and
		 * will issue a hardware RESET.
		 */
		if (InstancePtr->HandlerFunc) {
			(InstancePtr->HandlerFunc)(InstancePtr->HandlerRef,
						   IrqSts);
		}
		else {
			for (;;);
		}

		/* If we get here there is nothing more to do. The user
		 * should have reset the core.
		 */
		return;
	}

	/* Check if we have a user handler that needs to be called.
	 */
	if (InstancePtr->HandlerFunc) {
		(InstancePtr->HandlerFunc)(InstancePtr->HandlerRef, IrqSts);
	}

	/* We are done. After RESET we don't proceed in the interrupt
	 * handler.
	 */
}


/*****************************************************************************/
/**
* This function handles a Setup Packet interrupt. It will notify the interrupt
* handler callback of the RESET condition.
*
* @param	InstancePtr is a pointer to the XUsbPs instance of the
*		controller.
*
* @return	None
*
* @Note 	None
*
******************************************************************************/
static void XUsbPs_IntrHandleEp0Setup(XUsbPs *InstancePtr)
{

	XUsbPs_EpOut	*Ep;

	/* Notifiy the user. */
	Ep = &InstancePtr->DeviceConfig.Ep[0].Out;

	if (Ep->HandlerFunc) {
		Ep->HandlerFunc(Ep->HandlerRef, 0,
				XUSBPS_EP_EVENT_SETUP_DATA_RECEIVED, NULL);
	}
}


/** @} */
