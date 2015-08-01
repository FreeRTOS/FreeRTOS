/* $Id: xemacps_intr.c,v 1.1.2.1 2011/01/20 03:39:02 sadanan Exp $ */
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
/*****************************************************************************/
/**
*
* @file xemacps_intr.c
*
* Functions in this file implement general purpose interrupt processing related
* functionality. See xemacps.h for a detailed description of the driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a wsy  01/10/10 First release
* 1.03a asa  01/24/13 Fix for CR #692702 which updates error handling for
*		      Rx errors. Under heavy Rx traffic, there will be a large
*		      number of errors related to receive buffer not available.
*		      Because of a HW bug (SI #692601), under such heavy errors,
*		      the Rx data path can become unresponsive. To reduce the
*		      probabilities for hitting this HW bug, the SW writes to
*		      bit 18 to flush a packet from Rx DPRAM immediately. The
*		      changes for it are done in the function
*		      XEmacPs_IntrHandler.
* </pre>
******************************************************************************/

/***************************** Include Files *********************************/

#include "xemacps.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
 * Install an asynchronious handler function for the given HandlerType:
 *
 * @param InstancePtr is a pointer to the instance to be worked on.
 * @param HandlerType indicates what interrupt handler type is.
 *        XEMACPS_HANDLER_DMASEND, XEMACPS_HANDLER_DMARECV and
 *        XEMACPS_HANDLER_ERROR.
 * @param FuncPtr is the pointer to the callback function
 * @param CallBackRef is the upper layer callback reference passed back when
 *        when the callback function is invoked.
 *
 * @return
 *
 * None.
 *
 * @note
 * There is no assert on the CallBackRef since the driver doesn't know what
 * it is.
 *
 *****************************************************************************/
int XEmacPs_SetHandler(XEmacPs *InstancePtr, u32 HandlerType,
			void *FuncPtr, void *CallBackRef)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(FuncPtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	switch (HandlerType) {
	case XEMACPS_HANDLER_DMASEND:
		InstancePtr->SendHandler = (XEmacPs_Handler) FuncPtr;
		InstancePtr->SendRef = CallBackRef;
		break;
	case XEMACPS_HANDLER_DMARECV:
		InstancePtr->RecvHandler = (XEmacPs_Handler) FuncPtr;
		InstancePtr->RecvRef = CallBackRef;
		break;
	case XEMACPS_HANDLER_ERROR:
		InstancePtr->ErrorHandler = (XEmacPs_ErrHandler) FuncPtr;
		InstancePtr->ErrorRef = CallBackRef;
		break;
	default:
		return (XST_INVALID_PARAM);
	}
	return (XST_SUCCESS);
}

/*****************************************************************************/
/**
* Master interrupt handler for EMAC driver. This routine will query the
* status of the device, bump statistics, and invoke user callbacks.
*
* This routine must be connected to an interrupt controller using OS/BSP
* specific methods.
*
* @param XEmacPsPtr is a pointer to the XEMACPS instance that has caused the
*        interrupt.
*
******************************************************************************/
void XEmacPs_IntrHandler(void *XEmacPsPtr)
{
	u32 RegISR;
	u32 RegSR;
	u32 RegCtrl;
	XEmacPs *InstancePtr = (XEmacPs *) XEmacPsPtr;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* This ISR will try to handle as many interrupts as it can in a single
	 * call. However, in most of the places where the user's error handler
         * is called, this ISR exits because it is expected that the user will
         * reset the device in nearly all instances.
	 */
	RegISR = XEmacPs_ReadReg(InstancePtr->Config.BaseAddress,
				   XEMACPS_ISR_OFFSET);

	/* Clear the interrupt status register */
	XEmacPs_WriteReg(InstancePtr->Config.BaseAddress, XEMACPS_ISR_OFFSET,
			   RegISR);

	/* Receive complete interrupt */
	if (RegISR & (XEMACPS_IXR_FRAMERX_MASK)) {
		/* Clear RX status register RX complete indication but preserve
		 * error bits if there is any */
		XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
				   XEMACPS_RXSR_OFFSET,
				   XEMACPS_RXSR_FRAMERX_MASK |
				   XEMACPS_RXSR_BUFFNA_MASK);
		InstancePtr->RecvHandler(InstancePtr->RecvRef);
	}

	/* Transmit complete interrupt */
	if (RegISR & (XEMACPS_IXR_TXCOMPL_MASK)) {
		/* Clear TX status register TX complete indication but preserve
		 * error bits if there is any */
		XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
				   XEMACPS_TXSR_OFFSET,
				   XEMACPS_TXSR_TXCOMPL_MASK |
				   XEMACPS_TXSR_USEDREAD_MASK);
		InstancePtr->SendHandler(InstancePtr->SendRef);
	}

	/* Receive error conditions interrupt */
	if (RegISR & (XEMACPS_IXR_RX_ERR_MASK)) {
		/* Clear RX status register */
		RegSR = XEmacPs_ReadReg(InstancePtr->Config.BaseAddress,
					  XEMACPS_RXSR_OFFSET);
		XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
				   XEMACPS_RXSR_OFFSET, RegSR);

		/* Fix for CR # 692702. Write to bit 18 of net_ctrl
		 * register to flush a packet out of Rx SRAM upon
		 * an error for receive buffer not available. */
		if (RegISR & XEMACPS_IXR_RXUSED_MASK) {
			RegCtrl =
			XEmacPs_ReadReg(InstancePtr->Config.BaseAddress,
						XEMACPS_NWCTRL_OFFSET);
			RegCtrl |= XEMACPS_NWCTRL_FLUSH_DPRAM_MASK;
			XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
					XEMACPS_NWCTRL_OFFSET, RegCtrl);
		}
		InstancePtr->ErrorHandler(InstancePtr->ErrorRef, XEMACPS_RECV,
					  RegSR);
	}

        /* When XEMACPS_IXR_TXCOMPL_MASK is flaged, XEMACPS_IXR_TXUSED_MASK
         * will be asserted the same time.
         * Have to distinguish this bit to handle the real error condition.
         */
	/* Transmit error conditions interrupt */
        if (RegISR & (XEMACPS_IXR_TX_ERR_MASK) &&
            !(RegISR & (XEMACPS_IXR_TXCOMPL_MASK))) {
		/* Clear TX status register */
		RegSR = XEmacPs_ReadReg(InstancePtr->Config.BaseAddress,
					  XEMACPS_TXSR_OFFSET);
		XEmacPs_WriteReg(InstancePtr->Config.BaseAddress,
				   XEMACPS_TXSR_OFFSET, RegSR);
		InstancePtr->ErrorHandler(InstancePtr->ErrorRef, XEMACPS_SEND,
					  RegSR);
	}

}
