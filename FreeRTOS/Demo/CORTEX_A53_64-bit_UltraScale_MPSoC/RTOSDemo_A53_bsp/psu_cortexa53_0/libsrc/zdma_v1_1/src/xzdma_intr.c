/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc.  All rights reserved.
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
* @file xzdma_intr.c
* @addtogroup zdma_v1_0
* @{
*
* This file contains interrupt related functions of Xilinx ZDMA core.
* Please see xzdma.h for more details of the driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- ------------------------------------------------------
* 1.0   vns     2/27/15  First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xzdma.h"

/***************** Macros (Inline Functions) Definitions *********************/


/**************************** Type Definitions *******************************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/************************** Function Definitions *****************************/


/*****************************************************************************/
/**
*
* This function is the interrupt handler for the ZDMA core.
*
* This handler reads the pending interrupt from Status register, determines the
* source of the interrupts and calls the respective callbacks for the
* interrupts that are enabled in IRQ_ENABLE register, and finally clears the
* interrupts.
*
* The application is responsible for connecting this function to the interrupt
* system. Application beyond this driver is also responsible for providing
* callbacks to handle interrupts and installing the callbacks using
* XZDma_SetCallBack() during initialization phase. .
*
* @param	Instance is a pointer to the XZDma instance to be worked on.
*
* @return	None.
*
* @note		To generate interrupt required interrupts should be enabled.
*
******************************************************************************/
void XZDma_IntrHandler(void *Instance)
{
	u32 PendingIntr;
	u32 ErrorStatus;
	XZDma *InstancePtr = NULL;
	InstancePtr = (XZDma *)((void *)Instance);

	/* Verify arguments. */
	Xil_AssertVoid(InstancePtr != NULL);

	/* Get pending interrupts */
	PendingIntr = (u32)(XZDma_IntrGetStatus(InstancePtr));
	PendingIntr &= (~XZDma_GetIntrMask(InstancePtr));

	/* ZDMA transfer has completed */
	ErrorStatus = (PendingIntr) & (XZDMA_IXR_DMA_DONE_MASK);
	if ((ErrorStatus) != 0U) {
		XZDma_DisableIntr(InstancePtr, XZDMA_IXR_ALL_INTR_MASK);
		InstancePtr->ChannelState = XZDMA_IDLE;
		InstancePtr->DoneHandler(InstancePtr->DoneRef);
	}

	/* An error has been occurred */
	ErrorStatus = PendingIntr & (XZDMA_IXR_ERR_MASK);
	if ((ErrorStatus) != 0U) {
		if ((ErrorStatus & XZDMA_IXR_DMA_PAUSE_MASK) ==
				XZDMA_IXR_DMA_PAUSE_MASK) {
			InstancePtr->ChannelState = XZDMA_PAUSE;
		}
		else {
			if ((ErrorStatus & (XZDMA_IXR_AXI_WR_DATA_MASK |
				XZDMA_IXR_AXI_RD_DATA_MASK |
				XZDMA_IXR_AXI_RD_DST_DSCR_MASK |
				XZDMA_IXR_AXI_RD_SRC_DSCR_MASK)) != 0x00U) {
				InstancePtr->ChannelState = XZDMA_IDLE;
			}
		}
		InstancePtr->ErrorHandler(InstancePtr->ErrorRef, ErrorStatus);
	}

	/* Clear pending interrupt(s) */
	XZDma_IntrClear(InstancePtr, PendingIntr);
}

/*****************************************************************************/
/**
*
* This routine installs an asynchronous callback function for the given
* HandlerType.
*
* <pre>
* HandlerType              Callback Function Type
* -----------------------  --------------------------------------------------
* XZDMA_HANDLER_DONE	   Done handler
* XZDMA_HANDLER_ERROR	   Error handler
*
* </pre>
*
* @param	InstancePtr is a pointer to the XZDma instance to be worked on.
* @param	HandlerType specifies which callback is to be attached.
* @param	CallBackFunc is the address of the callback function.
* @param	CallBackRef is a user data item that will be passed to the
* 		callback function when it is invoked.
*
* @return
*		- XST_SUCCESS when handler is installed.
*		- XST_INVALID_PARAM when HandlerType is invalid.
*
* @note		Invoking this function for a handler that already has been
*		installed replaces it with the new handler.
*
******************************************************************************/
s32 XZDma_SetCallBack(XZDma *InstancePtr, XZDma_Handler HandlerType,
	void *CallBackFunc, void *CallBackRef)
{
	s32 Status;

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(CallBackFunc != NULL);
	Xil_AssertNonvoid(CallBackRef != NULL);
	Xil_AssertNonvoid((HandlerType == XZDMA_HANDLER_DONE) ||
				(HandlerType == XZDMA_HANDLER_ERROR));
	Xil_AssertNonvoid(InstancePtr->IsReady ==
				(u32)(XIL_COMPONENT_IS_READY));

	/*
	 * Calls the respective callback function corresponding to
	 * the handler type
	 */
	switch (HandlerType) {
		case XZDMA_HANDLER_DONE:
			InstancePtr->DoneHandler =
				(XZDma_DoneHandler)((void *)CallBackFunc);
			InstancePtr->DoneRef = CallBackRef;
			Status = (XST_SUCCESS);
			break;

		case XZDMA_HANDLER_ERROR:
			InstancePtr->ErrorHandler =
				(XZDma_ErrorHandler)((void *)CallBackFunc);
			InstancePtr->ErrorRef = CallBackRef;
			Status = (XST_SUCCESS);
			break;

		default:
			Status = (XST_INVALID_PARAM);
			break;
	}

	return Status;
}
/** @} */
