/* $Id: xemacps_intr.c,v 1.1.2.1 2011/01/20 03:39:02 sadanan Exp $ */
/******************************************************************************
*
* (c) Copyright 2010 Xilinx, Inc. All rights reserved.
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
