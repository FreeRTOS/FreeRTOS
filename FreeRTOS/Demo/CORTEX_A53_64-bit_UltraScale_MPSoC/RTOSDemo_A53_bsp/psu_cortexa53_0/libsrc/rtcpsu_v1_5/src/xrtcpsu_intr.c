/******************************************************************************
*
* Copyright (C) 2015 Xilinx, Inc.  All rights reserved.
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
* XILINX BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
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
* @file xrtcpsu_intr.c
* @addtogroup rtcpsu_v1_5
* @{
*
* This file contains functions related to RTC interrupt handling.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- -----  -------- -----------------------------------------------
* 1.00  kvn    04/21/15 First release
* 1.3   vak    04/25/16 Changed the XRtcPsu_InterruptHandler() for updating RTC
*                       read and write time logic(cr#948833).
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xrtcpsu.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions ****************************/

/****************************************************************************/
/**
*
* This function sets the interrupt mask.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance
* @param	Mask contains the interrupts to be enabled.
*		A '1' enables an interupt, and a '0' disables.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XRtcPsu_SetInterruptMask(XRtcPsu *InstancePtr, u32 Mask)
{
	/*
	 * Clear the Status register to be sure of no pending interrupts.
	 * Writing mask values to interrupt bits as it is a WTC register.
	 */
	XRtcPsu_WriteReg(InstancePtr->RtcConfig.BaseAddr + XRTC_INT_STS_OFFSET,
			((u32)XRTC_INT_STS_ALRM_MASK | (u32)XRTC_INT_STS_SECS_MASK));

	/*
	 * XRTC_INT_MSK_RSTVAL contains the valid interrupts
	 * for the RTC device. The AND operation on Mask makes sure one
	 * of the valid bits are only set.
	 */

	/* Write the mask to the IER Register */
	XRtcPsu_WriteReg(InstancePtr->RtcConfig.BaseAddr+XRTC_INT_EN_OFFSET,
					(Mask & (u32)XRTC_INT_MSK_RSTVAL));

}

/****************************************************************************/
/**
*
* This function clears the interrupt mask.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance
* @param	Mask contains the interrupts to be disabled.
*		A '1' enables an interrupt, and a '0' disables.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XRtcPsu_ClearInterruptMask(XRtcPsu *InstancePtr, u32 Mask)
{
	/*
	 * XRTC_INT_MSK_RSTVAL contains the valid interrupts
	 * for the RTC device. The AND operation on mask makes sure one
	 * of the valid bits are only cleared.
	 */

	/* Write the Mask to the IDR register */
	XRtcPsu_WriteReg(InstancePtr->RtcConfig.BaseAddr+XRTC_INT_DIS_OFFSET,
					(Mask & (u32)XRTC_INT_MSK_RSTVAL));
}

/****************************************************************************/
/**
*
* This function sets the handler that will be called when an event (interrupt)
* occurs that needs application's attention.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance
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
void XRtcPsu_SetHandler(XRtcPsu *InstancePtr, XRtcPsu_Handler FuncPtr,
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
void XRtcPsu_InterruptHandler(XRtcPsu *InstancePtr)
{
	u32 IsrStatus;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the interrupt ID register to determine which
	 * interrupt is active.
	 */
	IsrStatus = ~(XRtcPsu_ReadReg(InstancePtr->RtcConfig.BaseAddr +
			XRTC_INT_MSK_OFFSET));

	IsrStatus &= XRtcPsu_ReadReg(InstancePtr->RtcConfig.BaseAddr +
			XRTC_INT_STS_OFFSET);

	/*
	 * Clear the interrupt status to allow future
	 * interrupts before this generated interrupt is serviced.
	 */
	XRtcPsu_WriteReg(InstancePtr->RtcConfig.BaseAddr +
			XRTC_INT_STS_OFFSET, IsrStatus);

	/* Handle the generated interrupts appropriately. */

	/* Alarm interrupt */
	if((IsrStatus & XRTC_INT_STS_ALRM_MASK) != (u32)0) {

		if(InstancePtr->IsPeriodicAlarm != 0U) {
			XRtcPsu_SetAlarm(InstancePtr,
					(XRtcPsu_GetCurrentTime(InstancePtr)+InstancePtr->PeriodicAlarmTime),1U);
		}

		/*
		 * Call the application handler to indicate that there is an
		 * alarm interrupt. If the application cares about this alarm,
		 * it will act accordingly through its own handler.
		 */
		InstancePtr->Handler(InstancePtr->CallBackRef,
					XRTCPSU_EVENT_ALARM_GEN);
	}

	/* Seconds interrupt */
	if((IsrStatus & XRTC_INT_STS_SECS_MASK) != (u32)0) {
		/* Set the CurrTimeUpdated flag to 1 */
		InstancePtr->CurrTimeUpdated = 1;

		if(InstancePtr->TimeUpdated == (u32)1) {
			/* Clear the TimeUpdated */
			InstancePtr->TimeUpdated = (u32)0;
		}

		/*
		 * Call the application handler to indicate that there is an
		 * seconds interrupt. If the application cares about this seconds
		 * interrupt, it will act accordingly through its own handler.
		 */
		InstancePtr->Handler(InstancePtr->CallBackRef,
					XRTCPSU_EVENT_SECS_GEN);
	}

}
/** @} */
