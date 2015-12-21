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
* @file xiicps_intr.c
* @addtogroup iicps_v2_1
* @{
*
* Contains functions of the XIicPs driver for interrupt-driven transfers.
* See xiicps.h for a detailed description of the device and driver.
*
* <pre> MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- -----------------------------------------------
* 1.00a drg/jz  01/30/10 First release
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xiicps.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************* Variable Definitions *****************************/

/*****************************************************************************/
/**
*
* This function sets the status callback function, the status handler, which the
* driver calls when it encounters conditions that should be reported to the
* higher layer software. The handler executes in an interrupt context, so
* the amount of processing should be minimized
*
* Refer to the xiicps.h file for a list of the Callback events. The events are
* defined to start with XIICPS_EVENT_*.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	CallBackRef is the upper layer callback reference passed back
*		when the callback function is invoked.
* @param	FuncPtr is the pointer to the callback function.
*
* @return	None.
*
* @note
*
* The handler is called within interrupt context, so it should finish its
* work quickly.
*
******************************************************************************/
void XIicPs_SetStatusHandler(XIicPs *InstancePtr, void *CallBackRef,
				  XIicPs_IntrHandler FuncPtr)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(FuncPtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	InstancePtr->StatusHandler = FuncPtr;
	InstancePtr->CallBackRef = CallBackRef;
}
/** @} */
