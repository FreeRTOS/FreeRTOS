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
/****************************************************************************/
/**
 *
 * @file xusbps_hw.c
* @addtogroup usbps_v2_1
* @{
 *
 * The implementation of the XUsbPs interface reset functionality
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.05a kpc  10/10/10 first version
 * </pre>
 *
 *****************************************************************************/

/***************************** Include Files ********************************/

#include "xstatus.h"
#include "xusbps.h"
#include "xparameters.h"


/************************** Constant Definitions ****************************/
#define XUSBPS_RESET_TIMEOUT 0xFFFFF
/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/


/************************** Function Prototypes *****************************/


/*****************************************************************************/
/**
* This function perform the reset sequence to the given usbps interface by 
* configuring the appropriate control bits in the usbps specifc registers.
* the usbps reset sequence involves the below steps
* 	Disbale the interrupts
*	Clear the status registers
*	Apply the reset command and wait for reset complete status
*	Update the relevant control registers with reset values
* @param   BaseAddress of the interface
*
* @return   N/A.
*
* @note     None.
*
******************************************************************************/
void XUsbPs_ResetHw(u32 BaseAddress)
{
	u32 RegVal;
	u32 Timeout = 0;
	
	/* Host and device mode */
	/* Disable the interrupts */
	XUsbPs_WriteReg(BaseAddress,XUSBPS_IER_OFFSET,0x0);
	/* Clear the interuupt status */
	RegVal = XUsbPs_ReadReg(BaseAddress,XUSBPS_ISR_OFFSET);
	XUsbPs_WriteReg(BaseAddress,XUSBPS_ISR_OFFSET,RegVal);

	/* Perform the reset operation using USB CMD register */	
	RegVal = XUsbPs_ReadReg(BaseAddress,XUSBPS_CMD_OFFSET);
	RegVal = RegVal | XUSBPS_CMD_RST_MASK;
	XUsbPs_WriteReg(BaseAddress,XUSBPS_CMD_OFFSET,RegVal);
	RegVal = XUsbPs_ReadReg(BaseAddress,XUSBPS_CMD_OFFSET);
	/* Wait till the reset operation returns success */
	/*
	* FIX ME: right now no indication to the caller or user about
	* timeout overflow
	*/
	while ((RegVal & XUSBPS_CMD_RST_MASK) && (Timeout < XUSBPS_RESET_TIMEOUT))
	{
		RegVal = XUsbPs_ReadReg(BaseAddress,XUSBPS_CMD_OFFSET);	
		Timeout++;
	}
	/* Update periodic list base address register with reset value */		
	XUsbPs_WriteReg(BaseAddress,XUSBPS_LISTBASE_OFFSET,0x0);	
	/* Update async/endpoint list base address register with reset value */		
	XUsbPs_WriteReg(BaseAddress,XUSBPS_ASYNCLISTADDR_OFFSET,0x0);		
	
}



/** @} */
