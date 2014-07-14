/******************************************************************************
*
* (c) Copyright 2010-14 Xilinx, Inc. All rights reserved.
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
/****************************************************************************/
/**
 *
 * @file xusbps_hw.c
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



