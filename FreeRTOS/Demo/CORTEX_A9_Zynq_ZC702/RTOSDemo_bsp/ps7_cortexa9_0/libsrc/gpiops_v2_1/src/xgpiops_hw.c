/******************************************************************************
*
* Copyright (C) 2013 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xgpiops_hw.c
*
* This file contains low level GPIO functions.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.02a hk   08/22/13 First Release
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xgpiops_hw.h"
#include "xgpiops.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/


/*****************************************************************************/
/*
*
* This function resets the GPIO module by writing reset values to
* all registers
*
* @param	Base address of GPIO module
*
* @return	None
*
* @note		None.
*
******************************************************************************/
void XGpioPs_ResetHw(u32 BaseAddress)
{
	u32 BankCount;

	/*
	 * Write reset values to all mask data registers
	 */
	for(BankCount = 2; BankCount < XGPIOPS_MAX_BANKS; BankCount++) {

		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_DATA_MASK_OFFSET) +
				 XGPIOPS_DATA_LSW_OFFSET), 0x0);
		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_DATA_MASK_OFFSET) +
				 XGPIOPS_DATA_MSW_OFFSET), 0x0);
	}
	/*
	 * Write reset values to all output data registers
	 */
	for(BankCount = 2; BankCount < XGPIOPS_MAX_BANKS; BankCount++) {

		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_DATA_BANK_OFFSET) +
				 XGPIOPS_DATA_OFFSET), 0x0);
	}

	/*
	 * Reset all registers of all 4 banks
	 */
	for(BankCount = 0; BankCount < XGPIOPS_MAX_BANKS; BankCount++) {

		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_REG_MASK_OFFSET) +
				 XGPIOPS_DIRM_OFFSET), 0x0);
		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_REG_MASK_OFFSET) +
				 XGPIOPS_OUTEN_OFFSET), 0x0);
		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_REG_MASK_OFFSET) +
				 XGPIOPS_INTMASK_OFFSET), 0x0);
		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_REG_MASK_OFFSET) +
				 XGPIOPS_INTEN_OFFSET), 0x0);
		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_REG_MASK_OFFSET) +
				 XGPIOPS_INTDIS_OFFSET), 0x0);
		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_REG_MASK_OFFSET) +
				 XGPIOPS_INTSTS_OFFSET), 0x0);
		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_REG_MASK_OFFSET) +
				 XGPIOPS_INTPOL_OFFSET), 0x0);
		XGpioPs_WriteReg(BaseAddress,
				((BankCount * XGPIOPS_REG_MASK_OFFSET) +
				 XGPIOPS_INTANY_OFFSET), 0x0);
	}

	/*
	 * Bank 0 Int type
	 */
	XGpioPs_WriteReg(BaseAddress, XGPIOPS_INTTYPE_OFFSET,
			XGPIOPS_INTTYPE_BANK0_RESET);
	/*
	 * Bank 1 Int type
	 */
	XGpioPs_WriteReg(BaseAddress,
			(XGPIOPS_REG_MASK_OFFSET + XGPIOPS_INTTYPE_OFFSET),
			XGPIOPS_INTTYPE_BANK1_RESET);
	/*
	 * Bank 2 Int type
	 */
	XGpioPs_WriteReg(BaseAddress,
			((2*XGPIOPS_REG_MASK_OFFSET) + XGPIOPS_INTTYPE_OFFSET),
			XGPIOPS_INTTYPE_BANK2_RESET);
	/*
	 * Bank 3 Int type
	 */
	XGpioPs_WriteReg(BaseAddress,
			((3*XGPIOPS_REG_MASK_OFFSET) + XGPIOPS_INTTYPE_OFFSET),
			XGPIOPS_INTTYPE_BANK3_RESET);

}


