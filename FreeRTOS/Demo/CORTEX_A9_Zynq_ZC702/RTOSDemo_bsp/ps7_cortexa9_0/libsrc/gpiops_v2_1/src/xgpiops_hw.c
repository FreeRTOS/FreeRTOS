/******************************************************************************
*
* (c) Copyright 2013-14 Xilinx, Inc. All rights reserved.
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


