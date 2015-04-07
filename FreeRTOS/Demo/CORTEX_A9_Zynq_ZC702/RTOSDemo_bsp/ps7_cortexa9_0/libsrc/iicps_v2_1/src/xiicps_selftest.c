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
/*****************************************************************************/
/**
*
* @file xiicps_selftest.c
*
* This component contains the implementation of selftest functions for the
* XIicPs driver component.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------
* 1.00a drg/jz 01/30/10 First release
* 1.00a sdm    09/22/11 Removed unused code
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xiicps.h"

/************************** Constant Definitions *****************************/

#define REG_TEST_VALUE    0x00000005

/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Runs a self-test on the driver/device. The self-test is destructive in that
* a reset of the device is performed in order to check the reset values of
* the registers and to get the device into a known state.
*
* Upon successful return from the self-test, the device is reset.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return
*		- XST_SUCCESS if successful.
*		- XST_REGISTER_ERROR indicates a register did not read or write
*		correctly
*
* @note		None.
*
******************************************************************************/
int XIicPs_SelfTest(XIicPs *InstancePtr)
{

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * All the IIC registers should be in their default state right now.
	 */
	if ((XIICPS_CR_RESET_VALUE !=
		 XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				  XIICPS_CR_OFFSET)) ||
		(XIICPS_TO_RESET_VALUE !=
		 XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				  XIICPS_TIME_OUT_OFFSET)) ||
		(XIICPS_IXR_ALL_INTR_MASK !=
		 XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				  XIICPS_IMR_OFFSET))) {
		return XST_FAILURE;
	}

	XIicPs_Reset(InstancePtr);

	/*
	 * Write, Read then write a register
	 */
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XIICPS_SLV_PAUSE_OFFSET, REG_TEST_VALUE);

	if (REG_TEST_VALUE != XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
						   XIICPS_SLV_PAUSE_OFFSET)) {
		return XST_FAILURE;
	}

	XIicPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XIICPS_SLV_PAUSE_OFFSET, 0);

	XIicPs_Reset(InstancePtr);

	return XST_SUCCESS;
}

