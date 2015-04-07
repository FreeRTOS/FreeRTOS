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
* @file xiicps_hw.c
*
* Contains implementation of required functions for providing the reset sequence
* to the i2c interface
*
* <pre> MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- --------------------------------------------
* 1.04a kpc     11/07/13 First release
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xiicps_hw.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/
/*****************************************************************************/
/**
* This function perform the reset sequence to the given I2c interface by 
* configuring the appropriate control bits in the I2c specifc registers
* the i2cps reset squence involves the following steps
*	Disable all the interuupts 
*	Clear the status
*	Clear FIFO's and disable hold bit
*	Clear the line status
*	Update relevant config registers with reset values
*
* @param   BaseAddress of the interface
*
* @return N/A
*
* @note 
* This function will not modify the slcr registers that are relavant for 
* I2c controller
******************************************************************************/
void XIicPs_ResetHw(u32 BaseAddress)
{
	u32 RegVal;
	
	/* Disable all the interrupts */
	XIicPs_WriteReg(BaseAddress, XIICPS_IDR_OFFSET, XIICPS_IXR_ALL_INTR_MASK);
	/* Clear the interrupt status */	
	RegVal = XIicPs_ReadReg(BaseAddress,XIICPS_ISR_OFFSET);
	XIicPs_WriteReg(BaseAddress, XIICPS_ISR_OFFSET, RegVal);	
	/* Clear the hold bit,master enable bit and ack bit */		
	RegVal = XIicPs_ReadReg(BaseAddress,XIICPS_CR_OFFSET);
	RegVal &= ~(XIICPS_CR_HOLD_MASK|XIICPS_CR_MS_MASK|XIICPS_CR_ACKEN_MASK);
	/* Clear the fifos */			
	RegVal |= XIICPS_CR_CLR_FIFO_MASK;	
	XIicPs_WriteReg(BaseAddress, XIICPS_CR_OFFSET, RegVal);	
	/* Clear the timeout register */
	XIicPs_WriteReg(BaseAddress, XIICPS_TIME_OUT_OFFSET, 0x0);	
	/* Clear the transfer size register */	
	XIicPs_WriteReg(BaseAddress, XIICPS_TRANS_SIZE_OFFSET, 0x0);
	/* Clear the status register */	
	RegVal = XIicPs_ReadReg(BaseAddress,XIICPS_SR_OFFSET);
	XIicPs_WriteReg(BaseAddress, XIICPS_SR_OFFSET, RegVal);	
	/* Update the configuraqtion register with reset value */		
	XIicPs_WriteReg(BaseAddress, XIICPS_CR_OFFSET, 0x0);		
}

