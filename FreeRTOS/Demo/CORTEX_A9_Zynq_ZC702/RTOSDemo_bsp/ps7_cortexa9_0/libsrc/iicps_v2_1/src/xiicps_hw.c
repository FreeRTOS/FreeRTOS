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
* @file xiicps_hw.c
* @addtogroup iicps_v2_1
* @{
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

/** @} */
