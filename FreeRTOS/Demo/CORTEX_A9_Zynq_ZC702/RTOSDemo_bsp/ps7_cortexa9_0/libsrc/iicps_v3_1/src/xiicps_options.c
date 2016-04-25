/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xiicps_options.c
* @addtogroup iicps_v3_0
* @{
*
* Contains functions for the configuration of the XIccPs driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- -----------------------------------------------
* 1.00a drg/jz  01/30/10 First release
* 1.02a sg	08/29/12 Updated the logic to arrive at the best divisors
*			 to achieve I2C clock with minimum error.
*			 This is a fix for CR #674195
* 1.03a hk  05/04/13 Initialized BestDivA and BestDivB to 0.
*			 This is fix for CR#704398 to remove warning.
* 2.0   hk  03/07/14 Limited frequency set when 100KHz or 400KHz is
*                    selected. This is a hardware limitation. CR#779290.
* 2.1   hk  04/24/14 Fix for CR# 761060 - provision for repeated start.
* 2.3	sk	10/07/14 Repeated start feature removed.
* 3.0	sk	12/06/14 Implemented Repeated start feature.
*			01/31/15 Modified the code according to MISRAC 2012 Compliant.
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


/************************** Variable Definitions *****************************/
/*
 * Create the table of options which are processed to get/set the device
 * options. These options are table driven to allow easy maintenance and
 * expansion of the options.
 */
typedef struct {
		u32 Option;
		u32 Mask;
} OptionsMap;

static OptionsMap OptionsTable[] = {
		{XIICPS_7_BIT_ADDR_OPTION, XIICPS_CR_NEA_MASK},
		{XIICPS_10_BIT_ADDR_OPTION, XIICPS_CR_NEA_MASK},
		{XIICPS_SLAVE_MON_OPTION, XIICPS_CR_SLVMON_MASK},
		{XIICPS_REP_START_OPTION, XIICPS_CR_HOLD_MASK},
};

#define XIICPS_NUM_OPTIONS      (sizeof(OptionsTable) / sizeof(OptionsMap))

/*****************************************************************************/
/**
*
* This function sets the options for the IIC device driver. The options control
* how the device behaves relative to the IIC bus. The device must be idle
* rather than busy transferring data before setting these device options.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	Options contains the specified options to be set. This is a bit
*		mask where a 1 means to turn the option on. One or more bit
*		values may be contained in the mask. See the bit definitions
*		named XIICPS_*_OPTION in xiicps.h.
*
* @return
*		- XST_SUCCESS if options are successfully set.
*		- XST_DEVICE_IS_STARTED if the device is currently transferring
*		data. The transfer must complete or be aborted before setting
*		options.
*
* @note		None.
*
******************************************************************************/
s32 XIicPs_SetOptions(XIicPs *InstancePtr, u32 Options)
{
	u32 ControlReg;
	u32 Index;
	u32 OptionsVar = Options;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == (u32)XIL_COMPONENT_IS_READY);

	ControlReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				      XIICPS_CR_OFFSET);

	/*
	 * If repeated start option is requested, set the flag.
	 * The hold bit in CR will be written by driver when the next transfer
	 * is initiated.
	 */
	if ((OptionsVar & XIICPS_REP_START_OPTION) != 0U ) {
		InstancePtr->IsRepeatedStart = 1;
		OptionsVar = OptionsVar & (~XIICPS_REP_START_OPTION);
	}

	/*
	 * Loop through the options table, turning the option on.
	 */
	for (Index = 0U; Index < XIICPS_NUM_OPTIONS; Index++) {
		if ((OptionsVar & OptionsTable[Index].Option) != (u32)0x0U) {
			/*
			 * 10-bit option is specially treated, because it is
			 * using the 7-bit option, so turning it on means
			 * turning 7-bit option off.
			 */
			if ((OptionsTable[Index].Option &
				XIICPS_10_BIT_ADDR_OPTION) != (u32)0x0U) {
				/* Turn 7-bit off */
				ControlReg &= ~OptionsTable[Index].Mask;
			} else {
				/* Turn 7-bit on */
				ControlReg |= OptionsTable[Index].Mask;
			}
		}
	}

	/*
	 * Now write to the control register. Leave it to the upper layers
	 * to restart the device.
	 */
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress, XIICPS_CR_OFFSET,
			  ControlReg);

	/*
	 * Keep a copy of what options this instance has.
	 */
	InstancePtr->Options = XIicPs_GetOptions(InstancePtr);

	return (s32)XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function clears the options for the IIC device driver. The options
* control how the device behaves relative to the IIC bus. The device must be
* idle rather than busy transferring data before setting these device options.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	Options contains the specified options to be cleared. This is a
*		bit mask where a 1 means to turn the option off. One or more bit
*		values may be contained in the mask. See the bit definitions
*		named XIICPS_*_OPTION in xiicps.h.
*
* @return
*		- XST_SUCCESS if options are successfully set.
*		- XST_DEVICE_IS_STARTED if the device is currently transferring
*		data. The transfer must complete or be aborted before setting
*		options.
*
* @note		None
*
******************************************************************************/
s32 XIicPs_ClearOptions(XIicPs *InstancePtr, u32 Options)
{
	u32 ControlReg;
	u32 Index;
	u32 OptionsVar = Options;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == (u32)XIL_COMPONENT_IS_READY);

	ControlReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
					XIICPS_CR_OFFSET);

	/*
	 * If repeated start option is cleared, set the flag.
	 * The hold bit in CR will be cleared by driver when the
	 * following transfer ends.
	 */
	if ((OptionsVar & XIICPS_REP_START_OPTION) != (u32)0x0U ) {
		InstancePtr->IsRepeatedStart = 0;
		OptionsVar = OptionsVar & (~XIICPS_REP_START_OPTION);
	}

	/*
	 * Loop through the options table and clear the specified options.
	 */
	for (Index = 0U; Index < XIICPS_NUM_OPTIONS; Index++) {
		if ((OptionsVar & OptionsTable[Index].Option) != (u32)0x0U) {

			/*
			 * 10-bit option is specially treated, because it is
			 * using the 7-bit option, so clearing it means turning
			 * 7-bit option on.
			 */
			if ((OptionsTable[Index].Option &
				XIICPS_10_BIT_ADDR_OPTION) != (u32)0x0U) {

				/* Turn 7-bit on */
				ControlReg |= OptionsTable[Index].Mask;
			} else {

				/* Turn 7-bit off */
				ControlReg &= ~OptionsTable[Index].Mask;
			}
		}
	}


	/*
	 * Now write the control register. Leave it to the upper layers
	 * to restart the device.
	 */
	XIicPs_WriteReg(InstancePtr->Config.BaseAddress, XIICPS_CR_OFFSET,
			  ControlReg);

	/*
	 * Keep a copy of what options this instance has.
	 */
	InstancePtr->Options = XIicPs_GetOptions(InstancePtr);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function gets the options for the IIC device. The options control how
* the device behaves relative to the IIC bus.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return	32 bit mask of the options, where a 1 means the option is on,
*		and a 0 means to the option is off. One or more bit values may
*		be contained in the mask. See the bit definitions named
* 		XIICPS_*_OPTION in the file xiicps.h.
*
* @note		None.
*
******************************************************************************/
u32 XIicPs_GetOptions(XIicPs *InstancePtr)
{
	u32 OptionsFlag = 0U;
	u32 ControlReg;
	u32 Index;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == (u32)XIL_COMPONENT_IS_READY);

	/*
	 * Read control register to find which options are currently set.
	 */
	ControlReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				      XIICPS_CR_OFFSET);

	/*
	 * Loop through the options table to determine which options are set.
	 */
	for (Index = 0U; Index < XIICPS_NUM_OPTIONS; Index++) {
		if ((ControlReg & OptionsTable[Index].Mask) != (u32)0x0U) {
			OptionsFlag |= OptionsTable[Index].Option;
		}
		if ((ControlReg & XIICPS_CR_NEA_MASK) == (u32)0x0U) {
			OptionsFlag |= XIICPS_10_BIT_ADDR_OPTION;
		}
	}

	if (InstancePtr->IsRepeatedStart != 0 ) {
		OptionsFlag |= XIICPS_REP_START_OPTION;
	}
	return OptionsFlag;
}

/*****************************************************************************/
/**
*
* This function sets the serial clock rate for the IIC device. The device
* must be idle rather than busy transferring data before setting these device
* options.
*
* The data rate is set by values in the control register. The formula for
* determining the correct register values is:
* Fscl = Fpclk/(22 x (divisor_a+1) x (divisor_b+1))
* See the hardware data sheet for a full explanation of setting the serial
* clock rate.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
* @param	FsclHz is the clock frequency in Hz. The two most common clock
*		rates are 100KHz and 400KHz.
*
* @return
*		- XST_SUCCESS if options are successfully set.
*		- XST_DEVICE_IS_STARTED if the device is currently transferring
*		data. The transfer must complete or be aborted before setting
*		options.
*		- XST_FAILURE if the Fscl frequency can not be set.
*
* @note		The clock can not be faster than the input clock divide by 22.
*
******************************************************************************/
s32 XIicPs_SetSClk(XIicPs *InstancePtr, u32 FsclHz)
{
	u32 Div_a;
	u32 Div_b;
	u32 ActualFscl;
	u32 Temp;
	u32 TempLimit;
	u32 LastError;
	u32 BestError;
	u32 CurrentError;
	u32 ControlReg;
	u32 CalcDivA;
	u32 CalcDivB;
	u32 BestDivA = 0;
	u32 BestDivB = 0;
	u32 FsclHzVar = FsclHz;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == (u32)XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(FsclHzVar > 0U);

	if (0U != XIicPs_In32((InstancePtr->Config.BaseAddress) +
					XIICPS_TRANS_SIZE_OFFSET)) {
		return (s32)XST_DEVICE_IS_STARTED;
	}

	/*
	 * Assume Div_a is 0 and calculate (divisor_a+1) x (divisor_b+1).
	 */
	Temp = (InstancePtr->Config.InputClockHz) / ((u32)22U * FsclHzVar);

	/*
	 * If the answer is negative or 0, the Fscl input is out of range.
	 */
	if ((u32)(0U) == Temp) {
		return (s32)XST_FAILURE;
	}

	/*
	 * If frequency 400KHz is selected, 384.6KHz should be set.
	 * If frequency 100KHz is selected, 90KHz should be set.
	 * This is due to a hardware limitation.
	 */
	if(FsclHzVar > 384600U) {
		FsclHzVar = 384600U;
	}

	if((FsclHzVar <= 100000U) && (FsclHzVar > 90000U)) {
		FsclHzVar = 90000U;
	}

	/*
	 * TempLimit helps in iterating over the consecutive value of Temp to
	 * find the closest clock rate achievable with divisors.
	 * Iterate over the next value only if fractional part is involved.
	 */
	TempLimit = (((InstancePtr->Config.InputClockHz) %
			((u32)22 * FsclHzVar)) != 	(u32)0x0U) ?
						Temp + (u32)1U : Temp;
	BestError = FsclHzVar;

	BestDivA = 0U;
	BestDivB = 0U;
	for ( ; Temp <= TempLimit ; Temp++)
	{
		LastError = FsclHzVar;
		CalcDivA = 0U;
		CalcDivB = 0U;

		for (Div_b = 0U; Div_b < 64U; Div_b++) {

			Div_a = Temp / (Div_b + 1U);

			if (Div_a != 0U){
				Div_a = Div_a - (u32)1U;
			}
			if (Div_a > 3U){
				continue;
			}
			ActualFscl = (InstancePtr->Config.InputClockHz) /
						(22U * (Div_a + 1U) * (Div_b + 1U));

			if (ActualFscl > FsclHzVar){
				CurrentError = (ActualFscl - FsclHzVar);}
			else{
				CurrentError = (FsclHzVar - ActualFscl);}

			if (LastError > CurrentError) {
				CalcDivA = Div_a;
				CalcDivB = Div_b;
				LastError = CurrentError;
			}
		}

		/*
		 * Used to capture the best divisors.
		 */
		if (LastError < BestError) {
			BestError = LastError;
			BestDivA = CalcDivA;
			BestDivB = CalcDivB;
		}
	}


	/*
	 * Read the control register and mask the Divisors.
	 */
	ControlReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
					  (u32)XIICPS_CR_OFFSET);
	ControlReg &= ~((u32)XIICPS_CR_DIV_A_MASK | (u32)XIICPS_CR_DIV_B_MASK);
	ControlReg |= (BestDivA << XIICPS_CR_DIV_A_SHIFT) |
		(BestDivB << XIICPS_CR_DIV_B_SHIFT);

	XIicPs_WriteReg(InstancePtr->Config.BaseAddress, (u32)XIICPS_CR_OFFSET,
			  ControlReg);

	return (s32)XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function gets the serial clock rate for the IIC device. The device
* must be idle rather than busy transferring data before setting these device
* options.
*
* @param	InstancePtr is a pointer to the XIicPs instance.
*
* @return	The value of the IIC clock to the nearest Hz based on the
*		control register settings. The actual value may not be exact to
*		to integer math rounding errors.
*
* @note		None.
*
******************************************************************************/
u32 XIicPs_GetSClk(XIicPs *InstancePtr)
{
	u32 ControlReg;
	u32 ActualFscl;
	u32 Div_a;
	u32 Div_b;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == (u32)XIL_COMPONENT_IS_READY);

	ControlReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
					  XIICPS_CR_OFFSET);

	Div_a = (ControlReg & XIICPS_CR_DIV_A_MASK) >> XIICPS_CR_DIV_A_SHIFT;
	Div_b = (ControlReg & XIICPS_CR_DIV_B_MASK) >> XIICPS_CR_DIV_B_SHIFT;

	ActualFscl = (InstancePtr->Config.InputClockHz) /
		(22U * (Div_a + 1U) * (Div_b + 1U));

	return ActualFscl;
}
/** @} */
