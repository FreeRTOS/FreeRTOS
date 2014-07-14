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
* @file xiicps_options.c
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
int XIicPs_SetOptions(XIicPs *InstancePtr, u32 Options)
{
	u32 ControlReg;
	unsigned int Index;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	ControlReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				      XIICPS_CR_OFFSET);

	/*
	 * If repeated start option is requested, set the flag.
	 * The hold bit in CR will be written by driver when the next transfer
	 * is initiated.
	 */
	if (Options & XIICPS_REP_START_OPTION) {
		InstancePtr->IsRepeatedStart = 1;
		Options = Options & (~XIICPS_REP_START_OPTION);
	}

	/*
	 * Loop through the options table, turning the option on.
	 */
	for (Index = 0; Index < XIICPS_NUM_OPTIONS; Index++) {
 		if (Options & OptionsTable[Index].Option) {
			/*
			 * 10-bit option is specially treated, because it is
			 * using the 7-bit option, so turning it on means
			 * turning 7-bit option off.
			 */
			if (OptionsTable[Index].Option &
				XIICPS_10_BIT_ADDR_OPTION) {
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

	return XST_SUCCESS;
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
int XIicPs_ClearOptions(XIicPs *InstancePtr, u32 Options)
{
	u32 ControlReg;
	unsigned int Index;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	ControlReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
					XIICPS_CR_OFFSET);

	/*
	 * If repeated start option is cleared, set the flag.
	 * The hold bit in CR will be cleared by driver when the
	 * following transfer ends.
	 */
	if (Options & XIICPS_REP_START_OPTION) {
		InstancePtr->IsRepeatedStart = 0;
		Options = Options & (~XIICPS_REP_START_OPTION);
	}

	/*
	 * Loop through the options table and clear the specified options.
	 */
	for (Index = 0; Index < XIICPS_NUM_OPTIONS; Index++) {
 		if (Options & OptionsTable[Index].Option) {

			/*
			 * 10-bit option is specially treated, because it is
			 * using the 7-bit option, so clearing it means turning
			 * 7-bit option on.
			 */
			if (OptionsTable[Index].Option &
						XIICPS_10_BIT_ADDR_OPTION) {

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
	u32 OptionsFlag = 0;
	u32 ControlReg;
	unsigned int Index;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read control register to find which options are currently set.
	 */
	ControlReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
				      XIICPS_CR_OFFSET);

	/*
	 * Loop through the options table to determine which options are set.
	 */
	for (Index = 0; Index < XIICPS_NUM_OPTIONS; Index++) {
		if (ControlReg & OptionsTable[Index].Mask) {
			OptionsFlag |= OptionsTable[Index].Option;
		}
		if ((ControlReg & XIICPS_CR_NEA_MASK) == 0) {
			OptionsFlag |= XIICPS_10_BIT_ADDR_OPTION;
		}
	}

	if (InstancePtr->IsRepeatedStart) {
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
int XIicPs_SetSClk(XIicPs *InstancePtr, u32 FsclHz)
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

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(FsclHz > 0);

	if (0 != XIicPs_In32((InstancePtr->Config.BaseAddress) +
					XIICPS_TRANS_SIZE_OFFSET)) {
		return XST_DEVICE_IS_STARTED;
	}

	/*
	 * Assume Div_a is 0 and calculate (divisor_a+1) x (divisor_b+1).
	 */
	Temp = (InstancePtr->Config.InputClockHz) / (22 * FsclHz);

	/*
	 * If the answer is negative or 0, the Fscl input is out of range.
	 */
	if (0 == Temp) {
		return XST_FAILURE;
	}

	/*
	 * If frequency 400KHz is selected, 384.6KHz should be set.
	 * If frequency 100KHz is selected, 90KHz should be set.
	 * This is due to a hardware limitation.
	 */
	if(FsclHz > 384600) {
		FsclHz = 384600;
	}

	if((FsclHz <= 100000) && (FsclHz > 90000)) {
		FsclHz = 90000;
	}

	/*
	 * TempLimit helps in iterating over the consecutive value of Temp to
	 * find the closest clock rate achievable with divisors.
	 * Iterate over the next value only if fractional part is involved.
	 */
	TempLimit = ((InstancePtr->Config.InputClockHz) % (22 * FsclHz)) ?
							Temp + 1 : Temp;
	BestError = FsclHz;

	for ( ; Temp <= TempLimit ; Temp++)
	{
		LastError = FsclHz;
		CalcDivA = 0;
		CalcDivB = 0;
		CurrentError = 0;

		for (Div_b = 0; Div_b < 64; Div_b++) {

			Div_a = Temp / (Div_b + 1);

			if (Div_a != 0)
				Div_a = Div_a - 1;

			if (Div_a > 3)
				continue;

			ActualFscl = (InstancePtr->Config.InputClockHz) /
						(22 * (Div_a + 1) * (Div_b + 1));

			if (ActualFscl > FsclHz)
				CurrentError = (ActualFscl - FsclHz);
			else
				CurrentError = (FsclHz - ActualFscl);

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
					  XIICPS_CR_OFFSET);
	ControlReg &= ~(XIICPS_CR_DIV_A_MASK | XIICPS_CR_DIV_B_MASK);
	ControlReg |= (BestDivA << XIICPS_CR_DIV_A_SHIFT) |
		(BestDivB << XIICPS_CR_DIV_B_SHIFT);

	XIicPs_WriteReg(InstancePtr->Config.BaseAddress, XIICPS_CR_OFFSET,
			  ControlReg);

	return XST_SUCCESS;
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
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	ControlReg = XIicPs_ReadReg(InstancePtr->Config.BaseAddress,
					  XIICPS_CR_OFFSET);

	Div_a = (ControlReg & XIICPS_CR_DIV_A_MASK) >> XIICPS_CR_DIV_A_SHIFT;
	Div_b = (ControlReg & XIICPS_CR_DIV_B_MASK) >> XIICPS_CR_DIV_B_SHIFT;

	ActualFscl = (InstancePtr->Config.InputClockHz) /
		(22 * (Div_a + 1) * (Div_b + 1));

	return ActualFscl;
}

