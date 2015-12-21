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
* @file xttcps.c
* @addtogroup ttcps_v2_0
* @{
*
* This file contains the implementation of the XTtcPs driver. This driver
* controls the operation of one timer counter in the Triple Timer Counter (TTC)
* module in the Ps block. Refer to xttcps.h for more detailed description
* of the driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- -------------------------------------------------
* 1.00a drg/jz 01/21/10 First release
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xttcps.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Initializes a specific XTtcPs instance such that the driver is ready to use.
* This function initializes a single timer counter in the triple timer counter
* function block.
*
* The state of the device after initialization is:
*  - Overflow Mode
*  - Internal (pclk) selected
*  - Counter disabled
*  - All Interrupts disabled
*  - Output waveforms disabled
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
* @param	ConfigPtr is a reference to a structure containing information
*		about a specific TTC device.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. The caller is responsible for keeping the address
*		mapping from EffectiveAddr to the device physical base address
*		unchanged once this function is invoked. Unexpected errors may
*		occur if the address mapping changes after this function is
*		called. If address translation is not used, then use
*		ConfigPtr->BaseAddress for this parameter, passing the physical
*		address instead.
*
* @return
*
* 		- XST_SUCCESS if the initialization is successful.
*		- XST_DEVICE_IS_STARTED if the device is started. It must be
*		  stopped to re-initialize.
*
* @note		Device has to be stopped first to call this function to
*		initialize it.
*
******************************************************************************/
int XTtcPs_CfgInitialize(XTtcPs *InstancePtr, XTtcPs_Config *ConfigPtr,
			      u32 EffectiveAddr)
{
	/*
	 * Assert to validate input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/*
	 * Set some default values
	 */
	InstancePtr->Config.DeviceId = ConfigPtr->DeviceId;
	InstancePtr->Config.BaseAddress = EffectiveAddr;
	InstancePtr->Config.InputClockHz = ConfigPtr->InputClockHz;

	/*
	 * If the timer counter has already started, return an error
	 * Device should be stopped first.
	 */
	if(XTtcPs_IsStarted(InstancePtr)) {
		return XST_DEVICE_IS_STARTED;
	}

	/*
	 * Reset the count control register to it's default value.
	 */
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_CNT_CNTRL_OFFSET,
			  XTTCPS_CNT_CNTRL_RESET_VALUE);

	/*
	 * Reset the rest of the registers to the default values.
	 */
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_CLK_CNTRL_OFFSET, 0x00);
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_INTERVAL_VAL_OFFSET, 0x00);
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_MATCH_1_OFFSET, 0x00);
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_MATCH_2_OFFSET, 0x00);
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_MATCH_2_OFFSET, 0x00);
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_IER_OFFSET, 0x00);
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_ISR_OFFSET, XTTCPS_IXR_ALL_MASK);

	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	/*
	 * Reset the counter value
	 */
	XTtcPs_ResetCounterValue(InstancePtr);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function is used to set the match registers. There are three match
* registers.
*
* The match 0 register is special. If the waveform output mode is enabled, the
* waveform will change polarity when the count matches the value in the match 0
* register. The polarity of the waveform output can also be set using the
* XTtcPs_SetOptions() function.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
* @param	MatchIndex is the index to the match register to be set.
*		Valid values are 0, 1, or 2.
* @param	Value is the 16-bit value to be set in the match register.
*
* @return	None
*
* @note		None
*
****************************************************************************/
void XTtcPs_SetMatchValue(XTtcPs *InstancePtr, u8 MatchIndex, u16 Value)
{
	/*
	 * Assert to validate input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(MatchIndex < XTTCPS_NUM_MATCH_REG);

	/*
	 * Write the value to the correct match register with MatchIndex
	 */
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTtcPs_Match_N_Offset(MatchIndex), Value);
}

/*****************************************************************************/
/**
*
* This function is used to get the value of the match registers. There are
* three match registers.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
* @param	MatchIndex is the index to the match register to be set.
*		Valid values are 0, 1, or 2.
*
* @return	None
*
* @note		None
*
****************************************************************************/
u16 XTtcPs_GetMatchValue(XTtcPs *InstancePtr, u8 MatchIndex)
{
	u32 MatchReg;

	/*
	 * Assert to validate input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(MatchIndex < XTTCPS_NUM_MATCH_REG);

	MatchReg = XTtcPs_ReadReg(InstancePtr->Config.BaseAddress,
			    XTtcPs_Match_N_Offset(MatchIndex));

	return (u16) MatchReg;
}

/*****************************************************************************/
/**
*
* This function sets the prescaler enable bit and if needed sets the prescaler
* bits in the control register.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
* @param	PrescalerValue is a number from 0-16 that sets the prescaler
*		to use.
*		If the parameter is 0 - 15, use a prescaler on the clock of
*		2^(PrescalerValue+1), or 2-65536.
*		If the parameter is XTTCPS_CLK_CNTRL_PS_DISABLE, do not use a
*		prescaler.
*
* @return	None
*
* @note		None
*
****************************************************************************/
void XTtcPs_SetPrescaler(XTtcPs *InstancePtr, u8 PrescalerValue)
{
	u32 ClockReg;

	/*
	 * Assert to validate input arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(PrescalerValue <= XTTCPS_CLK_CNTRL_PS_DISABLE);

	/*
	 * Read the clock control register
	 */
	ClockReg = XTtcPs_ReadReg(InstancePtr->Config.BaseAddress,
			   XTTCPS_CLK_CNTRL_OFFSET);

	/*
	 * Clear all of the prescaler control bits in the register
	 */
	ClockReg &=
		~(XTTCPS_CLK_CNTRL_PS_VAL_MASK | XTTCPS_CLK_CNTRL_PS_EN_MASK);

	if (PrescalerValue < XTTCPS_CLK_CNTRL_PS_DISABLE) {
		/*
		 * Set the prescaler value and enable prescaler
		 */
		ClockReg |= (PrescalerValue << XTTCPS_CLK_CNTRL_PS_VAL_SHIFT) &
			XTTCPS_CLK_CNTRL_PS_VAL_MASK;
		ClockReg |= XTTCPS_CLK_CNTRL_PS_EN_MASK;
	}

	/*
	 * Write the register with the new values.
	 */
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_CLK_CNTRL_OFFSET, ClockReg);
}

/*****************************************************************************/
/**
*
* This function gets the input clock prescaler
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
*
* <pre>
* @return	The value(n) from which the prescalar value is calculated
*		as 2^(n+1). Some example values are given below :
*
* 	Value		Prescaler
* 	0		2
* 	1		4
* 	N		2^(n+1)
* 	15		65536
* 	16		1
* </pre>
*
* @note		None.
*
****************************************************************************/
u8 XTtcPs_GetPrescaler(XTtcPs *InstancePtr)
{
	u32 ClockReg;

	/*
	 * Assert to validate input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the clock control register
	 */
	ClockReg = XTtcPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XTTCPS_CLK_CNTRL_OFFSET);

	if (0 == (ClockReg & XTTCPS_CLK_CNTRL_PS_EN_MASK)) {
		/*
		 * Prescaler is disabled. Return the correct flag value
		 */
		return XTTCPS_CLK_CNTRL_PS_DISABLE;
	}

	return ((ClockReg & XTTCPS_CLK_CNTRL_PS_VAL_MASK) >>
		XTTCPS_CLK_CNTRL_PS_VAL_SHIFT);
}

/*****************************************************************************/
/**
*
* This function calculates the interval value as well as the prescaler value
* for a given frequency.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
* @param	Freq is the requested output frequency for the device.
* @param	Interval is the interval value for the given frequency,
*		it is the output value for this function.
* @param	Prescaler is the prescaler value for the given frequency,
*		it is the output value for this function.
*
* @return	None.
*
* @note
*  Upon successful calculation for the given frequency, Interval and Prescaler
*  carry the settings for the timer counter; Upon unsuccessful calculation,
*  Interval and Prescaler are set to 0xFF(FF) for their maximum values to
*  signal the caller of failure. Therefore, caller needs to check the return
*  interval or prescaler values for whether the function has succeeded.
*
****************************************************************************/
void XTtcPs_CalcIntervalFromFreq(XTtcPs *InstancePtr, u32 Freq,
        u16 *Interval, u8 *Prescaler)
{
	u8 TmpPrescaler;
	u32 TempValue;
	u32 InputClock;

	InputClock = InstancePtr->Config.InputClockHz;
	/*
	 * Find the smallest prescaler that will work for a given frequency. The
	 * smaller the prescaler, the larger the count and the more accurate the
	 *  PWM setting.
	 */
	TempValue = InputClock/ Freq;

	if (TempValue < 4) {
		/*
		 * The frequency is too high, it is too close to the input
		 * clock value. Use maximum values to signal caller.
		 */
		*Interval = 0xFFFF;
		*Prescaler = 0xFF;
		return;
	}

	/*
	 * First, do we need a prescaler or not?
	 */
	if (65536 > TempValue) {
		/*
		 * We do not need a prescaler, so set the values appropriately
		 */
		*Interval = TempValue;
		*Prescaler = XTTCPS_CLK_CNTRL_PS_DISABLE;
		return;
	}


	for (TmpPrescaler = 0; TmpPrescaler < XTTCPS_CLK_CNTRL_PS_DISABLE;
	     TmpPrescaler++) {
		TempValue =	InputClock/ (Freq * (1 << (TmpPrescaler + 1)));

		/*
		 * The first value less than 2^16 is the best bet
		 */
		if (65536 > TempValue) {
			/*
			 * Set the values appropriately
			 */
			*Interval = TempValue;
			*Prescaler = TmpPrescaler;
			return;
		}
	}

	/* Can not find interval values that work for the given frequency.
	 * Return maximum values to signal caller.
	 */
	*Interval = 0XFFFF;
	*Prescaler = 0XFF;
	return;
}

/** @} */
