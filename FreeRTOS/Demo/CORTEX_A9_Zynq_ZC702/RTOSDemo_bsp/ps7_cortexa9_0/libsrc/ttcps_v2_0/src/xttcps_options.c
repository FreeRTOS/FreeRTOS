/* $Id: xttcps_options.c,v 1.1.2.1 2011/01/20 04:08:59 sadanan Exp $ */
/******************************************************************************
*
* (c) Copyright 2010 Xilinx, Inc. All rights reserved.
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
* @file xttcps_options.c
*
* This file contains functions to get or set option features for the device.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------
* 1.00a drg/jz 01/21/10 First release
* 1.01a nm     03/05/2012 Removed break statement after return to remove
*                         compilation warnings.
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

/*
 * Create the table of options which are processed to get/set the device
 * options. These options are table driven to allow easy maintenance and
 * expansion of the options.
 */
typedef struct {
	u32 Option;
	u32 Mask;
	u32 Register;
} OptionsMap;

static OptionsMap TmrCtrOptionsTable[] = {
	{XTTCPS_OPTION_EXTERNAL_CLK, XTTCPS_CLK_CNTRL_SRC_MASK,
	 XTTCPS_CLK_CNTRL_OFFSET},
	{XTTCPS_OPTION_CLK_EDGE_NEG, XTTCPS_CLK_CNTRL_EXT_EDGE_MASK,
	 XTTCPS_CLK_CNTRL_OFFSET},
	{XTTCPS_OPTION_INTERVAL_MODE, XTTCPS_CNT_CNTRL_INT_MASK,
	 XTTCPS_CNT_CNTRL_OFFSET},
	{XTTCPS_OPTION_DECREMENT, XTTCPS_CNT_CNTRL_DECR_MASK,
	 XTTCPS_CNT_CNTRL_OFFSET},
	{XTTCPS_OPTION_MATCH_MODE, XTTCPS_CNT_CNTRL_MATCH_MASK,
	 XTTCPS_CNT_CNTRL_OFFSET},
	{XTTCPS_OPTION_WAVE_DISABLE, XTTCPS_CNT_CNTRL_EN_WAVE_MASK,
	 XTTCPS_CNT_CNTRL_OFFSET},
	{XTTCPS_OPTION_WAVE_POLARITY, XTTCPS_CNT_CNTRL_POL_WAVE_MASK,
	 XTTCPS_CNT_CNTRL_OFFSET},
};

#define XTTCPS_NUM_TMRCTR_OPTIONS (sizeof(TmrCtrOptionsTable) / \
				sizeof(OptionsMap))

/*****************************************************************************/
/**
*
* This function sets the options for the TTC device.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
* @param	Options contains the specified options to be set. This is a bit
*		mask where a 1 means to turn the option on, and a 0 means to
*		turn the option off. One or more bit values may be contained
*		in the mask. See the bit definitions named XTTCPS_*_OPTION in
*		the file xttcps.h.
*
* @return
*		- XST_SUCCESS if options are successfully set.
*		- XST_FAILURE if any of the options are unknown.
*
* @note		None
*
******************************************************************************/
int XTtcPs_SetOptions(XTtcPs *InstancePtr, u32 Options)
{
	u32 CountReg;
	u32 ClockReg;
	unsigned Index;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	ClockReg = XTtcPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XTTCPS_CLK_CNTRL_OFFSET);
	CountReg = XTtcPs_ReadReg(InstancePtr->Config.BaseAddress,
				    XTTCPS_CNT_CNTRL_OFFSET);

	/*
	 * Loop through the options table, turning the option on or off
	 * depending on whether the bit is set in the incoming options flag.
	 */
	for (Index = 0; Index < XTTCPS_NUM_TMRCTR_OPTIONS; Index++) {
		if (Options & TmrCtrOptionsTable[Index].Option) {

			switch (TmrCtrOptionsTable[Index].Register) {

			case XTTCPS_CLK_CNTRL_OFFSET:
				/* Add option */
				ClockReg |= TmrCtrOptionsTable[Index].Mask;
				break;

			case XTTCPS_CNT_CNTRL_OFFSET:
				/* Add option */
				CountReg |= TmrCtrOptionsTable[Index].Mask;
				break;

			default:
				return XST_FAILURE;
			}
		}
		else {
			switch (TmrCtrOptionsTable[Index].Register) {

			case XTTCPS_CLK_CNTRL_OFFSET:
				/* Remove option*/
				ClockReg &= ~TmrCtrOptionsTable[Index].Mask;
				break;

			case XTTCPS_CNT_CNTRL_OFFSET:
				/* Remove option*/
				CountReg &= ~TmrCtrOptionsTable[Index].Mask;
				break;

			default:
				return XST_FAILURE;
			}
		}
	}

	/*
	 * Now write the registers. Leave it to the upper layers to restart the
	 * device.
	 */
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_CLK_CNTRL_OFFSET, ClockReg);
	XTtcPs_WriteReg(InstancePtr->Config.BaseAddress,
			  XTTCPS_CNT_CNTRL_OFFSET, CountReg);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function gets the settings for the options for the TTC device.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
*
* @return
*
* The return u32 contains the specified options that are set. This is a bit
* mask where a '1' means the option is on, and a'0' means the option is off.
* One or more bit values may be contained in the mask. See the bit definitions
* named XTTCPS_*_OPTION in the file xttcps.h.
*
* @note		None.
*
******************************************************************************/
u32 XTtcPs_GetOptions(XTtcPs *InstancePtr)
{
	u32 OptionsFlag = 0;
	u32 Register;
	unsigned Index;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	/*
	 * Loop through the options table to determine which options are set
	 */
	for (Index = 0; Index < XTTCPS_NUM_TMRCTR_OPTIONS; Index++) {
		/*
		 * Get the control register to determine which options are
		 * currently set.
		 */
		Register = XTtcPs_ReadReg(InstancePtr->Config.BaseAddress,
					      TmrCtrOptionsTable[Index].
					      Register);

		if (Register & TmrCtrOptionsTable[Index].Mask) {
			OptionsFlag |= TmrCtrOptionsTable[Index].Option;
		}
	}

	return OptionsFlag;
}
