/******************************************************************************
*
* (c) Copyright 2011-13  Xilinx, Inc. All rights reserved.
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
* @file xl2cc_counter.c
*
* This file contains APIs for configuring and controlling the event counters
* in PL310 L2 cache controller. For more information about the event counters,
* see xl2cc_counter.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a sdm  07/11/11 First release
* 3.07a asa  08/30/12 Updated for CR 675636 to provide the L2 Base Address
*		      inside the APIs
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include <stdint.h>
#include "xparameters_ps.h"
#include "xl2cc_counter.h"
#include "xl2cc.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

void XL2cc_EventCtrReset(void);

/******************************************************************************/

/****************************************************************************/
/**
*
* This function initializes the event counters in L2 Cache controller with a
* set of event codes specified by the user.
*
* @param	Event0 is the event code for counter 0.
* @param	Event1 is the event code for counter 1.
*		Use the event codes defined by XL2CC_* in xl2cc_counter.h.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XL2cc_EventCtrInit(int Event0, int Event1)
{

	/* Write event code into cnt1 cfg reg */
	*((volatile u32*)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNT1_CTRL_OFFSET)) = (Event1 << 2);

	/* Write event code into cnt0 cfg reg */
	*((volatile u32*)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNT0_CTRL_OFFSET)) = (Event0 << 2);

	/* Reset counters */
	XL2cc_EventCtrReset();
}

/****************************************************************************/
/**
*
* This function starts the event counters in L2 Cache controller.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XL2cc_EventCtrStart(void)
{
	XL2cc_EventCtrReset();

	/* Enable counter */
	*((volatile u32*)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNTRL_OFFSET)) = 1;
}

/****************************************************************************/
/**
*
* This function disables the event counters in L2 Cache controller, saves the
* counter values and resets the counters.
*
* @param	EveCtr0 is an output parameter which is used to return the value
*		in event counter 0.
*		EveCtr1 is an output parameter which is used to return the value
*		in event counter 1.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XL2cc_EventCtrStop(u32 *EveCtr0, u32 *EveCtr1)
{
	/* Disable counter */
	*((volatile u32*) (XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNTRL_OFFSET)) = 0;

	/* Save counter values */
	*EveCtr1 = *((volatile u32*)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNT1_VAL_OFFSET));
	*EveCtr0 = *((volatile u32*)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNT0_VAL_OFFSET));

	XL2cc_EventCtrReset();
}

/****************************************************************************/
/**
*
* This function resets the event counters in L2 Cache controller.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XL2cc_EventCtrReset(void)
{
	*((volatile u32*)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNTRL_OFFSET)) = 0x6;
}
