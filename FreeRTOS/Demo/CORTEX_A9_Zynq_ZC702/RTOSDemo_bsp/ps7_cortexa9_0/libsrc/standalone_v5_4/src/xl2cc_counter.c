/******************************************************************************
*
* Copyright (C) 2011 - 2015 Xilinx, Inc.  All rights reserved.
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
void XL2cc_EventCtrInit(s32 Event0, s32 Event1)
{

	/* Write event code into cnt1 cfg reg */
	*((volatile u32*)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNT1_CTRL_OFFSET)) = (((u32)Event1) << 2);

	/* Write event code into cnt0 cfg reg */
	*((volatile u32*)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNT0_CTRL_OFFSET)) = (((u32)Event0) << 2);

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
	u32 *LocalPtr;
	LocalPtr = (u32 *)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNTRL_OFFSET);
	XL2cc_EventCtrReset();

	/* Enable counter */
	/* *((volatile u32*)((void *)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNTRL_OFFSET))) = 1 */
	*LocalPtr = (u32)1;
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
	*((volatile u32*) (XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNTRL_OFFSET)) = 0U;

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
	*((volatile u32*)(XPS_L2CC_BASEADDR + XPS_L2CC_EVNT_CNTRL_OFFSET)) = 0x6U;
}
