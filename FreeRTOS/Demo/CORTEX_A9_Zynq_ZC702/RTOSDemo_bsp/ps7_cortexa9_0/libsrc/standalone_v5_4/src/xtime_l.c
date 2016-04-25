/******************************************************************************
*
* Copyright (C) 2009 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xtime_l.c
*
* This file contains low level functions to get/set time from the Global Timer
* register in the ARM Cortex A9 MP core.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------------
* 1.00a rp/sdm 11/03/09 Initial release.
* 3.07a sgd    07/05/12 Upadted get/set time functions to make use Global Timer
* </pre>
*
* @note		None.
*
******************************************************************************/
/***************************** Include Files *********************************/

#include "xtime_l.h"
#include "xpseudo_asm.h"
#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/***************** Macros (Inline Functions) Definitions *********************/

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

/****************************************************************************
*
* Set the time in the Global Timer Counter Register.
*
* @param	Value to be written to the Global Timer Counter Register.
*
* @return	None.
*
* @note		In multiprocessor environment reference time will reset/lost for
*		all processors, when this function called by any one processor.
*
****************************************************************************/
void XTime_SetTime(XTime Xtime_Global)
{
	/* Disable Global Timer */
	Xil_Out32((u32)GLOBAL_TMR_BASEADDR + (u32)GTIMER_CONTROL_OFFSET, (u32)0x0);

	/* Updating Global Timer Counter Register */
	Xil_Out32((u32)GLOBAL_TMR_BASEADDR + (u32)GTIMER_COUNTER_LOWER_OFFSET, (u32)Xtime_Global);
	Xil_Out32((u32)GLOBAL_TMR_BASEADDR + (u32)GTIMER_COUNTER_UPPER_OFFSET,
		(u32)((u32)(Xtime_Global>>32U)));

	/* Enable Global Timer */
	Xil_Out32((u32)GLOBAL_TMR_BASEADDR + (u32)GTIMER_CONTROL_OFFSET, (u32)0x1);
}

/****************************************************************************
*
* Get the time from the Global Timer Counter Register.
*
* @param	Pointer to the location to be updated with the time.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void XTime_GetTime(XTime *Xtime_Global)
{
	u32 low;
	u32 high;

	/* Reading Global Timer Counter Register */
	do
	{
		high = Xil_In32(GLOBAL_TMR_BASEADDR + GTIMER_COUNTER_UPPER_OFFSET);
		low = Xil_In32(GLOBAL_TMR_BASEADDR + GTIMER_COUNTER_LOWER_OFFSET);
	} while(Xil_In32(GLOBAL_TMR_BASEADDR + GTIMER_COUNTER_UPPER_OFFSET) != high);

	*Xtime_Global = (((XTime) high) << 32U) | (XTime) low;
}
