/******************************************************************************
*
* Copyright (C) 2014 - 2016 Xilinx, Inc. All rights reserved.
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
* register in the ARM Cortex A53 MP core.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------------
* 5.00 	pkp	   05/29/14 First release
* 5.05	pkp	   04/13/16 Added XTime_StartTimer API to start the global timer
*						counter if it is disabled. Also XTime_GetTime calls
*						this API to ensure the global timer counter is enabled
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
#include "bspconfig.h"

/***************** Macros (Inline Functions) Definitions *********************/

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

/****************************************************************************
*
* Start the Global Timer Counter.
*
* @param	None.
*
* @return	None.
*
* @note		None.
*
****************************************************************************/
void XTime_StartTimer(void)
{
	/* Enable the global timer counter only if it is disabled */
	if(((Xil_In32(XIOU_SCNTRS_BASEADDR + XIOU_SCNTRS_CNT_CNTRL_REG_OFFSET))
				& XIOU_SCNTRS_CNT_CNTRL_REG_EN_MASK) !=
				XIOU_SCNTRS_CNT_CNTRL_REG_EN){
		/*write frequency to System Time Stamp Generator Register*/
		Xil_Out32((XIOU_SCNTRS_BASEADDR + XIOU_SCNTRS_FREQ_REG_OFFSET),
				XIOU_SCNTRS_FREQ);
		/*Enable the timer/counter*/
		Xil_Out32((XIOU_SCNTRS_BASEADDR + XIOU_SCNTRS_CNT_CNTRL_REG_OFFSET),
					XIOU_SCNTRS_CNT_CNTRL_REG_EN);
	}
}
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
/*As the generic timer of A53 runs constantly time can not be set as desired
so the API is left unimplemented*/
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
	/* Start global timer counter, it will only be enabled if it is disabled */
	XTime_StartTimer();

	*Xtime_Global = mfcp(CNTPCT_EL0);
}
