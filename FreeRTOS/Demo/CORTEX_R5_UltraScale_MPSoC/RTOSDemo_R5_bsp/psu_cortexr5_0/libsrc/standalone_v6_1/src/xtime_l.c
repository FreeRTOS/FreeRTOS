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
* register in the ARM Cortex R5 core.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------------
* 5.00 	pkp    08/29/14 First release
* 5.04  pkp	   02/19/16 XTime_StartTimer API is added to configure TTC3 timer
*						when present. XTime_GetTime is modified to give 64bit
*						output using timer overflow when TTC3 present.
*						XTime_SetTime is modified to configure TTC3 counter
*						value when present.
* 5.04	pkp	   03/11/16 XTime_StartTimer is modified to avoid enabling the
*						overflow interrupt and XTime_GetTime & XTime_SetTime
*						are modified to read and write TTC counter value
*						respectively
* 5.04	pkp
* 6.0   mus    08/11/16  Removed implementation of XTime_SetTime API, since
*                        TTC counter value register is read only.
*
* </pre>
*
* @note		None.
*
******************************************************************************/
/***************************** Include Files *********************************/

#include "xtime_l.h"
#include "xpseudo_asm.h"
#include "xil_assert.h"
#include "xil_io.h"
#include "xdebug.h"

/***************** Macros (Inline Functions) Definitions *********************/

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/
#define RST_LPD_IOU2 					0xFF5E0238U
#define RST_LPD_IOU2_TTC3_RESET_MASK	0x00004000U
/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

/* Function definitions are applicable only when TTC3 is present*/
#ifdef SLEEP_TIMER_BASEADDR
/****************************************************************************
*
* Start the TTC timer.
*
* @param	None.
*
* @return	None.
*
* @note		In multiprocessor environment reference time will reset/lost for
*		all processors, when this function called by any one processor.
*
****************************************************************************/
void XTime_StartTimer(void)
{
	u32 LpdRst;
	u32 TimerPrescalar;
	u32 TimerCntrl;

	LpdRst = Xil_In32(RST_LPD_IOU2);
	if ((LpdRst & RST_LPD_IOU2_TTC3_RESET_MASK) != 0 ) {
			LpdRst = LpdRst & (~RST_LPD_IOU2_TTC3_RESET_MASK);
			Xil_Out32(RST_LPD_IOU2, LpdRst);

	} else {
		TimerCntrl = Xil_In32(SLEEP_TIMER_BASEADDR +
								SLEEP_TIMER_CNTR_CNTRL_OFFSET);
		/* check if Timer is disabled */
		if ((TimerCntrl & SLEEP_TIMER_COUNTER_CONTROL_DIS_MASK) == 0) {
			TimerPrescalar = Xil_In32(SLEEP_TIMER_BASEADDR +
									SLEEP_TIMER_CLK_CNTRL_OFFSET);

		/* check if Timer is configured with proper functionalty for sleep */
			if ((TimerPrescalar & SLEEP_TIMER_CLOCK_CONTROL_PS_EN_MASK) == 0)
						return;
		}
	}
	/* Disable the timer to configure */
	TimerCntrl = Xil_In32(SLEEP_TIMER_BASEADDR +
							SLEEP_TIMER_CNTR_CNTRL_OFFSET);
	TimerCntrl = TimerCntrl | SLEEP_TIMER_COUNTER_CONTROL_DIS_MASK;
	Xil_Out32(SLEEP_TIMER_BASEADDR + SLEEP_TIMER_CNTR_CNTRL_OFFSET,
				TimerCntrl);

	/* Disable the prescalar */
	TimerPrescalar = Xil_In32(SLEEP_TIMER_BASEADDR +
								SLEEP_TIMER_CLK_CNTRL_OFFSET);
	TimerPrescalar = TimerPrescalar & (~SLEEP_TIMER_CLOCK_CONTROL_PS_EN_MASK);
	Xil_Out32(SLEEP_TIMER_BASEADDR + SLEEP_TIMER_CLK_CNTRL_OFFSET,
				TimerPrescalar);

	/* Enable the Timer */
	TimerCntrl = SLEEP_TIMER_COUNTER_CONTROL_RST_MASK &
					(~SLEEP_TIMER_COUNTER_CONTROL_DIS_MASK);
	Xil_Out32(SLEEP_TIMER_BASEADDR + SLEEP_TIMER_CNTR_CNTRL_OFFSET,
				TimerCntrl);

}
/****************************************************************************
*
* Set the time in the Timer Counter Register.
*
* @param	Value to be written to the Timer Counter Register.
*
* @return	None.
*
* @note		In multiprocessor environment reference time will reset/lost for
*		all processors, when this function called by any one processor.
*
****************************************************************************/
void XTime_SetTime(XTime Xtime_Global)
{
/*Timer cannot be set to desired value, so the API is left unimplemented*/
    xdbg_printf(XDBG_DEBUG_GENERAL,
                "XTime_SetTime:Timer cannot be set to desired value,so API is not implemented\n");
}

/****************************************************************************
*
* Get the time from the Timer Counter Register.
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
	*Xtime_Global = Xil_In32(SLEEP_TIMER_BASEADDR +
								SLEEP_TIMER_CNTR_VAL_OFFSET);
}
#endif
