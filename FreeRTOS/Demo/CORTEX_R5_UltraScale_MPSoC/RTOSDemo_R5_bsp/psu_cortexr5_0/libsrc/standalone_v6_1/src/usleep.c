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
*
* @file usleep.c
*
* This function provides a microsecond delay using the Global Timer register in
* the ARM Cortex R5 MP core.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who      Date     Changes
* ----- -------- -------- -----------------------------------------------
* 5.00 	pkp  	 02/20/14 First release
* 5.04  pkp		 02/19/16 usleep routine is modified to use TTC3 if present
*						  else it will use set of assembly instructions to
*						  provide the required delay
* 5.04	pkp		 03/09/16 Assembly routine for usleep is modified to avoid
*						  disabling the interrupt
* 5.04	pkp		 03/11/16 Compare the counter value to previously read value
*						  to detect the overflow for TTC3
* 6.0   asa      08/15/16 Updated the usleep signature. Fix for CR#956899.
* </pre>
*
******************************************************************************/
/***************************** Include Files *********************************/

#include "sleep.h"
#include "xtime_l.h"
#include "xparameters.h"
#include "xil_types.h"
#include "xpseudo_asm.h"
#include "xreg_cortexr5.h"

/*****************************************************************************/
/**
*
* This API gives a delay in microseconds
*
* @param	useconds requested
*
* @return	0 always
*
* @note		The usleep API is implemented using TTC3 counter 0 timer if present
*			When TTC3 is absent, usleep is implemented using assembly
*			instructions which is tested with instruction and data caches
*			enabled and it gives proper delay. It may give more delay than
*			exepcted when caches are disabled. If interrupt comes when usleep
*			using assembly instruction is being executed, the delay may be
*			greater than what is expected since once the interrupt is served
*			count resumes from where it was interrupted unlike the case of TTC3
*			where counter keeps running while interrupt is being served.
*
****************************************************************************/

int usleep(unsigned long useconds)
{

#ifdef SLEEP_TIMER_BASEADDR
	u64 tEnd;
	u64 tCur;
	u32 TimeHighVal;
	XTime TimeLowVal1;
	XTime TimeLowVal2;

	TimeHighVal = 0;

	XTime_GetTime(&TimeLowVal1);
	tEnd  = (u64)TimeLowVal1 + (((u64) useconds) * COUNTS_PER_USECOND);

	do
	{
		XTime_GetTime(&TimeLowVal2);
	    if (TimeLowVal2 < TimeLowVal1) {
				TimeHighVal++;
		}
		TimeLowVal1 = TimeLowVal2;
		tCur = (((u64) TimeHighVal) << 32U) | (u64)TimeLowVal2;
	} while (tCur < tEnd);

	return 0;
#else
	__asm__ __volatile__ (
			" push {r0,r1}		\n\t"
			" mov r0, %[usec]	\n\t"
			" 1: \n\t"
			" mov r1, %[iter] 	\n\t"
			" 2:				\n\t"
			" subs r1, r1, #0x1 \n\t"
			" bne   2b    		\n\t"
			" subs r0,r0,#0x1 	\n\t"
			"  bne 1b 			\n\t"
			" pop {r0,r1} 		\n\t"
			:: [iter] "r" (ITERS_PER_USEC), [usec] "r" (useconds)
	);
#endif
}
