/******************************************************************************
*
* Copyright (C) 2014 - 2017 Xilinx, Inc. All rights reserved.
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
/*****************************************************************************
*
* @file sleep.c
*
* This function provides a second delay using the Global Timer register in
* the ARM Cortex A53 MP core.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who      Date     Changes
* ----- -------- -------- -----------------------------------------------
* 5.00 	pkp  	 05/29/14 First release
* 5.04	pkp		 28/01/16 Modified the sleep API to configure Time Stamp
*						  generator only when disable using frequency from
*						  xparamters.h instead of hardcoding
* 5.05	pkp		 13/04/16 Modified sleep routine to call XTime_StartTimer
*						  which enables timer only when it is disabled and
*						  read counter value directly from register instead
*						  of calling XTime_GetTime for optimization
* 6.0   asa      08/15/16 Updated the sleep/usleep signature. Fix for CR#956899.
* 6.6	srm      10/18/17 Updated sleep routines to support user configurable
*                         implementation. Now sleep routines will use Timer
*                         specified by the user (i.e. Global timer/TTC timer)
*       srm      01/11/18 Fixed the compilation warning.
* </pre>
*
******************************************************************************/
/***************************** Include Files *********************************/

#include "sleep.h"
#include "xtime_l.h"
#include "xparameters.h"

#if defined (SLEEP_TIMER_BASEADDR)
#include "xil_sleeptimer.h"
#endif
/****************************  Constant Definitions  ************************/

#if defined (SLEEP_TIMER_BASEADDR)
#define COUNTS_PER_USECOND  (COUNTS_PER_SECOND / 1000000 )
#else
/* Global Timer is always clocked at half of the CPU frequency */
#define COUNTS_PER_USECOND  (COUNTS_PER_SECOND / 1000000 )
#endif

/************************************************************************/
#if !defined (SLEEP_TIMER_BASEADDR)
static void sleep_common(u32 n, u32 count)
{
	XTime tEnd, tCur;
	/* Start global timer counter, it will only be enabled if it is disabled */
	XTime_StartTimer();

	tCur = mfcp(CNTPCT_EL0);
	tEnd = tCur + (((XTime) n) * count);
	do {
		tCur = mfcp(CNTPCT_EL0);
	} while (tCur < tEnd);
}
#endif
/*****************************************************************************/
/**
*
* This API gives a delay in microseconds
*
* @param	useconds requested
*
* @return	0 if the delay can be achieved, -1 if the requested delay
*		is out of range
*
* @note		None.
*
****************************************************************************/
int usleep_A53(unsigned long useconds)
{
#if defined (SLEEP_TIMER_BASEADDR)
	Xil_SleepTTCCommon(useconds, COUNTS_PER_USECOND);
#else
	sleep_common((u32)useconds, COUNTS_PER_USECOND);
#endif

	return 0;
}

/*****************************************************************************/
/*
*
* This API is used to provide delays in seconds
*
* @param	seconds requested
*
* @return	0 always
*
* @note		None.
*
****************************************************************************/
unsigned sleep_A53(unsigned int seconds)
{
#if defined (SLEEP_TIMER_BASEADDR)
	Xil_SleepTTCCommon(seconds, COUNTS_PER_SECOND);
#else
	sleep_common(seconds, COUNTS_PER_SECOND);
#endif

	return 0;
}
