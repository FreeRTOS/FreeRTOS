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
/*****************************************************************************/
/**
*
* @file usleep.c
*
* This function supports user configurable sleep implementation.
* This provides a microsecond delay using the timer specified by the user in
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
* 6.6	srm      10/18/17 Updated sleep routines to support user configurable
*			  implementation. Now sleep routines will use TTC
*                         instance specified by user.
*
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

#if defined (SLEEP_TIMER_BASEADDR)
#include "xil_sleeptimer.h"
#endif

/*****************************************************************************/
/**
*
* This API gives a delay in microseconds
*
* @param	useconds requested
*
* @return	0 always
*
* @note		By default, usleep is implemented using TTC3. Although user is
*               given an option to select other instances of TTC. When the user
*               selects other instances of TTC, usleep is implemented by that
*		specific TTC instance. If the user didn't select any other instance
*		of TTC specifically and when TTC3 is absent, usleep is implemented
*      	        using assembly instructions which is tested with instruction and
*		data caches enabled and it gives proper delay. It may give more
*		delay than exepcted when caches are disabled. If interrupt comes
*		when usleep using assembly instruction is being executed, the delay
*		may be greater than what is expected since once the interrupt is
*		served count resumes from where it was interrupted unlike the case
*		of TTC3 where counter keeps running while interrupt is being served.
*
****************************************************************************/

int usleep_R5(unsigned long useconds)
{
#if defined (SLEEP_TIMER_BASEADDR)
	Xil_SleepTTCCommon(useconds, COUNTS_PER_USECOND);
#else
#if defined (__GNUC__)
	__asm__ __volatile__ (
#elif defined (__ICCARM__)
	__asm volatile (
#endif
		"push {r0,r1,r3} \n"
		"mov r0, %[usec] \n"
		"mov r1, %[iter] \n"
		"1: \n"
		"mov r3, r1 \n"
		"2: \n"
		"subs r3, r3, #0x1\n"
		"bne 2b \n"
		"subs r0, r0, #0x1 \n"
		"bne 1b \n"
		"pop {r0,r1,r3} \n"
		::[iter] "r" (ITERS_PER_USEC), [usec] "r" (useconds)
		);
#endif

return 0;
}
