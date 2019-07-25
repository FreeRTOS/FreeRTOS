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
* @file xtime_l.h
*
* @addtogroup r5_time_apis Cortex R5 Time Functions
* The xtime_l.h provides access to 32-bit TTC timer counter. These functions
* can be used by applications to track the time.
*
* @{
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------------
* 5.00 	pkp	   05/29/14 First release
* 5.04  pkp	   02/19/16 Added timer configuration register offset definitions
* 5.04	pkp	   03/11/16 Removed definitions for overflow interrupt register
*						and mask
* 6.6   srm    10/22/17 Added a warning message for the user configurable sleep
*                       implementation when default timer is selected by the user
* </pre>
*
******************************************************************************/

#ifndef XTIME_H /* prevent circular inclusions */
#define XTIME_H /* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/
#include "xil_types.h"
#include "xparameters.h"
/***************** Macros (Inline Functions) Definitions *********************/

/************************** Constant Definitions *****************************/

#ifdef SLEEP_TIMER_BASEADDR

#define COUNTS_PER_SECOND				SLEEP_TIMER_FREQUENCY
#define COUNTS_PER_USECOND 				COUNTS_PER_SECOND/1000000

#else
#define ITERS_PER_SEC  (XPAR_CPU_CORTEXR5_0_CPU_CLK_FREQ_HZ / 4)
#define ITERS_PER_USEC  (XPAR_CPU_CORTEXR5_0_CPU_CLK_FREQ_HZ / 4000000)
#define IRQ_FIQ_MASK 	0xC0	/* Mask IRQ and FIQ interrupts in cpsr */
#endif

#if defined (XSLEEP_TIMER_IS_DEFAULT_TIMER)
#pragma message ("For the sleep routines, TTC3 is used if present else the assembly instructions are called")
#endif

/**************************** Type Definitions *******************************/

/* The following definitions are applicable only when TTC3 is present*/
#ifdef SLEEP_TIMER_BASEADDR
typedef u32 XTime;

void XTime_SetTime(XTime Xtime_Global);
void XTime_GetTime(XTime *Xtime_Global);
#endif

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* XTIME_H */
/**
* @} End of "@addtogroup r5_time_apis".
*/
