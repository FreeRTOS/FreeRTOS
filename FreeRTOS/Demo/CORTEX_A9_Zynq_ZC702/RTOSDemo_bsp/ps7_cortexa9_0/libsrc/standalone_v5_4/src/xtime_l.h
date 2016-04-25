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
* @file xtime_l.h
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------------
* 1.00a rp/sdm 11/03/09 Initial release.
* 3.06a sgd    05/15/12 Upadted get/set time functions to make use Global Timer
* 3.06a asa    06/17/12 Reverted back the changes to make use Global Timer.
* 3.07a sgd    07/05/12 Upadted get/set time functions to make use Global Timer
* </pre>
*
* @note		None.
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

/**************************** Type Definitions *******************************/

typedef u64 XTime;

/************************** Constant Definitions *****************************/
#define GLOBAL_TMR_BASEADDR               XPAR_GLOBAL_TMR_BASEADDR
#define GTIMER_COUNTER_LOWER_OFFSET       0x00U
#define GTIMER_COUNTER_UPPER_OFFSET       0x04U
#define GTIMER_CONTROL_OFFSET             0x08U


/* Global Timer is always clocked at half of the CPU frequency */
#define COUNTS_PER_SECOND          (XPAR_CPU_CORTEXA9_CORE_CLOCK_FREQ_HZ /2)
/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

void XTime_SetTime(XTime Xtime_Global);
void XTime_GetTime(XTime *Xtime_Global);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* XTIME_H */
