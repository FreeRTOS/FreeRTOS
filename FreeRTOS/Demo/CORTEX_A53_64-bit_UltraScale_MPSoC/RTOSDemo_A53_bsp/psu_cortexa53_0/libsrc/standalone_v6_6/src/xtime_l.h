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
* @addtogroup a53_64_time_apis Cortex A53 64bit Mode Time Functions
* xtime_l.h provides access to the 64-bit physical timer counter.
*
* @{
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- ---------------------------------------------------
* 5.00 	pkp	   05/29/14 First release
* 6.6   srm    10/23/17 Updated the macros to support user configurable sleep
*		        implementation
* </pre>
*
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

#if defined (SLEEP_TIMER_BASEADDR)
#define COUNTS_PER_SECOND     SLEEP_TIMER_FREQUENCY
#else
#define COUNTS_PER_SECOND     XPAR_CPU_CORTEXA53_0_TIMESTAMP_CLK_FREQ
#endif

#if defined (XSLEEP_TIMER_IS_DEFAULT_TIMER)
#pragma message ("For the sleep routines, Global timer is being used")
#endif

#define XIOU_SCNTRS_BASEADDR      	    0xFF260000U
#define XIOU_SCNTRS_CNT_CNTRL_REG_OFFSET    0x00000000U
#define XIOU_SCNTRS_FREQ_REG_OFFSET    	    0x00000020U
#define XIOU_SCNTRS_FREQ		    XPAR_CPU_CORTEXA53_0_TIMESTAMP_CLK_FREQ
#define XIOU_SCNTRS_CNT_CNTRL_REG_EN        0x00000001U
#define XIOU_SCNTRS_CNT_CNTRL_REG_EN_MASK   0x00000001U
/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

void XTime_StartTimer(void);
void XTime_SetTime(XTime Xtime_Global);
void XTime_GetTime(XTime *Xtime_Global);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* XTIME_H */
/**
* @} End of "addtogroup a53_64_time_apis".
*/
