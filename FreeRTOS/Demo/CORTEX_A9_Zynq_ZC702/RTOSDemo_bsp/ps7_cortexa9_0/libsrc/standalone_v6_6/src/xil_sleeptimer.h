/******************************************************************************
*
* Copyright (C) 2017 Xilinx, Inc.  All rights reserved.
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
* @file xil_sleeptimer.h
*
* This header file contains ARM Cortex A53,A9,R5 specific sleep related APIs.
* For sleep related functions that can be used across all Xilinx supported
* processors, please use xil_sleeptimer.h.
*
*
* <pre>
* MODIFICATION HISTORY :
*
* Ver   Who  Date	 Changes
* ----- ---- -------- -------------------------------------------------------
* 6.6	srm  10/18/17 First Release.
*
* </pre>
*****************************************************************************/

#ifndef XIL_SLEEPTIMER_H		/* prevent circular inclusions */
#define XIL_SLEEPTIMER_H		/* by using protection macros */
/****************************  Include Files  ********************************/

#include "xil_io.h"
#include "xparameters.h"
#include "bspconfig.h"

/************************** Constant Definitions *****************************/

#if defined (ARMR5) || (__aarch64__) || (ARMA53_32)
#define XSLEEP_TIMER_REG_SHIFT  32U
#define XSleep_ReadCounterVal   Xil_In32
#define XCntrVal 			    u32
#else
#define XSLEEP_TIMER_REG_SHIFT  16U
#define XSleep_ReadCounterVal   Xil_In16
#define XCntrVal 			    u16
#endif

#if defined(ARMR5) || (defined (__aarch64__) && EL3==1) || defined (ARMA53_32)
#define RST_LPD_IOU2 					    0xFF5E0238U
#define RST_LPD_IOU2_TTC_BASE_RESET_MASK 	0x00000800U
#endif

#if defined (SLEEP_TIMER_BASEADDR)
/** @name Register Map
*
* Register offsets from the base address of the TTC device
*
* @{
*/
 #define XSLEEP_TIMER_TTC_CLK_CNTRL_OFFSET		0x00000000U
					     /**< Clock Control Register */
 #define XSLEEP_TIMER_TTC_CNT_CNTRL_OFFSET		0x0000000CU
	                                     /**< Counter Control Register*/
 #define XSLEEP_TIMER_TTC_COUNT_VALUE_OFFSET	0x00000018U
					     /**< Current Counter Value */
/* @} */
/** @name Clock Control Register
* Clock Control Register definitions of TTC
* @{
*/
 #define XSLEEP_TIMER_TTC_CLK_CNTRL_PS_EN_MASK		0x00000001U
						   /**< Prescale enable */
/* @} */
/** @name Counter Control Register
* Counter Control Register definitions of TTC
* @{
*/
#define XSLEEP_TIMER_TTC_CNT_CNTRL_DIS_MASK		0x00000001U
						/**< Disable the counter */
#define XSLEEP_TIMER_TTC_CNT_CNTRL_RST_MASK		0x00000010U
						  /**< Reset counter */
/* @} */

/**************************** Type Definitions *******************************/

/************************** Function Prototypes ******************************/

void Xil_SleepTTCCommon(u32 delay, u64 frequency);
void XTime_StartTTCTimer();

#endif
#endif /* XIL_SLEEPTIMER_H */
