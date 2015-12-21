/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xttcps_hw.h
* @addtogroup ttcps_v2_0
* @{
*
* This file defines the hardware interface to one of the three timer counters
* in the Ps block.
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- -------------------------------------------------
* 1.00a drg/jz 01/21/10 First release
*
* </pre>
*
******************************************************************************/

#ifndef XTTCPS_HW_H		/* prevent circular inclusions */
#define XTTCPS_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

/** @name Register Map
 *
 * Register offsets from the base address of the device.
 *
 * @{
 */
#define XTTCPS_CLK_CNTRL_OFFSET		0x00000000  /**< Clock Control Register */
#define XTTCPS_CNT_CNTRL_OFFSET		0x0000000C  /**< Counter Control Register*/
#define XTTCPS_COUNT_VALUE_OFFSET	0x00000018  /**< Current Counter Value */
#define XTTCPS_INTERVAL_VAL_OFFSET	0x00000024  /**< Interval Count Value */
#define XTTCPS_MATCH_0_OFFSET		0x00000030  /**< Match 1 value */
#define XTTCPS_MATCH_1_OFFSET		0x0000003C  /**< Match 2 value */
#define XTTCPS_MATCH_2_OFFSET		0x00000048  /**< Match 3 value */
#define XTTCPS_ISR_OFFSET		0x00000054  /**< Interrupt Status Register */
#define XTTCPS_IER_OFFSET		0x00000060  /**< Interrupt Enable Register */
/* @} */

/** @name Clock Control Register
 * Clock Control Register definitions
 * @{
 */
#define XTTCPS_CLK_CNTRL_PS_EN_MASK	0x00000001  /**< Prescale enable */
#define XTTCPS_CLK_CNTRL_PS_VAL_MASK	0x0000001E  /**< Prescale value */
#define XTTCPS_CLK_CNTRL_PS_VAL_SHIFT		1   /**< Prescale shift */
#define XTTCPS_CLK_CNTRL_PS_DISABLE		16  /**< Prescale disable */
#define XTTCPS_CLK_CNTRL_SRC_MASK	0x00000020  /**< Clock source */
#define XTTCPS_CLK_CNTRL_EXT_EDGE_MASK	0x00000040  /**< External Clock edge */
/* @} */

/** @name Counter Control Register
 * Counter Control Register definitions
 * @{
 */
#define XTTCPS_CNT_CNTRL_DIS_MASK	0x00000001 /**< Disable the counter */
#define XTTCPS_CNT_CNTRL_INT_MASK	0x00000002 /**< Interval mode */
#define XTTCPS_CNT_CNTRL_DECR_MASK	0x00000004 /**< Decrement mode */
#define XTTCPS_CNT_CNTRL_MATCH_MASK	0x00000008 /**< Match mode */
#define XTTCPS_CNT_CNTRL_RST_MASK	0x00000010 /**< Reset counter */
#define XTTCPS_CNT_CNTRL_EN_WAVE_MASK	0x00000020 /**< Enable waveform */
#define XTTCPS_CNT_CNTRL_POL_WAVE_MASK	0x00000040 /**< Waveform polarity */
#define XTTCPS_CNT_CNTRL_RESET_VALUE	0x00000021 /**< Reset value */
/* @} */

/** @name Current Counter Value Register
 * Current Counter Value Register definitions
 * @{
 */
#define XTTCPS_COUNT_VALUE_MASK		0x0000FFFF /**< 16-bit counter value */
/* @} */

/** @name Interval Value Register
 * Interval Value Register is the maximum value the counter will count up or
 * down to.
 * @{
 */
#define XTTCPS_INTERVAL_VAL_MASK	0x0000FFFF /**< 16-bit Interval value*/
/* @} */

/** @name Match Registers
 * Definitions for Match registers, each timer counter has three match
 * registers.
 * @{
 */
#define XTTCPS_MATCH_MASK		0x0000FFFF /**< 16-bit Match value */
#define XTTCPS_NUM_MATCH_REG			3  /**< Num of Match reg */
/* @} */

/** @name Interrupt Registers
 * Following register bit mask is for all interrupt registers.
 *
 * @{
 */
#define XTTCPS_IXR_INTERVAL_MASK	0x00000001  /**< Interval Interrupt */
#define XTTCPS_IXR_MATCH_0_MASK		0x00000002  /**< Match 1 Interrupt */
#define XTTCPS_IXR_MATCH_1_MASK		0x00000004  /**< Match 2 Interrupt */
#define XTTCPS_IXR_MATCH_2_MASK		0x00000008  /**< Match 3 Interrupt */
#define XTTCPS_IXR_CNT_OVR_MASK		0x00000010  /**< Counter Overflow */
#define XTTCPS_IXR_ALL_MASK		0x0000001F  /**< All valid Interrupts */
/* @} */


/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* Read the given Timer Counter register.
*
* @param	BaseAddress is the base address of the timer counter device.
* @param	RegOffset is the register offset to be read
*
* @return	The 32-bit value of the register
*
* @note		C-style signature:
*		u32 XTtcPs_ReadReg(u32 BaseAddress, u32 RegOffset)
*
*****************************************************************************/
#define XTtcPs_ReadReg(BaseAddress, RegOffset) \
    (Xil_In32((BaseAddress) + (RegOffset)))

/****************************************************************************/
/**
*
* Write the given Timer Counter register.
*
* @param	BaseAddress is the base address of the timer counter device.
* @param	RegOffset is the register offset to be written
* @param	Data is the 32-bit value to write to the register
*
* @return	None.
*
* @note		C-style signature:
*		void XTtcPs_WriteReg(XTtcPs BaseAddress, u32 RegOffset,
*		u32 Data)
*
*****************************************************************************/
#define XTtcPs_WriteReg(BaseAddress, RegOffset, Data) \
    (Xil_Out32((BaseAddress) + (RegOffset), (Data)))

/****************************************************************************/
/**
*
* Calculate a match register offset using the Match Register index.
*
* @param	MatchIndex is the 0-2 value of the match register
*
* @return	MATCH_N_OFFSET.
*
* @note		C-style signature:
*		u32 XTtcPs_Match_N_Offset(u8 MatchIndex)
*
*****************************************************************************/
#define XTtcPs_Match_N_Offset(MatchIndex) \
		(XTTCPS_MATCH_0_OFFSET + (12 * (MatchIndex)))

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/
#ifdef __cplusplus
}
#endif
#endif /* end of protection macro */
/** @} */
