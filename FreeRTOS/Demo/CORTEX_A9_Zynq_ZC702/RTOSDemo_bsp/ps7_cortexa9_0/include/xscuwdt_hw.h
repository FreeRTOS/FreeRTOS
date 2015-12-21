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
/****************************************************************************/
/**
*
* @file xscuwdt_hw.h
* @addtogroup scuwdt_v2_0
* @{
*
* This file contains the hardware interface to the Xilinx SCU private Watch Dog
* Timer (XSCUWDT).
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a sdm 01/15/10 First release
* 1.01a bss 02/27/12 Updated the register offsets to start at 0x0 instead
*                    of 0x20 as the base address obtained from the tools
*		     starts at 0x20.
* 1.02a  sg 07/17/12 Included xil_assert.h for CR 667947. This is an issue
*		     when the xstatus.h in the common driver overwrites
*		     the xstatus.h of the standalone BSP during the
*		     libgen.
* </pre>
*
******************************************************************************/
#ifndef XSCUWDT_HW_H		/* prevent circular inclusions */
#define XSCUWDT_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_io.h"
#include "xil_assert.h"
/************************** Constant Definitions *****************************/

/** @name Register Map
 * Offsets of registers from the start of the device. The WDT registers start at
 * an offset 0x20
 * @{
 */

#define XSCUWDT_LOAD_OFFSET	0x00 /**< Watchdog Load Register */
#define XSCUWDT_COUNTER_OFFSET	0x04 /**< Watchdog Counter Register */
#define XSCUWDT_CONTROL_OFFSET	0x08 /**< Watchdog Control Register */
#define XSCUWDT_ISR_OFFSET	0x0C /**< Watchdog Interrupt Status Register */
#define XSCUWDT_RST_STS_OFFSET	0x10 /**< Watchdog Reset Status Register */
#define XSCUWDT_DISABLE_OFFSET	0x14 /**< Watchdog Disable Register */
/* @} */

/** @name Watchdog Control register
 * This register bits control the prescaler, WD/Timer mode, Intr enable,
 * auto-reload, watchdog enable.
 * @{
 */

#define XSCUWDT_CONTROL_PRESCALER_MASK	 0x0000FF00 /**< Prescaler */
#define XSCUWDT_CONTROL_PRESCALER_SHIFT	 8
#define XSCUWDT_CONTROL_WD_MODE_MASK	 0x00000008 /**< Watchdog/Timer mode */
#define XSCUWDT_CONTROL_IT_ENABLE_MASK	 0x00000004 /**< Intr enable (in
							 timer mode) */
#define XSCUWDT_CONTROL_AUTO_RELOAD_MASK 0x00000002 /**< Auto-reload (in
							 timer mode) */
#define XSCUWDT_CONTROL_WD_ENABLE_MASK	 0x00000001 /**< Watchdog enable */
/* @} */

/** @name Interrupt Status register
 * This register indicates the Counter register has reached zero in Counter
 * mode.
 * @{
 */

#define XSCUWDT_ISR_EVENT_FLAG_MASK	0x00000001 /**< Event flag */
/*@}*/

/** @name Reset Status register
 * This register indicates the Counter register has reached zero in Watchdog
 * mode and a reset request is sent.
 * @{
 */

#define XSCUWDT_RST_STS_RESET_FLAG_MASK	0x00000001 /**< Time out occured */
/*@}*/

/** @name Disable register
 * This register is used to switch from watchdog mode to timer mode.
 * The software must write 0x12345678 and 0x87654321 successively to the
 * Watchdog Disable Register so that the watchdog mode bit in the Watchdog
 * Control Register is set to zero.
 * @{
 */
#define XSCUWDT_DISABLE_VALUE1		0x12345678 /**< Watchdog mode disable
							value 1 */
#define XSCUWDT_DISABLE_VALUE2		0x87654321 /**< Watchdog mode disable
							value 2 */
/*@}*/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* Read the given register.
*
* @param	BaseAddr is the base address of the device
* @param	RegOffset is the register offset to be read
*
* @return	The 32-bit value of the register
*
* @note		C-style signature:
*		u32 XScuWdt_ReadReg(u32 BaseAddr, u32 RegOffset)
*
*****************************************************************************/
#define XScuWdt_ReadReg(BaseAddr, RegOffset)		\
	Xil_In32((BaseAddr) + (RegOffset))

/****************************************************************************/
/**
*
* Write the given register.
*
* @param	BaseAddr is the base address of the device
* @param	RegOffset is the register offset to be written
* @param	Data is the 32-bit value to write to the register
*
* @return	None.
*
* @note		C-style signature:
*		void XScuWdt_WriteReg(u32 BaseAddr, u32 RegOffset, u32 Data)
*
*****************************************************************************/
#define XScuWdt_WriteReg(BaseAddr, RegOffset, Data)	\
	Xil_Out32((BaseAddr) + (RegOffset), (Data))

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

#ifdef __cplusplus
}
#endif

#endif	/* end of protection macro */
/** @} */
