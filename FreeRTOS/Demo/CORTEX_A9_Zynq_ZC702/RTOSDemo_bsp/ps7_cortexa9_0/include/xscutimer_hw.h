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
* @file xscutimer_hw.h
* @addtogroup scutimer_v2_0
* @{
*
* This file contains the hardware interface to the Timer.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a nm  03/10/10 First release
* 1.01a sdm 02/02/12 Added low level macros to read/write load, counter, control
*		     and interrupt registers
* 1.02a  sg 07/17/12 Included xil_assert.h for CR 667947. This is an issue
*		     when the xstatus.h in the common driver overwrites
*		     the xstatus.h of the standalone BSP during the
*		     libgen.
* </pre>
*
******************************************************************************/
#ifndef XSCUTIMER_HW_H		/* prevent circular inclusions */
#define XSCUTIMER_HW_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/
#include "xil_types.h"
#include "xil_io.h"
#include "xil_assert.h"
/************************** Constant Definitions *****************************/

/** @name Register Map
 * Offsets of registers from the start of the device
 * @{
 */

#define XSCUTIMER_LOAD_OFFSET		0x00 /**< Timer Load Register */
#define XSCUTIMER_COUNTER_OFFSET	0x04 /**< Timer Counter Register */
#define XSCUTIMER_CONTROL_OFFSET	0x08 /**< Timer Control Register */
#define XSCUTIMER_ISR_OFFSET		0x0C /**< Timer Interrupt
						  Status Register */
/* @} */

/** @name Timer Control register
 * This register bits control the prescaler, Intr enable,
 * auto-reload and timer enable.
 * @{
 */

#define XSCUTIMER_CONTROL_PRESCALER_MASK	0x0000FF00 /**< Prescaler */
#define XSCUTIMER_CONTROL_PRESCALER_SHIFT	8
#define XSCUTIMER_CONTROL_IRQ_ENABLE_MASK	0x00000004 /**< Intr enable */
#define XSCUTIMER_CONTROL_AUTO_RELOAD_MASK	0x00000002 /**< Auto-reload */
#define XSCUTIMER_CONTROL_ENABLE_MASK		0x00000001 /**< Timer enable */
/* @} */

/** @name Interrupt Status register
 * This register indicates the Timer counter register has reached zero.
 * @{
 */

#define XSCUTIMER_ISR_EVENT_FLAG_MASK		0x00000001 /**< Event flag */
/*@}*/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* Write to the timer load register. This will also update the
* timer counter register with the new value. This macro can be used to
* change the time-out value.
*
* @param	BaseAddr is the base address of the scu timer.
* @param	Value is the count to be loaded in to the load register.
*
* @return	None.
*
* @note		C-style signature:
*		void XScuTimer_SetLoadReg(u32 BaseAddr, u32 Value)
*
******************************************************************************/
#define XScuTimer_SetLoadReg(BaseAddr, Value)				\
	XScuTimer_WriteReg(BaseAddr, XSCUTIMER_LOAD_OFFSET, Value)

/****************************************************************************/
/**
*
* Returns the current timer load register value.
*
* @param	BaseAddr is the base address of the scu timer.
*
* @return	Contents of the timer load register.
*
* @note		C-style signature:
*		u32 XScuTimer_GetLoadReg(u32 BaseAddr)
*
******************************************************************************/
#define XScuTimer_GetLoadReg(BaseAddr)					\
	XScuTimer_ReadReg(BaseAddr, XSCUTIMER_LOAD_OFFSET)

/****************************************************************************/
/**
*
* Write to the timer counter register.
*
* @param	BaseAddr is the base address of the scu timer.
* @param	Value is the count to be loaded in to the counter register.
*
* @return	None.
*
* @note		C-style signature:
*		void XScuTimer_SetCounterReg(u32 BaseAddr, u32 Value)
*
******************************************************************************/
#define XScuTimer_SetCounterReg(BaseAddr, Value)			\
	XScuTimer_WriteReg(BaseAddr, XSCUTIMER_COUNTER_OFFSET, Value)

/****************************************************************************/
/**
*
* Returns the current timer counter register value.
*
* @param	BaseAddr is the base address of the scu timer.
*
* @return	Contents of the timer counter register.
*
* @note		C-style signature:
		u32 XScuTimer_GetCounterReg(u32 BaseAddr)
*
******************************************************************************/
#define XScuTimer_GetCounterReg(BaseAddr)				\
	XScuTimer_ReadReg(BaseAddr, XSCUTIMER_COUNTER_OFFSET)

/****************************************************************************/
/**
*
* Write to the timer load register. This will also update the
* timer counter register with the new value. This macro can be used to
* change the time-out value.
*
* @param	BaseAddr is the base address of the scu timer.
* @param	Value is the count to be loaded in to the load register.
*
* @return	None.
*
* @note		C-style signature:
*		void XScuTimer_SetControlReg(u32 BaseAddr, u32 Value)
*
******************************************************************************/
#define XScuTimer_SetControlReg(BaseAddr, Value)			\
	XScuTimer_WriteReg(BaseAddr, XSCUTIMER_CONTROL_OFFSET, Value)

/****************************************************************************/
/**
*
* Returns the current timer load register value.
*
* @param	BaseAddr is the base address of the scu timer.
*
* @return	Contents of the timer load register.
*
* @note		C-style signature:
		u32 XScuTimer_GetControlReg(u32 BaseAddr)
*
******************************************************************************/
#define XScuTimer_GetControlReg(BaseAddr)				\
	XScuTimer_ReadReg(BaseAddr, XSCUTIMER_CONTROL_OFFSET)

/****************************************************************************/
/**
*
* Write to the timer counter register.
*
* @param	BaseAddr is the base address of the scu timer.
* @param	Value is the count to be loaded in to the counter register.
*
* @return	None.
*
* @note		C-style signature:
*		void XScuTimer_SetIntrReg(u32 BaseAddr, u32 Value)
*
******************************************************************************/
#define XScuTimer_SetIntrReg(BaseAddr, Value)				\
	XScuTimer_WriteReg(BaseAddr, XSCUTIMER_ISR_OFFSET, Value)

/****************************************************************************/
/**
*
* Returns the current timer counter register value.
*
* @param	BaseAddr is the base address of the scu timer.
*
* @return	Contents of the timer counter register.
*
* @note		C-style signature:
		u32 XScuTimer_GetIntrReg(u32 BaseAddr)
*
******************************************************************************/
#define XScuTimer_GetIntrReg(BaseAddr)					\
	XScuTimer_ReadReg(BaseAddr, XSCUTIMER_ISR_OFFSET)

/****************************************************************************/
/**
*
* Read from the given Timer register.
*
* @param	BaseAddr is the base address of the device
* @param	RegOffset is the register offset to be read
*
* @return	The 32-bit value of the register
*
* @note		C-style signature:
*		u32 XScuTimer_ReadReg(u32 BaseAddr, u32 RegOffset)
*
*****************************************************************************/
#define XScuTimer_ReadReg(BaseAddr, RegOffset)		\
	Xil_In32((BaseAddr) + (RegOffset))

/****************************************************************************/
/**
*
* Write to the given Timer register.
*
* @param	BaseAddr is the base address of the device
* @param	RegOffset is the register offset to be written
* @param	Data is the 32-bit value to write to the register
*
* @return	None.
*
* @note		C-style signature:
*		void XScuTimer_WriteReg(u32 BaseAddr, u32 RegOffset, u32 Data)
*
*****************************************************************************/
#define XScuTimer_WriteReg(BaseAddr, RegOffset, Data)	\
	Xil_Out32((BaseAddr) + (RegOffset), (Data))

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

#ifdef __cplusplus
}
#endif

#endif	/* end of protection macro */
/** @} */
