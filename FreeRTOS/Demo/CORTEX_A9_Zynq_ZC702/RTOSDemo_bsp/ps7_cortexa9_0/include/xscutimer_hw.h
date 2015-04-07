/******************************************************************************
*
* (c) Copyright 2010-12 Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
*
******************************************************************************/
/****************************************************************************/
/**
*
* @file xscutimer_hw.h
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
