/******************************************************************************
*
* Copyright (C) 2002 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xtmrctr_l.h
*
* This header file contains identifiers and low-level driver functions (or
* macros) that can be used to access the device.  The user should refer to the
* hardware device specification for more details of the device operation.
* High-level driver functions are defined in xtmrctr.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00b jhl  04/24/02 First release
* 1.10b mta  03/21/07 Updated to new coding style
* 2.00a ktn  10/30/09 Updated to use HAL API's. _m is removed from all the macro
*		      definitions.
* 2.01a ktn  07/12/10 Renamed the macro XTimerCtr_ReadReg as XTmrCtr_ReadReg
*		      for naming consistency (CR 559142).
* 2.04a sdm  07/12/11 Added the CASC mode bit in the TCSRO register for the
*		      cascade mode operation.
*		      The cascade mode of operation is present in the latest
*		      versions of the axi_timer IP. Please check the HW
*		      Datasheet to see whether this feature is present in the
*		      version of the IP that you are using.
* </pre>
*
******************************************************************************/

#ifndef XTMRCTR_L_H		/* prevent circular inclusions */
#define XTMRCTR_L_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/

/**
 * Defines the number of timer counters within a single hardware device. This
 * number is not currently parameterized in the hardware but may be in the
 * future.
 */
#define XTC_DEVICE_TIMER_COUNT		2

/* Each timer counter consumes 16 bytes of address space */

#define XTC_TIMER_COUNTER_OFFSET	16

/** @name Register Offset Definitions
 * Register offsets within a timer counter, there are multiple
 * timer counters within a single device
 * @{
 */

#define XTC_TCSR_OFFSET		0	/**< Control/Status register */
#define XTC_TLR_OFFSET		4	/**< Load register */
#define XTC_TCR_OFFSET		8	/**< Timer counter register */

/* @} */

/** @name Control Status Register Bit Definitions
 * Control Status Register bit masks
 * Used to configure the timer counter device.
 * @{
 */

#define XTC_CSR_CASC_MASK		0x00000800 /**< Cascade Mode */
#define XTC_CSR_ENABLE_ALL_MASK		0x00000400 /**< Enables all timer
							counters */
#define XTC_CSR_ENABLE_PWM_MASK		0x00000200 /**< Enables the Pulse Width
							Modulation */
#define XTC_CSR_INT_OCCURED_MASK	0x00000100 /**< If bit is set, an
							interrupt has occured.
							If set and '1' is
							written to this bit
							position, bit is
							cleared. */
#define XTC_CSR_ENABLE_TMR_MASK		0x00000080 /**< Enables only the
							specific timer */
#define XTC_CSR_ENABLE_INT_MASK		0x00000040 /**< Enables the interrupt
							output. */
#define XTC_CSR_LOAD_MASK		0x00000020 /**< Loads the timer using
							the load value provided
							earlier in the Load
							Register,
							XTC_TLR_OFFSET. */
#define XTC_CSR_AUTO_RELOAD_MASK	0x00000010 /**< In compare mode,
							configures
							the timer counter to
							reload  from the
							Load Register. The
							default  mode
							causes the timer counter
							to hold when the compare
							value is hit. In capture
							mode, configures  the
							timer counter to not
							hold the previous
							capture value if a new
							event occurs. The
							default mode cause the
							timer counter to hold
							the capture value until
							recognized. */
#define XTC_CSR_EXT_CAPTURE_MASK	0x00000008 /**< Enables the
							external input
							to the timer counter. */
#define XTC_CSR_EXT_GENERATE_MASK	0x00000004 /**< Enables the
							external generate output
							for the timer. */
#define XTC_CSR_DOWN_COUNT_MASK		0x00000002 /**< Configures the timer
							counter to count down
							from start value, the
							default is to count
							up.*/
#define XTC_CSR_CAPTURE_MODE_MASK	0x00000001 /**< Enables the timer to
							capture the timer
							counter value when the
							external capture line is
							asserted. The default
							mode is compare mode.*/
/* @} */

/**************************** Type Definitions *******************************/

extern u8 XTmrCtr_Offsets[];

/***************** Macros (Inline Functions) Definitions *********************/

/*****************************************************************************/
/**
* Read one of the timer counter registers.
*
* @param	BaseAddress contains the base address of the timer counter
*		device.
* @param	TmrCtrNumber contains the specific timer counter within the
*		device, a zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
* @param	RegOffset contains the offset from the 1st register of the timer
*		counter to select the specific register of the timer counter.
*
* @return	The value read from the register, a 32 bit value.
*
* @note		C-Style signature:
* 		u32 XTmrCtr_ReadReg(u32 BaseAddress, u8 TimerNumber,
					unsigned RegOffset);
******************************************************************************/
#define XTmrCtr_ReadReg(BaseAddress, TmrCtrNumber, RegOffset)	\
	Xil_In32((BaseAddress) + XTmrCtr_Offsets[(TmrCtrNumber)] + \
			(RegOffset))

#ifndef XTimerCtr_ReadReg
#define XTimerCtr_ReadReg XTmrCtr_ReadReg
#endif

/*****************************************************************************/
/**
* Write a specified value to a register of a timer counter.
*
* @param	BaseAddress is the base address of the timer counter device.
* @param	TmrCtrNumber is the specific timer counter within the device, a
*		zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
* @param	RegOffset contain the offset from the 1st register of the timer
*		counter to select the specific register of the timer counter.
* @param	ValueToWrite is the 32 bit value to be written to the register.
*
* @note		C-Style signature:
* 		void XTmrCtr_WriteReg(u32 BaseAddress, u8 TimerNumber,
*					unsigned RegOffset, u32 ValueToWrite);
******************************************************************************/
#define XTmrCtr_WriteReg(BaseAddress, TmrCtrNumber, RegOffset, ValueToWrite)\
	Xil_Out32(((BaseAddress) + XTmrCtr_Offsets[(TmrCtrNumber)] +	\
			   (RegOffset)), (ValueToWrite))

/****************************************************************************/
/**
*
* Set the Control Status Register of a timer counter to the specified value.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device, a
*		zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
* @param	RegisterValue is the 32 bit value to be written to the register.
*
* @return	None.
*
* @note		C-Style signature:
* 		void XTmrCtr_SetControlStatusReg(u32 BaseAddress,
*					u8 TmrCtrNumber,u32 RegisterValue);
*****************************************************************************/
#define XTmrCtr_SetControlStatusReg(BaseAddress, TmrCtrNumber, RegisterValue)\
	XTmrCtr_WriteReg((BaseAddress), (TmrCtrNumber), XTC_TCSR_OFFSET,     \
					   (RegisterValue))

/****************************************************************************/
/**
*
* Get the Control Status Register of a timer counter.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device,
*		a zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	The value read from the register, a 32 bit value.
*
* @note		C-Style signature:
* 		u32 XTmrCtr_GetControlStatusReg(u32 BaseAddress,
*						u8 TmrCtrNumber);
*****************************************************************************/
#define XTmrCtr_GetControlStatusReg(BaseAddress, TmrCtrNumber)		\
	XTmrCtr_ReadReg((BaseAddress), (TmrCtrNumber), XTC_TCSR_OFFSET)

/****************************************************************************/
/**
*
* Get the Timer Counter Register of a timer counter.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device,
*		a zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	The value read from the register, a 32 bit value.
*
* @note		C-Style signature:
* 		u32 XTmrCtr_GetTimerCounterReg(u32 BaseAddress,
*						u8 TmrCtrNumber);
*****************************************************************************/
#define XTmrCtr_GetTimerCounterReg(BaseAddress, TmrCtrNumber)		  \
	XTmrCtr_ReadReg((BaseAddress), (TmrCtrNumber), XTC_TCR_OFFSET) \

/****************************************************************************/
/**
*
* Set the Load Register of a timer counter to the specified value.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device, a
*		zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
* @param	RegisterValue is the 32 bit value to be written to the register.
*
* @return	None.
*
* @note		C-Style signature:
* 		void XTmrCtr_SetLoadReg(u32 BaseAddress, u8 TmrCtrNumber,
*						  u32 RegisterValue);
*****************************************************************************/
#define XTmrCtr_SetLoadReg(BaseAddress, TmrCtrNumber, RegisterValue)	 \
	XTmrCtr_WriteReg((BaseAddress), (TmrCtrNumber), XTC_TLR_OFFSET, \
					   (RegisterValue))

/****************************************************************************/
/**
*
* Get the Load Register of a timer counter.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device, a
*		zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	The value read from the register, a 32 bit value.
*
* @note		C-Style signature:
* 		u32 XTmrCtr_GetLoadReg(u32 BaseAddress, u8 TmrCtrNumber);
*****************************************************************************/
#define XTmrCtr_GetLoadReg(BaseAddress, TmrCtrNumber)	\
XTmrCtr_ReadReg((BaseAddress), (TmrCtrNumber), XTC_TLR_OFFSET)

/****************************************************************************/
/**
*
* Enable a timer counter such that it starts running.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device, a
*		zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	None.
*
* @note		C-Style signature:
* 		void XTmrCtr_Enable(u32 BaseAddress, u8 TmrCtrNumber);
*****************************************************************************/
#define XTmrCtr_Enable(BaseAddress, TmrCtrNumber)			    \
	XTmrCtr_WriteReg((BaseAddress), (TmrCtrNumber), XTC_TCSR_OFFSET,   \
			(XTmrCtr_ReadReg((BaseAddress), ( TmrCtrNumber), \
			XTC_TCSR_OFFSET) | XTC_CSR_ENABLE_TMR_MASK))

/****************************************************************************/
/**
*
* Disable a timer counter such that it stops running.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device,
*		a zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	None.
*
* @note		C-Style signature:
* 		void XTmrCtr_Disable(u32 BaseAddress, u8 TmrCtrNumber);
*****************************************************************************/
#define XTmrCtr_Disable(BaseAddress, TmrCtrNumber)			  \
	XTmrCtr_WriteReg((BaseAddress), (TmrCtrNumber), XTC_TCSR_OFFSET, \
			(XTmrCtr_ReadReg((BaseAddress), (TmrCtrNumber),\
			XTC_TCSR_OFFSET) & ~ XTC_CSR_ENABLE_TMR_MASK))

/****************************************************************************/
/**
*
* Enable the interrupt for a timer counter.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device, a
*		zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	None.
*
* @note		C-Style signature:
* 		void XTmrCtr_EnableIntr(u32 BaseAddress, u8 TmrCtrNumber);
*****************************************************************************/
#define XTmrCtr_EnableIntr(BaseAddress, TmrCtrNumber)			    \
	XTmrCtr_WriteReg((BaseAddress), (TmrCtrNumber), XTC_TCSR_OFFSET,   \
			(XTmrCtr_ReadReg((BaseAddress), (TmrCtrNumber),  \
			XTC_TCSR_OFFSET) | XTC_CSR_ENABLE_INT_MASK))

/****************************************************************************/
/**
*
* Disable the interrupt for a timer counter.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device, a
*		zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	None.
*
* @note		C-Style signature:
* 		void XTmrCtr_DisableIntr(u32 BaseAddress, u8 TmrCtrNumber);
*****************************************************************************/
#define XTmrCtr_DisableIntr(BaseAddress, TmrCtrNumber)			   \
	XTmrCtr_WriteReg((BaseAddress), (TmrCtrNumber), XTC_TCSR_OFFSET,  \
	(XTmrCtr_ReadReg((BaseAddress), (TmrCtrNumber),		   \
		XTC_TCSR_OFFSET) & ~ XTC_CSR_ENABLE_INT_MASK))

/****************************************************************************/
/**
*
* Cause the timer counter to load it's Timer Counter Register with the value
* in the Load Register.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device, a
*		   zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	None.
*
* @note		C-Style signature:
* 		void XTmrCtr_LoadTimerCounterReg(u32 BaseAddress,
					u8 TmrCtrNumber);
*****************************************************************************/
#define XTmrCtr_LoadTimerCounterReg(BaseAddress, TmrCtrNumber)		  \
	XTmrCtr_WriteReg((BaseAddress), (TmrCtrNumber), XTC_TCSR_OFFSET, \
			(XTmrCtr_ReadReg((BaseAddress), (TmrCtrNumber),\
			XTC_TCSR_OFFSET) | XTC_CSR_LOAD_MASK))

/****************************************************************************/
/**
*
* Determine if a timer counter event has occurred.  Events are defined to be
* when a capture has occurred or the counter has roller over.
*
* @param	BaseAddress is the base address of the device.
* @param	TmrCtrNumber is the specific timer counter within the device, a
*		zero based number, 0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @note		C-Style signature:
* 		int XTmrCtr_HasEventOccurred(u32 BaseAddress, u8 TmrCtrNumber);
*****************************************************************************/
#define XTmrCtr_HasEventOccurred(BaseAddress, TmrCtrNumber)		\
		((XTmrCtr_ReadReg((BaseAddress), (TmrCtrNumber),	\
		XTC_TCSR_OFFSET) & XTC_CSR_INT_OCCURED_MASK) ==		\
		XTC_CSR_INT_OCCURED_MASK)

/************************** Function Prototypes ******************************/
/************************** Variable Definitions *****************************/
#ifdef __cplusplus
}
#endif
#endif /* end of protection macro */
