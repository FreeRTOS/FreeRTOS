/* $Id: xttcps.h,v 1.1.2.1 2011/01/20 04:08:59 sadanan Exp $ */
/******************************************************************************
*
* (c) Copyright 2010 Xilinx, Inc. All rights reserved.
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
/*****************************************************************************/
/**
*
* @file xttcps.h
*
* This is the driver for one 16-bit timer counter in the Triple Timer Counter
* (TTC) module in the Ps block.
*
* The TTC module provides three independent timer/counter modules that can each
* be clocked using either the system clock (pclk) or an externally driven
* clock (ext_clk). In addition, each counter can independently prescale its
* selected clock input (divided by 2 to 65536). Counters can be set to
* decrement or increment.
*
* Each of the counters can be programmed to generate interrupt pulses:
*	. At a regular, predefined period, that is on a timed interval
*	. When the counter registers overflow
* 	. When the count matches any one of the three 'match' registers
*
* Therefore, up to six different events can trigger a timer interrupt: three
* match interrupts, an overflow interrupt, an interval interrupt and an event
* timer interrupt. Note that the overflow interrupt and the interval interrupt
* are mutually exclusive.
*
* <b>Initialization & Configuration</b>
*
* An XTtcPs_Config structure is used to configure a driver instance.
* Information in the XTtcPs_Config structure is the hardware properties
* about the device.
*
* A driver instance is initialized through
* XTtcPs_CfgInitialize(InstancePtr, CfgPtr, EffectiveAddr). Where CfgPtr
* is a pointer to the XTtcPs_Config structure, it can be looked up statically
* through XTtcPs_LookupConfig(DeviceID), or passed in by the caller. The
* EffectiveAddr can be the static base address of the device or virtual
* mapped address if address translation is supported.
*
* <b>Interrupts</b>
*
* Interrupt handler is not provided by the driver, as handling of interrupt
* is application specific.
*
* @note
* The default setting for a timer/counter is:
*  - Overflow Mode
*  - Internal clock (pclk) selected
*  - Counter disabled
*  - All Interrupts disabled
*  - Output waveforms disabled
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- ------ -------- -----------------------------------------------------
* 1.00a drg/jz 01/20/10 First release..
* 2.0   adk    12/10/13 Updated as per the New Tcl API's
*
* </pre>
*
******************************************************************************/

#ifndef XTTCPS_H		/* prevent circular inclusions */
#define XTTCPS_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xttcps_hw.h"
#include "xstatus.h"

/************************** Constant Definitions *****************************/

/** @name Configuration options
 *
 * Options for the device. Each of the options is bit field, so more than one
 * options can be specified.
 *
 * @{
 */
#define XTTCPS_OPTION_EXTERNAL_CLK	0x0001 	/**< External clock source */
#define XTTCPS_OPTION_CLK_EDGE_NEG	0x0002	/**< Clock on trailing edge for
						     external clock*/
#define XTTCPS_OPTION_INTERVAL_MODE	0x0004	/**< Interval mode */
#define XTTCPS_OPTION_DECREMENT		0x0008	/**< Decrement the counter */
#define XTTCPS_OPTION_MATCH_MODE	0x0010	/**< Match mode */
#define XTTCPS_OPTION_WAVE_DISABLE	0x0020 	/**< No waveform output */
#define XTTCPS_OPTION_WAVE_POLARITY	0x0040	/**< Waveform polarity */
/*@}*/

/**************************** Type Definitions *******************************/

/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;	  /**< Unique ID for device */
	u32 BaseAddress;  /**< Base address for device */
	u32 InputClockHz; /**< Input clock frequency */
} XTtcPs_Config;

/**
 * The XTtcPs driver instance data. The user is required to allocate a
 * variable of this type for each PS timer/counter device in the system. A
 * pointer to a variable of this type is then passed to various driver API
 * functions.
 */
typedef struct {
	XTtcPs_Config Config;	/**< Configuration structure */
	u32 IsReady;		/**< Device is initialized and ready */
} XTtcPs;


/***************** Macros (Inline Functions) Definitions *********************/

/*
 * Internal helper macros
 */
#define InstReadReg(InstancePtr, RegOffset) \
    (Xil_In32(((InstancePtr)->Config.BaseAddress) + (RegOffset)))

#define InstWriteReg(InstancePtr, RegOffset, Data) \
    (Xil_Out32(((InstancePtr)->Config.BaseAddress) + (RegOffset), (Data)))

/*****************************************************************************/
/**
*
* This function starts the counter/timer without resetting the counter value.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
*
* @return	None
*
* @note		C-style signature:
*		void XTtcPs_Start(XTtcPs *InstancePtr)
*
****************************************************************************/
#define XTtcPs_Start(InstancePtr)	\
		InstWriteReg((InstancePtr), XTTCPS_CNT_CNTRL_OFFSET,	\
		(InstReadReg((InstancePtr), XTTCPS_CNT_CNTRL_OFFSET) &	\
		 ~XTTCPS_CNT_CNTRL_DIS_MASK))

/*****************************************************************************/
/**
*
* This function stops the counter/timer. This macro may be called at any time
* to stop the counter. The counter holds the last value until it is reset,
* restarted or enabled.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
*
* @return	None
*
* @note		C-style signature:
*		void XTtcPs_Stop(XTtcPs *InstancePtr)
*
****************************************************************************/
#define XTtcPs_Stop(InstancePtr)		\
		InstWriteReg((InstancePtr), XTTCPS_CNT_CNTRL_OFFSET,	\
		(InstReadReg((InstancePtr), XTTCPS_CNT_CNTRL_OFFSET) |	\
		 XTTCPS_CNT_CNTRL_DIS_MASK))

/*****************************************************************************/
/**
*
* This function checks whether the timer counter has already started.
*
* @param	InstancePtr is a pointer to the XTtcPs instance
*
* @return	Non-zero if the device has started, '0' otherwise.
*
* @note		C-style signature:
*		int XTtcPs_IsStarted(XTtcPs *InstancePtr)
*
****************************************************************************/
#define XTtcPs_IsStarted(InstancePtr) \
     (int)((InstReadReg((InstancePtr), XTTCPS_CNT_CNTRL_OFFSET) & \
       XTTCPS_CNT_CNTRL_DIS_MASK) == 0)

/*****************************************************************************/
/**
*
* This function returns the current 16-bit counter value. It may be called at
* any time.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
*
* @return	16-bit counter value.
*
* @note		C-style signature:
*		u16 XTtcPs_GetCounterValue(XTtcPs *InstancePtr)
*
****************************************************************************/
#define XTtcPs_GetCounterValue(InstancePtr) \
		(u16)InstReadReg((InstancePtr), XTTCPS_COUNT_VALUE_OFFSET)

/*****************************************************************************/
/**
*
* This function sets the interval value to be used in interval mode.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
* @param	Value is the 16-bit value to be set in the interval register.
*
* @return	None
*
* @note		C-style signature:
*		void XTtcPs_SetInterval(XTtcPs *InstancePtr, u16 Value)
*
****************************************************************************/
#define XTtcPs_SetInterval(InstancePtr, Value)	\
		InstWriteReg((InstancePtr), XTTCPS_INTERVAL_VAL_OFFSET, (Value))

/*****************************************************************************/
/**
*
* This function gets the interval value from the interval register.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
*
* @return	16-bit interval value
*
* @note		C-style signature:
*		u16 XTtcPs_GetInterval(XTtcPs *InstancePtr)
*
****************************************************************************/
#define XTtcPs_GetInterval(InstancePtr) \
		(u16)InstReadReg((InstancePtr), XTTCPS_INTERVAL_VAL_OFFSET)

/*****************************************************************************/
/**
*
* This macro resets the count register. It may be called at any time. The
* counter is reset to either 0 or 0xFFFF, or the interval value, depending on
* the increment/decrement mode. The state of the counter, as started or
* stopped, is not affected by calling reset.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
*
* @return	None
*
* @note		C-style signature:
*		void XTtcPs_ResetCounterValue(XTtcPs *InstancePtr)
*
****************************************************************************/
#define XTtcPs_ResetCounterValue(InstancePtr) \
		InstWriteReg((InstancePtr), XTTCPS_CNT_CNTRL_OFFSET,	\
		(InstReadReg((InstancePtr), XTTCPS_CNT_CNTRL_OFFSET) | \
		 XTTCPS_CNT_CNTRL_RST_MASK))

/*****************************************************************************/
/**
*
* This function enables the interrupts.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
* @param	InterruptMask defines which interrupt should be enabled.
*		Constants are defined in xttcps_hw.h as XTTCPS_IXR_*.
*		This is a bit mask, all set bits will be enabled, cleared bits
*		will not be disabled.
*
* @return	None.
*
* @note
* C-style signature:
*	void XTtcPs_EnableInterrupts(XTtcPs *InstancePtr, u32 InterruptMask)
*
******************************************************************************/
#define XTtcPs_EnableInterrupts(InstancePtr, InterruptMask)		\
		InstWriteReg((InstancePtr), XTTCPS_IER_OFFSET,		\
		(InstReadReg((InstancePtr), XTTCPS_IER_OFFSET) |	\
		 (InterruptMask)))

/*****************************************************************************/
/**
*
* This function disables the interrupts.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
* @param	InterruptMask defines which interrupt should be disabled.
*		Constants are defined in xttcps_hw.h as XTTCPS_IXR_*.
*		This is a bit mask, all set bits will be disabled, cleared bits
*		will not be disabled.
*
* @return	None.
*
* @note
* C-style signature:
*	void XTtcPs_DisableInterrupts(XTtcPs *InstancePtr, u32 InterruptMask)
*
******************************************************************************/
#define XTtcPs_DisableInterrupts(InstancePtr, InterruptMask) \
		InstWriteReg((InstancePtr), XTTCPS_IER_OFFSET,	\
		(InstReadReg((InstancePtr), XTTCPS_IER_OFFSET) &	\
		 ~(InterruptMask)))

/*****************************************************************************/
/**
*
* This function reads the interrupt status.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
*
* @return	None.
*
* @note		C-style signature:
*		u32 XTtcPs_GetInterruptStatus(XTtcPs *InstancePtr)
*
******************************************************************************/
#define XTtcPs_GetInterruptStatus(InstancePtr)	 \
		InstReadReg((InstancePtr), XTTCPS_ISR_OFFSET)

/*****************************************************************************/
/**
*
* This function clears the interrupt status.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
* @param	InterruptMask defines which interrupt should be cleared.
*		Constants are defined in xttcps_hw.h as XTTCPS_IXR_*.
*		This is a bit mask, all set bits will be cleared, cleared bits
*		will not be cleared.
*
* @return	None.
*
* @note
* C-style signature:
*	void XTtcPs_ClearInterruptStatus(XTtcPs *InstancePtr, u32 InterruptMask)
*
******************************************************************************/
#define XTtcPs_ClearInterruptStatus(InstancePtr, InterruptMask) \
		InstWriteReg((InstancePtr), XTTCPS_ISR_OFFSET, \
		 (InterruptMask))


/************************** Function Prototypes ******************************/

/*
 * Initialization functions in xttcps_sinit.c
 */
XTtcPs_Config *XTtcPs_LookupConfig(u16 DeviceId);

/*
 * Required functions, in xttcps.c
 */
int XTtcPs_CfgInitialize(XTtcPs *InstancePtr,
         XTtcPs_Config * ConfigPtr, u32 EffectiveAddr);

void XTtcPs_SetMatchValue(XTtcPs *InstancePtr, u8 MatchIndex, u16 Value);
u16 XTtcPs_GetMatchValue(XTtcPs *InstancePtr, u8 MatchIndex);

void XTtcPs_SetPrescaler(XTtcPs *InstancePtr, u8 PrescalerValue);
u8 XTtcPs_GetPrescaler(XTtcPs *InstancePtr);

void XTtcPs_CalcIntervalFromFreq(XTtcPs *InstancePtr, u32 Freq,
        u16 *Interval, u8 *Prescaler);

/*
 * Functions for options, in file xttcps_options.c
 */
int XTtcPs_SetOptions(XTtcPs *InstancePtr, u32 Options);
u32 XTtcPs_GetOptions(XTtcPs *InstancePtr);

/*
 * Function for self-test, in file xttcps_selftest.c
 */
int XTtcPs_SelfTest(XTtcPs *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
