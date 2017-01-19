/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xttcps.h
* @addtogroup ttcps_v3_0
* @{
* @details
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
* 3.0	pkp    12/09/14 Added support for Zynq Ultrascale Mp.Also code
*			modified for MISRA-C:2012 compliance.
* 3.2   mus    10/28/16 Modified XTtcPs_GetCounterValue and XTtcPs_SetInterval
*                       macros to return 32 bit values for zynq ultrascale+mpsoc
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
/*
 * Flag for a9 processor
 */
 #if !defined (ARMR5) && !defined (__aarch64__) && !defined (ARMA53_32)
 #define ARMA9
 #endif

/*
 * Maximum Value for interval counter
 */
 #if defined(ARMA9)
 #define XTTCPS_MAX_INTERVAL_COUNT 0xFFFFU
 #else
 #define XTTCPS_MAX_INTERVAL_COUNT 0xFFFFFFFFU
 #endif

/** @name Configuration options
 *
 * Options for the device. Each of the options is bit field, so more than one
 * options can be specified.
 *
 * @{
 */
#define XTTCPS_OPTION_EXTERNAL_CLK	0x00000001U 	/**< External clock source */
#define XTTCPS_OPTION_CLK_EDGE_NEG	0x00000002U	/**< Clock on trailing edge for
						     external clock*/
#define XTTCPS_OPTION_INTERVAL_MODE	0x00000004U	/**< Interval mode */
#define XTTCPS_OPTION_DECREMENT		0x00000008U	/**< Decrement the counter */
#define XTTCPS_OPTION_MATCH_MODE	0x00000010U	/**< Match mode */
#define XTTCPS_OPTION_WAVE_DISABLE	0x00000020U 	/**< No waveform output */
#define XTTCPS_OPTION_WAVE_POLARITY	0x00000040U	/**< Waveform polarity */
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

/**
 * This typedef contains interval count
 */
#if defined(ARMA9)
typedef u16 XInterval;
#else
typedef u32 XInterval;
#endif
/***************** Macros (Inline Functions) Definitions *********************/

/*
 * Internal helper macros
 */
#define InstReadReg(InstancePtr, RegOffset) \
    (Xil_In32(((InstancePtr)->Config.BaseAddress) + (u32)(RegOffset)))

#define InstWriteReg(InstancePtr, RegOffset, Data) \
    (Xil_Out32(((InstancePtr)->Config.BaseAddress) + (u32)(RegOffset), (u32)(Data)))

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
     ((InstReadReg((InstancePtr), XTTCPS_CNT_CNTRL_OFFSET) & \
       XTTCPS_CNT_CNTRL_DIS_MASK) == 0U)

/*****************************************************************************/
/**
*
* This function returns the current 16-bit counter value. It may be called at
* any time.
*
* @param	InstancePtr is a pointer to the XTtcPs instance.
*
* @return	zynq:16 bit counter value.
*           zynq ultrascale+mpsoc:32 bit counter value.
*
* @note		C-style signature:
*		zynq: u16 XTtcPs_GetCounterValue(XTtcPs *InstancePtr)
*       zynq ultrascale+mpsoc: u32 XTtcPs_GetCounterValue(XTtcPs *InstancePtr)
*
****************************************************************************/
#if defined(ARMA9)
/*
 * ttc supports 16 bit counter for zynq
 */
#define XTtcPs_GetCounterValue(InstancePtr) \
		(u16)InstReadReg((InstancePtr), XTTCPS_COUNT_VALUE_OFFSET)
#else
/*
 * ttc supports 32 bit counter for zynq ultrascale+mpsoc
 */
#define XTtcPs_GetCounterValue(InstancePtr) \
               InstReadReg((InstancePtr), XTTCPS_COUNT_VALUE_OFFSET)
#endif

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
* @return	zynq:16 bit interval value.
*           zynq ultrascale+mpsoc:32 bit interval value.
*
* @note		C-style signature:
*		zynq: u16 XTtcPs_GetInterval(XTtcPs *InstancePtr)
*       zynq ultrascale+mpsoc: u32 XTtcPs_GetInterval(XTtcPs *InstancePtr)
*
****************************************************************************/
#if defined(ARMA9)
/*
 * ttc supports 16 bit interval counter for zynq
 */
#define XTtcPs_GetInterval(InstancePtr) \
		(u16)InstReadReg((InstancePtr), XTTCPS_INTERVAL_VAL_OFFSET)
#else
/*
 * ttc supports 32 bit interval counter for zynq ultrascale+mpsoc
 */
#define XTtcPs_GetInterval(InstancePtr) \
		InstReadReg((InstancePtr), XTTCPS_INTERVAL_VAL_OFFSET)
#endif
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
		 (u32)XTTCPS_CNT_CNTRL_RST_MASK))

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
s32 XTtcPs_CfgInitialize(XTtcPs *InstancePtr,
         XTtcPs_Config * ConfigPtr, u32 EffectiveAddr);

void XTtcPs_SetMatchValue(XTtcPs *InstancePtr, u8 MatchIndex, u16 Value);
u16 XTtcPs_GetMatchValue(XTtcPs *InstancePtr, u8 MatchIndex);

void XTtcPs_SetPrescaler(XTtcPs *InstancePtr, u8 PrescalerValue);
u8 XTtcPs_GetPrescaler(XTtcPs *InstancePtr);

void XTtcPs_CalcIntervalFromFreq(XTtcPs *InstancePtr, u32 Freq,
        XInterval *Interval, u8 *Prescaler);

/*
 * Functions for options, in file xttcps_options.c
 */
s32 XTtcPs_SetOptions(XTtcPs *InstancePtr, u32 Options);
u32 XTtcPs_GetOptions(XTtcPs *InstancePtr);

/*
 * Function for self-test, in file xttcps_selftest.c
 */
s32 XTtcPs_SelfTest(XTtcPs *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
/** @} */
