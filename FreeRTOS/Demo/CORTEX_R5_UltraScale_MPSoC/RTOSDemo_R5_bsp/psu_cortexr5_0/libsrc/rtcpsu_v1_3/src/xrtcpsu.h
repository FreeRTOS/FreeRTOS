/******************************************************************************
*
* Copyright (C) 2015 Xilinx, Inc.  All rights reserved.
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
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* XILINX CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
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
* @file xrtcpsu.h
* @addtogroup rtcpsu_v1_0
* @{
* @details
*
* The Xilinx RTC driver component.  This component supports the Xilinx
* RTC Controller. RTC Core and RTC controller are the two main important sub-
* components for this RTC module. RTC core can run even in the battery powered
* domain when the power from auxiliary source is down. Because of this, RTC core
* latches the calibration,programmed time. This core interfaces with the crystal
* oscillator and maintains current time in seconds.Calibration circuitry
* calculates a second with maximum 1 PPM inaccuracy using a crystal oscillator
* with arbitrary static inaccuracy. Core also responsible to maintain control
* value used by the oscillator and power switching circuitry.
*
* RTC controller includes an APB interface responsible for register access with
* in controller and core. It contains alarm generation logic including the alarm
* register to hold alarm time in seconds.Interrupt management using Interrupt
* status, Interrupt mask, Interrupt enable, Interrupt disable registers are
* included to manage alarm and seconds interrupts. Address Slave error interrupts
* are not being handled by this driver component.
*
* This driver supports the following features:
* - Setting the RTC time.
* - Setting the Alarm value that can be one-time alarm or a periodic alarm.
* - Modifying the calibration value.
*
* <b>Initialization & Configuration</b>
*
* The XRtcPsu_Config structure is used by the driver to configure itself.
* Fields inside this structure are properties of XRtcPsu based on its hardware
* build.
*
* To support multiple runtime loading and initialization strategies employed
* by various operating systems, the driver instance can be initialized in the
* following way:
*
*   - XRtcPsu_CfgInitialize(InstancePtr, CfgPtr, EffectiveAddr) - Uses a
*	 configuration structure provided by the caller. If running in a system
*	 with address translation, the parameter EffectiveAddr should be the
* 	  virtual address.
*
* <b>Interrupts</b>
*
* The driver defaults to no interrupts at initialization such that interrupts
* must be enabled if desired. An interrupt is generated for one of the
* following conditions.
*
* - Alarm is generated.
* - A new second is generated.
*
* The application can control which interrupts are enabled using the
* XRtcPsu_SetInterruptMask() function.
*
* In order to use interrupts, it is necessary for the user to connect the
* driver interrupt handler, XRtcPsu_InterruptHandler(), to the interrupt
* system of the application. A separate handler should be provided by the
* application to communicate with the interrupt system, and conduct
* application specific interrupt handling. An application registers its own
* handler through the XRtcPsu_SetHandler() function.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- -----  -------- -----------------------------------------------
* 1.00  kvn    04/21/15 First release
* 1.1   kvn    09/25/15 Modify control register to enable battery
*                       switching when vcc_psaux is not available.
* 1.3   vak    04/25/16 Corrected the RTC read and write time logic(cr#948833).
* </pre>
*
******************************************************************************/


#ifndef XRTC_H_			/* prevent circular inclusions */
#define XRTC_H_			/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xil_assert.h"
#include "xil_io.h"
#include "xrtcpsu_hw.h"
#include "xil_types.h"

/************************** Constant Definitions *****************************/

/** @name Callback events
 *
 * These constants specify the handler events that an application can handle
 * using its specific handler function. Note that these constants are not bit
 * mask, so only one event can be passed to an application at a time.
 *
 * @{
 */
#define XRTCPSU_EVENT_ALARM_GEN		1U /**< Alarm generated event */
#define XRTCPSU_EVENT_SECS_GEN		2U /**< A new second generated event */
/*@}*/

#define XRTCPSU_CRYSTAL_OSC_EN		(u32)1 << XRTC_CTL_OSC_SHIFT
/**< Separate Mask for Crystal oscillator bit Enable */

/**************************** Type Definitions *******************************/

/******************************************************************************/
/**
 * This data type defines a handler that an application defines to communicate
 * with interrupt system to retrieve state information about an application.
 *
 * @param	CallBackRef is a callback reference passed in by the upper layer
 *		when setting the handler, and is passed back to the upper layer
 *		when the handler is called. It is used to find the device driver
 *		instance.
 * @param	Event contains one of the event constants indicating events that
 *		have occurred.
 * @param	EventData contains the number of bytes sent or received at the
 *		time of the call for send and receive events and contains the
 *		modem status for modem events.
 *
 ******************************************************************************/
typedef void (*XRtcPsu_Handler) (void *CallBackRef, u32 Event);

/**
 * This typedef contains configuration information for a device.
 */
typedef struct {
	u16 DeviceId;		/**< Unique ID of device */
	u32 BaseAddr;		/**< Register base address */
} XRtcPsu_Config;

/**
 * The XRtcPsu driver instance data. The user is required to allocate a
 * variable of this type for the RTC device in the system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XRtcPsu_Config RtcConfig; 	/**< Device configuration */
	u32 IsReady;				/**< Device is initialized and ready */
	u32 PeriodicAlarmTime;
	u8 IsPeriodicAlarm;
	u32 OscillatorFreq;
	u32 CalibrationValue;
	XRtcPsu_Handler Handler;
	void *CallBackRef;			/**< Callback reference for event handler */
	u32 TimeUpdated;
	u32 CurrTimeUpdated;
} XRtcPsu;

/**
 * This typedef contains DateTime format structure.
 */
typedef struct {
	u32 Year;
	u32 Month;
	u32 Day;
	u32 Hour;
	u32 Min;
	u32 Sec;
	u32 WeekDay;
} XRtcPsu_DT;


/************************* Variable Definitions ******************************/


/***************** Macros (Inline Functions) Definitions *********************/

#define XRTC_CALIBRATION_VALUE 0x00198231U
#define XRTC_TYPICAL_OSC_FREQ 33330U

/****************************************************************************/
/**
*
* This macro updates the current time of RTC device.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
* @param	Time is the desired time for RTC in seconds.
*
* @return	None.
*
* @note		C-Style signature:
* 		void XRtcPsu_SetTime(XRtcPsu *InstancePtr, u32 Time)
*
*****************************************************************************/
#define XRtcPsu_WriteSetTime(InstancePtr,Time) \
	XRtcPsu_WriteReg(((InstancePtr)->RtcConfig.BaseAddr + \
				XRTC_SET_TIME_WR_OFFSET),(Time))

/****************************************************************************/
/**
*
* This macro returns the last set time of RTC device. Whenever a reset
* happens, the last set time will be zeroth day first sec.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
*
* @return	The last set time in seconds.
*
* @note		C-Style signature:
* 		u32 XRtcPsu_GetLastSetTime(XRtcPsu *InstancePtr)
*
*****************************************************************************/
#define XRtcPsu_GetLastSetTime(InstancePtr) \
	XRtcPsu_ReadReg((InstancePtr)->RtcConfig.BaseAddr + XRTC_SET_TIME_RD_OFFSET)

/****************************************************************************/
/**
*
* This macro returns the calibration value of RTC device.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
*
* @return	Calibration value for RTC.
*
* @note		C-Style signature:
* 		u32 XRtcPsu_GetCalibration(XRtcPsu *InstancePtr)
*
*****************************************************************************/
#define XRtcPsu_GetCalibration(InstancePtr) \
	XRtcPsu_ReadReg((InstancePtr)->RtcConfig.BaseAddr+XRTC_CALIB_RD_OFFSET)

/****************************************************************************/
/**
*
* This macro returns the current time of RTC device.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
*
* @return	Current Time. This current time will be in seconds.
*
* @note		C-Style signature:
* 		u32 XRtcPsu_ReadCurrentTime(XRtcPsu *InstancePtr)
*
*****************************************************************************/
#define XRtcPsu_ReadCurrentTime(InstancePtr) \
	XRtcPsu_ReadReg((InstancePtr)->RtcConfig.BaseAddr+XRTC_CUR_TIME_OFFSET)

/****************************************************************************/
/**
*
* This macro sets the control register value of RTC device.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
* @param	Value is the desired control register value for RTC.
*
* @return	None.
*
* @note		C-Style signature:
* 		void XRtcPsu_SetControlRegister(XRtcPsu *InstancePtr, u32 Value)
*
*****************************************************************************/
#define XRtcPsu_SetControlRegister(InstancePtr, Value) \
	XRtcPsu_WriteReg((InstancePtr)->RtcConfig.BaseAddr + \
			XRTC_CTL_OFFSET,(Value))

/****************************************************************************/
/**
*
* This macro returns the safety check register value of RTC device.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
*
* @return	Safety check register value.
*
* @note		C-Style signature:
* 		u32 XRtcPsu_GetSafetyCheck(XRtcPsu *InstancePtr)
*
*****************************************************************************/
#define XRtcPsu_GetSafetyCheck(InstancePtr)	\
	XRtcPsu_ReadReg((InstancePtr)->RtcConfig.BaseAddr+XRTC_SFTY_CHK_OFFSET)

/****************************************************************************/
/**
*
* This macro sets the safety check register value of RTC device.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
* @param	Value is a safety check value to be written in register.
*
* @return	None.
*
* @note		C-Style signature:
* 		void XRtcPsu_SetSafetyCheck(XRtcPsu *InstancePtr, u32 Value)
*
*****************************************************************************/
#define XRtcPsu_SetSafetyCheck(InstancePtr, Value)	\
	XRtcPsu_WriteReg((InstancePtr)->RtcConfig.BaseAddr + \
			XRTC_SFTY_CHK_OFFSET,(Value))

/****************************************************************************/
/**
*
* This macro resets the alarm register
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
*
* @return	None.
*
* @note		C-Style signature:
* 		u32 XRtcPsu_ResetAlarm(XRtcPsu *InstancePtr)
*
*****************************************************************************/
#define XRtcPsu_ResetAlarm(InstancePtr) \
		XRtcPsu_WriteReg((InstancePtr)->RtcConfig.BaseAddr + \
				XRTC_ALRM_OFFSET,XRTC_ALRM_RSTVAL)

/****************************************************************************/
/**
*
* This macro rounds off the given number
*
* @param	Number is the one that needs to be rounded off..
*
* @return	The rounded off value of the input number.
*
* @note		C-Style signature:
* 		u32 XRtcPsu_RoundOff(float Number)
*
*****************************************************************************/
#define XRtcPsu_RoundOff(Number) \
	(u32)(((Number) < (u32)0) ? ((Number) - (u32)0.5) : ((Number) + (u32)0.5))

/************************** Function Prototypes ******************************/

/* Functions in xrtcpsu.c */
s32 XRtcPsu_CfgInitialize(XRtcPsu *InstancePtr, XRtcPsu_Config *ConfigPtr,
				u32 EffectiveAddr);

void XRtcPsu_SetAlarm(XRtcPsu *InstancePtr, u32 Alarm, u32 Periodic);
void XRtcPsu_SecToDateTime(u32 Seconds, XRtcPsu_DT *dt);
u32 XRtcPsu_DateTimeToSec(XRtcPsu_DT *dt);
void XRtcPsu_CalculateCalibration(XRtcPsu *InstancePtr,u32 TimeReal,
		u32 CrystalOscFreq);
u32 XRtcPsu_IsSecondsEventGenerated(XRtcPsu *InstancePtr);
u32 XRtcPsu_IsAlarmEventGenerated(XRtcPsu *InstancePtr);
u32 XRtcPsu_GetCurrentTime(XRtcPsu *InstancePtr);
void XRtcPsu_SetTime(XRtcPsu *InstancePtr,u32 Time);

/* interrupt functions in xrtcpsu_intr.c */
void XRtcPsu_SetInterruptMask(XRtcPsu *InstancePtr, u32 Mask);
void XRtcPsu_ClearInterruptMask(XRtcPsu *InstancePtr, u32 Mask);
void XRtcPsu_InterruptHandler(XRtcPsu *InstancePtr);
void XRtcPsu_SetHandler(XRtcPsu *InstancePtr, XRtcPsu_Handler FuncPtr,
			 void *CallBackRef);

/* Functions in xrtcpsu_selftest.c */
s32 XRtcPsu_SelfTest(XRtcPsu *InstancePtr);

/* Functions in xrtcpsu_sinit.c */
XRtcPsu_Config *XRtcPsu_LookupConfig(u16 DeviceId);


#endif /* XRTC_H_ */
/** @} */
