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
*
* @file xrtcpsu.c
* @addtogroup rtcpsu_v1_0
* @{
*
* Functions in this file are the minimum required functions for the XRtcPsu
* driver. See xrtcpsu.h for a detailed description of the driver.
*
* @note 	None.
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	Changes
* ----- -----  -------- -----------------------------------------------
* 1.00  kvn    04/21/15 First release
* 1.1   kvn    09/25/15 Modify control register to enable battery
*                       switching when vcc_psaux is not available.
* 1.2          02/15/16 Corrected Calibration mask and Fractional
*                       mask in CalculateCalibration API.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xrtcpsu.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Variable Definitions *****************************/

static const u32 DaysInMonth[] = {31,28,31,30,31,30,31,31,30,31,30,31};

/************************** Function Prototypes ******************************/

static void XRtcPsu_StubHandler(void *CallBackRef, u32 Event);

/*****************************************************************************/
/*
*
* This function initializes a XRtcPsu instance/driver.
*
* The initialization entails:
* - Initialize all members of the XRtcPsu structure.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
* @param	ConfigPtr points to the XRtcPsu device configuration structure.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. If the address translation is not used then the
*		physical address is passed.
*		Unexpected errors may occur if the address mapping is changed
*		after this function is invoked.
*
* @return	XST_SUCCESS always.
*
* @note		None.
*
******************************************************************************/
s32 XRtcPsu_CfgInitialize(XRtcPsu *InstancePtr, XRtcPsu_Config *ConfigPtr,
				u32 EffectiveAddr)
{
	s32 Status;
	u32 ControlRegister;
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/*
	 * Set some default values for instance data, don't indicate the device
	 * is ready to use until everything has been initialized successfully.
	 */
	InstancePtr->IsReady = 0U;
	InstancePtr->RtcConfig.BaseAddr = EffectiveAddr;
	InstancePtr->RtcConfig.DeviceId = ConfigPtr->DeviceId;

	if(InstancePtr->OscillatorFreq == 0U) {
		InstancePtr->CalibrationValue = XRTC_CALIBRATION_VALUE;
		InstancePtr->OscillatorFreq = XRTC_TYPICAL_OSC_FREQ;
	}

	/* Set all handlers to stub values, let user configure this data later. */
	InstancePtr->Handler = XRtcPsu_StubHandler;

	InstancePtr->IsPeriodicAlarm = 0U;

	/* Set the calibration value in calibration register. */
	XRtcPsu_WriteReg(InstancePtr->RtcConfig.BaseAddr + XRTC_CALIB_WR_OFFSET,
				InstancePtr->CalibrationValue);

	/* Set the Oscillator crystal and Battery switch enable in control register. */
	ControlRegister = XRtcPsu_ReadReg(InstancePtr->RtcConfig.BaseAddr + XRTC_CTL_OFFSET);
	XRtcPsu_WriteReg(InstancePtr->RtcConfig.BaseAddr + XRTC_CTL_OFFSET,
			(ControlRegister | (u32)XRTCPSU_CRYSTAL_OSC_EN | (u32)XRTC_CTL_BATTERY_EN_MASK));

	/* Clear the Interrupt Status and Disable the interrupts. */
	XRtcPsu_WriteReg(InstancePtr->RtcConfig.BaseAddr + XRTC_INT_STS_OFFSET,
			((u32)XRTC_INT_STS_ALRM_MASK | (u32)XRTC_INT_STS_SECS_MASK));
	XRtcPsu_WriteReg(InstancePtr->RtcConfig.BaseAddr + XRTC_INT_DIS_OFFSET,
			((u32)XRTC_INT_DIS_ALRM_MASK | (u32)XRTC_INT_DIS_SECS_MASK));

	/* Indicate the component is now ready to use. */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	Status = XST_SUCCESS;
	return Status;
}

/****************************************************************************/
/**
*
* This function is a stub handler that is the default handler such that if the
* application has not set the handler when interrupts are enabled, this
* function will be called.
*
* @param	CallBackRef is unused by this function.
* @param	Event is unused by this function.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
static void XRtcPsu_StubHandler(void *CallBackRef, u32 Event)
{
	(void *) CallBackRef;
	(void) Event;
	/* Assert occurs always since this is a stub and should never be called */
	Xil_AssertVoidAlways();
}

/****************************************************************************/
/**
*
* This function sets the alarm value of RTC device.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance
* @param	Alarm is the desired alarm time for RTC.
* @param	Periodic says whether the alarm need to set at periodic
* 			Intervals or a one-time alarm.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XRtcPsu_SetAlarm(XRtcPsu *InstancePtr, u32 Alarm, u32 Periodic)
{
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Alarm != 0U);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((Alarm - XRtcPsu_GetCurrentTime(InstancePtr)) > (u32)0);

	XRtcPsu_WriteReg(InstancePtr->RtcConfig.BaseAddr+XRTC_ALRM_OFFSET, Alarm);
	if(Periodic != 0U) {
		InstancePtr->IsPeriodicAlarm = 1U;
		InstancePtr->PeriodicAlarmTime =
				Alarm - XRtcPsu_GetCurrentTime(InstancePtr);
	}
}


/****************************************************************************/
/**
*
* This function translates time in seconds to a YEAR:MON:DAY HR:MIN:SEC
* format and saves it in the DT structure variable. It also reports the weekday.
*
* @param	Seconds is the time value that has to be shown in DateTime
* 			format.
* @param	dt is the DateTime format variable that stores the translated
* 			time.
*
* @return	None.
*
* @note		This API supports this century i.e., 2000 - 2099 years only.
*
*****************************************************************************/
void XRtcPsu_SecToDateTime(u32 Seconds, XRtcPsu_DT *dt)
{
	u32 CurrentTime, TempDays, Leap, DaysPerMonth;

	CurrentTime = Seconds;
	dt->Sec = CurrentTime % 60U;
	CurrentTime /= 60U;
	dt->Min = CurrentTime % 60U;
	CurrentTime /= 60U;
	dt->Hour = CurrentTime % 24U;
	TempDays = CurrentTime / 24U;

	if (TempDays == 0U) {
		TempDays = 1U;
	}
	dt->WeekDay = TempDays % 7U;

	for (dt->Year = 0U; dt->Year <= 99U; ++(dt->Year)) {
		if ((dt->Year % 4U) == 0U ) {
			Leap = 1U;
		}
		else {
			Leap = 0U;
		}
		if (TempDays < (365U + Leap)) {
			break;
		}
		TempDays -= (365U + Leap);
	}

	for (dt->Month = 1U; dt->Month >= 1U; ++(dt->Month)) {
		DaysPerMonth = DaysInMonth[dt->Month - 1];
		if ((Leap == 1U) && (dt->Month == 2U)) {
			DaysPerMonth++;
		}
		if (TempDays < DaysPerMonth) {
			break;
		}
		TempDays -= DaysPerMonth;
	}

	dt->Day = TempDays;
	dt->Year += 2000U;
}

/****************************************************************************/
/**
*
* This function translates time in YEAR:MON:DAY HR:MIN:SEC format to
* seconds.
*
* @param	dt is a pointer to a DatetTime format structure variable
* 			of time that has to be shown in seconds.
*
* @return	Seconds value of provided in dt time.
*
* @note		None.
*
*****************************************************************************/
u32 XRtcPsu_DateTimeToSec(XRtcPsu_DT *dt)
{
	u32 i, Days;
	u32 Seconds;
	Xil_AssertNonvoid(dt != NULL);

	if (dt->Year >= 2000U) {
		dt->Year -= 2000U;
	}

	for (i = 1U; i < dt->Month; i++) {
		dt->Day += (u32)DaysInMonth[i-1];
	}

	if ((dt->Month > 2U) && ((dt->Year % 4U) == 0U)) {
		dt->Day++;
	}
	Days = dt->Day + (365U * dt->Year) + ((dt->Year + 3U) / 4U);
	Seconds = (((((Days * 24U) + dt->Hour) * 60U) + dt->Min) * 60U) + dt->Sec;
	return Seconds;
}

/****************************************************************************/
/**
*
* This function calculates the calibration value depending on the actual
* realworld time and also helps in deriving new calibration value if
* the user wishes to change his oscillator frequency.TimeReal is generally the
* internet time with EPOCH time as reference i.e.,1/1/1970 1st second.
* But this RTC driver assumes start time from 1/1/2000 1st second. Hence,if
* the user maps the internet time InternetTimeInSecs, then he has to use
* 	XRtcPsu_SecToDateTime(InternetTimeInSecs,&InternetTime),
* 	TimeReal = XRtcPsu_DateTimeToSec(InternetTime)
* 	consecutively to arrive at TimeReal value.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
* @param	TimeReal is the actual realworld time generally an
* 		network time / Internet time in seconds.
*
* @param	CrystalOscFreq is the Oscillator new frequency. Say, If the user
* 		is going with the typical 32768Hz, then he inputs the same
* 		frequency value.
*
* @return	None.
*
* @note		After Calculating the calibration register, user / application has to
* 			call again CfgInitialize API to bring the new calibration into effect.
*
*****************************************************************************/
void XRtcPsu_CalculateCalibration(XRtcPsu *InstancePtr,u32 TimeReal,
		u32 CrystalOscFreq)
{
	u32 ReadTime, SetTime;
	u32 Cprev,Fprev,Cnew,Fnew,Xf,Calibration;
	Xil_AssertVoid(TimeReal != 0U);
	Xil_AssertVoid(CrystalOscFreq != 0U);

	ReadTime = XRtcPsu_GetCurrentTime(InstancePtr);
	SetTime = XRtcPsu_GetLastSetTime(InstancePtr);
	Calibration = XRtcPsu_GetCalibration(InstancePtr);
	/*
	 * When board gets reseted, Calibration value is zero
	 * and Last setTime will be marked as 1st  second. This implies
	 * CurrentTime to be in few seconds say something in tens. TimeReal will
	 * be huge, say something in thousands. So to prevent such reset case, Cnew
	 * and Fnew will not be calculated.
	 */
	if((Calibration == 0U) || (CrystalOscFreq != InstancePtr->OscillatorFreq)) {
		Cnew = CrystalOscFreq - (u32)1;
		Fnew = 0U;
	} else {
		Cprev = Calibration & XRTC_CALIB_RD_MAX_TCK_MASK;
		Fprev = Calibration & XRTC_CALIB_RD_FRACTN_DATA_MASK;

		Xf = ((ReadTime - SetTime) * ((Cprev+1U) + ((Fprev+1U)/16U))) / (TimeReal - SetTime);
		Cnew = (u32)(Xf) - (u32)1;
		Fnew = XRtcPsu_RoundOff((Xf - Cnew) * 16U) - (u32)1;
	}

	Calibration = (Fnew << XRTC_CALIB_RD_FRACTN_DATA_SHIFT) + Cnew;
	Calibration |= XRTC_CALIB_RD_FRACTN_EN_MASK;

	InstancePtr->CalibrationValue = Calibration;
	InstancePtr->OscillatorFreq = CrystalOscFreq;
}

/****************************************************************************/
/**
*
* This function returns the seconds event status by reading
* interrupt status register.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
*
* @return	Returns 1 if a new second event is generated.Else 0..
*
* @note		This API is used in polled mode operation of RTC.
* 			This also clears interrupt status seconds bit.
*
*****************************************************************************/
u32 XRtcPsu_IsSecondsEventGenerated(XRtcPsu *InstancePtr)
{
	u32 Status;

	/* Loop the interrupt status register for Seconds Event */
	if ((XRtcPsu_ReadReg(InstancePtr->RtcConfig.BaseAddr +
			XRTC_INT_STS_OFFSET) & (XRTC_INT_STS_SECS_MASK)) == 0U) {
		Status = 0U;
	} else {
		/* Clear the interrupt status register */
		XRtcPsu_WriteReg((InstancePtr)->RtcConfig.BaseAddr +
				XRTC_INT_STS_OFFSET, XRTC_INT_STS_SECS_MASK);
		Status = 1U;
	}
	return Status;
}

/****************************************************************************/
/**
*
* This function returns the alarm event status by reading
* interrupt status register.
*
* @param	InstancePtr is a pointer to the XRtcPsu instance.
*
* @return	Returns 1 if the alarm event is generated.Else 0.
*
* @note		This API is used in polled mode operation of RTC.
* 			This also clears interrupt status alarm bit.
*
*****************************************************************************/
u32 XRtcPsu_IsAlarmEventGenerated(XRtcPsu *InstancePtr)
{
	u32 Status;

	/* Loop the interrupt status register for Alarm Event */
	if ((XRtcPsu_ReadReg(InstancePtr->RtcConfig.BaseAddr +
			XRTC_INT_STS_OFFSET) & (XRTC_INT_STS_ALRM_MASK)) == 0U) {
		Status = 0U;
	} else {
		/* Clear the interrupt status register */
		XRtcPsu_WriteReg((InstancePtr)->RtcConfig.BaseAddr +
				XRTC_INT_STS_OFFSET, XRTC_INT_STS_ALRM_MASK);
		Status = 1U;
	}
	return Status;
}
/** @} */
