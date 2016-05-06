/******************************************************************************
*
* Copyright (C) 2016 Xilinx, Inc.  All rights reserved.
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
* @file xsysmonpsu.c
*
* Functions in this file are the minimum required functions for the XSysMonPsu
* driver. See xsysmonpsu.h for a detailed description of the driver.
*
* @note 	None.
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date	    Changes
* ----- -----  -------- -----------------------------------------------
* 1.0   kvn    12/15/15 First release.
*              02/15/16 Corrected Assert function call in
*                       XSysMonPsu_GetMonitorStatus API.
*              03/03/16 Added Temperature remote channel for Setsingle
*                       channel API. Also corrected external mux channel
*                       numbers.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xsysmonpsu.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Function Prototypes *****************************/

static void XSysMonPsu_StubHandler(void *CallBackRef);

/************************** Variable Definitions ****************************/

/*****************************************************************************/
/**
*
* This function initializes XSysMonPsu device/instance. This function
* must be called prior to using the System Monitor device.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	ConfigPtr points to the XSysMonPsu device configuration structure.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. If the address translation is not used then the
*		physical address is passed.
*		Unexpected errors may occur if the address mapping is changed
*		after this function is invoked.
*
* @return
*		- XST_SUCCESS if successful.
*
* @note		The user needs to first call the XSysMonPsu_LookupConfig() API
*		which returns the Configuration structure pointer which is
*		passed as a parameter to the XSysMonPsu_CfgInitialize() API.
*
******************************************************************************/
s32 XSysMonPsu_CfgInitialize(XSysMonPsu *InstancePtr, XSysMonPsu_Config *ConfigPtr,
			  u32 EffectiveAddr)
{
	u32 PsSysmonControlStatus;
	u32 PlSysmonControlStatus;

	/* Assert the input arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/* Set the values read from the device config and the base address. */
	InstancePtr->Config.DeviceId = ConfigPtr->DeviceId;
	InstancePtr->Config.BaseAddress = EffectiveAddr;


	/* Set all handlers to stub values, let user configure this data later. */
	InstancePtr->Handler = XSysMonPsu_StubHandler;

	/* Reset the device such that it is in a known state. */
	XSysMonPsu_Reset(InstancePtr);

	PsSysmonControlStatus = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
			XSYSMONPSU_PS_SYSMON_CSTS_OFFSET);

	/* Check if the PS Sysmon is in Idle / ready state or not */
	while(PsSysmonControlStatus != XSYSMONPSU_PS_SYSMON_READY) {
		PsSysmonControlStatus = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
					XSYSMONPSU_PS_SYSMON_CSTS_OFFSET);
	}

	PlSysmonControlStatus = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
			XSYSMONPSU_PL_SYSMON_CSTS_OFFSET);

	/* Check if the PL Sysmon is accessible to PS Sysmon or not */
	while((PlSysmonControlStatus & XSYSMONPSU_PL_SYSMON_CSTS_ACESBLE_MASK)
				!= XSYSMONPSU_PL_SYSMON_CSTS_ACESBLE_MASK) {
		PlSysmonControlStatus = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
					XSYSMONPSU_PL_SYSMON_CSTS_OFFSET);
	}

	/* Indicate the instance is now ready to use, initialized without error */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	return XST_SUCCESS;
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
static void XSysMonPsu_StubHandler(void *CallBackRef)
{
	(void *) CallBackRef;

	/* Assert occurs always since this is a stub and should never be called */
	Xil_AssertVoidAlways();
}

/*****************************************************************************/
/**
*
* This function resets the SystemMonitor
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
*
* @return	None.
*
* @note		Upon reset, all Maximum and Minimum status registers will be
*		reset to their default values. Currently running and any averaging
*		will restart. Refer to the device data sheet for the device status and
*		register values after the reset.
*
******************************************************************************/
void XSysMonPsu_Reset(XSysMonPsu *InstancePtr)
{
	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);

	/* RESET the PS SYSMON */
	XSysmonPsu_WriteReg(InstancePtr->Config.BaseAddress + XPS_BA_OFFSET +
			XSYSMONPSU_VP_VN_OFFSET, XSYSMONPSU_VP_VN_MASK);

	/* RESET the PL SYSMON */
	XSysmonPsu_WriteReg(InstancePtr->Config.BaseAddress + XPL_BA_OFFSET +
			XSYSMONPSU_VP_VN_OFFSET, XSYSMONPSU_VP_VN_MASK);

}

/****************************************************************************/
/**
*
* This function reads the contents of the Status Register.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	A 32-bit value representing the contents of the Status Register.
*		Use the XSYSMONPSU_MON_STS_* constants defined in xsysmonpsu_hw.h to
*		interpret the returned value.
*
* @note		None.
*****************************************************************************/
u32 XSysMonPsu_GetStatus(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	u32 Status;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Read the Sysmon Status Register and return the value. */
	Status = XSysmonPsu_ReadReg(EffectiveBaseAddress + XSYSMONPSU_MON_STS_OFFSET);

	return Status;
}

/****************************************************************************/
/**
*
* This function starts the ADC conversion in the Single Channel event driven
* sampling mode. The EOC bit in Status Register will be set once the conversion
* is finished. Refer to the device specification for more details.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
*
* @return	None.
*
* @note		The default state of the CONVST bit is a logic 0. The conversion
*		is started when the CONVST bit is set to 1 from 0.
*		This bit is self-clearing so that the next conversion
*		can be started by setting this bit.
*
*****************************************************************************/
void XSysMonPsu_StartAdcConversion(XSysMonPsu *InstancePtr)
{
	u32 ControlStatus;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Start the conversion by setting the CONVST bit to 1 only if auto-convst
	 * bit is not enabled. This convst bit is self-clearing.
	 */
	ControlStatus = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
			XSYSMONPSU_PS_SYSMON_CSTS_OFFSET);

	if ((ControlStatus & XSYSMONPSU_PS_SYSMON_CSTS_AUTO_CONVST_MASK )
			!= XSYSMONPSU_PS_SYSMON_CSTS_AUTO_CONVST_MASK) {
		XSysmonPsu_WriteReg(InstancePtr->Config.BaseAddress +
					XSYSMONPSU_PS_SYSMON_CSTS_OFFSET,
					(ControlStatus | (u32)XSYSMONPSU_PS_SYSMON_CSTS_CONVST_MASK));
	}
}

/****************************************************************************/
/**
*
* Get the ADC converted data for the specified channel.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	Channel is the channel number. Use the XSM_CH_* defined in
*		the file xsysmonpsu.h. The valid channels for PS / PL SysMon are 0 - 6,
*		8 - 10 and 13 - 37. For AMS, 38 - 53 channels are valid.
* @param	Block is the value that tells whether it is for PS Sysmon block
*       or PL Sysmon block or the AMS controller register region.
*
* @return	A 16-bit value representing the ADC converted data for the
*		specified channel. The System Monitor device guarantees
* 		a 10 bit resolution for the ADC converted data and data is the
*		10 MSB bits of the 16 data read from the device.
*
* @note		Please make sure that the proper channel number is passed.
*
*****************************************************************************/
u16 XSysMonPsu_GetAdcData(XSysMonPsu *InstancePtr, u8 Channel, u32 Block)
{
	u16 AdcData;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((Channel <= XSM_CH_SUPPLY3) ||
			  ((Channel >= XSM_CH_SUPPLY_CALIB) &&
			  (Channel <= XSM_CH_GAINERR_CALIB)) ||
			  ((Channel >= XSM_CH_SUPPLY4) &&
			  (Channel <= XSM_CH_RESERVE1)));
	Xil_AssertNonvoid((Block == XSYSMON_PS)||(Block == XSYSMON_PL)
						||(Block == XSYSMON_AMS));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					Block);

	/*
	 * Read the selected ADC converted data for the specified channel
	 * and return the value.
	 */
	if (Channel <= XSM_CH_AUX_MAX) {
		AdcData = (u16) (XSysmonPsu_ReadReg(EffectiveBaseAddress + ((u32)Channel << 2U)));
	} else if ((Channel >= XSM_CH_SUPPLY7) && (Channel <= XSM_CH_TEMP_REMTE)){
		AdcData = (u16) (XSysmonPsu_ReadReg(EffectiveBaseAddress + XSM_ADC_CH_OFFSET +
				(((u32)Channel - XSM_CH_SUPPLY7) << 2U)));
	} else {
		AdcData = (u16) (XSysmonPsu_ReadReg(EffectiveBaseAddress + XSM_AMS_CH_OFFSET +
				(((u32)Channel - XSM_CH_VCC_PSLL0) << 2U)));
	}

	return AdcData;
}

/****************************************************************************/
/**
*
* This function gets the calibration coefficient data for the specified
* parameter.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	CoeffType specifies the calibration coefficient
*		to be read. Use XSM_CALIB_* constants defined in xsysmonpsu.h to
*		specify the calibration coefficient to be read.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	A 16-bit value representing the calibration coefficient.
*		The System Monitor device guarantees a 10 bit resolution for
*		the ADC converted data and data is the 10 MSB bits of the 16
*		data read from the device.
*
* @note		None.
*
*****************************************************************************/
u16 XSysMonPsu_GetCalibCoefficient(XSysMonPsu *InstancePtr, u8 CoeffType,
		u32 SysmonBlk)
{
	u16 CalibData;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(CoeffType <= XSM_CALIB_GAIN_ERROR_COEFF);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Read the selected calibration coefficient. */
	CalibData = (u16) XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_CAL_SUP_OFF_OFFSET + ((u32)CoeffType << 2U));

	return CalibData;
}

/****************************************************************************/
/**
*
* This function reads the Minimum/Maximum measurement for one of the
* XSM_MIN_* or XSM_MAX_* constants defined in xsysmonpsu.h
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	MeasurementType specifies the parameter for which the
*		Minimum/Maximum measurement has to be read.
*		Use XSM_MAX_* and XSM_MIN_* constants defined in xsysmonpsu.h to
*		specify the data to be read.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	A 16-bit value representing the maximum/minimum measurement for
*		specified parameter.
*		The System Monitor device guarantees a 10 bit resolution for
*		the ADC converted data and data is the 10 MSB bits of  16 bit
*		data read from the device.
*
*****************************************************************************/
u16 XSysMonPsu_GetMinMaxMeasurement(XSysMonPsu *InstancePtr, u8 MeasurementType,
		u32 SysmonBlk)
{
	u16 MinMaxData;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((MeasurementType <= XSM_MAX_SUPPLY6) ||
			((MeasurementType >= XSM_MIN_SUPPLY4) &&
			(MeasurementType <= XSM_MIN_SUPPLY6)) ||
			((MeasurementType >= XSM_MAX_SUPPLY7) &&
			(MeasurementType <= XSM_MAX_TEMP_REMOTE)) ||
			((MeasurementType >= XSM_MIN_SUPPLY7) &&
			(MeasurementType <= XSM_MIN_TEMP_REMOTE)));
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Read and return the specified Minimum/Maximum measurement. */
	MinMaxData = (u16) (XSysmonPsu_ReadReg(EffectiveBaseAddress +
							XSM_MIN_MAX_CH_OFFSET + ((u32)MeasurementType << 2U)));

	return MinMaxData;
}

/****************************************************************************/
/**
*
* This function sets the number of samples of averaging that is to be done for
* all the channels in both the single channel mode and sequence mode of
* operations.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	Average is the number of samples of averaging programmed to the
*		Configuration Register 0. Use the XSM_AVG_* definitions defined
*		in xsysmonpsu.h file :
*		- XSM_AVG_0_SAMPLES for no averaging
*		- XSM_AVG_16_SAMPLES for 16 samples of averaging
*		- XSM_AVG_64_SAMPLES for 64 samples of averaging
*		- XSM_AVG_256_SAMPLES for 256 samples of averaging
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XSysMonPsu_SetAvg(XSysMonPsu *InstancePtr, u8 Average, u32 SysmonBlk)
{
	u32 RegValue;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Average <= XSM_AVG_256_SAMPLES);
	Xil_AssertVoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Write the averaging value into the Configuration Register 0. */
	RegValue = XSysmonPsu_ReadReg(EffectiveBaseAddress + XSYSMONPSU_CFG_REG0_OFFSET)
						& (u32)(~XSYSMONPSU_CFG_REG0_AVRGNG_MASK);
	RegValue |= (((u32) Average << XSYSMONPSU_CFG_REG0_AVRGNG_SHIFT));
	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_CFG_REG0_OFFSET,
			 RegValue);
}

/****************************************************************************/
/**
*
* This function returns the number of samples of averaging configured for all
* the channels in the Configuration Register 0.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	The averaging read from the Configuration Register 0 is
*		returned. Use the XSM_AVG_* bit definitions defined in xsysmonpsu.h
*		file to interpret the returned value :
*		- XSM_AVG_0_SAMPLES means no averaging
*		- XSM_AVG_16_SAMPLES means 16 samples of averaging
*		- XSM_AVG_64_SAMPLES means 64 samples of averaging
*		- XSM_AVG_256_SAMPLES means 256 samples of averaging
*
* @note		None.
*
*****************************************************************************/
u8 XSysMonPsu_GetAvg(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	u32 Average;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Read the averaging value from the Configuration Register 0. */
	Average = XSysmonPsu_ReadReg(EffectiveBaseAddress +
				XSYSMONPSU_CFG_REG0_OFFSET) & XSYSMONPSU_CFG_REG0_AVRGNG_MASK;

	return (u8)(Average >> XSYSMONPSU_CFG_REG0_AVRGNG_SHIFT);
}

/****************************************************************************/
/**
*
* The function sets the given parameters in the Configuration Register 0 in
* the single channel mode.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	Channel is the channel number for conversion. The valid
*		channels are 0 - 6, 8 - 10, 13 - 37.
* @param	IncreaseAcqCycles is a boolean parameter which specifies whether
*		the Acquisition time for the external channels has to be
*		increased to 10 ADCCLK cycles (specify TRUE) or remain at the
*		default 4 ADCCLK cycles (specify FALSE). This parameter is
*		only valid for the external channels.
* @param	IsEventMode is a boolean parameter that specifies continuous
*		sampling (specify FALSE) or event driven sampling mode (specify
*		TRUE) for the given channel.
* @param	IsDifferentialMode is a boolean parameter which specifies
*		unipolar(specify FALSE) or differential mode (specify TRUE) for
*		the analog inputs. The 	input mode is only valid for the
*		external channels.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the Configuration Register 0.
*		- XST_FAILURE if the channel sequencer is enabled or the input
*		parameters are not valid for the selected channel.
*
* @note
*		- The number of samples for the averaging for all the channels
*		is set by using the function XSysMonPsu_SetAvg.
*		- The calibration of the device is done by doing a ADC
*		conversion on the calibration channel(channel 8). The input
*		parameters IncreaseAcqCycles, IsDifferentialMode and
*		IsEventMode are not valid for this channel.
*
*****************************************************************************/
s32 XSysMonPsu_SetSingleChParams(XSysMonPsu *InstancePtr, u8 Channel,
				u32 IncreaseAcqCycles, u32 IsEventMode,
				u32 IsDifferentialMode, u32 SysmonBlk)
{
	u32 RegValue;
	u32 EffectiveBaseAddress;
	s32 Status;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((Channel <= XSM_CH_SUPPLY3) ||
			  ((Channel >= XSM_CH_SUPPLY_CALIB) &&
			  (Channel <= XSM_CH_GAINERR_CALIB)) ||
			  ((Channel >= XSM_CH_SUPPLY4) &&
			  (Channel <= XSM_CH_TEMP_REMTE)));
	Xil_AssertNonvoid((IncreaseAcqCycles == TRUE) ||
			  (IncreaseAcqCycles == FALSE));
	Xil_AssertNonvoid((IsEventMode == TRUE) || (IsEventMode == FALSE));
	Xil_AssertNonvoid((IsDifferentialMode == TRUE) ||
			  (IsDifferentialMode == FALSE));
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Check if the device is in single channel mode else return failure */
	if ((XSysMonPsu_GetSequencerMode(InstancePtr, SysmonBlk)
				!= XSM_SEQ_MODE_SINGCHAN)) {
		Status = (s32)XST_FAILURE;
		goto End;
	}

	/* Read the Configuration Register 0 and extract out Averaging value. */
	RegValue = XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_CFG_REG0_OFFSET) & XSYSMONPSU_CFG_REG0_AVRGNG_MASK;

	/*
	 * Select the number of acquisition cycles. The acquisition cycles is
	 * only valid for the external channels.
	 */
	if (IncreaseAcqCycles == TRUE) {
		if (((Channel >= XSM_CH_AUX_MIN) && (Channel <= XSM_CH_AUX_MAX))
		    || (Channel == XSM_CH_VPVN)) {
			RegValue |= XSYSMONPSU_CFG_REG0_ACQ_MASK;
		} else {
			Status = (s32)XST_FAILURE;
			goto End;
		}
	}

	/*
	 * Select the input mode. The input mode is only valid for the
	 * external channels.
	 */
	if (IsDifferentialMode == TRUE) {

		if (((Channel >= XSM_CH_AUX_MIN) && (Channel <= XSM_CH_AUX_MAX))
		    || (Channel == XSM_CH_VPVN)) {
			RegValue |= XSYSMONPSU_CFG_REG0_BU_MASK;
		} else {
			Status = (s32)XST_FAILURE;
			goto End;
		}
	}

	/* Select the ADC mode. */
	if (IsEventMode == TRUE) {
		RegValue |= XSYSMONPSU_CFG_REG0_EC_MASK;
	}

	/* Write the given values into the Configuration Register 0. */
	RegValue |= ((u32)Channel & XSYSMONPSU_CFG_REG0_MUX_CH_MASK);
	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_CFG_REG0_OFFSET,
			 RegValue);

	Status = (s32)XST_SUCCESS;

End:
	return Status;
}

/****************************************************************************/
/**
*
* This function enables the alarm outputs for the specified alarms in the
* Configuration Registers 1:
*
*		- OT for Over Temperature (XSYSMONPSU_CFR_REG1_ALRM_OT_MASK)
*		- ALM0 for On board Temperature (XSYSMONPSU_CFR_REG1_ALRM_TEMP_MASK)
*		- ALM1 for SUPPLY1 (XSYSMONPSU_CFR_REG1_ALRM_SUPPLY1_MASK)
*		- ALM2 for SUPPLY2 (XSYSMONPSU_CFR_REG1_ALRM_SUPPLY2_MASK)
* 		- ALM3 for SUPPLY3 (XSYSMONPSU_CFR_REG1_ALRM_SUPPLY3_MASK)
* 		- ALM4 for SUPPLY4 (XSYSMONPSU_CFR_REG1_ALRM__SUPPLY4_MASK)
*		- ALM5 for SUPPLY5 (XSYSMONPSU_CFR_REG1_ALRM_SUPPLY5_MASK)
* 		- ALM6 for SUPPLY6 (XSYSMONPSU_CFR_REG1_ALRM_SUPPLY6_MASK)
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	AlmEnableMask is the bit-mask of the alarm outputs to be enabled
*		in the Configuration Register 1.
*		Bit positions of 1 will be enabled. Bit positions of 0 will be
*		disabled. This mask is formed by OR'ing XSYSMONPSU_CFR_REG1_ALRM_*_MASK
*		masks defined in xsysmonpsu.h.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	None.
*
* @note		The implementation of the alarm enables in the Configuration
*		register 1 is such that the alarms for bit positions of 0 will
*		be enabled and alarms for bit positions of 1 will be disabled.
*		The alarm outputs specified by the AlmEnableMask are negated
*		before writing to the Configuration Register 1 because it
*		was Disable register bits.
*
*****************************************************************************/
void XSysMonPsu_SetAlarmEnables(XSysMonPsu *InstancePtr, u32 AlmEnableMask,
		u32 SysmonBlk)
{
	u32 RegValue;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(AlmEnableMask <= XSYSMONPSU_CFG_REG1_ALRM_ALL_MASK);
	Xil_AssertVoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	RegValue = XSysmonPsu_ReadReg(EffectiveBaseAddress +
					XSYSMONPSU_CFG_REG1_OFFSET);
	RegValue &= (u32)(~XSYSMONPSU_CFG_REG1_ALRM_ALL_MASK);
	RegValue |= (~AlmEnableMask & (u32)XSYSMONPSU_CFG_REG1_ALRM_ALL_MASK);

	/*
	 * Enable/disables the alarm enables for the specified alarm bits in the
	 * Configuration Register 1.
	 */
	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_CFG_REG1_OFFSET,
			 RegValue);
}

/****************************************************************************/
/**
*
* This function gets the status of the alarm output enables in the
* Configuration Register 1.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	This is the bit-mask of the enabled alarm outputs in the
*		Configuration Register 1. Use the masks XSYSMONPSU_CFG_REG1_ALRM_*_MASK
*		masks defined in xsysmonpsu.h to interpret the returned value.
*
*		Bit positions of 1 indicate that the alarm output is enabled.
*		Bit positions of 0 indicate that the alarm output is disabled.
*
*
* @note		The implementation of the alarm enables in the Configuration
*		register 1 is such that alarms for the bit positions of 1 will
*		be disabled and alarms for bit positions of 0 will be enabled.
*		The enabled alarm outputs returned by this function is the
*		negated value of the the data read from the Configuration
*		Register 1.
*
*****************************************************************************/
u32 XSysMonPsu_GetAlarmEnables(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	u32 RegValue;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Read the status of alarm output enables from the Configuration
	 * Register 1.
	 */
	RegValue = XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_CFG_REG1_OFFSET) & XSYSMONPSU_CFG_REG1_ALRM_ALL_MASK;
	RegValue = (~RegValue & XSYSMONPSU_CFG_REG1_ALRM_ALL_MASK);

	return RegValue;
}

/****************************************************************************/
/**
*
* This function sets the specified Channel Sequencer Mode in the Configuration
* Register 1 :
*		- Default safe mode (XSM_SEQ_MODE_SAFE)
*		- One pass through sequence (XSM_SEQ_MODE_ONEPASS)
*		- Continuous channel sequencing (XSM_SEQ_MODE_CONTINPASS)
*		- Single Channel/Sequencer off (XSM_SEQ_MODE_SINGCHAN)
*		- Olympus sampling mode (XSM_SEQ_MODE_OYLMPUS)
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SequencerMode is the sequencer mode to be set.
*		Use XSM_SEQ_MODE_* bits defined in xsysmonpsu.h.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	None.
*
* @note		Only one of the modes can be enabled at a time.
*
*****************************************************************************/
void XSysMonPsu_SetSequencerMode(XSysMonPsu *InstancePtr, u8 SequencerMode,
		u32 SysmonBlk)
{
	u32 RegValue;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((SequencerMode <= XSM_SEQ_MODE_SINGCHAN) ||
			(SequencerMode == XSM_SEQ_MODE_OYLMPUS));
	Xil_AssertVoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Set the specified sequencer mode in the Configuration Register 1. */
	RegValue = XSysmonPsu_ReadReg(EffectiveBaseAddress +
					XSYSMONPSU_CFG_REG1_OFFSET);
	RegValue &= (u32)(~ XSYSMONPSU_CFG_REG1_SEQ_MDE_MASK);
	RegValue |= (((u32)SequencerMode  << XSYSMONPSU_CFG_REG1_SEQ_MDE_SHIFT) &
					XSYSMONPSU_CFG_REG1_SEQ_MDE_MASK);
	XSysmonPsu_WriteReg(EffectiveBaseAddress +
					XSYSMONPSU_CFG_REG1_OFFSET, RegValue);
}

/****************************************************************************/
/**
*
* This function gets the channel sequencer mode from the Configuration
* Register 1.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	The channel sequencer mode :
*		- XSM_SEQ_MODE_SAFE : Default safe mode
*		- XSM_SEQ_MODE_ONEPASS : One pass through sequence
*		- XSM_SEQ_MODE_CONTINPASS : Continuous channel sequencing
*		- XSM_SEQ_MODE_SINGCHAN : Single channel/Sequencer off
*		- XSM_SEQ_MODE_OLYMPUS : Olympus sampling mode
*
* @note		None.
*
*****************************************************************************/
u8 XSysMonPsu_GetSequencerMode(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	u8 SequencerMode;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Read the channel sequencer mode from the Configuration Register 1. */
	SequencerMode =  ((u8) ((XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_CFG_REG1_OFFSET) & XSYSMONPSU_CFG_REG1_SEQ_MDE_MASK) >>
			XSYSMONPSU_CFG_REG1_SEQ_MDE_SHIFT));

	return SequencerMode;
}

/****************************************************************************/
/**
*
* The function enables the Event mode or Continuous mode in the sequencer mode.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	IsEventMode is a boolean parameter that specifies continuous
*		sampling (specify FALSE) or event driven sampling mode (specify
*		TRUE) for the channel.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XSysMonPsu_SetSequencerEvent(XSysMonPsu *InstancePtr, u32 IsEventMode,
		u32 SysmonBlk)
{
	u32 RegValue;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((IsEventMode == TRUE) || (IsEventMode == FALSE));
	Xil_AssertVoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Read the Configuration Register 0. */
	RegValue = XSysmonPsu_ReadReg(EffectiveBaseAddress +
					XSYSMONPSU_CFG_REG0_OFFSET);

	/* Set the ADC mode. */
	if (IsEventMode == TRUE) {
		RegValue |= XSYSMONPSU_CFG_REG0_EC_MASK;
	} else {
		RegValue &= (u32)(~XSYSMONPSU_CFG_REG0_EC_MASK);
	}

	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_CFG_REG0_OFFSET,
			 RegValue);
}

/****************************************************************************/
/**
*
* The function returns the mode of the sequencer.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	Returns the Sequencer mode. XSYSMONPSU_EVENT_MODE for Event mode
* 		and XSYSMONPSU_CONTINUOUS_MODE for continuous mode.
*
* @note		None.
*
*****************************************************************************/
s32 XSysMonPsu_GetSequencerEvent(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	s32 Mode;
	u32 RegValue;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Read the Configuration Register 0. */
	RegValue = XSysmonPsu_ReadReg(EffectiveBaseAddress +
					XSYSMONPSU_CFG_REG0_OFFSET);

	RegValue &= XSYSMONPSU_CFG_REG0_EC_MASK;

	if (RegValue == XSYSMONPSU_CFG_REG0_EC_MASK) {
		Mode = XSYSMONPSU_EVENT_MODE;
	} else {
		Mode = XSYSMONPSU_CONTINUOUS_MODE;
	}

	return Mode;
}

/****************************************************************************/
/**
*
* The function enables the external mux and connects a channel to the mux.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	Channel is the channel number used to connect to the external
*		Mux. The valid channels are 0 to 5 and 16 to 31.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the Configuration Register 0.
*		- XST_FAILURE if the channel sequencer is enabled or the input
*		parameters are not valid for the selected channel.
*
* @note		None.
*
*****************************************************************************/
void XSysMonPsu_SetExtenalMux(XSysMonPsu *InstancePtr, u8 Channel, u32 SysmonBlk)
{
	u32 RegValue;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((Channel <= XSM_CH_VREFN) ||
			  ((Channel >= XSM_CH_AUX_MIN) &&
			  (Channel <= XSM_CH_AUX_MAX)));
	Xil_AssertVoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Read the Configuration Register 0 and the clear the channel selection
	 * bits.
	 */
	RegValue = XSysmonPsu_ReadReg(EffectiveBaseAddress +
					XSYSMONPSU_CFG_REG0_OFFSET);
	RegValue &= ~(XSYSMONPSU_CFG_REG0_MUX_CH_MASK);

	/* Enable the External Mux and select the channel. */
	RegValue |= (XSYSMONPSU_CFG_REG0_XTRNL_MUX_MASK | (u32)Channel);
	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_CFG_REG0_OFFSET,
			 RegValue);
}

/****************************************************************************/
/**
*
* The function returns the external mux channel.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	Returns the channel number used to connect to the external
*		Mux. The valid channels are 0 to 6, 8 to 16, and 31 to 36..
*
* @note		None.
*
*****************************************************************************/
u32 XSysMonPsu_GetExtenalMux(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	u32 RegValue;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Read the Configuration Register 0 and derive the channel selection
	 * bits.
	 */
	RegValue = XSysmonPsu_ReadReg(EffectiveBaseAddress +
					XSYSMONPSU_CFG_REG0_OFFSET);
	RegValue &= XSYSMONPSU_CFG_REG0_MUX_CH_MASK;

	return RegValue;
}

/****************************************************************************/
/**
*
* The function sets the frequency of the ADCCLK by configuring the DCLK to
* ADCCLK ratio in the Configuration Register #2.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	Divisor is clock divisor used to derive ADCCLK from DCLK.
*		Valid values of the divisor are
*		PS:
*		 - 0 means divide by 8.
*		 - 1,2 means divide by 2.
*		 - 3 to 255 means divide by that value.
*       PL:
*		 - 0,1,2 means divide by 2.
*		 - 3 to 255 means divide by that value.
*		Refer to the device specification for more details.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	None.
*
* @note		- The ADCCLK is an internal clock used by the ADC and is
*		synchronized to the DCLK clock. The ADCCLK is equal to DCLK
*		divided by the user selection in the Configuration Register 2.
*		- There is no Assert on the minimum value of the Divisor.
*
*****************************************************************************/
void XSysMonPsu_SetAdcClkDivisor(XSysMonPsu *InstancePtr, u8 Divisor,
            u32 SysmonBlk)
{
	u32 RegValue;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Read the Configuration Register 2 and the clear the clock divisor
	 * bits.
	 */
	RegValue = XSysmonPsu_ReadReg(EffectiveBaseAddress +
					XSYSMONPSU_CFG_REG2_OFFSET);
	RegValue &= ~(XSYSMONPSU_CFG_REG2_CLK_DVDR_MASK);

	/* Write the divisor value into the Configuration Register 2. */
	RegValue |= ((u32)Divisor << XSYSMONPSU_CFG_REG2_CLK_DVDR_SHIFT) &
					XSYSMONPSU_CFG_REG2_CLK_DVDR_MASK;
	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_CFG_REG2_OFFSET,
			 RegValue);

}

/****************************************************************************/
/**
*
* The function gets the ADCCLK divisor from the Configuration Register 2.
*
* @param	InstancePtr is a pointer to the XSysMon instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	The divisor read from the Configuration Register 2.
*
* @note		The ADCCLK is an internal clock used by the ADC and is
*		synchronized to the DCLK clock. The ADCCLK is equal to DCLK
*		divided by the user selection in the Configuration Register 2.
*
*****************************************************************************/
u8 XSysMonPsu_GetAdcClkDivisor(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	u16 Divisor;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Read the divisor value from the Configuration Register 2. */
	Divisor = (u16) XSysmonPsu_ReadReg(EffectiveBaseAddress +
							XSYSMONPSU_CFG_REG2_OFFSET);

	return (u8) (Divisor >> XSYSMONPSU_CFG_REG2_CLK_DVDR_SHIFT);
}

/****************************************************************************/
/**
*
* This function enables the specified channels in the ADC Channel Selection
* Sequencer Registers. The sequencer must be in the Safe Mode before writing
* to these registers.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	ChEnableMask is the bit mask of all the channels to be enabled.
*		Use XSYSMONPSU_SEQ_CH* defined in xsysmon_hw.h to specify the Channel
*		numbers. Bit masks of 1 will be enabled and bit mask of 0 will
*		be disabled.
*		The ChEnableMask is a 32 bit mask that is written to the two
*		16 bit ADC Channel Selection Sequencer Registers.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the ADC Channel Selection Sequencer Registers.
*		- XST_FAILURE if the channel sequencer is enabled.
*
* @note		None.
*
*****************************************************************************/
s32 XSysMonPsu_SetSeqChEnables(XSysMonPsu *InstancePtr, u32 ChEnableMask,
		u32 SysmonBlk)
{
	s32 Status;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/*
	 * The sequencer must be in the Default Safe Mode before writing
	 * to these registers. Return XST_FAILURE if the channel sequencer
	 * is enabled.
	 */
	if ((XSysMonPsu_GetSequencerMode(InstancePtr,SysmonBlk) != XSM_SEQ_MODE_SAFE)) {
		Status = (s32)XST_FAILURE;
		goto End;
	}

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Enable the specified channels in the ADC Channel Selection Sequencer
	 * Registers.
	 */
	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_SEQ_CH0_OFFSET,
			 (ChEnableMask & XSYSMONPSU_SEQ_CH0_VALID_MASK));

	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_SEQ_CH1_OFFSET,
			 (ChEnableMask >> XSM_SEQ_CH_SHIFT) &
			 XSYSMONPSU_SEQ_CH1_VALID_MASK);

	Status = (s32)XST_SUCCESS;

End:
	return Status;
}

/****************************************************************************/
/**
*
* This function gets the channel enable bits status from the ADC Channel
* Selection Sequencer Registers.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	Gets the channel enable bits. Use XSYSMONPSU_SEQ_CH* defined in
*		xsysmonpsu_hw.h to interpret the Channel numbers. Bit masks of 1
*		are the channels that are enabled and bit mask of 0 are
*		the channels that are disabled.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
u32 XSysMonPsu_GetSeqChEnables(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	u32 RegVal;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Read the channel enable bits for all the channels from the ADC
	 * Channel Selection Register.
	 */
	RegVal = XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_SEQ_CH0_OFFSET) & XSYSMONPSU_SEQ_CH0_VALID_MASK;
	RegVal |= (XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_SEQ_CH1_OFFSET) & XSYSMONPSU_SEQ_CH1_VALID_MASK) <<
					XSM_SEQ_CH_SHIFT;

	return RegVal;
}

/****************************************************************************/
/**
*
* This function enables the averaging for the specified channels in the ADC
* Channel Averaging Enable Sequencer Registers. The sequencer must be in
* the Safe Mode before writing to these registers.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	AvgEnableChMask is the bit mask of all the channels for which
*		averaging is to be enabled. Use XSYSMONPSU_SEQ_AVERAGE* defined in
*		xsysmonpsu_hw.h to specify the Channel numbers. Averaging will be
*		enabled for bit masks of 1 and disabled for bit mask of 0.
*		The AvgEnableChMask is a 32 bit mask that is written to the
*		two 16 bit ADC Channel Averaging Enable Sequencer Registers.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the ADC Channel Averaging Enables Sequencer Registers.
*		- XST_FAILURE if the channel sequencer is enabled.
*
* @note		None.
*
*****************************************************************************/
s32 XSysMonPsu_SetSeqAvgEnables(XSysMonPsu *InstancePtr, u32 AvgEnableChMask,
		u32 SysmonBlk)
{
	s32 Status;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * The sequencer must be disabled for writing any of these registers.
	 * Return XST_FAILURE if the channel sequencer is enabled.
	 */
	if ((XSysMonPsu_GetSequencerMode(InstancePtr,SysmonBlk)
	                                     != XSM_SEQ_MODE_SAFE)) {
		Status = (s32)XST_FAILURE;
		goto End;
	}

	/*
	 * Enable/disable the averaging for the specified channels in the
	 * ADC Channel Averaging Enables Sequencer Registers.
	 */
	XSysmonPsu_WriteReg(EffectiveBaseAddress +
			XSYSMONPSU_SEQ_AVERAGE0_OFFSET,
			(AvgEnableChMask & XSYSMONPSU_SEQ_AVERAGE0_MASK));

	XSysmonPsu_WriteReg(EffectiveBaseAddress +
			XSYSMONPSU_SEQ_AVERAGE1_OFFSET,
			 (AvgEnableChMask >> XSM_SEQ_CH_SHIFT) &
			 XSYSMONPSU_SEQ_AVERAGE1_MASK);

	Status = (s32)XST_SUCCESS;
End:
	return Status;
}

/****************************************************************************/
/**
*
* This function returns the channels for which the averaging has been enabled
* in the ADC Channel Averaging Enables Sequencer Registers.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @returns 	The status of averaging (enabled/disabled) for all the channels.
*		Use XSYSMONPSU_SEQ_AVERAGE* defined in xsysmonpsu_hw.h to interpret the
*		Channel numbers. Bit masks of 1 are the channels for which
*		averaging is enabled and bit mask of 0 are the channels for
*		averaging is disabled.
*
* @note		None.
*
*****************************************************************************/
u32 XSysMonPsu_GetSeqAvgEnables(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	u32 RegVal;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Read the averaging enable status for all the channels from the
	 * ADC Channel Averaging Enables Sequencer Registers.
	 */
	RegVal = XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_SEQ_AVERAGE0_OFFSET) & XSYSMONPSU_SEQ_AVERAGE0_MASK;
	RegVal |= (XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_SEQ_AVERAGE1_OFFSET) & XSYSMONPSU_SEQ_AVERAGE1_MASK) <<
			XSM_SEQ_CH_SHIFT;

	return RegVal;
}

/****************************************************************************/
/**
*
* This function sets the Analog input mode for the specified channels in the
* ADC Channel Analog-Input Mode Sequencer Registers. The sequencer must be in
* the Safe Mode before writing to these registers.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	InputModeChMask is the bit mask of all the channels for which
*		the input mode is differential mode. Use XSYSMONPSU_SEQ_INPUT_MDE*
*		defined in xsysmonpsu_hw.h to specify the channel numbers. Differential
*		or  Bipolar input mode will be set for bit masks of 1 and unipolar input
*		mode for bit masks of 0.
*		The InputModeChMask is a 32 bit mask that is written to the two
*		16 bit ADC Channel Analog-Input Mode Sequencer Registers.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the ADC Channel Analog-Input Mode Sequencer Registers.
*		- XST_FAILURE if the channel sequencer is enabled.
*
* @note		None.
*
*****************************************************************************/
s32 XSysMonPsu_SetSeqInputMode(XSysMonPsu *InstancePtr, u32 InputModeChMask,
		u32 SysmonBlk)
{
	s32 Status;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/*
	 * The sequencer must be in the Safe Mode before writing to
	 * these registers. Return XST_FAILURE if the channel sequencer
	 * is enabled.
	 */
	if ((XSysMonPsu_GetSequencerMode(InstancePtr,SysmonBlk)
	                                      != XSM_SEQ_MODE_SAFE)) {
		Status = (s32)XST_FAILURE;
		goto End;
	}

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Set the input mode for the specified channels in the ADC Channel
	 * Analog-Input Mode Sequencer Registers.
	 */
	XSysmonPsu_WriteReg(EffectiveBaseAddress +
			XSYSMONPSU_SEQ_INPUT_MDE0_OFFSET,
			 (InputModeChMask & XSYSMONPSU_SEQ_INPUT_MDE0_MASK));

	XSysmonPsu_WriteReg(EffectiveBaseAddress +
			XSYSMONPSU_SEQ_INPUT_MDE1_OFFSET,
			 (InputModeChMask >> XSM_SEQ_CH_SHIFT) &
			 XSYSMONPSU_SEQ_INPUT_MDE1_MASK);

	Status = (s32)XST_SUCCESS;

End:
	return Status;
}

/****************************************************************************/
/**
*
* This function gets the Analog input mode for all the channels from
* the ADC Channel Analog-Input Mode Sequencer Registers.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @returns 	The input mode for all the channels.
*		Use XSYSMONPSU_SEQ_INPUT_MDE* defined in xsysmonpsu_hw.h to interpret the
*		Channel numbers. Bit masks of 1 are the channels for which
*		input mode is differential/Bipolar and bit mask of 0 are the channels
*		for which input mode is unipolar.
*
* @note		None.
*
*****************************************************************************/
u32 XSysMonPsu_GetSeqInputMode(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	u32 InputMode;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 *  Get the input mode for all the channels from the ADC Channel
	 * Analog-Input Mode Sequencer Registers.
	 */
	InputMode = XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_SEQ_INPUT_MDE0_OFFSET) & XSYSMONPSU_SEQ_INPUT_MDE0_MASK;
	InputMode |= (XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_SEQ_INPUT_MDE1_OFFSET) & XSYSMONPSU_SEQ_INPUT_MDE1_MASK) <<
				XSM_SEQ_CH_SHIFT;

	return InputMode;
}

/****************************************************************************/
/**
*
* This function sets the number of Acquisition cycles in the ADC Channel
* Acquisition Time Sequencer Registers. The sequencer must be in the Safe Mode
* before writing to these registers.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	AcqCyclesChMask is the bit mask of all the channels for which
*		the number of acquisition cycles is to be extended.
*		Use XSYSMONPSU_SEQ_ACQ* defined in xsysmonpsu_hw.h to specify the Channel
*		numbers. Acquisition cycles will be extended to 10 ADCCLK cycles
*		for bit masks of 1 and will be the default 4 ADCCLK cycles for
*		bit masks of 0.
*		The AcqCyclesChMask is a 32 bit mask that is written to the two
*		16 bit ADC Channel Acquisition Time Sequencer Registers.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the Channel Sequencer Registers.
*		- XST_FAILURE if the channel sequencer is enabled.
*
* @note		None.
*
*****************************************************************************/
s32 XSysMonPsu_SetSeqAcqTime(XSysMonPsu *InstancePtr, u32 AcqCyclesChMask,
		u32 SysmonBlk)
{
	s32 Status;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/*
	 * The sequencer must be in the Safe Mode before writing
	 * to these registers. Return XST_FAILURE if the channel
	 * sequencer is enabled.
	 */
	if ((XSysMonPsu_GetSequencerMode(InstancePtr,SysmonBlk)
	                                     != XSM_SEQ_MODE_SAFE)) {
		Status = (s32)XST_FAILURE;
		goto End;
	}

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Set the Acquisition time for the specified channels in the
	 * ADC Channel Acquisition Time Sequencer Registers.
	 */
	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_SEQ_ACQ0_OFFSET,
			 (AcqCyclesChMask & XSYSMONPSU_SEQ_ACQ0_MASK));

	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_SEQ_ACQ1_OFFSET,
			 (AcqCyclesChMask >> XSM_SEQ_CH_SHIFT) & XSYSMONPSU_SEQ_ACQ1_MASK);

	Status = (s32)XST_SUCCESS;

End:
	return Status;
}

/****************************************************************************/
/**
*
* This function gets the status of acquisition time from the ADC Channel Acquisition
* Time Sequencer Registers.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @returns 	The acquisition time for all the channels.
*		Use XSYSMONPSU_SEQ_ACQ* defined in xsysmonpsu_hw.h to interpret the
*		Channel numbers. Bit masks of 1 are the channels for which
*		acquisition cycles are extended and bit mask of 0 are the
*		channels for which acquisition cycles are not extended.
*
* @note		None.
*
*****************************************************************************/
u32 XSysMonPsu_GetSeqAcqTime(XSysMonPsu *InstancePtr, u32 SysmonBlk)
{
	u32 RegValAcq;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Get the Acquisition cycles for the specified channels from the ADC
	 * Channel Acquisition Time Sequencer Registers.
	 */
	RegValAcq = XSysmonPsu_ReadReg(EffectiveBaseAddress +
					XSYSMONPSU_SEQ_ACQ0_OFFSET) & XSYSMONPSU_SEQ_ACQ0_MASK;
	RegValAcq |= (XSysmonPsu_ReadReg(EffectiveBaseAddress +
					XSYSMONPSU_SEQ_ACQ1_OFFSET) & XSYSMONPSU_SEQ_ACQ1_MASK) <<
					XSM_SEQ_CH_SHIFT;

	return RegValAcq;
}

/****************************************************************************/
/**
*
* This functions sets the contents of the given Alarm Threshold Register.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	AlarmThrReg is the index of an Alarm Threshold Register to
*		be set. Use XSM_ATR_* constants defined in xsysmonpsu.h to
*		specify the index.
* @param	Value is the 16-bit threshold value to write into the register.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XSysMonPsu_SetAlarmThreshold(XSysMonPsu *InstancePtr, u8 AlarmThrReg,
		u16 Value, u32 SysmonBlk)
{
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((AlarmThrReg <= XSM_ATR_TEMP_RMTE_UPPER) ||
			((AlarmThrReg >= XSM_ATR_SUP7_LOWER) &&
			(AlarmThrReg <= XSM_ATR_TEMP_RMTE_LOWER)));
	Xil_AssertVoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/* Write the value into the specified Alarm Threshold Register. */
	XSysmonPsu_WriteReg(EffectiveBaseAddress + XSYSMONPSU_ALRM_TEMP_UPR_OFFSET +
			((u32)AlarmThrReg << 2U), Value);
}

/****************************************************************************/
/**
*
* This function returns the contents of the specified Alarm Threshold Register.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
* @param	AlarmThrReg is the index of an Alarm Threshold Register
*		to be read. Use XSM_ATR_* constants defined in xsysmonpsu.h
*		to specify the index.
* @param	SysmonBlk is the value that tells whether it is for PS Sysmon
*       block or PL Sysmon block register region.
*
* @return	A 16-bit value representing the contents of the selected Alarm
*		Threshold Register.
*
* @note		None.
*
*****************************************************************************/
u16 XSysMonPsu_GetAlarmThreshold(XSysMonPsu *InstancePtr, u8 AlarmThrReg,
		u32 SysmonBlk)
{
	u16 AlarmThreshold;
	u32 EffectiveBaseAddress;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((AlarmThrReg <= XSM_ATR_TEMP_RMTE_UPPER) ||
			((AlarmThrReg >= XSM_ATR_SUP7_LOWER) &&
			(AlarmThrReg <= XSM_ATR_TEMP_RMTE_LOWER)));
	Xil_AssertNonvoid((SysmonBlk == XSYSMON_PS)||(SysmonBlk == XSYSMON_PL));

	/* Calculate the effective baseaddress based on the Sysmon instance. */
	EffectiveBaseAddress =
			XSysMonPsu_GetEffBaseAddress(InstancePtr->Config.BaseAddress,
					SysmonBlk);

	/*
	 * Read the specified Alarm Threshold Register and return
	 * the value.
	 */
	AlarmThreshold = (u16) XSysmonPsu_ReadReg(EffectiveBaseAddress +
			XSYSMONPSU_ALRM_TEMP_UPR_OFFSET + ((u32)AlarmThrReg << 2));

	return AlarmThreshold;
}

/****************************************************************************/
/**
*
* This function sets the conversion to be automatic for PS SysMon.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
*
* @return	None
*
* @note		In the auto-trigger mode, sample rate is of 1 Million samples.
*
*****************************************************************************/
void XSysMonPsu_SetPSAutoConversion(XSysMonPsu *InstancePtr)
{
	u32 PSSysMonStatusReg;

	/* Assert the arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Set the automatic conversion triggering in PS control register. */
	PSSysMonStatusReg = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
			XSYSMONPSU_PS_SYSMON_CSTS_OFFSET);
	PSSysMonStatusReg |= XSYSMONPSU_PS_SYSMON_CSTS_AUTO_CONVST_MASK;
	XSysmonPsu_WriteReg(InstancePtr->Config.BaseAddress +
			XSYSMONPSU_PS_SYSMON_CSTS_OFFSET, PSSysMonStatusReg);
}

/****************************************************************************/
/**
*
* This function gets the AMS monitor status.
*
* @param	InstancePtr is a pointer to the XSysMonPsu instance.
*
* @return	Returns the monitor status. See XSYSMONPSU_MON_STS_*_MASK
* 		definations present in xsysmonpsu_hw.h for knowing the status.
*
* @note		None
* .
*****************************************************************************/
u32 XSysMonPsu_GetMonitorStatus(XSysMonPsu *InstancePtr)
{
	u32 AMSMonStatusReg;

	/* Assert the arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the AMS monitor status. This gives tells about JTAG Locked / ADC
	 * busy / ADC Current Channel number and its ADC output.
	 */
	AMSMonStatusReg = XSysmonPsu_ReadReg(InstancePtr->Config.BaseAddress +
			XSYSMONPSU_MON_STS_OFFSET);

	return AMSMonStatusReg;
}

/** @} */
