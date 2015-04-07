/******************************************************************************
*
* (c) Copyright 2012-2013 Xilinx, Inc. All rights reserved.
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
* @file xadcps.c
*
* This file contains the driver API functions that can be used to access
* the XADC device.
*
* Refer to the xadcps.h header file for more information about this driver.
*
* @note 	None.
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.00a ssb    12/22/11 First release based on the XPS/AXI xadc driver
* 1.01a bss    02/18/13	Modified XAdcPs_SetSeqChEnables,XAdcPs_SetSeqAvgEnables
*			XAdcPs_SetSeqInputMode and XAdcPs_SetSeqAcqTime APIs
*			to fix CR #693371
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xadcps.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Function Prototypes *****************************/

void XAdcPs_WriteInternalReg(XAdcPs *InstancePtr, u32 RegOffset, u32 Data);
u32 XAdcPs_ReadInternalReg(XAdcPs *InstancePtr, u32 RegOffset);


/************************** Variable Definitions ****************************/


/*****************************************************************************/
/**
*
* This function initializes a specific XAdcPs device/instance. This function
* must be called prior to using the XADC device.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	ConfigPtr points to the XAdcPs device configuration structure.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. If the address translation is not used then the
*		physical address is passed.
*		Unexpected errors may occur if the address mapping is changed
*		after this function is invoked.
*
* @return
*		- XST_SUCCESS if successful.
*
* @note		The user needs to first call the XAdcPs_LookupConfig() API
*		which returns the Configuration structure pointer which is
*		passed as a parameter to the XAdcPs_CfgInitialize() API.
*
******************************************************************************/
int XAdcPs_CfgInitialize(XAdcPs *InstancePtr, XAdcPs_Config *ConfigPtr,
				u32 EffectiveAddr)
{

	u32 RegValue;
	/*
	 * Assert the input arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);


	/*
	 * Set the values read from the device config and the base address.
	 */
	InstancePtr->Config.DeviceId = ConfigPtr->DeviceId;
	InstancePtr->Config.BaseAddress = EffectiveAddr;

	/* Write Unlock value to Device Config Unlock register */
	XAdcPs_WriteReg((InstancePtr)->Config.BaseAddress,
				XADCPS_UNLK_OFFSET, XADCPS_UNLK_VALUE);

	/* Enable the PS access of xadc and set FIFO thresholds */

	RegValue = XAdcPs_ReadReg((InstancePtr)->Config.BaseAddress,
			XADCPS_CFG_OFFSET);

	RegValue = RegValue | XADCPS_CFG_ENABLE_MASK |
			XADCPS_CFG_CFIFOTH_MASK | XADCPS_CFG_DFIFOTH_MASK;

	XAdcPs_WriteReg((InstancePtr)->Config.BaseAddress,
					XADCPS_CFG_OFFSET, RegValue);

	/* Release xadc from reset */

	XAdcPs_WriteReg((InstancePtr)->Config.BaseAddress,
						XADCPS_MCTL_OFFSET, 0x00);

	/*
	 * Indicate the instance is now ready to use and
	 * initialized without error.
	 */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	return XST_SUCCESS;
}


/****************************************************************************/
/**
*
* The functions sets the contents of the Config Register.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Data is the 32 bit data to be written to the Register.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_SetConfigRegister(XAdcPs *InstancePtr, u32 Data)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	XAdcPs_WriteReg((InstancePtr)->Config.BaseAddress,
				XADCPS_CFG_OFFSET, Data);

}


/****************************************************************************/
/**
*
* The functions reads the contents of the Config Register.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	A 32-bit value representing the contents of the Config Register.
*		Use the XADCPS_SR_*_MASK constants defined in xadcps_hw.h to
*		interpret the returned value.
*
* @note		None.
*
*****************************************************************************/
u32 XAdcPs_GetConfigRegister(XAdcPs *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Config Register and return the value.
	 */
	return XAdcPs_ReadReg((InstancePtr)->Config.BaseAddress,
				XADCPS_CFG_OFFSET);
}


/****************************************************************************/
/**
*
* The functions reads the contents of the Miscellaneous Status Register.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	A 32-bit value representing the contents of the Miscellaneous
*		Status Register. Use the XADCPS_MSTS_*_MASK constants defined
*		in xadcps_hw.h to interpret the returned value.
*
* @note		None.
*
*****************************************************************************/
u32 XAdcPs_GetMiscStatus(XAdcPs *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Miscellaneous Status Register and return the value.
	 */
	return XAdcPs_ReadReg((InstancePtr)->Config.BaseAddress,
				XADCPS_MSTS_OFFSET);
}


/****************************************************************************/
/**
*
* The functions sets the contents of the Miscellaneous Control register.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Data is the 32 bit data to be written to the Register.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_SetMiscCtrlRegister(XAdcPs *InstancePtr, u32 Data)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Write to the Miscellaneous control register Register.
	 */
	 XAdcPs_WriteReg((InstancePtr)->Config.BaseAddress,
	 			XADCPS_MCTL_OFFSET, Data);
}


/****************************************************************************/
/**
*
* The functions reads the contents of the Miscellaneous control register.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	A 32-bit value representing the contents of the Config Register.
*		Use the XADCPS_SR_*_MASK constants defined in xadcps_hw.h to
*		interpret the returned value.
*
* @note		None.
*
*****************************************************************************/
u32 XAdcPs_GetMiscCtrlRegister(XAdcPs *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Miscellaneous control register and return the value.
	 */
	return XAdcPs_ReadReg((InstancePtr)->Config.BaseAddress,
				XADCPS_MCTL_OFFSET);
}


/*****************************************************************************/
/**
*
* This function resets the XADC Hard Macro in the device.
*
* @param	InstancePtr is a pointer to the Xxadc instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XAdcPs_Reset(XAdcPs *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Generate the reset by Control
	 * register and release from reset
	 */
	XAdcPs_WriteReg((InstancePtr)->Config.BaseAddress,
	 			XADCPS_MCTL_OFFSET, 0x10);
	XAdcPs_WriteReg((InstancePtr)->Config.BaseAddress,
	 			XADCPS_MCTL_OFFSET, 0x00);
}


/****************************************************************************/
/**
*
* Get the ADC converted data for the specified channel.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Channel is the channel number. Use the XADCPS_CH_* defined in
*		the file xadcps.h.
*		The valid channels are
*		- 0 to 6
*		- 13 to 31
*
* @return	A 16-bit value representing the ADC converted data for the
*		specified channel. The XADC Monitor/ADC device guarantees
* 		a 10 bit resolution for the ADC converted data and data is the
*		10 MSB bits of the 16 data read from the device.
*
* @note		The channels 7,8,9 are used for calibration of the device and
*		hence there is no associated data with this channel.
*
*****************************************************************************/
u16 XAdcPs_GetAdcData(XAdcPs *InstancePtr, u8 Channel)
{

	u32 RegData;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((Channel <= XADCPS_CH_VBRAM) ||
			 ((Channel >= XADCPS_CH_VCCPINT) &&
			 (Channel <= XADCPS_CH_AUX_MAX)));

	RegData = XAdcPs_ReadInternalReg(InstancePtr,
						(XADCPS_TEMP_OFFSET +
						Channel));
	return (u16) RegData;
}

/****************************************************************************/
/**
*
* This function gets the calibration coefficient data for the specified
* parameter.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	CoeffType specifies the calibration coefficient
*		to be read. Use XADCPS_CALIB_* constants defined in xadcps.h to
*		specify the calibration coefficient to be read.
*
* @return	A 16-bit value representing the calibration coefficient.
*		The XADC device guarantees a 10 bit resolution for
*		the ADC converted data and data is the 10 MSB bits of the 16
*		data read from the device.
*
* @note		None.
*
*****************************************************************************/
u16 XAdcPs_GetCalibCoefficient(XAdcPs *InstancePtr, u8 CoeffType)
{
	u32 RegData;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(CoeffType <= XADCPS_CALIB_GAIN_ERROR_COEFF);

	/*
	 * Read the selected calibration coefficient.
	 */
	RegData = XAdcPs_ReadInternalReg(InstancePtr,
					(XADCPS_ADC_A_SUPPLY_CALIB_OFFSET +
					CoeffType));
	return (u16) RegData;
}

/****************************************************************************/
/**
*
* This function reads the Minimum/Maximum measurement for one of the
* specified parameters. Use XADCPS_MAX_* and XADCPS_MIN_* constants defined in
* xadcps.h to specify the parameters (Temperature, VccInt, VccAux, VBram,
* VccPInt, VccPAux and VccPDro).
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	MeasurementType specifies the parameter for which the
*		Minimum/Maximum measurement has to be read.
*		Use XADCPS_MAX_* and XADCPS_MIN_* constants defined in xadcps.h to
*		specify the data to be read.
*
* @return	A 16-bit value representing the maximum/minimum measurement for
*		specified parameter.
*		The XADC device guarantees a 10 bit resolution for
*		the ADC converted data and data is the 10 MSB bits of the 16
*		data read from the device.
*
* @note		None.
*
*****************************************************************************/
u16 XAdcPs_GetMinMaxMeasurement(XAdcPs *InstancePtr, u8 MeasurementType)
{
	u32 RegData;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((MeasurementType <= XADCPS_MAX_VCCPDRO) ||
			((MeasurementType >= XADCPS_MIN_VCCPINT) &&
			(MeasurementType <= XADCPS_MIN_VCCPDRO)))

	/*
	 * Read and return the specified Minimum/Maximum measurement.
	 */
	RegData = XAdcPs_ReadInternalReg(InstancePtr,
					(XADCPS_MAX_TEMP_OFFSET +
					MeasurementType));
	return (u16) RegData;
}

/****************************************************************************/
/**
*
* This function sets the number of samples of averaging that is to be done for
* all the channels in both the single channel mode and sequence mode of
* operations.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Average is the number of samples of averaging programmed to the
*		Configuration Register 0. Use the XADCPS_AVG_* definitions defined
*		in xadcps.h file :
*		- XADCPS_AVG_0_SAMPLES for no averaging
*		- XADCPS_AVG_16_SAMPLES for 16 samples of averaging
*		- XADCPS_AVG_64_SAMPLES for 64 samples of averaging
*		- XADCPS_AVG_256_SAMPLES for 256 samples of averaging
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_SetAvg(XAdcPs *InstancePtr, u8 Average)
{
	u32 RegData;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Average <= XADCPS_AVG_256_SAMPLES);

	/*
	 * Write the averaging value into the Configuration Register 0.
	 */
	RegData = XAdcPs_ReadInternalReg(InstancePtr,
					XADCPS_CFR0_OFFSET) &
					(~XADCPS_CFR0_AVG_VALID_MASK);

	RegData |=  (((u32) Average << XADCPS_CFR0_AVG_SHIFT));
	XAdcPs_WriteInternalReg(InstancePtr, XADCPS_CFR0_OFFSET,
					RegData);

}

/****************************************************************************/
/**
*
* This function returns the number of samples of averaging configured for all
* the channels in the Configuration Register 0.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	The averaging read from the Configuration Register 0 is
*		returned. Use the XADCPS_AVG_* bit definitions defined in
*		xadcps.h file to interpret the returned value :
*		- XADCPS_AVG_0_SAMPLES means no averaging
*		- XADCPS_AVG_16_SAMPLES means 16 samples of averaging
*		- XADCPS_AVG_64_SAMPLES means 64 samples of averaging
*		- XADCPS_AVG_256_SAMPLES means 256 samples of averaging
*
* @note		None.
*
*****************************************************************************/
u8 XAdcPs_GetAvg(XAdcPs *InstancePtr)
{
	u32 Average;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the averaging value from the Configuration Register 0.
	 */
	Average = XAdcPs_ReadInternalReg(InstancePtr,
			XADCPS_CFR0_OFFSET) & XADCPS_CFR0_AVG_VALID_MASK;


	return ((u8) (Average >> XADCPS_CFR0_AVG_SHIFT));
}

/****************************************************************************/
/**
*
* The function sets the given parameters in the Configuration Register 0 in
* the single channel mode.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Channel is the channel number for the singel channel mode.
*		The valid channels are 0 to 5, 8, and 16 to 31.
*		If the external Mux is used then this specifies the channel
*		oonnected to the external Mux. Please read the Device Spec
*		to know which channels are valid.
* @param 	IncreaseAcqCycles is a boolean parameter which specifies whether
*		the Acquisition time for the external channels has to be
*		increased to 10 ADCCLK cycles (specify TRUE) or remain at the
*		default 4 ADCCLK cycles (specify FALSE). This parameter is
*		only valid for the external channels.
* @param 	IsDifferentialMode is a boolean parameter which specifies
*		unipolar(specify FALSE) or differential mode (specify TRUE) for
*		the analog inputs. The 	input mode is only valid for the
*		external channels.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the Configuration Register 0.
*		- XST_FAILURE if the channel sequencer is enabled or the input
*		parameters are not valid for the selected channel.
*
* @note
*		- The number of samples for the averaging for all the channels
*		is set by using the function XAdcPs_SetAvg.
*		- The calibration of the device is done by doing a ADC
*		conversion on the calibration channel(channel 8). The input
*		parameters IncreaseAcqCycles, IsDifferentialMode and
*		IsEventMode are not valid for this channel
*
*
*****************************************************************************/
int XAdcPs_SetSingleChParams(XAdcPs *InstancePtr,
				u8 Channel,
				int IncreaseAcqCycles,
				int IsEventMode,
				int IsDifferentialMode)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid((Channel <= XADCPS_CH_VREFN) ||
			(Channel == XADCPS_CH_ADC_CALIB) ||
			((Channel >= XADCPS_CH_AUX_MIN) &&
			(Channel <= XADCPS_CH_AUX_MAX)));
	Xil_AssertNonvoid((IncreaseAcqCycles == TRUE) ||
			(IncreaseAcqCycles == FALSE));
	Xil_AssertNonvoid((IsEventMode == TRUE) || (IsEventMode == FALSE));
	Xil_AssertNonvoid((IsDifferentialMode == TRUE) ||
			(IsDifferentialMode == FALSE));

	/*
	 * Check if the device is in single channel mode else return failure
	 */
	if ((XAdcPs_GetSequencerMode(InstancePtr) !=
		XADCPS_SEQ_MODE_SINGCHAN)) {
		return XST_FAILURE;
	}

	/*
	 * Read the Configuration Register 0.
	 */
	RegValue = XAdcPs_ReadInternalReg(InstancePtr,
					XADCPS_CFR0_OFFSET) &
					XADCPS_CFR0_AVG_VALID_MASK;

	/*
	 * Select the number of acquisition cycles. The acquisition cycles is
	 * only valid for the external channels.
	 */
	if (IncreaseAcqCycles == TRUE) {
		if (((Channel >= XADCPS_CH_AUX_MIN) &&
			(Channel <= XADCPS_CH_AUX_MAX)) ||
			(Channel == XADCPS_CH_VPVN)){
			RegValue |= XADCPS_CFR0_ACQ_MASK;
		} else {
			return XST_FAILURE;
		}

	}

	/*
	 * Select the input mode. The input mode is only valid for the
	 * external channels.
	 */
	if (IsDifferentialMode == TRUE) {

		if (((Channel >= XADCPS_CH_AUX_MIN) &&
			(Channel <= XADCPS_CH_AUX_MAX)) ||
			(Channel == XADCPS_CH_VPVN)){
			RegValue |= XADCPS_CFR0_DU_MASK;
		} else {
			return XST_FAILURE;
		}
	}

	/*
	 * Select the ADC mode.
	 */
	if (IsEventMode == TRUE) {
		RegValue |= XADCPS_CFR0_EC_MASK;
	}

	/*
	 * Write the given values into the Configuration Register 0.
	 */
	RegValue |= (Channel & XADCPS_CFR0_CHANNEL_MASK);
	XAdcPs_WriteInternalReg(InstancePtr, XADCPS_CFR0_OFFSET,
				RegValue);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* This function enables the alarm outputs for the specified alarms in the
* Configuration Register 1.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	AlmEnableMask is the bit-mask of the alarm outputs to be enabled
*		in the Configuration Register 1.
*		Bit positions of 1 will be enabled. Bit positions of 0 will be
*		disabled. This mask is formed by OR'ing XADCPS_CFR1_ALM_*_MASK and
*		XADCPS_CFR1_OT_MASK masks defined in xadcps_hw.h.
*
* @return	None.
*
* @note		The implementation of the alarm enables in the Configuration
*		register 1 is such that the alarms for bit positions of 1 will
*		be disabled and alarms for bit positions of 0 will be enabled.
*		The alarm outputs specified by the AlmEnableMask are negated
*		before writing to the Configuration Register 1.
*
*
*****************************************************************************/
void XAdcPs_SetAlarmEnables(XAdcPs *InstancePtr, u16 AlmEnableMask)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	RegValue = XAdcPs_ReadInternalReg(InstancePtr, XADCPS_CFR1_OFFSET);

	RegValue &= (u32)~XADCPS_CFR1_ALM_ALL_MASK;
	RegValue |= (~AlmEnableMask & XADCPS_CFR1_ALM_ALL_MASK);

	/*
	 * Enable/disables the alarm enables for the specified alarm bits in the
	 * Configuration Register 1.
	 */
	XAdcPs_WriteInternalReg(InstancePtr, XADCPS_CFR1_OFFSET,
				RegValue);
}

/****************************************************************************/
/**
*
* This function gets the status of the alarm output enables in the
* Configuration Register 1.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	This is the bit-mask of the enabled alarm outputs in the
*		Configuration Register 1. Use the masks XADCPS_CFR1_ALM*_* and
*		XADCPS_CFR1_OT_MASK defined in xadcps_hw.h to interpret the
*		returned value.
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
u16 XAdcPs_GetAlarmEnables(XAdcPs *InstancePtr)
{
	u32 RegValue;

	/*
	 * Assert the arguments
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the status of alarm output enables from the Configuration
	 * Register 1.
	 */
	RegValue = XAdcPs_ReadInternalReg(InstancePtr,
			XADCPS_CFR1_OFFSET) & XADCPS_CFR1_ALM_ALL_MASK;
	return (u16) (~RegValue & XADCPS_CFR1_ALM_ALL_MASK);
}

/****************************************************************************/
/**
*
* This function enables the specified calibration in the Configuration
* Register 1 :
*
* - XADCPS_CFR1_CAL_ADC_OFFSET_MASK : Calibration 0 -ADC offset correction
* - XADCPS_CFR1_CAL_ADC_GAIN_OFFSET_MASK : Calibration 1 -ADC gain and offset
*						correction
* - XADCPS_CFR1_CAL_PS_OFFSET_MASK : Calibration 2 -Power Supply sensor
*					offset correction
* - XADCPS_CFR1_CAL_PS_GAIN_OFFSET_MASK : Calibration 3 -Power Supply sensor
*						gain and offset correction
* - XADCPS_CFR1_CAL_DISABLE_MASK : No Calibration
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Calibration is the Calibration to be applied.
*		Use XADCPS_CFR1_CAL*_* bits defined in xadcps_hw.h.
*		Multiple calibrations can be enabled at a time by oring the
*		XADCPS_CFR1_CAL_ADC_* and XADCPS_CFR1_CAL_PS_* bits.
*		Calibration can be disabled by specifying
		XADCPS_CFR1_CAL_DISABLE_MASK;
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_SetCalibEnables(XAdcPs *InstancePtr, u16 Calibration)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(((Calibration >= XADCPS_CFR1_CAL_ADC_OFFSET_MASK) &&
			(Calibration <= XADCPS_CFR1_CAL_VALID_MASK)) ||
			(Calibration == XADCPS_CFR1_CAL_DISABLE_MASK));

	/*
	 * Set the specified calibration in the Configuration Register 1.
	 */
	RegValue = XAdcPs_ReadInternalReg(InstancePtr,
					XADCPS_CFR1_OFFSET);

	RegValue &= (~ XADCPS_CFR1_CAL_VALID_MASK);
	RegValue |= (Calibration & XADCPS_CFR1_CAL_VALID_MASK);
	XAdcPs_WriteInternalReg(InstancePtr, XADCPS_CFR1_OFFSET,
				RegValue);

}

/****************************************************************************/
/**
*
* This function reads the value of the calibration enables from the
* Configuration Register 1.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	The value of the calibration enables in the Configuration
*		Register 1 :
*		- XADCPS_CFR1_CAL_ADC_OFFSET_MASK : ADC offset correction
*		- XADCPS_CFR1_CAL_ADC_GAIN_OFFSET_MASK : ADC gain and offset
*				correction
*		- XADCPS_CFR1_CAL_PS_OFFSET_MASK : Power Supply sensor offset
*				correction
*		- XADCPS_CFR1_CAL_PS_GAIN_OFFSET_MASK : Power Supply sensor
*				gain and offset correction
*		- XADCPS_CFR1_CAL_DISABLE_MASK : No Calibration
*
* @note		None.
*
*****************************************************************************/
u16 XAdcPs_GetCalibEnables(XAdcPs *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the calibration enables from the Configuration Register 1.
	 */
	return (u16) XAdcPs_ReadInternalReg(InstancePtr,
			XADCPS_CFR1_OFFSET) & XADCPS_CFR1_CAL_VALID_MASK;

}

/****************************************************************************/
/**
*
* This function sets the specified Channel Sequencer Mode in the Configuration
* Register 1 :
*		- Default safe mode (XADCPS_SEQ_MODE_SAFE)
*		- One pass through sequence (XADCPS_SEQ_MODE_ONEPASS)
*		- Continuous channel sequencing (XADCPS_SEQ_MODE_CONTINPASS)
*		- Single Channel/Sequencer off (XADCPS_SEQ_MODE_SINGCHAN)
*		- Simulataneous sampling mode (XADCPS_SEQ_MODE_SIMUL_SAMPLING)
*		- Independent mode (XADCPS_SEQ_MODE_INDEPENDENT)
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	SequencerMode is the sequencer mode to be set.
*		Use XADCPS_SEQ_MODE_* bits defined in xadcps.h.
* @return	None.
*
* @note		Only one of the modes can be enabled at a time. Please
*		read the Spec of the XADC for further information about the
*		sequencer modes.
*
*
*****************************************************************************/
void XAdcPs_SetSequencerMode(XAdcPs *InstancePtr, u8 SequencerMode)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((SequencerMode <= XADCPS_SEQ_MODE_SIMUL_SAMPLING) ||
			(SequencerMode == XADCPS_SEQ_MODE_INDEPENDENT));

	/*
	 * Set the specified sequencer mode in the Configuration Register 1.
	 */
	RegValue = XAdcPs_ReadInternalReg(InstancePtr,
					XADCPS_CFR1_OFFSET);
	RegValue &= (~ XADCPS_CFR1_SEQ_VALID_MASK);
	RegValue |= ((SequencerMode  << XADCPS_CFR1_SEQ_SHIFT) &
					XADCPS_CFR1_SEQ_VALID_MASK);
	XAdcPs_WriteInternalReg(InstancePtr, XADCPS_CFR1_OFFSET,
				RegValue);

}

/****************************************************************************/
/**
*
* This function gets the channel sequencer mode from the Configuration
* Register 1.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	The channel sequencer mode :
*		- XADCPS_SEQ_MODE_SAFE : Default safe mode
*		- XADCPS_SEQ_MODE_ONEPASS : One pass through sequence
*		- XADCPS_SEQ_MODE_CONTINPASS : Continuous channel sequencing
*		- XADCPS_SEQ_MODE_SINGCHAN : Single channel/Sequencer off
*		- XADCPS_SEQ_MODE_SIMUL_SAMPLING : Simulataneous sampling mode
*		- XADCPS_SEQ_MODE_INDEPENDENT : Independent mode
*
*
* @note		None.
*
*****************************************************************************/
u8 XAdcPs_GetSequencerMode(XAdcPs *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the channel sequencer mode from the Configuration Register 1.
	 */
	return ((u8) ((XAdcPs_ReadInternalReg(InstancePtr,
			XADCPS_CFR1_OFFSET) & XADCPS_CFR1_SEQ_VALID_MASK) >>
			XADCPS_CFR1_SEQ_SHIFT));

}

/****************************************************************************/
/**
*
* The function sets the frequency of the ADCCLK by configuring the DCLK to
* ADCCLK ratio in the Configuration Register #2
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	Divisor is clock divisor used to derive ADCCLK from DCLK.
*		Valid values of the divisor are
*		 - 0 to 255. Values 0, 1, 2 are all mapped to 2.
*		Refer to the device specification for more details
*
* @return	None.
*
* @note		- The ADCCLK is an internal clock used by the ADC and is
*		  synchronized to the DCLK clock. The ADCCLK is equal to DCLK
*		  divided by the user selection in the Configuration Register 2.
*		- There is no Assert on the minimum value of the Divisor.
*
*****************************************************************************/
void XAdcPs_SetAdcClkDivisor(XAdcPs *InstancePtr, u8 Divisor)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Write the divisor value into the Configuration Register #2.
	 */
	XAdcPs_WriteInternalReg(InstancePtr, XADCPS_CFR2_OFFSET,
			  Divisor << XADCPS_CFR2_CD_SHIFT);

}

/****************************************************************************/
/**
*
* The function gets the ADCCLK divisor from the Configuration Register 2.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	The divisor read from the Configuration Register 2.
*
* @note		The ADCCLK is an internal clock used by the ADC and is
*		synchronized to the DCLK clock. The ADCCLK is equal to DCLK
*		divided by the user selection in the Configuration Register 2.
*
*****************************************************************************/
u8 XAdcPs_GetAdcClkDivisor(XAdcPs *InstancePtr)
{
	u16 Divisor;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the divisor value from the Configuration Register 2.
	 */
	Divisor = (u16) XAdcPs_ReadInternalReg(InstancePtr,
					 XADCPS_CFR2_OFFSET);

	return (u8) (Divisor >> XADCPS_CFR2_CD_SHIFT);
}

/****************************************************************************/
/**
*
* This function enables the specified channels in the ADC Channel Selection
* Sequencer Registers. The sequencer must be disabled before writing to these
* regsiters.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	ChEnableMask is the bit mask of all the channels to be enabled.
*		Use XADCPS_SEQ_CH__* defined in xadcps_hw.h to specify the Channel
*		numbers. Bit masks of 1 will be enabled and bit mask of 0 will
*		be disabled.
*		The ChEnableMask is a 32 bit mask that is written to the two
*		16 bit ADC Channel Selection Sequencer Registers.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the ADC Channel Selection Sequencer Registers.
*		- XST_FAILURE if the channel sequencer is enabled.
*
* @note		None
*
*****************************************************************************/
int XAdcPs_SetSeqChEnables(XAdcPs *InstancePtr, u32 ChEnableMask)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * The sequencer must be disabled for writing any of these registers
	 * Return XST_FAILURE if the channel sequencer is enabled.
	 */
	if ((XAdcPs_GetSequencerMode(InstancePtr) != XADCPS_SEQ_MODE_SAFE)) {
		return XST_FAILURE;
	}

	/*
	 * Enable the specified channels in the ADC Channel Selection Sequencer
	 * Registers.
	 */
	XAdcPs_WriteInternalReg(InstancePtr,
				XADCPS_SEQ00_OFFSET,
				(ChEnableMask & XADCPS_SEQ00_CH_VALID_MASK));

	XAdcPs_WriteInternalReg(InstancePtr,
				XADCPS_SEQ01_OFFSET,
				(ChEnableMask >> XADCPS_SEQ_CH_AUX_SHIFT) &
				XADCPS_SEQ01_CH_VALID_MASK);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* This function gets the channel enable bits status from the ADC Channel
* Selection Sequencer Registers.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	Gets the channel enable bits. Use XADCPS_SEQ_CH__* defined in
*		xadcps_hw.h to interpret the Channel numbers. Bit masks of 1
*		are the channels that are enabled and bit mask of 0 are
*		the channels that are disabled.
*
* @return	None
*
* @note		None
*
*****************************************************************************/
u32 XAdcPs_GetSeqChEnables(XAdcPs *InstancePtr)
{
	u32 RegValEnable;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 *  Read the channel enable bits for all the channels from the ADC
	 *  Channel Selection Register.
	 */
	RegValEnable = XAdcPs_ReadInternalReg(InstancePtr,
				XADCPS_SEQ00_OFFSET) &
				XADCPS_SEQ00_CH_VALID_MASK;
	RegValEnable |= (XAdcPs_ReadInternalReg(InstancePtr,
				XADCPS_SEQ01_OFFSET) &
				XADCPS_SEQ01_CH_VALID_MASK) <<
				XADCPS_SEQ_CH_AUX_SHIFT;


	return RegValEnable;
}

/****************************************************************************/
/**
*
* This function enables the averaging for the specified channels in the ADC
* Channel Averaging Enable Sequencer Registers. The sequencer must be disabled
* before writing to these regsiters.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	AvgEnableChMask is the bit mask of all the channels for which
*		averaging is to be enabled. Use XADCPS_SEQ_CH__* defined in
*		xadcps_hw.h to specify the Channel numbers. Averaging will be
*		enabled for bit masks of 1 and disabled for bit mask of 0.
*		The AvgEnableChMask is a 32 bit mask that is written to the two
*		16 bit ADC Channel Averaging Enable Sequencer Registers.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the ADC Channel Averaging Enables Sequencer Registers.
*		- XST_FAILURE if the channel sequencer is enabled.
*
* @note		None
*
*****************************************************************************/
int XAdcPs_SetSeqAvgEnables(XAdcPs *InstancePtr, u32 AvgEnableChMask)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * The sequencer must be disabled for writing any of these registers
	 * Return XST_FAILURE if the channel sequencer is enabled.
	 */
	if ((XAdcPs_GetSequencerMode(InstancePtr) != XADCPS_SEQ_MODE_SAFE)) {
		return XST_FAILURE;
	}

	/*
	 * Enable/disable the averaging for the specified channels in the
	 * ADC Channel Averaging Enables Sequencer Registers.
	 */
	XAdcPs_WriteInternalReg(InstancePtr,
				XADCPS_SEQ02_OFFSET,
				(AvgEnableChMask & XADCPS_SEQ02_CH_VALID_MASK));

	XAdcPs_WriteInternalReg(InstancePtr,
				XADCPS_SEQ03_OFFSET,
				(AvgEnableChMask >> XADCPS_SEQ_CH_AUX_SHIFT) &
				XADCPS_SEQ03_CH_VALID_MASK);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* This function returns the channels for which the averaging has been enabled
* in the ADC Channel Averaging Enables Sequencer Registers.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @returns 	The status of averaging (enabled/disabled) for all the channels.
*		Use XADCPS_SEQ_CH__* defined in xadcps_hw.h to interpret the
*		Channel numbers. Bit masks of 1 are the channels for which
*		averaging is enabled and bit mask of 0 are the channels for
*		averaging is disabled
*
* @note		None
*
*****************************************************************************/
u32 XAdcPs_GetSeqAvgEnables(XAdcPs *InstancePtr)
{
	u32 RegValAvg;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the averaging enable status for all the channels from the
	 * ADC Channel Averaging Enables Sequencer Registers.
	 */
	RegValAvg = XAdcPs_ReadInternalReg(InstancePtr,
				XADCPS_SEQ02_OFFSET) & XADCPS_SEQ02_CH_VALID_MASK;
	RegValAvg |= (XAdcPs_ReadInternalReg(InstancePtr,
			XADCPS_SEQ03_OFFSET) & XADCPS_SEQ03_CH_VALID_MASK) <<
			XADCPS_SEQ_CH_AUX_SHIFT;

	return RegValAvg;
}

/****************************************************************************/
/**
*
* This function sets the Analog input mode for the specified channels in the ADC
* Channel Analog-Input Mode Sequencer Registers. The sequencer must be disabled
* before writing to these regsiters.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	InputModeChMask is the bit mask of all the channels for which
*		the input mode is differential mode. Use XADCPS_SEQ_CH__* defined
*		in xadcps_hw.h to specify the channel numbers. Differential
*		input mode will be set for bit masks of 1 and unipolar input
*		mode for bit masks of 0.
*		The InputModeChMask is a 32 bit mask that is written to the two
*		16 bit ADC Channel Analog-Input Mode Sequencer Registers.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the ADC Channel Analog-Input Mode Sequencer Registers.
*		- XST_FAILURE if the channel sequencer is enabled.
*
* @note		None
*
*****************************************************************************/
int XAdcPs_SetSeqInputMode(XAdcPs *InstancePtr, u32 InputModeChMask)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * The sequencer must be disabled for writing any of these registers
	 * Return XST_FAILURE if the channel sequencer is enabled.
	 */
	if ((XAdcPs_GetSequencerMode(InstancePtr) != XADCPS_SEQ_MODE_SAFE)) {
		return XST_FAILURE;
	}

	/*
	 * Set the input mode for the specified channels in the ADC Channel
	 * Analog-Input Mode Sequencer Registers.
	 */
	XAdcPs_WriteInternalReg(InstancePtr,
				XADCPS_SEQ04_OFFSET,
				(InputModeChMask & XADCPS_SEQ04_CH_VALID_MASK));

	XAdcPs_WriteInternalReg(InstancePtr,
				XADCPS_SEQ05_OFFSET,
				(InputModeChMask >> XADCPS_SEQ_CH_AUX_SHIFT) &
				XADCPS_SEQ05_CH_VALID_MASK);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* This function gets the Analog input mode for all the channels from
* the ADC Channel Analog-Input Mode Sequencer Registers.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @returns 	The input mode for all the channels.
*		Use XADCPS_SEQ_CH_* defined in xadcps_hw.h to interpret the
*		Channel numbers. Bit masks of 1 are the channels for which
*		input mode is differential and bit mask of 0 are the channels
*		for which input mode is unipolar.
*
* @note		None.
*
*****************************************************************************/
u32 XAdcPs_GetSeqInputMode(XAdcPs *InstancePtr)
{
	u32 InputMode;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 *  Get the input mode for all the channels from the ADC Channel
	 * Analog-Input Mode Sequencer Registers.
	 */
	InputMode = XAdcPs_ReadInternalReg(InstancePtr,
				XADCPS_SEQ04_OFFSET) &
				XADCPS_SEQ04_CH_VALID_MASK;
	InputMode |= (XAdcPs_ReadInternalReg(InstancePtr,
				XADCPS_SEQ05_OFFSET) &
				XADCPS_SEQ05_CH_VALID_MASK) <<
				XADCPS_SEQ_CH_AUX_SHIFT;

	return InputMode;
}

/****************************************************************************/
/**
*
* This function sets the number of Acquisition cycles in the ADC Channel
* Acquisition Time Sequencer Registers. The sequencer must be disabled
* before writing to these regsiters.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	AcqCyclesChMask is the bit mask of all the channels for which
*		the number of acquisition cycles is to be extended.
*		Use XADCPS_SEQ_CH__* defined in xadcps_hw.h to specify the Channel
*		numbers. Acquisition cycles will be extended to 10 ADCCLK cycles
*		for bit masks of 1 and will be the default 4 ADCCLK cycles for
*		bit masks of 0.
*		The AcqCyclesChMask is a 32 bit mask that is written to the two
*		16 bit ADC Channel Acquisition Time Sequencer Registers.
*
* @return
*		- XST_SUCCESS if the given values were written successfully to
*		the Channel Sequencer Registers.
*		- XST_FAILURE if the channel sequencer is enabled.
*
* @note		None.
*
*****************************************************************************/
int XAdcPs_SetSeqAcqTime(XAdcPs *InstancePtr, u32 AcqCyclesChMask)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * The sequencer must be disabled for writing any of these registers
	 * Return XST_FAILURE if the channel sequencer is enabled.
	 */
	if ((XAdcPs_GetSequencerMode(InstancePtr) !=
			XADCPS_SEQ_MODE_SAFE)) {
		return XST_FAILURE;
	}

	/*
	 * Set the Acquisition time for the specified channels in the
	 * ADC Channel Acquisition Time Sequencer Registers.
	 */
	XAdcPs_WriteInternalReg(InstancePtr,
				XADCPS_SEQ06_OFFSET,
				(AcqCyclesChMask & XADCPS_SEQ06_CH_VALID_MASK));

	XAdcPs_WriteInternalReg(InstancePtr,
				XADCPS_SEQ07_OFFSET,
				(AcqCyclesChMask >> XADCPS_SEQ_CH_AUX_SHIFT) &
				XADCPS_SEQ07_CH_VALID_MASK);

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* This function gets the status of acquisition from the ADC Channel Acquisition
* Time Sequencer Registers.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @returns 	The acquisition time for all the channels.
*		Use XADCPS_SEQ_CH__* defined in xadcps_hw.h to interpret the
*		Channel numbers. Bit masks of 1 are the channels for which
*		acquisition cycles are extended and bit mask of 0 are the
*		channels for which acquisition cycles are not extended.
*
* @note		None
*
*****************************************************************************/
u32 XAdcPs_GetSeqAcqTime(XAdcPs *InstancePtr)
{
	u32 RegValAcq;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Get the Acquisition cycles for the specified channels from the ADC
	 * Channel Acquisition Time Sequencer Registers.
	 */
	RegValAcq = XAdcPs_ReadInternalReg(InstancePtr,
				XADCPS_SEQ06_OFFSET) &
				XADCPS_SEQ06_CH_VALID_MASK;
	RegValAcq |= (XAdcPs_ReadInternalReg(InstancePtr,
				XADCPS_SEQ07_OFFSET) &
				XADCPS_SEQ07_CH_VALID_MASK) <<
				XADCPS_SEQ_CH_AUX_SHIFT;

	return RegValAcq;
}

/****************************************************************************/
/**
*
* This functions sets the contents of the given Alarm Threshold Register.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	AlarmThrReg is the index of an Alarm Threshold Register to
*		be set. Use XADCPS_ATR_* constants defined in xadcps.h to
*		specify the index.
* @param	Value is the 16-bit threshold value to write into the register.
*
* @return	None.
*
* @note		Use XAdcPs_SetOverTemp() to set the Over Temperature upper
*		threshold value.
*
*****************************************************************************/
void XAdcPs_SetAlarmThreshold(XAdcPs *InstancePtr, u8 AlarmThrReg, u16 Value)
{

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(AlarmThrReg <= XADCPS_ATR_VCCPDRO_LOWER);

	/*
	 * Write the value into the specified Alarm Threshold Register.
	 */
	XAdcPs_WriteInternalReg(InstancePtr, XADCPS_ATR_TEMP_UPPER_OFFSET +
					AlarmThrReg,Value);

}

/****************************************************************************/
/**
*
* This function returns the contents of the specified Alarm Threshold Register.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	AlarmThrReg is the index of an Alarm Threshold Register
*		to be read. Use XADCPS_ATR_* constants defined in 	xadcps_hw.h
*		to specify the index.
*
* @return	A 16-bit value representing the contents of the selected Alarm
*		Threshold Register.
*
* @note		None.
*
*****************************************************************************/
u16 XAdcPs_GetAlarmThreshold(XAdcPs *InstancePtr, u8 AlarmThrReg)
{
	u32 RegData;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(AlarmThrReg <= XADCPS_ATR_VCCPDRO_LOWER);

	/*
	 * Read the specified Alarm Threshold Register and return
	 * the value
	 */
	RegData = XAdcPs_ReadInternalReg(InstancePtr,
				(XADCPS_ATR_TEMP_UPPER_OFFSET + AlarmThrReg));

	return (u16) RegData;
}


/****************************************************************************/
/**
*
* This function enables programming of the powerdown temperature for the
* OverTemp signal in the OT Powerdown register.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_EnableUserOverTemp(XAdcPs *InstancePtr)
{
	u16 OtUpper;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the OT upper Alarm Threshold Register.
	 */
	OtUpper = XAdcPs_ReadInternalReg(InstancePtr,
				   XADCPS_ATR_OT_UPPER_OFFSET);
	OtUpper &= ~(XADCPS_ATR_OT_UPPER_ENB_MASK);

	/*
	 * Preserve the powerdown value and write OT enable value the into the
	 * OT Upper Alarm Threshold Register.
	 */
	OtUpper |= XADCPS_ATR_OT_UPPER_ENB_VAL;
	XAdcPs_WriteInternalReg(InstancePtr,
			  XADCPS_ATR_OT_UPPER_OFFSET, OtUpper);
}

/****************************************************************************/
/**
*
* This function disables programming of the powerdown temperature for the
* OverTemp signal in the OT Powerdown register.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	None.
*
* @note		None.
*
*
*****************************************************************************/
void XAdcPs_DisableUserOverTemp(XAdcPs *InstancePtr)
{
	u16 OtUpper;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the OT Upper Alarm Threshold Register.
	 */
	OtUpper = XAdcPs_ReadInternalReg(InstancePtr,
					 XADCPS_ATR_OT_UPPER_OFFSET);
	OtUpper &= ~(XADCPS_ATR_OT_UPPER_ENB_MASK);

	XAdcPs_WriteInternalReg(InstancePtr,
			  XADCPS_ATR_OT_UPPER_OFFSET, OtUpper);
}


/****************************************************************************/
/**
*
* The function enables the Event mode or Continuous mode in the sequencer mode.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	IsEventMode is a boolean parameter that specifies continuous
*		sampling (specify FALSE) or event driven sampling mode (specify
*		TRUE) for the given channel.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_SetSequencerEvent(XAdcPs *InstancePtr, int IsEventMode)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((IsEventMode == TRUE) || (IsEventMode == FALSE));

	/*
	 * Read the Configuration Register 0.
	 */
	RegValue = XAdcPs_ReadInternalReg(InstancePtr,
					XADCPS_CFR0_OFFSET) &
					(~XADCPS_CFR0_EC_MASK);

	/*
	 * Set the ADC mode.
	 */
	if (IsEventMode == TRUE) {
		RegValue |= XADCPS_CFR0_EC_MASK;
	} else {
		RegValue &= ~XADCPS_CFR0_EC_MASK;
	}

	XAdcPs_WriteInternalReg(InstancePtr, XADCPS_CFR0_OFFSET,
					RegValue);
}


/****************************************************************************/
/**
*
* This function returns the sampling mode.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	The sampling mode
*		- 0 specifies continuous sampling
*		- 1 specifies event driven sampling mode
*
* @note		None.
*
*****************************************************************************/
int XAdcPs_GetSamplingMode(XAdcPs *InstancePtr)
{
	u32 Mode;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the sampling mode from the Configuration Register 0.
	 */
	Mode = XAdcPs_ReadInternalReg(InstancePtr,
				   XADCPS_CFR0_OFFSET) &
				   XADCPS_CFR0_EC_MASK;
	if (Mode) {

		return 1;
	}

	return (0);
}


/****************************************************************************/
/**
*
* This function sets the External Mux mode.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param 	MuxMode specifies whether External Mux is used
*		- FALSE specifies NO external MUX
*		- TRUE specifies External Mux is used
* @param	Channel specifies the channel to be used for the
*		external Mux. Please read the Device Spec for which
*		channels are valid for which mode.
*
* @return	None.
*
* @note		There is no Assert in this function for checking the channel
*		number if the external Mux is used. The user should provide a
*		valid channel number.
*
*****************************************************************************/
void XAdcPs_SetMuxMode(XAdcPs *InstancePtr, int MuxMode, u8 Channel)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid((MuxMode == TRUE) || (MuxMode == FALSE));

	/*
	 * Read the Configuration Register 0.
	 */
	RegValue = XAdcPs_ReadInternalReg(InstancePtr,
					XADCPS_CFR0_OFFSET) &
					(~XADCPS_CFR0_MUX_MASK);
	/*
	 * Select the Mux mode and the channel to be used.
	 */
	if (MuxMode == TRUE) {
		RegValue |= XADCPS_CFR0_MUX_MASK;
		RegValue |= (Channel & XADCPS_CFR0_CHANNEL_MASK);

	}

	/*
	 * Write the mux mode into the Configuration Register 0.
	 */
	XAdcPs_WriteInternalReg(InstancePtr, XADCPS_CFR0_OFFSET,
					RegValue);
}


/****************************************************************************/
/**
*
* This function sets the Power Down mode.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param 	Mode specifies the Power Down Mode
*		- XADCPS_PD_MODE_NONE specifies NO Power Down (Both ADC A and
*		ADC B are enabled)
*		- XADCPS_PD_MODE_ADCB specfies the Power Down of ADC B
*		- XADCPS_PD_MODE_XADC specifies the Power Down of
*		both ADC A and ADC B.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAdcPs_SetPowerdownMode(XAdcPs *InstancePtr, u32 Mode)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(Mode < XADCPS_PD_MODE_XADC);


	/*
	 * Read the Configuration Register 2.
	 */
	RegValue = XAdcPs_ReadInternalReg(InstancePtr,
					XADCPS_CFR2_OFFSET) &
					(~XADCPS_CFR2_PD_MASK);
	/*
	 * Select the Power Down mode.
	 */
	RegValue |= (Mode << XADCPS_CFR2_PD_SHIFT);

	XAdcPs_WriteInternalReg(InstancePtr, XADCPS_CFR2_OFFSET,
					RegValue);
}

/****************************************************************************/
/**
*
* This function gets the Power Down mode.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	Mode specifies the Power Down Mode
*		- XADCPS_PD_MODE_NONE specifies NO Power Down (Both ADC A and
*		ADC B are enabled)
*		- XADCPS_PD_MODE_ADCB specfies the Power Down of ADC B
*		- XADCPS_PD_MODE_XADC specifies the Power Down of
*		both ADC A and ADC B.
*
* @note		None.
*
*****************************************************************************/
u32 XAdcPs_GetPowerdownMode(XAdcPs *InstancePtr)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Power Down Mode.
	 */
	RegValue = XAdcPs_ReadInternalReg(InstancePtr,
					XADCPS_CFR2_OFFSET) &
					(~XADCPS_CFR2_PD_MASK);
	/*
	 * Return the Power Down mode.
	 */
	return (RegValue >> XADCPS_CFR2_PD_SHIFT);

}

/****************************************************************************/
/**
*
* This function is used for writing to XADC Registers using the command FIFO.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	RegOffset is the offset of the XADC register to be written.
* @param	Data is the data to be written.
*
* @return	None.
*
* @note		None.
*
*
*****************************************************************************/
void XAdcPs_WriteInternalReg(XAdcPs *InstancePtr, u32 RegOffset, u32 Data)
{
	u32 RegData;

	/*
	 * Write the Data into the FIFO Register.
	 */
	RegData = XAdcPs_FormatWriteData(RegOffset, Data, TRUE);

	XAdcPs_WriteFifo(InstancePtr, RegData);

	/* Read the Read FIFO after any write since for each write
	 * one location of Read FIFO gets updated
	 */
	XAdcPs_ReadFifo(InstancePtr);

}


/****************************************************************************/
/**
*
* This function is used for reading from the XADC Registers using the Data FIFO.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
* @param	RegOffset is the offset of the XADC register to be read.
*
* @return	Data read from the FIFO
*
* @note		None.
*
*
*****************************************************************************/
u32 XAdcPs_ReadInternalReg(XAdcPs *InstancePtr, u32 RegOffset)
{

	u32 RegData;

	RegData = XAdcPs_FormatWriteData(RegOffset, 0x0, FALSE);

	/* Read cmd to FIFO*/
	XAdcPs_WriteFifo(InstancePtr, RegData);

	/* Do a Dummy read */
	RegData = XAdcPs_ReadFifo(InstancePtr);

	/* Do a Dummy write to get the actual read */
	XAdcPs_WriteFifo(InstancePtr, RegData);

	/* Do the Actual read */
	RegData = XAdcPs_ReadFifo(InstancePtr);

	return RegData;

}


