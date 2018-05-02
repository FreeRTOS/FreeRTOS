/******************************************************************************
*
* Copyright (C) 2011 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xadcps.h
* @addtogroup xadcps_v2_2
* @{
* @details
*
* The XAdcPs driver supports the Xilinx XADC/ADC device.
*
* The XADC/ADC device has the following features:
*	- 10-bit, 200-KSPS (kilo samples per second)
*		Analog-to-Digital Converter (ADC)
*	- Monitoring of on-chip supply voltages and temperature
*	- 1 dedicated differential analog-input pair and
*	  16 auxiliary differential analog-input pairs
*	- Automatic alarms based on user defined limits for the on-chip
*	  supply voltages and temperature
*	- Automatic Channel Sequencer, programmable averaging, programmable
*	  acquisition time for the external inputs, unipolar or differential
*	  input selection for the external inputs
*	- Inbuilt Calibration
*	- Optional interrupt request generation
*
*
* The user should refer to the hardware device specification for detailed
* information about the device.
*
* This header file contains the prototypes of driver functions that can
* be used to access the XADC/ADC device.
*
*
* <b> XADC Channel Sequencer Modes </b>
*
* The  XADC Channel Sequencer supports the following operating modes:
*
*   - <b> Default </b>: This is the default mode after power up.
*		In this mode of operation the XADC operates in
*		a sequence mode, monitoring the on chip sensors:
*		Temperature, VCCINT, and VCCAUX.
*   - <b> One pass through sequence </b>: In this mode the XADC
*		converts the channels enabled in the Sequencer Channel Enable
*		registers for a single pass and then stops.
*   - <b> Continuous cycling of sequence </b>: In this mode the XADC
*		converts the channels enabled in the Sequencer Channel Enable
*		registers continuously.
*   - <b> Single channel mode</b>: In this mode the XADC Channel
*		Sequencer is disabled and the XADC operates in a
*		Single Channel Mode.
*		The XADC can operate either in a Continuous or Event
*		driven sampling mode in the single channel mode.
*   - <b> Simultaneous Sampling Mode</b>: In this mode the XADC Channel
*		Sequencer will automatically sequence through eight fixed pairs
*		of auxiliary analog input channels for simulataneous conversion.
*   - <b> Independent ADC mode</b>: In this mode the first ADC (A) is used to
*		is used to implement a fixed monitoring mode similar to the
*		default mode but the alarm fucntions ar eenabled.
*		The second ADC (B) is available to be used with external analog
*		input channels only.
*
* Read the XADC spec for more information about the sequencer modes.
*
* <b> Initialization and Configuration </b>
*
* The device driver enables higher layer software (e.g., an application) to
* communicate to the XADC/ADC device.
*
* XAdcPs_CfgInitialize() API is used to initialize the XADC/ADC
* device. The user needs to first call the XAdcPs_LookupConfig() API which
* returns the Configuration structure pointer which is passed as a parameter to
* the XAdcPs_CfgInitialize() API.
*
*
* <b>Interrupts</b>
*
* The XADC/ADC device supports interrupt driven mode and the default
* operation mode is polling mode.
*
* The interrupt mode is available only if hardware is configured to support
* interrupts.
*
* This driver does not provide a Interrupt Service Routine (ISR) for the device.
* It is the responsibility of the application to provide one if needed. Refer to
* the interrupt example provided with this driver for details on using the
* device in interrupt mode.
*
*
* <b> Virtual Memory </b>
*
* This driver supports Virtual Memory. The RTOS is responsible for calculating
* the correct device base address in Virtual Memory space.
*
*
* <b> Threads </b>
*
* This driver is not thread safe. Any needs for threads or thread mutual
* exclusion must be satisfied by the layer above this driver.
*
*
* <b> Asserts </b>
*
* Asserts are used within all Xilinx drivers to enforce constraints on argument
* values. Asserts can be turned off on a system-wide basis by defining, at
* compile time, the NDEBUG identifier. By default, asserts are turned on and it
* is recommended that users leave asserts on during development.
*
*
* <b> Building the driver </b>
*
* The XAdcPs driver is composed of several source files. This allows the user
* to build and link only those parts of the driver that are necessary.
*
* <b> Limitations of the driver </b>
*
* XADC/ADC device can be accessed through the JTAG port and the PLB
* interface. The driver implementation does not support the simultaneous access
* of the device by both these interfaces. The user has to care of this situation
* in the user application code.
*
* <br><br>
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
*			in xadcps.c to fix CR #693371
* 1.03a bss    11/01/13 Modified xadcps_hw.h to use correct Register offsets
*			CR#749687
* 2.1   bss    08/05/14 Added declarations for XAdcPs_SetSequencerEvent,
*			XAdcPs_GetSamplingMode, XAdcPs_SetMuxMode,
*			XAdcPs_SetPowerdownMode and XAdcPs_GetPowerdownMode
*			functions.
*			Modified Assert for XAdcPs_SetSingleChParams in
*			xadcps.c to fix CR #807563.
* 2.2   bss    04/27/14 Modified to use correct Device Config base address in
*						xadcps.c (CR#854437).
*       ms     01/23/17 Added xil_printf statement in main function for all
*                       examples to ensure that "Successfully ran" and "Failed"
*                       strings are available in all examples. This is a fix
*                       for CR-965028.
*       ms     03/17/17 Added readme.txt file in examples folder for doxygen
*                       generation.
*       ms     04/05/17 Modified Comment lines in functions of xadcps
*                       examples to recognize it as documentation block
*                       for doxygen generation.
*
* </pre>
*
*****************************************************************************/
#ifndef XADCPS_H /* Prevent circular inclusions */
#define XADCPS_H /* by using protection macros  */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xadcps_hw.h"

/************************** Constant Definitions ****************************/


/**
 * @name Indexes for the different channels.
 * @{
 */
#define XADCPS_CH_TEMP		0x0  /**< On Chip Temperature */
#define XADCPS_CH_VCCINT	0x1  /**< VCCINT */
#define XADCPS_CH_VCCAUX	0x2  /**< VCCAUX */
#define XADCPS_CH_VPVN		0x3  /**< VP/VN Dedicated analog inputs */
#define XADCPS_CH_VREFP		0x4  /**< VREFP */
#define XADCPS_CH_VREFN		0x5  /**< VREFN */
#define XADCPS_CH_VBRAM		0x6  /**< On-chip VBRAM Data Reg, 7 series */
#define XADCPS_CH_SUPPLY_CALIB	0x07 /**< Supply Calib Data Reg */
#define XADCPS_CH_ADC_CALIB	0x08 /**< ADC Offset Channel Reg */
#define XADCPS_CH_GAINERR_CALIB 0x09 /**< Gain Error Channel Reg  */
#define XADCPS_CH_VCCPINT	0x0D /**< On-chip PS VCCPINT Channel , Zynq */
#define XADCPS_CH_VCCPAUX	0x0E /**< On-chip PS VCCPAUX Channel , Zynq */
#define XADCPS_CH_VCCPDRO	0x0F /**< On-chip PS VCCPDRO Channel , Zynq */
#define XADCPS_CH_AUX_MIN	 16 /**< Channel number for 1st Aux Channel */
#define XADCPS_CH_AUX_MAX	 31 /**< Channel number for Last Aux channel */

/*@}*/


/**
 * @name Indexes for reading the Calibration Coefficient Data.
 * @{
 */
#define XADCPS_CALIB_SUPPLY_COEFF     0 /**< Supply Offset Calib Coefficient */
#define XADCPS_CALIB_ADC_COEFF        1 /**< ADC Offset Calib Coefficient */
#define XADCPS_CALIB_GAIN_ERROR_COEFF 2 /**< Gain Error Calib Coefficient*/
/*@}*/


/**
 * @name Indexes for reading the Minimum/Maximum Measurement Data.
 * @{
 */
#define XADCPS_MAX_TEMP		0 /**< Maximum Temperature Data */
#define XADCPS_MAX_VCCINT	1 /**< Maximum VCCINT Data */
#define XADCPS_MAX_VCCAUX	2 /**< Maximum VCCAUX Data */
#define XADCPS_MAX_VBRAM	3 /**< Maximum VBRAM Data */
#define XADCPS_MIN_TEMP		4 /**< Minimum Temperature Data */
#define XADCPS_MIN_VCCINT	5 /**< Minimum VCCINT Data */
#define XADCPS_MIN_VCCAUX	6 /**< Minimum VCCAUX Data */
#define XADCPS_MIN_VBRAM	7 /**< Minimum VBRAM Data */
#define XADCPS_MAX_VCCPINT	8 /**< Maximum VCCPINT Register , Zynq */
#define XADCPS_MAX_VCCPAUX	9 /**< Maximum VCCPAUX Register , Zynq */
#define XADCPS_MAX_VCCPDRO	0xA /**< Maximum VCCPDRO Register , Zynq */
#define XADCPS_MIN_VCCPINT	0xC /**< Minimum VCCPINT Register , Zynq */
#define XADCPS_MIN_VCCPAUX	0xD /**< Minimum VCCPAUX Register , Zynq */
#define XADCPS_MIN_VCCPDRO	0xE /**< Minimum VCCPDRO Register , Zynq */

/*@}*/


/**
 * @name Alarm Threshold(Limit) Register (ATR) indexes.
 * @{
 */
#define XADCPS_ATR_TEMP_UPPER	 0 /**< High user Temperature */
#define XADCPS_ATR_VCCINT_UPPER  1 /**< VCCINT high voltage limit register */
#define XADCPS_ATR_VCCAUX_UPPER  2 /**< VCCAUX high voltage limit register */
#define XADCPS_ATR_OT_UPPER	 3 /**< VCCAUX high voltage limit register */
#define XADCPS_ATR_TEMP_LOWER	 4 /**< Upper Over Temperature limit Reg */
#define XADCPS_ATR_VCCINT_LOWER	 5 /**< VCCINT high voltage limit register */
#define XADCPS_ATR_VCCAUX_LOWER	 6 /**< VCCAUX low voltage limit register  */
#define XADCPS_ATR_OT_LOWER	 7 /**< Lower Over Temperature limit */
#define XADCPS_ATR_VBRAM_UPPER_  8 /**< VRBAM Upper Alarm Reg, 7 Series */
#define XADCPS_ATR_VCCPINT_UPPER 9 /**< VCCPINT Upper Alarm Reg, Zynq */
#define XADCPS_ATR_VCCPAUX_UPPER 0xA /**< VCCPAUX Upper Alarm Reg, Zynq */
#define XADCPS_ATR_VCCPDRO_UPPER 0xB /**< VCCPDRO Upper Alarm Reg, Zynq */
#define XADCPS_ATR_VBRAM_LOWER	 0xC /**< VRBAM Lower Alarm Reg, 7 Series */
#define XADCPS_ATR_VCCPINT_LOWER 0xD /**< VCCPINT Lower Alarm Reg , Zynq */
#define XADCPS_ATR_VCCPAUX_LOWER 0xE /**< VCCPAUX Lower Alarm Reg , Zynq */
#define XADCPS_ATR_VCCPDRO_LOWER 0xF /**< VCCPDRO Lower Alarm Reg , Zynq */

/*@}*/


/**
 * @name Averaging to be done for the channels.
 * @{
 */
#define XADCPS_AVG_0_SAMPLES	0  /**< No Averaging */
#define XADCPS_AVG_16_SAMPLES	1  /**< Average 16 samples */
#define XADCPS_AVG_64_SAMPLES	2  /**< Average 64 samples */
#define XADCPS_AVG_256_SAMPLES	3  /**< Average 256 samples */

/*@}*/


/**
 * @name Channel Sequencer Modes of operation
 * @{
 */
#define XADCPS_SEQ_MODE_SAFE		0  /**< Default Safe Mode */
#define XADCPS_SEQ_MODE_ONEPASS		1  /**< Onepass through Sequencer */
#define XADCPS_SEQ_MODE_CONTINPASS	2  /**< Continuous Cycling Sequencer */
#define XADCPS_SEQ_MODE_SINGCHAN	3  /**< Single channel -No Sequencing */
#define XADCPS_SEQ_MODE_SIMUL_SAMPLING	4  /**< Simultaneous sampling */
#define XADCPS_SEQ_MODE_INDEPENDENT	8  /**< Independent mode */

/*@}*/



/**
 * @name Power Down Modes
 * @{
 */
#define XADCPS_PD_MODE_NONE		0  /**< No Power Down  */
#define XADCPS_PD_MODE_ADCB		1  /**< Power Down ADC B */
#define XADCPS_PD_MODE_XADC		2  /**< Power Down ADC A and ADC B */
/*@}*/

/**************************** Type Definitions ******************************/

/**
 * This typedef contains configuration information for the XADC/ADC
 * device.
 */
typedef struct {
	u16  DeviceId;		/**< Unique ID of device */
	u32  BaseAddress;	/**< Device base address */
} XAdcPs_Config;


/**
 * The driver's instance data. The user is required to allocate a variable
 * of this type for every XADC/ADC device in the system. A pointer to
 * a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XAdcPs_Config Config;	/**< XAdcPs_Config of current device */
	u32  IsReady;		/**< Device is initialized and ready  */

} XAdcPs;

/***************** Macros (Inline Functions) Definitions ********************/

/****************************************************************************/
/**
*
* This macro checks if the XADC device is in Event Sampling mode.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return
*		- TRUE if the device is in Event Sampling Mode.
*		- FALSE if the device is in Continuous Sampling Mode.
*
* @note		C-Style signature:
*		int XAdcPs_IsEventSamplingMode(XAdcPs *InstancePtr);
*
*****************************************************************************/
#define XAdcPs_IsEventSamplingModeSet(InstancePtr)			\
	(((XAdcPs_ReadInternalReg(InstancePtr,	 			\
			XADCPS_CFR0_OFFSET) & XADCPS_CFR0_EC_MASK) ?	\
			TRUE : FALSE))


/****************************************************************************/
/**
*
* This macro checks if the XADC device is in External Mux mode.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return
*		- TRUE if the device is in External Mux Mode.
*		- FALSE if the device is NOT in External Mux Mode.
*
* @note		C-Style signature:
*		int XAdcPs_IsExternalMuxMode(XAdcPs *InstancePtr);
*
*****************************************************************************/
#define XAdcPs_IsExternalMuxModeSet(InstancePtr)			\
	(((XAdcPs_ReadInternalReg(InstancePtr,	 			\
			XADCPS_CFR0_OFFSET) & XADCPS_CFR0_MUX_MASK) ?	\
			TRUE : FALSE))

/****************************************************************************/
/**
*
* This macro converts XADC Raw Data to Temperature(centigrades).
*
* @param	AdcData is the Raw ADC Data from XADC.
*
* @return 	The Temperature in centigrades.
*
* @note		C-Style signature:
*		float XAdcPs_RawToTemperature(u32 AdcData);
*
*****************************************************************************/
#define XAdcPs_RawToTemperature(AdcData)				\
	((((float)(AdcData)/65536.0f)/0.00198421639f ) - 273.15f)

/****************************************************************************/
/**
*
* This macro converts XADC/ADC Raw Data to Voltage(volts).
*
* @param	AdcData is the XADC/ADC Raw Data.
*
* @return 	The Voltage in volts.
*
* @note		C-Style signature:
*		float XAdcPs_RawToVoltage(u32 AdcData);
*
*****************************************************************************/
#define XAdcPs_RawToVoltage(AdcData) 					\
	((((float)(AdcData))* (3.0f))/65536.0f)

/****************************************************************************/
/**
*
* This macro converts Temperature in centigrades to XADC/ADC Raw Data.
*
* @param	Temperature is the Temperature in centigrades to be
*		converted to XADC/ADC Raw Data.
*
* @return 	The XADC/ADC Raw Data.
*
* @note		C-Style signature:
*		int XAdcPs_TemperatureToRaw(float Temperature);
*
*****************************************************************************/
#define XAdcPs_TemperatureToRaw(Temperature)				\
	((int)(((Temperature) + 273.15f)*65536.0f*0.00198421639f))

/****************************************************************************/
/**
*
* This macro converts Voltage in Volts to XADC/ADC Raw Data.
*
* @param	Voltage is the Voltage in volts to be converted to
*		XADC/ADC Raw Data.
*
* @return 	The XADC/ADC Raw Data.
*
* @note		C-Style signature:
*		int XAdcPs_VoltageToRaw(float Voltage);
*
*****************************************************************************/
#define XAdcPs_VoltageToRaw(Voltage)			 		\
	((int)((Voltage)*65536.0f/3.0f))


/****************************************************************************/
/**
*
* This macro is used for writing to the XADC Registers using the
* command FIFO.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	None.
*
* @note		C-Style signature:
*		void XAdcPs_WriteFifo(XAdcPs *InstancePtr, u32 Data);
*
*****************************************************************************/
#define XAdcPs_WriteFifo(InstancePtr, Data)				\
	XAdcPs_WriteReg((InstancePtr)->Config.BaseAddress,		\
			  XADCPS_CMDFIFO_OFFSET, Data);


/****************************************************************************/
/**
*
* This macro is used for reading from the XADC Registers using the
* data FIFO.
*
* @param	InstancePtr is a pointer to the XAdcPs instance.
*
* @return	Data read from the FIFO
*
* @note		C-Style signature:
*		u32 XAdcPs_ReadFifo(XAdcPs *InstancePtr);
*
*****************************************************************************/
#define XAdcPs_ReadFifo(InstancePtr)				\
	XAdcPs_ReadReg((InstancePtr)->Config.BaseAddress,	\
			  XADCPS_RDFIFO_OFFSET);


/************************** Function Prototypes *****************************/



/**
 * Functions in xadcps_sinit.c
 */
XAdcPs_Config *XAdcPs_LookupConfig(u16 DeviceId);

/**
 * Functions in xadcps.c
 */
int XAdcPs_CfgInitialize(XAdcPs *InstancePtr,
				XAdcPs_Config *ConfigPtr,
				u32 EffectiveAddr);


u32 XAdcPs_GetStatus(XAdcPs *InstancePtr);

u32 XAdcPs_GetAlarmOutputStatus(XAdcPs *InstancePtr);

void XAdcPs_StartAdcConversion(XAdcPs *InstancePtr);

void XAdcPs_Reset(XAdcPs *InstancePtr);

u16 XAdcPs_GetAdcData(XAdcPs *InstancePtr, u8 Channel);

u16 XAdcPs_GetCalibCoefficient(XAdcPs *InstancePtr, u8 CoeffType);

u16 XAdcPs_GetMinMaxMeasurement(XAdcPs *InstancePtr, u8 MeasurementType);

void XAdcPs_SetAvg(XAdcPs *InstancePtr, u8 Average);
u8 XAdcPs_GetAvg(XAdcPs *InstancePtr);

int XAdcPs_SetSingleChParams(XAdcPs *InstancePtr,
				u8 Channel,
				int IncreaseAcqCycles,
				int IsEventMode,
				int IsDifferentialMode);


void XAdcPs_SetAlarmEnables(XAdcPs *InstancePtr, u16 AlmEnableMask);
u16 XAdcPs_GetAlarmEnables(XAdcPs *InstancePtr);

void XAdcPs_SetCalibEnables(XAdcPs *InstancePtr, u16 Calibration);
u16 XAdcPs_GetCalibEnables(XAdcPs *InstancePtr);

void XAdcPs_SetSequencerMode(XAdcPs *InstancePtr, u8 SequencerMode);
u8 XAdcPs_GetSequencerMode(XAdcPs *InstancePtr);

void XAdcPs_SetAdcClkDivisor(XAdcPs *InstancePtr, u8 Divisor);
u8 XAdcPs_GetAdcClkDivisor(XAdcPs *InstancePtr);

int XAdcPs_SetSeqChEnables(XAdcPs *InstancePtr, u32 ChEnableMask);
u32 XAdcPs_GetSeqChEnables(XAdcPs *InstancePtr);

int XAdcPs_SetSeqAvgEnables(XAdcPs *InstancePtr, u32 AvgEnableChMask);
u32 XAdcPs_GetSeqAvgEnables(XAdcPs *InstancePtr);

int XAdcPs_SetSeqInputMode(XAdcPs *InstancePtr, u32 InputModeChMask);
u32 XAdcPs_GetSeqInputMode(XAdcPs *InstancePtr);

int XAdcPs_SetSeqAcqTime(XAdcPs *InstancePtr, u32 AcqCyclesChMask);
u32 XAdcPs_GetSeqAcqTime(XAdcPs *InstancePtr);

void XAdcPs_SetAlarmThreshold(XAdcPs *InstancePtr, u8 AlarmThrReg, u16 Value);
u16 XAdcPs_GetAlarmThreshold(XAdcPs *InstancePtr, u8 AlarmThrReg);

void XAdcPs_EnableUserOverTemp(XAdcPs *InstancePtr);
void XAdcPs_DisableUserOverTemp(XAdcPs *InstancePtr);

void XAdcPs_SetSequencerEvent(XAdcPs *InstancePtr, int IsEventMode);

int XAdcPs_GetSamplingMode(XAdcPs *InstancePtr);

void XAdcPs_SetMuxMode(XAdcPs *InstancePtr, int MuxMode, u8 Channel);

void XAdcPs_SetPowerdownMode(XAdcPs *InstancePtr, u32 Mode);

u32 XAdcPs_GetPowerdownMode(XAdcPs *InstancePtr);

/**
 * Functions in xadcps_selftest.c
 */
int XAdcPs_SelfTest(XAdcPs *InstancePtr);

/**
 * Functions in xadcps_intr.c
 */
void XAdcPs_IntrEnable(XAdcPs *InstancePtr, u32 Mask);
void XAdcPs_IntrDisable(XAdcPs *InstancePtr, u32 Mask);
u32 XAdcPs_IntrGetEnabled(XAdcPs *InstancePtr);

u32 XAdcPs_IntrGetStatus(XAdcPs *InstancePtr);
void XAdcPs_IntrClear(XAdcPs *InstancePtr, u32 Mask);


#ifdef __cplusplus
}
#endif

#endif  /* End of protection macro. */
/** @} */
