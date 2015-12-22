/******************************************************************************
*
* Copyright (C) 2012 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xaxipmon.c
*
* This file contains the driver API functions that can be used to access
* the AXI Performance Monitor device.
*
* Refer to the xaxipmon.h header file for more information about this driver.
*
* @note 	None.
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.00a bss   02/27/12  First release
* 2.00a bss   06/23/12  Updated to support v2_00a version of IP.
* 3.00a bss   09/03/12  Deleted XAxiPmon_SetAgent, XAxiPmon_GetAgent APIs and
*			modified XAxiPmon_SetMetrics, XAxiPmon_GetMetrics APIs
*			to support v2_01a version of IP.
* 3.01a bss   10/25/12  Added XAxiPmon_StartCounters and XAxiPmon_StopCounters
*			APIs (CR #683799).
*			Added XAxiPmon_StartEventLog and XAxiPmon_StopEventLog
*			APIs (CR #683801).
*			Added XAxiPmon_GetMetricName API (CR #683803).
*			Modified XAxiPmon_SetMetrics and XAxiPmon_GetMetrics
*			(CR #683746)
*			Added XAxiPmon_EnableEventLog,
*			XAxiPmon_DisableMetricsCounter,
*			XAxiPmon_EnableMetricsCounter APIs to replace macros.
*			Added XAxiPmon_SetMetricCounterCutOff,
*			XAxiPmon_GetMetricCounterCutOff,
*			XAxiPmon_EnableExternalTrigger and
*			XAxiPmon_DisableExternalTrigger APIs to support new
*			version of IP.
* 4.00a bss   01/17/13  To support new version of IP:
* 			Added XAxiPmon_SetLogEnableRanges,
*	  		XAxiPmon_GetLogEnableRanges,
*			XAxiPmon_EnableMetricCounterTrigger,
*			XAxiPmon_DisableMetricCounterTrigger,
*			XAxiPmon_EnableEventLogTrigger,
*			XAxiPmon_DisableEventLogTrigger,
*			XAxiPmon_SetWriteLatencyId,
*			XAxiPmon_SetReadLatencyId,
*			XAxiPmon_GetWriteLatencyId,
*			XAxiPmon_GetReadLatencyId APIs and removed
*			XAxiPmon_SetMetricCounterCutOff,
*			XAxiPmon_GetMetricCounterCutOff,
*			XAxiPmon_EnableExternalTrigger and
*			XAxiPmon_DisableExternalTrigger APIs
* 5.00a bss   08/26/13  To support new version of IP:
*			Modified XAxiPmon_CfgInitialize to add Mode of APM and
*			ScaleFactor parameter.
*			Modified Assert functions depending on Mode.
*			Modified XAxiPmon_GetMetricCounter and
*			XAxiPmon_GetSampledMetricCounter to include
*			new Counters.
*			Modified XAxiPmon_SetSampleInterval and
*			XAxiPmon_GetSampleInterval to remove higher 32 bit
*			value of SampleInterval since Sample Interval Register
*			is only 32 bit.
*			Added XAxiPmon_SetWrLatencyStart,
*			XAxiPmon_SetWrLatencyEnd, XAxiPmon_SetRdLatencyStart
*			XAxiPmon_SetRdLatencyEnd, XAxiPmon_GetWrLatencyStart,
*			XAxiPmon_GetWrLatencyEnd, XAxiPmon_GetRdLatencyStart,
*			XAxiPmon_GetRdLatencyEnd, XAxiPmon_SetWriteIdMask,
*			XAxiPmon_SetReadIdMask,
*			XAxiPmon_GetWriteIdMask and
*			XAxiPmon_GetReadIdMask APIs.
*			Renamed:
*			XAxiPmon_SetWriteLatencyId to XAxiPmon_SetWriteId
*			XAxiPmon_SetReadLatencyId to XAxiPmon_SetReadId
*			XAxiPmon_GetWriteLatencyId to XAxiPmon_GetWriteId
*			XAxiPmon_SetReadLatencyId to XAxiPmon_GetReadId.
* 6.2   bss  04/21/14   Updated XAxiPmon_CfgInitialize to Reset counters
*			and FIFOs based on Modes(CR#782671). And if both
*			profile and trace modes are present set mode as
*			Advanced.
* 6.2	bss  03/02/15	Updated XAxiPmon_SetWriteId, XAxiPmon_SetReadId,
*						XAxiPmon_GetWriteId, XAxiPmon_GetReadId
*						XAxiPmon_SetWriteIdMask, XAxiPmon_SetReadIdMask,
*						XAxiPmon_GetWriteIdMask, XAxiPmon_GetReadIdMask
*						functions to support Zynq MP APM.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xaxipmon.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/*****************************************************************************/
/**
*
* This function initializes a specific XAxiPmon device/instance. This function
* must be called prior to using the AXI Performance Monitor device.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	ConfigPtr points to the XAxiPmon device configuration structure.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. If the address translation is not used then the
*		physical address is passed.
*		Unexpected errors may occur if the address mapping is changed
*		after this function is invoked.
*
* @return
*		- XST_SUCCESS if successful.
*
* @note		The user needs to first call the XAxiPmon_LookupConfig() API
*		which returns the Configuration structure pointer which is
*		passed as a parameter to the XAxiPmon_CfgInitialize() API.
*
******************************************************************************/
int XAxiPmon_CfgInitialize(XAxiPmon *InstancePtr, XAxiPmon_Config *ConfigPtr,
						u32 EffectiveAddr)
{
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
	InstancePtr->Config.GlobalClkCounterWidth =
				ConfigPtr->GlobalClkCounterWidth;
	InstancePtr->Config.MetricSampleCounterWidth =
				ConfigPtr->MetricSampleCounterWidth;
	InstancePtr->Config.IsEventCount =
				ConfigPtr->IsEventCount;
	InstancePtr->Config.NumberofSlots =
				ConfigPtr->NumberofSlots;
	InstancePtr->Config.NumberofCounters =
				ConfigPtr->NumberofCounters;
	InstancePtr->Config.HaveSampledCounters =
				ConfigPtr->HaveSampledCounters;
	InstancePtr->Config.IsEventLog =
				ConfigPtr->IsEventLog;
	InstancePtr->Config.FifoDepth =
				ConfigPtr->FifoDepth;
	InstancePtr->Config.FifoWidth =
				ConfigPtr->FifoWidth;
	InstancePtr->Config.TidWidth =
				ConfigPtr->TidWidth;
	InstancePtr->Config.Is32BitFiltering = ConfigPtr->Is32BitFiltering;

	InstancePtr->Config.ScaleFactor = ConfigPtr->ScaleFactor;

	if ((ConfigPtr->ModeProfile == ConfigPtr->ModeTrace)
			|| ConfigPtr->ModeAdvanced == 1)
	{
		InstancePtr->Mode = XAPM_MODE_ADVANCED;
	} else if (ConfigPtr->ModeTrace == 1) {
		InstancePtr->Mode = XAPM_MODE_TRACE;
	} else {
		InstancePtr->Mode = XAPM_MODE_PROFILE;
	}

	/*
	 * Indicate the instance is now ready to use, initialized without error.
	 */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	/*
	 * Reset the Counters and FIFO based on Modes.
	 */

	/* Advanced and Profile */
	if(InstancePtr->Mode == XAPM_MODE_ADVANCED ||
			InstancePtr->Mode == XAPM_MODE_PROFILE)
	{
		XAxiPmon_ResetMetricCounter(InstancePtr);
	}
	/* Advanced */
	if(InstancePtr->Mode == XAPM_MODE_ADVANCED)
	{
		XAxiPmon_ResetGlobalClkCounter(InstancePtr);
	}
	/* Advanced and Trace */
	if(InstancePtr->Mode == XAPM_MODE_ADVANCED ||
			InstancePtr->Mode == XAPM_MODE_TRACE)
	{
		XAxiPmon_ResetFifo(InstancePtr);
	}
	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function resets all Metric Counters and Sampled Metric Counters of
* AXI Performance Monitor.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	XST_SUCCESS
*
*
* @note		None.
*
******************************************************************************/
int XAxiPmon_ResetMetricCounter(XAxiPmon *InstancePtr)
{

	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode != XAPM_MODE_TRACE);

	/*
	 * Write the reset value to the Control register to reset
	 * Metric counters
	 */
	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							 XAPM_CTL_OFFSET);
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
					(RegValue | XAPM_CR_MCNTR_RESET_MASK));
	/*
	 * Release from Reset
	 */
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
				(RegValue & ~(XAPM_CR_MCNTR_RESET_MASK)));
	return XST_SUCCESS;

}

/*****************************************************************************/
/**
*
* This function resets Global Clock Counter of AXI Performance Monitor
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XAxiPmon_ResetGlobalClkCounter(XAxiPmon *InstancePtr)
{

	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode == XAPM_MODE_ADVANCED);

	/*
	 * Write the reset value to the Control register to reset
	 * Global Clock Counter
	 */
	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							 XAPM_CTL_OFFSET);
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
					(RegValue | XAPM_CR_GCC_RESET_MASK));

	/*
	 * Release from Reset
	 */
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
				(RegValue & ~(XAPM_CR_GCC_RESET_MASK)));

}

/*****************************************************************************/
/**
*
* This function resets Streaming FIFO of AXI Performance Monitor
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	XST_SUCCESS
*
* @note		None.
*
******************************************************************************/
int XAxiPmon_ResetFifo(XAxiPmon *InstancePtr)
{

	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode != XAPM_MODE_PROFILE);

	/* Check Event Logging is enabled in Hardware */
	if((InstancePtr->Config.IsEventLog == 0) &&
			(InstancePtr->Mode == XAPM_MODE_ADVANCED))
	{
		/*Event logging not enabled in Hardware*/
		return XST_SUCCESS;
	}
	/*
	 * Write the reset value to the Control register to reset
	 * FIFO
	 */
	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							 XAPM_CTL_OFFSET);
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
					(RegValue | XAPM_CR_FIFO_RESET_MASK));
	/*
	 * Release from Reset
	 */
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
				(RegValue & ~(XAPM_CR_FIFO_RESET_MASK)));

	return XST_SUCCESS;

}

/****************************************************************************/
/**
*
* This function sets Ranges for Incrementers depending on parameters passed.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	IncrementerNum specifies the Incrementer for which Ranges
*		need to be set
* @param 	RangeUpper specifies the Upper limit in 32 bit Register
* @param 	RangeLower specifies the Lower limit in 32 bit Register
*
* @return	None.
*
* @note		None
*
*****************************************************************************/
void XAxiPmon_SetIncrementerRange(XAxiPmon *InstancePtr, u8 IncrementerNum,
					u16 RangeUpper,	u16 RangeLower)
 {

	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode == XAPM_MODE_ADVANCED);
	Xil_AssertVoid(IncrementerNum < XAPM_MAX_COUNTERS);

	/*
	 * Write to the specified Range register
	 */
	RegValue = RangeUpper << 16;
	RegValue |= RangeLower;
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
			(XAPM_RANGE0_OFFSET + (IncrementerNum * 16)),
			RegValue);
 }

/****************************************************************************/
/**
*
* This function returns the Ranges of Incrementers Registers.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	IncrementerNum specifies the Incrementer for which Ranges
*		need to be returned.
* @param 	RangeUpper specifies the user reference variable which returns
*		the Upper Range Value of the specified Incrementer.
* @param 	RangeLower specifies the user reference variable which returns
*		the Lower Range Value of the specified Incrementer.
*
* @return	None.
*
* @note		None
*
*****************************************************************************/
void XAxiPmon_GetIncrementerRange(XAxiPmon *InstancePtr, u8 IncrementerNum,
				u16 *RangeUpper, u16 *RangeLower)
 {

	u32 RegValue;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode == XAPM_MODE_ADVANCED);
	Xil_AssertVoid(IncrementerNum < XAPM_MAX_COUNTERS);

	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
				(XAPM_RANGE0_OFFSET + (IncrementerNum * 16)));

	*RangeLower = RegValue & 0xFFFF;
	*RangeUpper = (RegValue >> 16) & 0xFFFF;
 }

/****************************************************************************/
/**
*
* This function sets the Sample Interval Register
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	SampleInterval is the Sample Interval value to be set
*
* @return	None
*
* @note		None.
*
*****************************************************************************/
void XAxiPmon_SetSampleInterval(XAxiPmon *InstancePtr, u32 SampleInterval)
{

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode != XAPM_MODE_TRACE);

	/*
	 * Set Sample Interval Lower
	 */
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
		XAPM_SI_LOW_OFFSET, SampleInterval);

}

/****************************************************************************/
/**
*
* This function returns the contents of Sample Interval Register
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	SampleInterval is a pointer where the Sample Interval
*		Counter value is returned.
*
* @return 	None.
*
* @note		None.
*
******************************************************************************/
void XAxiPmon_GetSampleInterval(XAxiPmon *InstancePtr, u32 *SampleInterval)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode != XAPM_MODE_TRACE);

	/*
	 * Set Sample Interval Lower
	 */
	*SampleInterval = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
				XAPM_SI_LOW_OFFSET);

}

/****************************************************************************/
/**
*
* This function sets Metrics for specified Counter in the corresponding
* Metric Selector Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	Slot is the slot ID for which specified counter has to
*		be connected.
* @param	Metrics is one of the Metric Sets. User has to use
*		XAPM_METRIC_SET_* macros in xaxipmon.h for this parameter
* @param	CounterNum is the Counter Number.
*		The valid values are 0 to 9.
*
* @return	XST_SUCCESS if Success
*		XST_FAILURE if Failure
*
* @note		None.
*
*****************************************************************************/
int XAxiPmon_SetMetrics(XAxiPmon *InstancePtr, u8 Slot, u8 Metrics,
						u8 CounterNum)
{
	u32 RegValue;
	u32 Mask;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode == XAPM_MODE_ADVANCED);
	Xil_AssertNonvoid(Slot < XAPM_MAX_AGENTS);
	Xil_AssertNonvoid((Metrics <= XAPM_METRIC_SET_22) ||
			(Metrics == XAPM_METRIC_SET_30));
	Xil_AssertNonvoid(CounterNum < XAPM_MAX_COUNTERS);

	/* Find Mask value to force zero in counternum byte range */
	if (CounterNum == 0 || CounterNum == 4 || CounterNum == 8) {
		Mask = 0xFFFFFF00;
	}
	else if (CounterNum == 1 || CounterNum == 5 || CounterNum == 9) {
		Mask = 0xFFFF00FF;
	}
	else if (CounterNum == 2 || CounterNum == 6) {
		Mask = 0xFF00FFFF;
	}
	else {
		Mask = 0x00FFFFFF;
	}

	if(CounterNum <= 3) {
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
					    XAPM_MSR0_OFFSET);

		RegValue = RegValue & Mask;
		RegValue = RegValue | (Metrics << (CounterNum * 8));
		RegValue = RegValue | (Slot << (CounterNum * 8 + 5));
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
					XAPM_MSR0_OFFSET,RegValue);
	}
	else if((CounterNum >= 4) && (CounterNum <= 7)) {
		CounterNum = CounterNum - 4;
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
					    XAPM_MSR1_OFFSET);

		RegValue = RegValue & Mask;
		RegValue = RegValue | (Metrics << (CounterNum * 8));
		RegValue = RegValue | (Slot << (CounterNum * 8 + 5));
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
					XAPM_MSR1_OFFSET,RegValue);
	}
	else {
		CounterNum = CounterNum - 8;
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
					    XAPM_MSR2_OFFSET);

		RegValue = RegValue & Mask;
		RegValue = RegValue | (Metrics << (CounterNum * 8));
		RegValue = RegValue | (Slot << (CounterNum * 8 + 5));
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
					XAPM_MSR2_OFFSET,RegValue);
	}
	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function returns Metrics in the specified Counter from the corresponding
* Metric Selector Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	CounterNum is the Counter Number.
*		The valid values are 0 to 9.
* @param	Metrics is a reference parameter from application where metrics
*		of specified counter is filled.
* @praram	Slot is a reference parameter in which slot Id of
*		specified counter is filled
* @return	XST_SUCCESS if Success
*		XST_FAILURE if Failure
*
* @note		None.
*
*****************************************************************************/
int XAxiPmon_GetMetrics(XAxiPmon *InstancePtr, u8 CounterNum, u8 *Metrics,
								u8 *Slot)
{
	u32 RegValue;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode == XAPM_MODE_ADVANCED);
	Xil_AssertNonvoid(CounterNum <= XAPM_MAX_COUNTERS);

	if(CounterNum <= 3) {
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
					XAPM_MSR0_OFFSET);
		*Metrics = (RegValue >> (CounterNum * 8)) & 0x1F;
		*Slot 	= (RegValue >> (CounterNum * 8 + 5)) & 0x7;

	}
	else if((CounterNum >= 4) && (CounterNum <= 7)) {
		CounterNum = CounterNum - 4;
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
					XAPM_MSR1_OFFSET);
		*Metrics = (RegValue >> (CounterNum * 8)) & 0x1F;
		*Slot 	= (RegValue >> (CounterNum * 8 + 5)) & 0x7;
	}
	else {
		CounterNum = CounterNum - 8;
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
					XAPM_MSR2_OFFSET);
		*Metrics = (RegValue >> (CounterNum * 8)) & 0x1F;
		*Slot 	= (RegValue >> (CounterNum * 8 + 5)) & 0x7;
	}
	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* This function returns the contents of the Global Clock Counter Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	CntHighValue is the user space pointer with which upper 32 bits
*		of Global Clock Counter has to be filled
* @param	CntLowValue is the user space pointer with which lower 32 bits
*		of Global Clock Counter has to be filled
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAxiPmon_GetGlobalClkCounter(XAxiPmon *InstancePtr,u32 *CntHighValue,
							u32 *CntLowValue)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode == XAPM_MODE_ADVANCED);

	*CntHighValue = 0x0;
	*CntLowValue  = 0x0;

	/*
	 * If Counter width is 64 bit then Counter Value has to be
	 * filled at CntHighValue address also.
	 */
	if(InstancePtr->Config.GlobalClkCounterWidth == 64) {

		/* Bits[63:32] exists at XAPM_GCC_HIGH_OFFSET */
		*CntHighValue = XAxiPmon_ReadReg(InstancePtr->
				Config.BaseAddress, XAPM_GCC_HIGH_OFFSET);
	}
	/* Bits[31:0] exists at XAPM_GCC_LOW_OFFSET */
	*CntLowValue = XAxiPmon_ReadReg(InstancePtr->
				Config.BaseAddress, XAPM_GCC_LOW_OFFSET);
}

/****************************************************************************/
/**
*
* This function returns the contents of the Metric Counter Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	CounterNum is the number of the Metric Counter to be read.
*		Use the XAPM_METRIC_COUNTER* defines for the counter number in
*		xaxipmon.h. The valid values are 0 (XAPM_METRIC_COUNTER_0) to
*		47(XAPM_METRIC_COUNTER_47).
* @return	RegValue is the content of specified Metric Counter.
*
* @note		None.
*
*****************************************************************************/
u32 XAxiPmon_GetMetricCounter(XAxiPmon *InstancePtr, u32 CounterNum)
{

	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode != XAPM_MODE_TRACE);
	Xil_AssertNonvoid(CounterNum < XAPM_MAX_COUNTERS_PROFILE);

	if (CounterNum < 10 ) {
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_MC0_OFFSET + (CounterNum * 16)));
	}
	else if (CounterNum >= 10 && CounterNum < 12) {
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_MC10_OFFSET + ((CounterNum - 10) * 16)));
	}
	else if (CounterNum >= 12 && CounterNum < 24) {
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_MC12_OFFSET + ((CounterNum - 12) * 16)));
	}
	else if (CounterNum >= 24 && CounterNum < 36) {
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_MC24_OFFSET + ((CounterNum - 24) * 16)));
	}
	else
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_MC36_OFFSET + ((CounterNum - 36) * 16)));

	return RegValue;
}

/****************************************************************************/
/**
*
* This function returns the contents of the Sampled Metric Counter Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	CounterNum is the number of the Sampled Metric Counter to read.
*		Use the XAPM_METRIC_COUNTER* defines for the counter number in
*		xaxipmon.h. The valid values are 0 (XAPM_METRIC_COUNTER_0) to
*		47(XAPM_METRIC_COUNTER_47).
*
* @return	RegValue is the content of specified Sampled Metric Counter.
*
* @note		None.
*
*****************************************************************************/
u32 XAxiPmon_GetSampledMetricCounter(XAxiPmon *InstancePtr, u32 CounterNum)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode != XAPM_MODE_TRACE);
	Xil_AssertNonvoid(CounterNum < XAPM_MAX_COUNTERS_PROFILE);
	Xil_AssertNonvoid(InstancePtr->Mode == XAPM_MODE_PROFILE ||
		((InstancePtr->Mode == XAPM_MODE_ADVANCED) &&
			(InstancePtr->Config.HaveSampledCounters == 1)));

	if (CounterNum < 10 ) {
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_SMC0_OFFSET + (CounterNum * 16)));
	}
	else if (CounterNum >= 10 && CounterNum < 12) {
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_SMC10_OFFSET + ((CounterNum - 10) * 16)));
	}
	else if (CounterNum >= 12 && CounterNum < 24) {
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_SMC12_OFFSET + ((CounterNum - 12) * 16)));
	}
	else if (CounterNum >= 24 && CounterNum < 36) {
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_SMC24_OFFSET + ((CounterNum - 24) * 16)));
	}
	else
		RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_SMC36_OFFSET + ((CounterNum - 36) * 16)));

	return RegValue;
}

/****************************************************************************/
/**
*
* This function returns the contents of the Incrementer Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	IncrementerNum is the number of the Incrementer register to
*		read.Use the XAPM_INCREMENTER_* defines for the Incrementer
*		number.The valid values are 0 (XAPM_INCREMENTER_0) to
*		9 (XAPM_INCREMENTER_9).
* @param	IncrementerNum is the number of the specified Incrementer
*		register
* @return	RegValue is content of specified Metric Incrementer register.
*
* @note		None.
*
*****************************************************************************/
u32 XAxiPmon_GetIncrementer(XAxiPmon *InstancePtr, u32 IncrementerNum)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode == XAPM_MODE_ADVANCED &&
				InstancePtr->Config.IsEventCount == 1);
	Xil_AssertNonvoid(IncrementerNum < XAPM_MAX_COUNTERS);

	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
			(XAPM_INC0_OFFSET + (IncrementerNum * 16)));

	return RegValue;
}

/****************************************************************************/
/**
*
* This function returns the contents of the Sampled Incrementer Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	IncrementerNum is the number of the Sampled Incrementer
*		register to read.Use the XAPM_INCREMENTER_* defines for the
*		Incrementer number.The valid values are 0 (XAPM_INCREMENTER_0)
*		to 9 (XAPM_INCREMENTER_9).
* @param	IncrementerNum is the number of the specified Sampled
*		Incrementer register
* @return	RegValue is content of specified Sampled Incrementer register.
*
* @note		None.
*
*****************************************************************************/
u32 XAxiPmon_GetSampledIncrementer(XAxiPmon *InstancePtr, u32 IncrementerNum)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode == XAPM_MODE_ADVANCED &&
				InstancePtr->Config.IsEventCount == 1 &&
				InstancePtr->Config.HaveSampledCounters == 1);
	Xil_AssertNonvoid(IncrementerNum < XAPM_MAX_COUNTERS);

	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
				(XAPM_SINC0_OFFSET + (IncrementerNum * 16)));
	return RegValue;
}

/****************************************************************************/
/**
*
* This function sets Software-written Data Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	SwData is the Software written Data.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XAxiPmon_SetSwDataReg(XAxiPmon *InstancePtr, u32 SwData)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Set Software-written Data Register
	 */
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_SWD_OFFSET,
								SwData);
}

/****************************************************************************/
/**
*
* This function returns contents of Software-written Data Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	SwData.
*
* @note		None.
*
*****************************************************************************/
u32 XAxiPmon_GetSwDataReg(XAxiPmon *InstancePtr)
{
	 u32 SwData;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Set Metric Selector Register
	 */
	SwData = (u32)XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
						XAPM_SWD_OFFSET);
	return SwData;
}

/*****************************************************************************/
/**
*
* This function enables the following in the AXI Performance Monitor:
*   - Event logging
*
* @param        InstancePtr is a pointer to the XAxiPmon instance.
* @param        FlagEnables is a value to write to the flag enables
*               register defined by XAPM_FEC_OFFSET. It is recommended
*               to use the XAPM_FEC_*_MASK mask bits to generate.
*               A value of 0x0 will disable all events to the event
*               log streaming FIFO.
*
* @return       XST_SUCCESS
*
* @note         None
*
******************************************************************************/
int XAxiPmon_StartEventLog(XAxiPmon *InstancePtr, u32 FlagEnables)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode == XAPM_MODE_TRACE ||
				((InstancePtr->Mode == XAPM_MODE_ADVANCED) &&
			(InstancePtr->Config.IsEventLog == 1)));

	/* Read current register value */
	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	/* Flag Enable register is present only in Advanced Mode */
	if(InstancePtr->Mode == XAPM_MODE_ADVANCED)
	{
		/* Now write to flag enables register */
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
				XAPM_FEC_OFFSET, FlagEnables);
	}

	/* Write the new value to the Control register to
	 *	enable event logging */
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
		                  RegValue | XAPM_CR_EVENTLOG_ENABLE_MASK);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function disables the following in the AXI Performance Monitor:
*   - Event logging
*
* @param        InstancePtr is a pointer to the XAxiPmon instance.
*
* @return       XST_SUCCESS
*
* @note         None
*
******************************************************************************/
int XAxiPmon_StopEventLog(XAxiPmon *InstancePtr)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode == XAPM_MODE_TRACE ||
			((InstancePtr->Mode == XAPM_MODE_ADVANCED) &&
			(InstancePtr->Config.IsEventLog == 1)));

	/* Read current register value */
	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
						XAPM_CTL_OFFSET);

	/* Write the new value to the Control register to disable
	 * event logging */
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
	                    RegValue & ~XAPM_CR_EVENTLOG_ENABLE_MASK);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function enables the following in the AXI Performance Monitor:
*   - Global clock counter
*   - All metric counters
*   - All sampled metric counters
*
* @param    InstancePtr is a pointer to the XAxiPmon instance.
*           SampleInterval is the sample interval for the sampled metric
*           counters
*
* @return   XST_SUCCESS
*
* @note	    None
******************************************************************************/
int XAxiPmon_StartCounters(XAxiPmon *InstancePtr, u32 SampleInterval)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode == XAPM_MODE_PROFILE ||
				((InstancePtr->Mode == XAPM_MODE_ADVANCED) &&
				(InstancePtr->Config.IsEventCount == 1)));

	/* Read current register value */
	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	/* Globlal Clock Counter is present in Advanced mode only */
	if(InstancePtr->Mode == XAPM_MODE_ADVANCED)
	{
		RegValue = RegValue | XAPM_CR_GCC_ENABLE_MASK;
	}

	/*
	 * Write the new value to the Control register to enable
	 * global clock counter and metric counters
	 */
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
              RegValue | XAPM_CR_MCNTR_ENABLE_MASK);

	/* Set, enable, and load sampled counters */
	XAxiPmon_SetSampleInterval(InstancePtr, SampleInterval);
	XAxiPmon_LoadSampleIntervalCounter(InstancePtr);
	XAxiPmon_EnableSampleIntervalCounter(InstancePtr);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function disables the following in the AXI Performance Monitor:
*   - Global clock counter
*   - All metric counters
*
* @param        InstancePtr is a pointer to the XAxiPmon instance.
*
* @return       XST_SUCCESS
*
* @note         None
*
******************************************************************************/
int XAxiPmon_StopCounters(XAxiPmon *InstancePtr)
{
	u32 RegValue;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(InstancePtr->Mode == XAPM_MODE_PROFILE ||
				((InstancePtr->Mode == XAPM_MODE_ADVANCED) &&
				(InstancePtr->Config.IsEventCount == 1)));

	/* Read current register value */
	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	/* Globlal Clock Counter is present in Advanced mode only */
	if(InstancePtr->Mode == XAPM_MODE_ADVANCED)
	{
		RegValue = RegValue & ~XAPM_CR_GCC_ENABLE_MASK;
	}

	/*
	 * Write the new value to the Control register to disable
	 * global clock counter and metric counters
	 */
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
	RegValue & ~XAPM_CR_MCNTR_ENABLE_MASK);

	return XST_SUCCESS;
}

/*****************************************************************************/
/**
*
* This function enables Metric Counters.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		None
*
*******************************************************************************/
void XAxiPmon_EnableMetricsCounter(XAxiPmon *InstancePtr)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode == XAPM_MODE_PROFILE ||
				((InstancePtr->Mode == XAPM_MODE_ADVANCED) &&
				(InstancePtr->Config.IsEventCount == 1)));

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
						XAPM_CTL_OFFSET);
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
					RegVal | XAPM_CR_MCNTR_ENABLE_MASK);
}
/****************************************************************************/
/**
*
* This function disables the Metric Counters.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		None
*
*****************************************************************************/
void XAxiPmon_DisableMetricsCounter(XAxiPmon *InstancePtr)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode == XAPM_MODE_PROFILE ||
				((InstancePtr->Mode == XAPM_MODE_ADVANCED) &&
				(InstancePtr->Config.IsEventCount == 1)));

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);

	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
					RegVal & ~(XAPM_CR_MCNTR_ENABLE_MASK));
}

/****************************************************************************/
/**
*
* This function sets the Upper and Lower Ranges for specified Metric Counter
* Log Enable Register.Event Logging starts when corresponding Metric Counter
* value falls in between these ranges
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	CounterNum is the Metric Counter number for which
*		Ranges are to be assigned.Use the XAPM_METRIC_COUNTER*
*		defines for the counter number in xaxipmon.h.
*		The valid values are 0 (XAPM_METRIC_COUNTER_0) to
*		9 (XAPM_METRIC_COUNTER_9).
* @param 	RangeUpper specifies the Upper limit in 32 bit Register
* @param 	RangeLower specifies the Lower limit in 32 bit Register
* @return	None
*
* @note		None.
*
*****************************************************************************/
void XAxiPmon_SetLogEnableRanges(XAxiPmon *InstancePtr, u32 CounterNum,
					u16 RangeUpper, u16 RangeLower)
{
	u32 RegValue;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(CounterNum < XAPM_MAX_COUNTERS);
	Xil_AssertVoid((InstancePtr->Mode == XAPM_MODE_ADVANCED) &&
				(InstancePtr->Config.IsEventCount == 1));


	/*
	 * Write the specified Ranges to corresponding Metric Counter Log
	 * Enable Register
	 */
	RegValue = RangeUpper << 16;
	RegValue |= RangeLower;
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
		(XAPM_MC0LOGEN_OFFSET + (CounterNum * 16)), RegValue);

}

/****************************************************************************/
/**
*
* This function returns the Ranges of specified Metric Counter Log
* Enable Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	CounterNum is the Metric Counter number for which
*		Ranges are to be returned.Use the XAPM_METRIC_COUNTER*
*		defines for the counter number in xaxipmon.h.
*		The valid values are 0 (XAPM_METRIC_COUNTER_0) to
*		9 (XAPM_METRIC_COUNTER_9).
*
* @param 	RangeUpper specifies the user reference variable which returns
*		the Upper Range Value of the specified Metric Counter
*		Log Enable Register.
* @param 	RangeLower specifies the user reference variable which returns
*		the Lower Range Value of the specified Metric Counter
*		Log Enable Register.
*
* @note		None.
*
*****************************************************************************/
void XAxiPmon_GetLogEnableRanges(XAxiPmon *InstancePtr, u32 CounterNum,
					u16 *RangeUpper, u16 *RangeLower)
{
	u32 RegValue;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(CounterNum < XAPM_MAX_COUNTERS);
	Xil_AssertVoid((InstancePtr->Mode == XAPM_MODE_ADVANCED) &&
				(InstancePtr->Config.IsEventCount == 1));


	RegValue = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
				(XAPM_MC0LOGEN_OFFSET + (CounterNum * 16)));

	*RangeLower = RegValue & 0xFFFF;
	*RangeUpper = (RegValue >> 16) & 0xFFFF;
}

/*****************************************************************************/
/**
*
* This function enables Event Logging.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		None
*
*******************************************************************************/
void XAxiPmon_EnableEventLog(XAxiPmon *InstancePtr)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode == XAPM_MODE_TRACE ||
				((InstancePtr->Mode == XAPM_MODE_ADVANCED) &&
				(InstancePtr->Config.IsEventLog == 1)));

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
				RegVal | XAPM_CR_EVENTLOG_ENABLE_MASK);
}

/*****************************************************************************/
/**
*
* This function enables External trigger pulse so that Metric Counters can be
* started on external trigger pulse for a Slot.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		None
*
*******************************************************************************/
void XAxiPmon_EnableMetricCounterTrigger(XAxiPmon *InstancePtr)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode != XAPM_MODE_TRACE);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
				RegVal | XAPM_CR_MCNTR_EXTTRIGGER_MASK);
}

/****************************************************************************/
/**
*
* This function disables the External trigger pulse used to start Metric
* Counters on external trigger pulse for a Slot.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		None
*
*****************************************************************************/
void XAxiPmon_DisableMetricCounterTrigger(XAxiPmon *InstancePtr)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode != XAPM_MODE_TRACE);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);

	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
				RegVal & ~(XAPM_CR_MCNTR_EXTTRIGGER_MASK));
}

/*****************************************************************************/
/**
*
* This function enables External trigger pulse for Event Log
* so that Event Logging can be started on external trigger pulse for a Slot.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		None
*
*******************************************************************************/
void XAxiPmon_EnableEventLogTrigger(XAxiPmon *InstancePtr)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode != XAPM_MODE_PROFILE);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
				RegVal | XAPM_CR_EVTLOG_EXTTRIGGER_MASK);
}

/****************************************************************************/
/**
*
* This function disables the External trigger pulse used to start Event
* Log on external trigger pulse for a Slot.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		None
*
*****************************************************************************/
void XAxiPmon_DisableEventLogTrigger(XAxiPmon *InstancePtr)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertVoid(InstancePtr->Mode != XAPM_MODE_PROFILE);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);

	XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress, XAPM_CTL_OFFSET,
				RegVal & ~(XAPM_CR_EVTLOG_EXTTRIGGER_MASK));
}

/****************************************************************************/
/**
*
* This function returns a name for a given Metric.
*
* @param        Metrics is one of the Metric Sets. User has to use
*               XAPM_METRIC_SET_* macros in xaxipmon.h for this parameter
*
* @return       const char *
*
* @note         None
*
*****************************************************************************/
const char * XAxiPmon_GetMetricName(u8 Metrics)
{
	if (Metrics == XAPM_METRIC_SET_0 ){
		return "Write Transaction Count";
	}
	if (Metrics == XAPM_METRIC_SET_1 ){
			return "Read Transaction Count";
	}
	if (Metrics == XAPM_METRIC_SET_2 ){
			return "Write Byte Count";
	}
	if (Metrics == XAPM_METRIC_SET_3 ){
			return "Read Byte Count";
	}
	if (Metrics == XAPM_METRIC_SET_4 ){
			return "Write Beat Count";
	}
	if (Metrics == XAPM_METRIC_SET_5 ){
			return "Total Read Latency";
	}
	if (Metrics == XAPM_METRIC_SET_6 ){
			return "Total Write Latency";
	}
	if (Metrics == XAPM_METRIC_SET_7 ){
		return "Slv_Wr_Idle_Cnt";
	}
	if (Metrics == XAPM_METRIC_SET_8 ){
			return "Mst_Rd_Idle_Cnt";
	}
	if (Metrics == XAPM_METRIC_SET_9 ){
			return "Num_BValids";
	}
	if (Metrics == XAPM_METRIC_SET_10){
		return "Num_WLasts";
	}
	if (Metrics == XAPM_METRIC_SET_11){
			return "Num_RLasts";
	}
	if (Metrics == XAPM_METRIC_SET_12){
			return "Minimum Write Latency";
	}
	if (Metrics == XAPM_METRIC_SET_13){
			return "Maximum Write Latency";
	}
	if (Metrics == XAPM_METRIC_SET_14){
			return "Minimum Read Latency";
	}
	if (Metrics == XAPM_METRIC_SET_15){
			return "Maximum Read Latency";
	}
	if (Metrics == XAPM_METRIC_SET_16){
			return "Transfer Cycle Count";
	}
	if (Metrics == XAPM_METRIC_SET_17){
			return "Packet Count";
	}
	if (Metrics == XAPM_METRIC_SET_18){
			return "Data Byte Count";
	}
	if (Metrics == XAPM_METRIC_SET_19){
			return "Position Byte Count";
	}
	if (Metrics == XAPM_METRIC_SET_20){
			return "Null Byte Count";
	}
	if (Metrics == XAPM_METRIC_SET_21){
			return "Slv_Idle_Cnt";
	}
	if (Metrics == XAPM_METRIC_SET_22){
			return "Mst_Idle_Cnt";
	}
	if (Metrics == XAPM_METRIC_SET_30){
			return "External event count";
	}
	return "Unsupported";
}

/****************************************************************************/
/**
*
* This function sets Write ID in ID register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	WriteId is the Write ID to be written in ID register.
*
* @return	None.
*
* @note
*			If ID filtering for write is of 32 bits(for Zynq MP APM) width then
*			WriteID is written to XAPM_ID_OFFSET or if it is 16 bit width
*			then lower 16 bits of WriteID are written to XAPM_ID_OFFSET.
*
*****************************************************************************/
void XAxiPmon_SetWriteId(XAxiPmon *InstancePtr, u32 WriteId)
{
	u32 RegVal;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if (InstancePtr->Config.Is32BitFiltering == 0)
	{
		RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_ID_OFFSET);
		RegVal = RegVal & ~(XAPM_ID_WID_MASK);
		RegVal = RegVal | WriteId;
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
					XAPM_ID_OFFSET, RegVal);
	} else {
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
					XAPM_ID_OFFSET, WriteId);
	}
}

/****************************************************************************/
/**
*
* This function sets Read ID in ID register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	ReadId is the Read ID to be written in ID register.
*
* @return	None.
*
* @note
*			If ID filtering for read is of 32 bits(for Zynq MP APM) width then
*			ReadId is written to XAPM_RID_OFFSET or if it is 16 bit width
*			then lower 16 bits of ReadId are written to XAPM_ID_OFFSET.
*
*****************************************************************************/
void XAxiPmon_SetReadId(XAxiPmon *InstancePtr, u32 ReadId)
{
	u32 RegVal;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if (InstancePtr->Config.Is32BitFiltering == 0)
	{
		RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_ID_OFFSET);
		RegVal = RegVal & ~(XAPM_ID_RID_MASK);
		RegVal = RegVal | (ReadId << 16);
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
					XAPM_ID_OFFSET, RegVal);
	} else {
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
					XAPM_RID_OFFSET, ReadId);
	}
}

/****************************************************************************/
/**
*
* This function returns Write ID in ID register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	WriteId is the required Write ID in ID register.
*
* @note		None.
*			If ID filtering for write is of 32 bits(for Zynq MP APM) width then
*			32 bit XAPM_ID_OFFSET contents are returned or if it is 16 bit
*			width then lower 16 bits of XAPM_ID_OFFSET register are returned.
*
*****************************************************************************/
u32 XAxiPmon_GetWriteId(XAxiPmon *InstancePtr)
{

	u32 WriteId;
	u32 RegVal;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if (InstancePtr->Config.Is32BitFiltering == 0)
	{
		RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_ID_OFFSET);
		WriteId = RegVal & XAPM_ID_WID_MASK;
	} else {
		WriteId = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_ID_OFFSET);
	}

	return WriteId;
}

/****************************************************************************/
/**
*
* This function returns Read ID in ID register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	ReadId is the required Read ID in ID register.
*
* @note		None.
*			If ID filtering for write is of 32 bits(for Zynq MP APM) width then
*			32 bit XAPM_RID_OFFSET contents are returned or if it is 16 bit
*			width then higher 16 bits of XAPM_ID_OFFSET register are returned.
*
*****************************************************************************/
u32 XAxiPmon_GetReadId(XAxiPmon *InstancePtr)
{

	u32 ReadId;
	u32 RegVal;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if (InstancePtr->Config.Is32BitFiltering == 0)
	{
		RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_ID_OFFSET);
		RegVal = RegVal & XAPM_ID_RID_MASK;
		ReadId = RegVal >> 16;
	} else {
		ReadId = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_RID_OFFSET);
	}

	return ReadId;
}

/*****************************************************************************/
/**
*
* This function sets Latency Start point to calculate write latency.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	Param is XAPM_LATENCY_ADDR_ISSUE or XAPM_LATENCY_ADDR_ACCEPT
*		in xaxipmon.h.
* @return	None
*
* @note		Param can be 0 - XAPM_LATENCY_ADDR_ISSUE
*		or 1 - XAPM_LATENCY_ADDR_ACCEPT
*
*******************************************************************************/
void XAxiPmon_SetWrLatencyStart(XAxiPmon *InstancePtr, u8 Param)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	if (Param == XAPM_LATENCY_ADDR_ACCEPT) {
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
		  XAPM_CTL_OFFSET, RegVal | XAPM_CR_WRLATENCY_START_MASK);
	}
	else {
		XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress,
			XAPM_CTL_OFFSET,
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress,
			XAPM_CTL_OFFSET) & ~(XAPM_CR_WRLATENCY_START_MASK));
	}
}

/*****************************************************************************/
/**
*
* This function sets Latency End point to calculate write latency.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	Param is XAPM_LATENCY_LASTWR or XAPM_LATENCY_FIRSTWR
* 		in xaxipmon.h.
*
* @return	None
*
* @note		Param can be 0 - XAPM_LATENCY_LASTWR
*		or 1 - XAPM_LATENCY_FIRSTWR
*
*******************************************************************************/
void XAxiPmon_SetWrLatencyEnd(XAxiPmon *InstancePtr, u8 Param)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	if (Param == XAPM_LATENCY_FIRSTWR) {
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
		  XAPM_CTL_OFFSET, RegVal | XAPM_CR_WRLATENCY_END_MASK);
	}
	else {
		XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress,
			XAPM_CTL_OFFSET,
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress,
			XAPM_CTL_OFFSET) & ~(XAPM_CR_WRLATENCY_END_MASK));
	}
}

/*****************************************************************************/
/**
*
* This function sets Latency Start point to calculate read latency.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	Param is XAPM_LATENCY_ADDR_ISSUE or XAPM_LATENCY_ADDR_ACCEPT
*		in xaxipmon.h.
*
* @return	None
*
* @note		Param can be 0 - XAPM_LATENCY_ADDR_ISSUE
*		or 1 - XAPM_LATENCY_ADDR_ACCEPT
*
*******************************************************************************/
void XAxiPmon_SetRdLatencyStart(XAxiPmon *InstancePtr, u8 Param)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	if (Param == XAPM_LATENCY_ADDR_ACCEPT) {
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
		  XAPM_CTL_OFFSET, RegVal | XAPM_CR_RDLATENCY_START_MASK);
	}
	else {
		XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress,
			XAPM_CTL_OFFSET,
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress,
			XAPM_CTL_OFFSET) & ~(XAPM_CR_RDLATENCY_START_MASK));
	}
}

/*****************************************************************************/
/**
*
* This function sets Latency End point to calculate read latency.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	Param is XAPM_LATENCY_LASTRD or XAPM_LATENCY_FIRSTRD
* 		in xaxipmon.h.
*
* @return	None
*
* @note		Param can be 0 - XAPM_LATENCY_LASTRD
*		or 1 - XAPM_LATENCY_FIRSTRD
*
*******************************************************************************/
void XAxiPmon_SetRdLatencyEnd(XAxiPmon *InstancePtr, u8 Param)
{
	u32 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	if (Param == XAPM_LATENCY_FIRSTRD) {
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
		  XAPM_CTL_OFFSET, RegVal | XAPM_CR_RDLATENCY_END_MASK);
	}
	else {
		XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress,
			XAPM_CTL_OFFSET,
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress,
			XAPM_CTL_OFFSET) & ~(XAPM_CR_RDLATENCY_END_MASK));
	}
}

/*****************************************************************************/
/**
*
* This function returns Write Latency Start point.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	Returns 0 - XAPM_LATENCY_ADDR_ISSUE or
*			1 - XAPM_LATENCY_ADDR_ACCEPT
*
* @note		None
*
*******************************************************************************/
u8 XAxiPmon_GetWrLatencyStart(XAxiPmon *InstancePtr)
{
	u8 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	RegVal = RegVal & XAPM_CR_WRLATENCY_START_MASK;
	if (RegVal != XAPM_LATENCY_ADDR_ISSUE) {
		return XAPM_LATENCY_ADDR_ACCEPT;
	}
	else {
		return XAPM_LATENCY_ADDR_ISSUE;
	}
}

/*****************************************************************************/
/**
*
* This function returns Write Latency End point.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	Returns 0 - XAPM_LATENCY_LASTWR or
*			1 - XAPM_LATENCY_FIRSTWR.
*
* @note		None
*
*******************************************************************************/
u8 XAxiPmon_GetWrLatencyEnd(XAxiPmon *InstancePtr)
{
	u8 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	RegVal = RegVal & XAPM_CR_WRLATENCY_END_MASK;
	if (RegVal != XAPM_LATENCY_LASTWR) {
		return XAPM_LATENCY_FIRSTWR;
	}
	else {
		return XAPM_LATENCY_LASTWR;
	}
}

/*****************************************************************************/
/**
*
* This function returns read Latency Start point.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	Returns 0 - XAPM_LATENCY_ADDR_ISSUE or
*			1 - XAPM_LATENCY_ADDR_ACCEPT
*
* @note		None
*
*******************************************************************************/
u8 XAxiPmon_GetRdLatencyStart(XAxiPmon *InstancePtr)
{
	u8 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	RegVal = RegVal & XAPM_CR_RDLATENCY_START_MASK;

	if (RegVal != XAPM_LATENCY_ADDR_ISSUE) {
		return	XAPM_LATENCY_ADDR_ACCEPT;
	}
	else {
		return XAPM_LATENCY_ADDR_ISSUE;
	}
}

/*****************************************************************************/
/**
*
* This function returns Read Latency End point.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	Returns 0 - XAPM_LATENCY_LASTRD or
*			1 - XAPM_LATENCY_FIRSTRD.
*
* @note		None
*
*******************************************************************************/
u8 XAxiPmon_GetRdLatencyEnd(XAxiPmon *InstancePtr)
{
	u8 RegVal;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_CTL_OFFSET);
	RegVal = RegVal & XAPM_CR_RDLATENCY_END_MASK;
	if (RegVal != XAPM_LATENCY_LASTRD) {
		return XAPM_LATENCY_FIRSTRD;
	}
	else {
		return XAPM_LATENCY_LASTRD;
	}

}

/****************************************************************************/
/**
*
* This function sets Write ID Mask in ID Mask register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	WrMask is the Write ID mask to be written in ID register.
*
* @return	None.
*
* @note
*			If ID masking for write is of 32 bits(for Zynq MP APM) width then
*			WrMask is written to XAPM_IDMASK_OFFSET or if it is 16 bit width
*			then lower 16 bits of WrMask are written to XAPM_IDMASK_OFFSET.
*
*****************************************************************************/
void XAxiPmon_SetWriteIdMask(XAxiPmon *InstancePtr, u32 WrMask)
{
	u32 RegVal;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if (InstancePtr->Config.Is32BitFiltering == 0)
	{
		RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_IDMASK_OFFSET);
		RegVal = RegVal & ~(XAPM_MASKID_WID_MASK);
		RegVal = RegVal | WrMask;
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
							XAPM_IDMASK_OFFSET, RegVal);
	} else {
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
							XAPM_IDMASK_OFFSET, WrMask);
	}
}

/****************************************************************************/
/**
*
* This function sets Read ID Mask in ID Mask register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	RdMask is the Read ID mask to be written in ID Mask register.
*
* @return	None.
*
* @note
*			If ID masking for read is of 32 bits(for Zynq MP APM) width then
*			RdMask is written to XAPM_RIDMASK_OFFSET or if it is 16 bit width
*			then lower 16 bits of RdMask are written to XAPM_IDMASK_OFFSET.
*
*****************************************************************************/
void XAxiPmon_SetReadIdMask(XAxiPmon *InstancePtr, u32 RdMask)
{
	u32 RegVal;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if (InstancePtr->Config.Is32BitFiltering == 0)
	{
		RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_IDMASK_OFFSET);
		RegVal = RegVal & ~(XAPM_MASKID_RID_MASK);
		RegVal = RegVal | (RdMask << 16);
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
					XAPM_IDMASK_OFFSET, RegVal);
	} else {
		XAxiPmon_WriteReg(InstancePtr->Config.BaseAddress,
					XAPM_RIDMASK_OFFSET, RdMask);
	}
}

/****************************************************************************/
/**
*
* This function returns Write ID Mask in ID Mask register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	WrMask is the required Write ID Mask in ID Mask register.
*
* @note
*			If ID masking for write is of 32 bits(for Zynq MP APM) width then
*			32 bit XAPM_IDMASK_OFFSET contents are returned or if it is 16 bit
*			width then lower 16 bits of XAPM_IDMASK_OFFSET register
*			are returned.
*
*****************************************************************************/
u32 XAxiPmon_GetWriteIdMask(XAxiPmon *InstancePtr)
{

	u32 WrMask;
	u32 RegVal;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if (InstancePtr->Config.Is32BitFiltering == 0)
	{
		RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_IDMASK_OFFSET);
		WrMask = RegVal & XAPM_MASKID_WID_MASK;
	} else {
		WrMask = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_IDMASK_OFFSET);
	}

	return WrMask;
}

/****************************************************************************/
/**
*
* This function returns Read ID Mask in ID Mask register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	RdMask is the required Read ID Mask in ID Mask register.
*
* @note
*			If ID masking for read is of 32 bits(for Zynq MP APM) width then
*			32 bit XAPM_RIDMASK_OFFSET contents are returned or if it is 16 bit
*			width then higher 16 bits of XAPM_IDMASK_OFFSET register
*			are returned.
*
*****************************************************************************/
u32 XAxiPmon_GetReadIdMask(XAxiPmon *InstancePtr)
{

	u32 RdMask;
	u32 RegVal;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	if (InstancePtr->Config.Is32BitFiltering == 0)
	{
		RegVal = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
							XAPM_IDMASK_OFFSET);
		RegVal = RegVal & XAPM_MASKID_RID_MASK;
		RdMask = RegVal >> 16;
	} else {
		RdMask = XAxiPmon_ReadReg(InstancePtr->Config.BaseAddress,
								XAPM_RIDMASK_OFFSET);
	}

	return RdMask;
}
