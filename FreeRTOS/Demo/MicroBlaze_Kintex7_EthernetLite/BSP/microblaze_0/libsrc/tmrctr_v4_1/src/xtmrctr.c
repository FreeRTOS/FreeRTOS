/******************************************************************************
*
* Copyright (C) 2002 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xtmrctr.c
* @addtogroup tmrctr_v4_0
* @{
*
* Contains required functions for the XTmrCtr driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a ecm  08/16/01 First release
* 1.00b jhl  02/21/02 Repartitioned the driver for smaller files
* 1.10b mta  03/21/07 Updated to new coding style
* 2.00a ktn  10/30/09 Updated to use HAL API's. _m is removed from all the macro
*		      definitions.
* 2.05a adk  15/05/13 Fixed the CR:693066
*		      Added the IsStartedTmrCtr0/IsStartedTmrCtr1 members to the
*		      XTmrCtr instance structure.
*		      The IsStartedTmrCtrX will be assigned XIL_COMPONENT_IS_STARTED in
*		      the XTmrCtr_Start function.
*		      The IsStartedTmrCtrX will be cleared in the XTmrCtr_Stop function.
*		      There will be no Initialization done in the
*		      XTmrCtr_Initialize if both the timers have already started and
*		      the XST_DEVICE_IS_STARTED Status is returned.
*		      Removed the logic in the XTmrCtr_Initialize function
*		      which was checking the Register Value to know whether
*		      a timer has started or not.
* 4.0   als  09/30/15 Updated initialization API.
* 4.1   sk   11/10/15 Used UINTPTR instead of u32 for Baseaddress CR# 867425.
*                     Changed the prototype of XTmrCtr_CfgInitialize API.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xparameters.h"
#include "xtmrctr.h"
#include "xtmrctr_i.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

static void XTmrCtr_StubCallback(void *CallBackRef, u8 TmrCtrNumber);

/************************** Variable Definitions *****************************/

/*****************************************************************************/
/**
* This function populates the timer counter's configuration structure and sets
* some configurations defaults.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	ConfigPtr is a pointer to the configuration structure that will
*		be used to copy the settings from.
* @param	EffectiveAddr is the device base address in the virtual memory
*		space. If the address translation is not used, then the physical
*		address is passed.
*
* @return	None.
*
* @note		Unexpected errors may occur if the address mapping is changed
*		after this function is invoked.
*
******************************************************************************/
void XTmrCtr_CfgInitialize(XTmrCtr *InstancePtr, XTmrCtr_Config *ConfigPtr,
		UINTPTR EffectiveAddr)
{
	/* Verify arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(ConfigPtr != NULL);
	Xil_AssertVoid(EffectiveAddr != 0x0);

	InstancePtr->IsReady = 0;
	InstancePtr->Config = *ConfigPtr;

	InstancePtr->Config.BaseAddress = EffectiveAddr;
	InstancePtr->BaseAddress = EffectiveAddr;

	InstancePtr->Handler = XTmrCtr_StubCallback;
	InstancePtr->CallBackRef = InstancePtr;
	InstancePtr->Stats.Interrupts = 0;

	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;
}

/*****************************************************************************/
/**
* (Re-)initialzes all timer counters which aren't started already.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
*
* @return
*		- XST_SUCCESS if at least one timer counter is stopped.
*		- XST_DEVICE_IS_STARTED otherwise.
*
* @note		None.
*
******************************************************************************/
int XTmrCtr_InitHw(XTmrCtr *InstancePtr)
{
	int Status = XST_DEVICE_IS_STARTED;
	u8 TmrIndex;
	u32 TmrCtrStarted[XTC_DEVICE_TIMER_COUNT];

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	TmrCtrStarted[0] = InstancePtr->IsStartedTmrCtr0;
	TmrCtrStarted[1] = InstancePtr->IsStartedTmrCtr1;

	for (TmrIndex = 0; TmrIndex < XTC_DEVICE_TIMER_COUNT; TmrIndex++) {
		/* Only initialize timers counters which aren't started. */
		if (TmrCtrStarted[TmrIndex] == XIL_COMPONENT_IS_STARTED) {
			continue;
		}

		/* Set the compare register to 0. */
		XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrIndex,
				  XTC_TLR_OFFSET, 0);
		/* Reset the timer and the interrupt. */
		XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrIndex,
				  XTC_TCSR_OFFSET,
				  XTC_CSR_INT_OCCURED_MASK | XTC_CSR_LOAD_MASK);
		/* Release the reset. */
		XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrIndex,
				  XTC_TCSR_OFFSET, 0);

		/* Indicate that at least one timer is not running and has been
		 * initialized. */
		Status = XST_SUCCESS;
	}

	return Status;
}

/*****************************************************************************/
/**
* Initializes a specific timer/counter instance/driver. Initialize fields of
* the XTmrCtr structure, then reset the timer/counter.If a timer is already
* running then it is not initialized.
*
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	DeviceId is the unique id of the device controlled by this
*		XTmrCtr component.  Passing in a device id associates the
*		generic XTmrCtr component to a specific device, as chosen by
*		the caller or application developer.
*
* @return
*		- XST_SUCCESS if initialization was successful
*		- XST_DEVICE_IS_STARTED if the device has already been started
*		- XST_DEVICE_NOT_FOUND if the device doesn't exist
*
* @note		None.
*
******************************************************************************/
int XTmrCtr_Initialize(XTmrCtr *InstancePtr, u16 DeviceId)
{
	XTmrCtr_Config *ConfigPtr;

	Xil_AssertNonvoid(InstancePtr != NULL);

	/* In case all timer counters are already started, don't proceed with
	 * re-initialization. */
	if ((InstancePtr->IsStartedTmrCtr0 == XIL_COMPONENT_IS_STARTED) &&
	    (InstancePtr->IsStartedTmrCtr1 == XIL_COMPONENT_IS_STARTED)) {
		return XST_DEVICE_IS_STARTED;
	}

	/* Retrieve configuration of timer counter core with matching ID. */
	ConfigPtr = XTmrCtr_LookupConfig(DeviceId);
	if (!ConfigPtr) {
		return XST_DEVICE_NOT_FOUND;
	}

	XTmrCtr_CfgInitialize(InstancePtr, ConfigPtr, ConfigPtr->BaseAddress);

	return XTmrCtr_InitHw(InstancePtr);
}

/*****************************************************************************/
/**
*
* Starts the specified timer counter of the device such that it starts running.
* The timer counter is reset before it is started and the reset value is
* loaded into the timer counter.
*
* If interrupt mode is specified in the options, it is necessary for the caller
* to connect the interrupt handler of the timer/counter to the interrupt source,
* typically an interrupt controller, and enable the interrupt within the
* interrupt controller.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	TmrCtrNumber is the timer counter of the device to operate on.
*		Each device may contain multiple timer counters. The timer
*		number is a zero based number with a range of
*		0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XTmrCtr_Start(XTmrCtr * InstancePtr, u8 TmrCtrNumber)
{
	u32 ControlStatusReg;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(TmrCtrNumber < XTC_DEVICE_TIMER_COUNT);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the current register contents such that only the necessary bits
	 * of the register are modified in the following operations
	 */
	ControlStatusReg = XTmrCtr_ReadReg(InstancePtr->BaseAddress,
					      TmrCtrNumber, XTC_TCSR_OFFSET);
	/*
	 * Reset the timer counter such that it reloads from the compare
	 * register and the interrupt is cleared simultaneously, the interrupt
	 * can only be cleared after reset such that the interrupt condition is
	 * cleared
	 */
	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TCSR_OFFSET,
			  XTC_CSR_LOAD_MASK);



	/*
	 * Indicate that the timer is started before enabling it
	 */
	if (TmrCtrNumber == 0) {
		InstancePtr->IsStartedTmrCtr0 = XIL_COMPONENT_IS_STARTED;
	} else {
		InstancePtr->IsStartedTmrCtr1 = XIL_COMPONENT_IS_STARTED;
	}


	/*
	 * Remove the reset condition such that the timer counter starts running
	 * with the value loaded from the compare register
	 */
	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TCSR_OFFSET,
			  ControlStatusReg | XTC_CSR_ENABLE_TMR_MASK);
}

/*****************************************************************************/
/**
*
* Stops the timer counter by disabling it.
*
* It is the callers' responsibility to disconnect the interrupt handler of the
* timer_counter from the interrupt source, typically an interrupt controller,
* and disable the interrupt within the interrupt controller.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	TmrCtrNumber is the timer counter of the device to operate on.
*		Each device may contain multiple timer counters. The timer
*		number is a zero based number with a range of
*		0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XTmrCtr_Stop(XTmrCtr * InstancePtr, u8 TmrCtrNumber)
{
	u32 ControlStatusReg;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(TmrCtrNumber < XTC_DEVICE_TIMER_COUNT);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the current register contents
	 */
	ControlStatusReg = XTmrCtr_ReadReg(InstancePtr->BaseAddress,
					      TmrCtrNumber, XTC_TCSR_OFFSET);
	/*
	 * Disable the timer counter such that it's not running
	 */
	ControlStatusReg &= ~(XTC_CSR_ENABLE_TMR_MASK);

	/*
	 * Write out the updated value to the actual register.
	 */
	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TCSR_OFFSET, ControlStatusReg);

	/*
	 * Indicate that the timer is stopped
	 */
	if (TmrCtrNumber == 0) {
		InstancePtr->IsStartedTmrCtr0 = 0;
	} else {
		InstancePtr->IsStartedTmrCtr1 = 0;
	}
}

/*****************************************************************************/
/**
*
* Get the current value of the specified timer counter.  The timer counter
* may be either incrementing or decrementing based upon the current mode of
* operation.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	TmrCtrNumber is the timer counter of the device to operate on.
*		Each device may contain multiple timer counters. The timer
*		number is a zero based number  with a range of
*		0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	The current value for the timer counter.
*
* @note		None.
*
******************************************************************************/
u32 XTmrCtr_GetValue(XTmrCtr * InstancePtr, u8 TmrCtrNumber)
{

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(TmrCtrNumber < XTC_DEVICE_TIMER_COUNT);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	return XTmrCtr_ReadReg(InstancePtr->BaseAddress,
				  TmrCtrNumber, XTC_TCR_OFFSET);
}

/*****************************************************************************/
/**
*
* Set the reset value for the specified timer counter. This is the value
* that is loaded into the timer counter when it is reset. This value is also
* loaded when the timer counter is started.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	TmrCtrNumber is the timer counter of the device to operate on.
*		Each device may contain multiple timer counters. The timer
*		number is a zero based number  with a range of
*		0 - (XTC_DEVICE_TIMER_COUNT - 1).
* @param	ResetValue contains the value to be used to reset the timer
*		counter.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XTmrCtr_SetResetValue(XTmrCtr * InstancePtr, u8 TmrCtrNumber,
			   u32 ResetValue)
{

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(TmrCtrNumber < XTC_DEVICE_TIMER_COUNT);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TLR_OFFSET, ResetValue);
}

/*****************************************************************************/
/**
*
* Returns the timer counter value that was captured the last time the external
* capture input was asserted.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	TmrCtrNumber is the timer counter of the device to operate on.
*		Each device may contain multiple timer counters. The timer
*		number is a zero based number  with a range of
*		0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	The current capture value for the indicated timer counter.
*
* @note		None.
*
*******************************************************************************/
u32 XTmrCtr_GetCaptureValue(XTmrCtr * InstancePtr, u8 TmrCtrNumber)
{

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(TmrCtrNumber < XTC_DEVICE_TIMER_COUNT);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	return XTmrCtr_ReadReg(InstancePtr->BaseAddress,
				  TmrCtrNumber, XTC_TLR_OFFSET);
}

/*****************************************************************************/
/**
*
* Resets the specified timer counter of the device. A reset causes the timer
* counter to set it's value to the reset value.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	TmrCtrNumber is the timer counter of the device to operate on.
*		Each device may contain multiple timer counters. The timer
*		number is a zero based number  with a range of
*		0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XTmrCtr_Reset(XTmrCtr * InstancePtr, u8 TmrCtrNumber)
{
	u32 CounterControlReg;

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(TmrCtrNumber < XTC_DEVICE_TIMER_COUNT);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read current contents of the register so it won't be destroyed
	 */
	CounterControlReg = XTmrCtr_ReadReg(InstancePtr->BaseAddress,
					       TmrCtrNumber, XTC_TCSR_OFFSET);
	/*
	 * Reset the timer by toggling the reset bit in the register
	 */
	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TCSR_OFFSET,
			  CounterControlReg | XTC_CSR_LOAD_MASK);

	XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
			  XTC_TCSR_OFFSET, CounterControlReg);
}

/*****************************************************************************/
/**
*
* Checks if the specified timer counter of the device has expired. In capture
* mode, expired is defined as a capture occurred. In compare mode, expired is
* defined as the timer counter rolled over/under for up/down counting.
*
* When interrupts are enabled, the expiration causes an interrupt. This function
* is typically used to poll a timer counter to determine when it has expired.
*
* @param	InstancePtr is a pointer to the XTmrCtr instance.
* @param	TmrCtrNumber is the timer counter of the device to operate on.
*		Each device may contain multiple timer counters. The timer
*		number is a zero based number  with a range of
*		0 - (XTC_DEVICE_TIMER_COUNT - 1).
*
* @return	TRUE if the timer has expired, and FALSE otherwise.
*
* @note		None.
*
******************************************************************************/
int XTmrCtr_IsExpired(XTmrCtr * InstancePtr, u8 TmrCtrNumber)
{
	u32 CounterControlReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(TmrCtrNumber < XTC_DEVICE_TIMER_COUNT);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Check if timer is expired
	 */
	CounterControlReg = XTmrCtr_ReadReg(InstancePtr->BaseAddress,
					       TmrCtrNumber, XTC_TCSR_OFFSET);

	return ((CounterControlReg & XTC_CSR_INT_OCCURED_MASK) ==
		XTC_CSR_INT_OCCURED_MASK);
}

/*****************************************************************************/
/**
* Default callback for the driver does nothing. It matches the signature of the
* XTmrCtr_Handler type.
*
* @param	CallBackRef is a pointer to the callback's data.
* @param	TmrCtrNumber is the ID of the timer counter which a user-defined
*		callback would normally operate on.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void XTmrCtr_StubCallback(void *CallBackRef, u8 TmrCtrNumber)
{
	Xil_AssertVoid(CallBackRef != NULL);
	Xil_AssertVoid(TmrCtrNumber < XTC_DEVICE_TIMER_COUNT);
}

/** @} */
