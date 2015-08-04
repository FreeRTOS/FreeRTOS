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
* @file xtmrctr.c
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


/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
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
int XTmrCtr_Initialize(XTmrCtr * InstancePtr, u16 DeviceId)
{
	XTmrCtr_Config *TmrCtrConfigPtr;
	int TmrCtrNumber;
	int TmrCtrLowIndex = 0;
	int TmrCtrHighIndex = XTC_DEVICE_TIMER_COUNT;

	Xil_AssertNonvoid(InstancePtr != NULL);


	/*
	 * If both the timers have already started, disallow the initialize and
	 * return a status indicating it is started.  This allows the user to stop
	 * the device and reinitialize, but prevents a user from inadvertently
	 * initializing.
	 * In case one of the timers has not started then that particular timer
	 * will be initialized
	 */
	if ((InstancePtr->IsStartedTmrCtr0 == XIL_COMPONENT_IS_STARTED) &&
	    (InstancePtr->IsStartedTmrCtr1 == XIL_COMPONENT_IS_STARTED)) {
		return XST_DEVICE_IS_STARTED;
	}


	/*
	 * Ensure that only the timer which is NOT started can be initialized
	 */
	if ((InstancePtr->IsStartedTmrCtr0 == XIL_COMPONENT_IS_STARTED)) {
		TmrCtrLowIndex = 1;
	} else if ((InstancePtr->IsStartedTmrCtr1 == XIL_COMPONENT_IS_STARTED)) {
		TmrCtrHighIndex = 1;
	} else {
		InstancePtr->IsStartedTmrCtr0 = 0;
		InstancePtr->IsStartedTmrCtr1 = 0;
	}



	/*
	 * Lookup the device configuration in the temporary CROM table. Use this
	 * configuration info down below when initializing this component.
	 */
	TmrCtrConfigPtr = XTmrCtr_LookupConfig(DeviceId);

	if (TmrCtrConfigPtr == (XTmrCtr_Config *) NULL) {
		return XST_DEVICE_NOT_FOUND;
	}

	/*
	 * Set some default values, including setting the callback
	 * handlers to stubs.
	 */
	InstancePtr->BaseAddress = TmrCtrConfigPtr->BaseAddress;
	InstancePtr->Handler = NULL;
	InstancePtr->CallBackRef = NULL;

	/*
	 * Clear the statistics for this driver
	 */
	InstancePtr->Stats.Interrupts = 0;

	/* Initialize the registers of each timer/counter in the device */

	for (TmrCtrNumber = TmrCtrLowIndex; TmrCtrNumber < TmrCtrHighIndex;
	     TmrCtrNumber++) {

		/*
		 * Set the Compare register to 0
		 */
		XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
				  XTC_TLR_OFFSET, 0);
		/*
		 * Reset the timer and the interrupt, the reset bit will need to
		 * be cleared after this
		 */
		XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
				  XTC_TCSR_OFFSET,
				  XTC_CSR_INT_OCCURED_MASK | XTC_CSR_LOAD_MASK);
		/*
		 * Set the control/status register to complete initialization by
		 * clearing the reset bit which was just set
		 */
		XTmrCtr_WriteReg(InstancePtr->BaseAddress, TmrCtrNumber,
				  XTC_TCSR_OFFSET, 0);
	}

	/*
	 * Indicate the instance is ready to use, successfully initialized
	 */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	return XST_SUCCESS;
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

/*****************************************************************************
*
* Looks up the device configuration based on the unique device ID. The table
* TmrCtrConfigTable contains the configuration info for each device in the
* system.
*
* @param	DeviceId is the unique device ID to search for in the config
*		table.
*
* @return	A pointer to the configuration that matches the given device ID,
* 		or NULL if no match is found.
*
* @note		None.
*
******************************************************************************/
XTmrCtr_Config *XTmrCtr_LookupConfig(u16 DeviceId)
{
	XTmrCtr_Config *CfgPtr = NULL;
	int Index;

	for (Index = 0; Index < XPAR_XTMRCTR_NUM_INSTANCES; Index++) {
		if (XTmrCtr_ConfigTable[Index].DeviceId == DeviceId) {
			CfgPtr = &XTmrCtr_ConfigTable[Index];
			break;
		}
	}

	return CfgPtr;
}
