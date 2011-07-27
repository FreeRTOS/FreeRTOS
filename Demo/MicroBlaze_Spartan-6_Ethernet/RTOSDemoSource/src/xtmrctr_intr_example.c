#define TESTAPP_GEN

/* $Id: xtmrctr_intr_example.c,v 1.1.2.1 2010/12/01 07:53:56 svemula Exp $ */
/******************************************************************************
*
* (c) Copyright 2002-2010 Xilinx, Inc. All rights reserved.
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
* @file  xtmrctr_intr_example.c
*
* This file contains a design example using the timer counter driver
* (XTmCtr) and hardware device using interrupt mode.This example assumes
* that the interrupt controller is also present as a part of the system
*
* This file can be used as a standalone example or by the TestAppGen utility
* to include a test for Timer interrupts.
*
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date	 Changes
* ----- ---- -------- -----------------------------------------------
* 1.00b jhl  02/13/02 First release
* 1.00b sv   04/26/05 Minor changes to comply to Doxygen and coding guidelines
* 1.00b sn   05/09/06 Modified to be used by TestAppGen to include test for
*		      interrupts.
* 2.00a ktn  10/30/09 Updated to use HAL API's and minor changes as per coding
*		      guidelines.
*</pre>
******************************************************************************/

/***************************** Include Files *********************************/

#include "xparameters.h"
#include "xtmrctr.h"
#include "xintc.h"
#include "xil_exception.h"

/************************** Constant Definitions *****************************/
#ifndef TESTAPP_GEN
/*
 * The following constants map to the XPAR parameters created in the
 * xparameters.h file. They are only defined here such that a user can easily
 * change all the needed parameters in one place.
 */
#define TMRCTR_DEVICE_ID	XPAR_TMRCTR_0_DEVICE_ID
#define INTC_DEVICE_ID		XPAR_INTC_0_DEVICE_ID
#define TMRCTR_INTERRUPT_ID	XPAR_INTC_0_TMRCTR_0_VEC_ID

/*
 * The following constant determines which timer counter of the device that is
 * used for this example, there are currently 2 timer counters in a device
 * and this example uses the first one, 0, the timer numbers are 0 based
 */
#define TIMER_CNTR_0	 0

#endif
/*
 * The following constant is used to set the reset value of the timer counter,
 * making this number larger reduces the amount of time this example consumes
 * because it is the value the timer counter is loaded with when it is started
 */
#define RESET_VALUE	 0xF0000000



/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

int TmrCtrIntrExample(XIntc* IntcInstancePtr,
			XTmrCtr* InstancePtr,
			u16 DeviceId,
			u16 IntrId,
			u8 TmrCtrNumber);

static int TmrCtrSetupIntrSystem(XIntc* IntcInstancePtr,
				XTmrCtr* InstancePtr,
				u16 DeviceId,
				u16 IntrId,
				u8 TmrCtrNumber);

void TimerCounterHandler(void *CallBackRef, u8 TmrCtrNumber);

void TmrCtrDisableIntr(XIntc* IntcInstancePtr, u16 IntrId);

/************************** Variable Definitions *****************************/
#ifndef TESTAPP_GEN
XIntc InterruptController;  /* The instance of the Interrupt Controller */

XTmrCtr TimerCounterInst;   /* The instance of the Timer Counter */
#endif
/*
 * The following variables are shared between non-interrupt processing and
 * interrupt processing such that they must be global.
 */
volatile int TimerExpired;


/*****************************************************************************/
/**
* This function is the main function of the Tmrctr example using Interrupts.
*
* @param	None.
*
* @return	XST_SUCCESS to indicate success, else XST_FAILURE to indicate a
*		Failure.
*
* @note		None.
*
******************************************************************************/
#ifndef TESTAPP_GEN
int main(void)
{

	int Status;

	/*
	 * Run the Timer Counter - Interrupt example.
	 */
	Status = TmrCtrIntrExample(&InterruptController,
				  &TimerCounterInst,
				  TMRCTR_DEVICE_ID,
				  TMRCTR_INTERRUPT_ID,
				  TIMER_CNTR_0);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	return XST_SUCCESS;

}
#endif

/*****************************************************************************/
/**
* This function does a minimal test on the timer counter device and driver as a
* design example.  The purpose of this function is to illustrate how to use the
* XTmrCtr component.  It initializes a timer counter and then sets it up in
* compare mode with auto reload such that a periodic interrupt is generated.
*
* This function uses interrupt driven mode of the timer counter.
*
* @param	IntcInstancePtr is a pointer to the Interrupt Controller
*		driver Instance
* @param	TmrCtrInstancePtr is a pointer to the XTmrCtr driver Instance
* @param	DeviceId is the XPAR_<TmrCtr_instance>_DEVICE_ID value from
*		xparameters.h
* @param	IntrId is XPAR_<INTC_instance>_<TmrCtr_instance>_INTERRUPT_INTR
*		value from xparameters.h
* @param	TmrCtrNumber is the number of the timer to which this
*		handler is associated with.
*
* @return	XST_SUCCESS if the Test is successful, otherwise XST_FAILURE
*
* @note		This function contains an infinite loop such that if interrupts
*		are not working it may never return.
*
*****************************************************************************/
int TmrCtrIntrExample(XIntc* IntcInstancePtr,
			XTmrCtr* TmrCtrInstancePtr,
			u16 DeviceId,
			u16 IntrId,
			u8 TmrCtrNumber)
{
	int Status;
	int LastTimerExpired = 0;

	/*
	 * Initialize the timer counter so that it's ready to use,
	 * specify the device ID that is generated in xparameters.h
	 */
	Status = XTmrCtr_Initialize(TmrCtrInstancePtr, DeviceId);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/*
	 * Perform a self-test to ensure that the hardware was built
	 * correctly, use the 1st timer in the device (0)
	 */
	Status = XTmrCtr_SelfTest(TmrCtrInstancePtr, TmrCtrNumber);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/*
	 * Connect the timer counter to the interrupt subsystem such that
	 * interrupts can occur.  This function is application specific.
	 */
	Status = TmrCtrSetupIntrSystem(IntcInstancePtr,
					TmrCtrInstancePtr,
					DeviceId,
					IntrId,
					TmrCtrNumber);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

	/*
	 * Setup the handler for the timer counter that will be called from the
	 * interrupt context when the timer expires, specify a pointer to the
	 * timer counter driver instance as the callback reference so the handler
	 * is able to access the instance data
	 */
	XTmrCtr_SetHandler(TmrCtrInstancePtr, TimerCounterHandler,
					   TmrCtrInstancePtr);

	/*
	 * Enable the interrupt of the timer counter so interrupts will occur
	 * and use auto reload mode such that the timer counter will reload
	 * itself automatically and continue repeatedly, without this option
	 * it would expire once only
	 */
	XTmrCtr_SetOptions(TmrCtrInstancePtr, TmrCtrNumber,
				XTC_INT_MODE_OPTION | XTC_AUTO_RELOAD_OPTION);

	/*
	 * Set a reset value for the timer counter such that it will expire
	 * eariler than letting it roll over from 0, the reset value is loaded
	 * into the timer counter when it is started
	 */
	XTmrCtr_SetResetValue(TmrCtrInstancePtr, TmrCtrNumber, RESET_VALUE);

	/*
	 * Start the timer counter such that it's incrementing by default,
	 * then wait for it to timeout a number of times
	 */
	XTmrCtr_Start(TmrCtrInstancePtr, TmrCtrNumber);

	while (1) {
		/*
		 * Wait for the first timer counter to expire as indicated by the
		 * shared variable which the handler will increment
		 */
		while (TimerExpired == LastTimerExpired) {
		}
		LastTimerExpired = TimerExpired;

		/*
		 * If it has expired a number of times, then stop the timer counter
		 * and stop this example
		 */
		if (TimerExpired == 3) {

			XTmrCtr_Stop(TmrCtrInstancePtr, TmrCtrNumber);
			break;
		}
	}

	TmrCtrDisableIntr(IntcInstancePtr, DeviceId);
	return XST_SUCCESS;
}

/*****************************************************************************/
/**
* This function is the handler which performs processing for the timer counter.
* It is called from an interrupt context such that the amount of processing
* performed should be minimized.  It is called when the timer counter expires
* if interrupts are enabled.
*
* This handler provides an example of how to handle timer counter interrupts
* but is application specific.
*
* @param	CallBackRef is a pointer to the callback function
* @param	TmrCtrNumber is the number of the timer to which this
*		handler is associated with.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void TimerCounterHandler(void *CallBackRef, u8 TmrCtrNumber)
{
	XTmrCtr *InstancePtr = (XTmrCtr *)CallBackRef;

	/*
	 * Check if the timer counter has expired, checking is not necessary
	 * since that's the reason this function is executed, this just shows
	 * how the callback reference can be used as a pointer to the instance
	 * of the timer counter that expired, increment a shared variable so
	 * the main thread of execution can see the timer expired
	 */
	if (XTmrCtr_IsExpired(InstancePtr, TmrCtrNumber)) {
		TimerExpired++;
		if(TimerExpired == 3) {
			XTmrCtr_SetOptions(InstancePtr, TmrCtrNumber, 0);
		}
	}
}

/*****************************************************************************/
/**
* This function setups the interrupt system such that interrupts can occur
* for the timer counter. This function is application specific since the actual
* system may or may not have an interrupt controller.  The timer counter could
* be directly connected to a processor without an interrupt controller.  The
* user should modify this function to fit the application.
*
* @param	IntcInstancePtr is a pointer to the Interrupt Controller
*		driver Instance.
* @param	TmrCtrInstancePtr is a pointer to the XTmrCtr driver Instance.
* @param	DeviceId is the XPAR_<TmrCtr_instance>_DEVICE_ID value from
*		xparameters.h.
* @param	IntrId is XPAR_<INTC_instance>_<TmrCtr_instance>_VEC_ID
*		value from xparameters.h.
* @param	TmrCtrNumber is the number of the timer to which this
*		handler is associated with.
*
* @return	XST_SUCCESS if the Test is successful, otherwise XST_FAILURE.
*
* @note		This function contains an infinite loop such that if interrupts
*		are not working it may never return.
*
******************************************************************************/
static int TmrCtrSetupIntrSystem(XIntc* IntcInstancePtr,
				 XTmrCtr* TmrCtrInstancePtr,
				 u16 DeviceId,
				 u16 IntrId,
				 u8 TmrCtrNumber)
{
	 int Status;

 #ifndef TESTAPP_GEN
	/*
	 * Initialize the interrupt controller driver so that
	 * it's ready to use, specify the device ID that is generated in
	 * xparameters.h
	 */
	Status = XIntc_Initialize(IntcInstancePtr, INTC_DEVICE_ID);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}
#endif
	/*
	 * Connect a device driver handler that will be called when an interrupt
	 * for the device occurs, the device driver handler performs the specific
	 * interrupt processing for the device
	 */
	Status = XIntc_Connect(IntcInstancePtr, IntrId,
				(XInterruptHandler)XTmrCtr_InterruptHandler,
				(void *)TmrCtrInstancePtr);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}

#ifndef TESTAPP_GEN
	/*
	 * Start the interrupt controller such that interrupts are enabled for
	 * all devices that cause interrupts, specific real mode so that
	 * the timer counter can cause interrupts thru the interrupt controller.
	 */
	Status = XIntc_Start(IntcInstancePtr, XIN_REAL_MODE);
	if (Status != XST_SUCCESS) {
		return XST_FAILURE;
	}
#endif

	/*
	 * Enable the interrupt for the timer counter
	 */
	XIntc_Enable(IntcInstancePtr, IntrId);

#ifndef TESTAPP_GEN
	/*
	 * Initialize the exception table.
	 */
	Xil_ExceptionInit();

	/*
	 * Register the interrupt controller handler with the exception table.
	 */
	Xil_ExceptionRegisterHandler(XIL_EXCEPTION_ID_INT,
					(Xil_ExceptionHandler)
					XIntc_InterruptHandler,
					IntcInstancePtr);

	/*
	 * Enable non-critical exceptions.
	 */
	Xil_ExceptionEnable();

#endif
	return XST_SUCCESS;
}


/******************************************************************************/
/**
*
* This function disables the interrupts for the Timer.
*
* @param	IntcInstancePtr is a reference to the Interrupt Controller
*		driver Instance.
* @param	IntrId is XPAR_<INTC_instance>_<Timer_instance>_VEC_ID
*		value from xparameters.h.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void TmrCtrDisableIntr(XIntc* IntcInstancePtr, u16 IntrId)
{
	/*
	 * Disable the interrupt for the timer counter
	 */
	XIntc_Disable(IntcInstancePtr, IntrId);

	return;
}


