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
* @file xintc_intr.c
* @addtogroup intc_v3_4
* @{
*
* This file contains the interrupt processing for the XIntc component which
* is the driver for the Xilinx Interrupt Controller.  The interrupt
* processing is partitioned seperately such that users are not required to
* use the provided interrupt processing.  This file requires other files of
* the driver to be linked in also.
*
* Two different interrupt handlers are provided for this driver such that the
* user must select the appropriate handler for the application.  The first
* interrupt handler, XIntc_VoidInterruptHandler, is provided for systems
* which use only a single interrupt controller or for systems that cannot
* otherwise provide an argument to the XIntc interrupt handler (e.g., the RTOS
* interrupt vector handler may not provide such a facility).  The constant
* XPAR_INTC_SINGLE_DEVICE_ID must be defined for this handler to be included in
* the driver.  The second interrupt handler, XIntc_InterruptHandler, uses an
* input argument which is an instance pointer to an interrupt controller driver
* such that multiple interrupt controllers can be supported.  This handler
* requires the calling function to pass it the appropriate argument, so another
* level of indirection may be required.
*
* Note that both of these handlers are now only provided for backward
* compatibility. The handler defined in xintc_l.c is the recommended handler.
*
* The interrupt processing may be used by connecting one of the interrupt
* handlers to the interrupt system.  These handlers do not save and restore
* the processor context but only handle the processing of the Interrupt
* Controller.  The two handlers are provided as working examples. The user is
* encouraged to supply their own interrupt handler when performance tuning is
* deemed necessary.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------------
* 1.00b jhl  02/13/02 First release
* 1.00c rpm  10/17/03 New release. Support the static vector table created
*                     in the xintc_g.c configuration table. Collapse handlers
*                     to use the XIntc_DeviceInterruptHandler() in xintc_l.c.
* 1.00c rpm  04/09/04 Added conditional compilation around the old handler
*                     XIntc_VoidInterruptHandler(). This handler will only be
*                     include/compiled if XPAR_INTC_SINGLE_DEVICE_ID is defined.
* 1.10c mta  03/21/07 Updated to new coding style
* 2.00a ktn  10/20/09 Updated to use HAL Processor APIs.
*
* </pre>
*
* @internal
*
* This driver assumes that the context of the processor has been saved prior to
* the calling of the Interrupt Controller interrupt handler and then restored
* after the handler returns. This requires either the running RTOS to save the
* state of the machine or that a wrapper be used as the destination of the
* interrupt vector to save the state of the processor and restore the state
* after the interrupt handler returns.
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xparameters.h"
#include "xintc.h"

/************************** Constant Definitions *****************************/



/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/


/************************** Variable Definitions *****************************/


/*****************************************************************************/
/**
*
* Interrupt handler for the driver used when there can be no argument passed
* to the handler.  This function is provided mostly for backward compatibility.
* The user should use XIntc_DeviceInterruptHandler(), defined in xintc_l.c,
* if possible.
*
* The user must connect this function to the interrupt system such that it is
* called whenever the devices which are connected to it cause an interrupt.
*
* @return	None.
*
* @note
*
* The constant XPAR_INTC_SINGLE_DEVICE_ID must be defined for this handler
* to be included in the driver compilation.
*
******************************************************************************/
#ifdef XPAR_INTC_SINGLE_DEVICE_ID
void XIntc_VoidInterruptHandler(void)
{
	/* Use the single instance to call the main interrupt handler */
	XIntc_DeviceInterruptHandler((void *) XPAR_INTC_SINGLE_DEVICE_ID);
}
#endif

/*****************************************************************************/
/**
*
* The interrupt handler for the driver. This function is provided mostly for
* backward compatibility.  The user should use XIntc_DeviceInterruptHandler(),
* defined in xintc_l.c when possible and pass the device ID of the interrupt
* controller device as its argument.
*
* The user must connect this function to the interrupt system such that it is
* called whenever the devices which are connected to it cause an interrupt.
*
* @param	InstancePtr is a pointer to the XIntc instance to be worked on.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XIntc_InterruptHandler(XIntc * InstancePtr)
{
	/* Assert that the pointer to the instance is valid
	 */
	Xil_AssertVoid(InstancePtr != NULL);

	/* Use the instance's device ID to call the main interrupt handler.
	 * (the casts are to avoid a compiler warning)
	 */
	XIntc_DeviceInterruptHandler((void *)
				     ((u32) (InstancePtr->CfgPtr->DeviceId)));
}
/** @} */
