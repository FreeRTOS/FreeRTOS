/******************************************************************************
*
* Copyright (C) 2005 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xuartlite_sinit.c
* @addtogroup uartlite_v3_1
* @{
*
* The implementation of the XUartLite component's static initialzation
* functionality.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.01a jvb  10/13/05 First release
* 2.00a ktn  10/20/09 Updated to use HAL Processor APIs.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xstatus.h"
#include "xparameters.h"
#include "xuartlite_i.h"

/************************** Constant Definitions ****************************/


/**************************** Type Definitions ******************************/


/***************** Macros (Inline Functions) Definitions ********************/


/************************** Variable Definitions ****************************/


/************************** Function Prototypes *****************************/

/****************************************************************************
*
* Looks up the device configuration based on the unique device ID.  The table
* UartliteConfigTable contains the configuration info for each device in the
* system.
*
* @param	DeviceId is the unique device ID to match on.
*
* @return	A pointer to the configuration data for the device, or
*		NULL if no match was found.
*
* @note		None.
*
******************************************************************************/
XUartLite_Config *XUartLite_LookupConfig(u16 DeviceId)
{
	XUartLite_Config *CfgPtr = NULL;
	u32 Index;

	for (Index=0; Index < XPAR_XUARTLITE_NUM_INSTANCES; Index++) {
		if (XUartLite_ConfigTable[Index].DeviceId == DeviceId) {
			CfgPtr = &XUartLite_ConfigTable[Index];
			break;
		}
	}

	return CfgPtr;
}

/****************************************************************************/
/**
*
* Initialize a XUartLite instance.  The receive and transmit FIFOs of the
* UART are not flushed, so the user may want to flush them. The hardware
* device does not have any way to disable the receiver such that any valid
* data may be present in the receive FIFO. This function disables the UART
* interrupt. The baudrate and format of the data are fixed in the hardware
* at hardware build time.
*
* @param	InstancePtr is a pointer to the XUartLite instance.
* @param	DeviceId is the unique id of the device controlled by this
*		XUartLite instance.  Passing in a device id associates the
*		generic XUartLite instance to a specific device, as chosen by
*		the caller or application developer.
*
* @return
* 		- XST_SUCCESS if everything starts up as expected.
* 		- XST_DEVICE_NOT_FOUND if the device is not found in the
*			configuration table.
*
* @note		None.
*
*****************************************************************************/
int XUartLite_Initialize(XUartLite *InstancePtr, u16 DeviceId)
{
	XUartLite_Config *ConfigPtr;

	/*
	 * Assert validates the input arguments
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);

	/*
	 * Lookup the device configuration in the configuration table. Use this
	 * configuration info when initializing this component.
	 */
	ConfigPtr = XUartLite_LookupConfig(DeviceId);

	if (ConfigPtr == (XUartLite_Config *)NULL) {
		return XST_DEVICE_NOT_FOUND;
	}
	return XUartLite_CfgInitialize(InstancePtr, ConfigPtr,
					ConfigPtr->RegBaseAddr);
}

/** @} */
