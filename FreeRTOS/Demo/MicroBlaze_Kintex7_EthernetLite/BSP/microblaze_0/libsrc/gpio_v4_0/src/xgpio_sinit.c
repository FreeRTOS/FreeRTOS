/******************************************************************************
*
* Copyright (C) 2003 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xgpio_sinit.c
*
* The implementation of the XGpio driver's static initialzation
* functionality.
*
* @note
*
* None
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 2.01a jvb  10/13/05 First release
* 2.11a mta  03/21/07 Updated to new coding style
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include "xstatus.h"
#include "xparameters.h"
#include "xgpio_i.h"

/************************** Constant Definitions ****************************/

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/

/************************** Variable Definitions ****************************/


/************************** Function Prototypes *****************************/


/******************************************************************************/
/**
* Lookup the device configuration based on the unique device ID.  The table
* ConfigTable contains the configuration info for each device in the system.
*
* @param	DeviceId is the device identifier to lookup.
*
* @return
*		 - A pointer of data type XGpio_Config which points to the
*		device configuration if DeviceID is found.
* 		- NULL if DeviceID is not found.
*
* @note		None.
*
******************************************************************************/
XGpio_Config *XGpio_LookupConfig(u16 DeviceId)
{
	XGpio_Config *CfgPtr = NULL;

	int Index;

	for (Index = 0; Index < XPAR_XGPIO_NUM_INSTANCES; Index++) {
		if (XGpio_ConfigTable[Index].DeviceId == DeviceId) {
			CfgPtr = &XGpio_ConfigTable[Index];
			break;
		}
	}

	return CfgPtr;
}


/****************************************************************************/
/**
* Initialize the XGpio instance provided by the caller based on the
* given DeviceID.
*
* Nothing is done except to initialize the InstancePtr.
*
* @param	InstancePtr is a pointer to an XGpio instance. The memory the
*		pointer references must be pre-allocated by the caller. Further
*		calls to manipulate the instance/driver through the XGpio API
*		must be made with this pointer.
* @param	DeviceId is the unique id of the device controlled by this XGpio
*		instance. Passing in a device id associates the generic XGpio
*		instance to a specific device, as chosen by the caller or
*		application developer.
*
* @return
*		- XST_SUCCESS if the initialization was successfull.
* 		- XST_DEVICE_NOT_FOUND  if the device configuration data was not
*		found for a device with the supplied device ID.
*
* @note		None.
*
*****************************************************************************/
int XGpio_Initialize(XGpio * InstancePtr, u16 DeviceId)
{
	XGpio_Config *ConfigPtr;

	/*
	 * Assert arguments
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);

	/*
	 * Lookup configuration data in the device configuration table.
	 * Use this configuration info down below when initializing this
	 * driver.
	 */
	ConfigPtr = XGpio_LookupConfig(DeviceId);
	if (ConfigPtr == (XGpio_Config *) NULL) {
		InstancePtr->IsReady = 0;
		return (XST_DEVICE_NOT_FOUND);
	}

	return XGpio_CfgInitialize(InstancePtr, ConfigPtr,
				   ConfigPtr->BaseAddress);
}
