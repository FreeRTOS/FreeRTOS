/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc.  All rights reserved.
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
* @file xqspipsu_sinit.c
* @addtogroup qspipsu_v1_7
* @{
*
* The implementation of the XQspiPsu component's static initialization
* functionality.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- -----------------------------------------------
* 1.0   hk  08/21/14 First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xstatus.h"
#include "xqspipsu.h"
#include "xparameters.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

extern XQspiPsu_Config XQspiPsu_ConfigTable[XPAR_XQSPIPSU_NUM_INSTANCES];

/*****************************************************************************/
/**
*
* Looks up the device configuration based on the unique device ID. A table
* contains the configuration info for each device in the system.
*
* @param	DeviceId contains the ID of the device to look up the
*		configuration for.
*
* @return
*
* A pointer to the configuration found or NULL if the specified device ID was
* not found. See xqspipsu.h for the definition of XQspiPsu_Config.
*
* @note		None.
*
******************************************************************************/
XQspiPsu_Config *XQspiPsu_LookupConfig(u16 DeviceId)
{
	XQspiPsu_Config *CfgPtr = NULL;
	s32 Index;

	for (Index = 0; Index < XPAR_XQSPIPSU_NUM_INSTANCES; Index++) {
		if (XQspiPsu_ConfigTable[Index].DeviceId == DeviceId) {
			CfgPtr = &XQspiPsu_ConfigTable[Index];
			break;
		}
	}
	return (XQspiPsu_Config *)CfgPtr;
}
/** @} */
