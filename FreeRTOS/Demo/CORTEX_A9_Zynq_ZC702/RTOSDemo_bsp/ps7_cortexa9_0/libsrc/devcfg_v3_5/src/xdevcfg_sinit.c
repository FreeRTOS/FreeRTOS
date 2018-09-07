/******************************************************************************
*
* Copyright (C) 2010 - 2017 Xilinx, Inc.  All rights reserved.
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
* @file xdevcfg_sinit.c
* @addtogroup devcfg_v3_5
* @{
*
* This file contains method for static initialization (compile-time) of the
* driver.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a hvm 02/07/11 First release
* 3.5   ms  08/07/17 Fixed compilation warnings.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xdevcfg.h"
#include "xparameters.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/*****************************************************************************/
/**
* Lookup the device configuration based on the unique device ID. The table
* contains the configuration info for each device in the system.
*
* @param	DeviceId is the unique device ID of the device being looked up.
*
* @return	A pointer to the configuration table entry corresponding to the
*		given device ID, or NULL if no match is found.
*
* @note		None.
*
******************************************************************************/
XDcfg_Config *XDcfg_LookupConfig(u16 DeviceId)
{
	extern XDcfg_Config XDcfg_ConfigTable[];
	XDcfg_Config *CfgPtr = NULL;
	u32 Index;

	for (Index = 0U; Index < XPAR_XDCFG_NUM_INSTANCES; Index++) {
		if (XDcfg_ConfigTable[Index].DeviceId == DeviceId) {
			CfgPtr = &XDcfg_ConfigTable[Index];
			break;
		}
	}

	return (CfgPtr);
}
/** @} */
