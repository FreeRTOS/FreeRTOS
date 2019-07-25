/******************************************************************************
*
* Copyright (C) 2015 Xilinx, Inc.  All rights reserved.
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
* @file xtmrctr_sinit.c
* @addtogroup tmrctr_v4_0
* @{
*
* This file contains static initialization methods for the XTmrCtr driver.
*
* @note	None.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 4.0   als  09/30/15 Creation of this file. Moved LookupConfig from xtmrctr.c.
* </pre>
*
******************************************************************************/

/******************************* Include Files *******************************/

#include "xparameters.h"
#include "xtmrctr.h"

/************************** Constant Definitions *****************************/

#ifndef XPAR_XTMRCTR_NUM_INSTANCES
#define XPAR_XTMRCTR_NUM_INSTANCES	0
#endif

/*************************** Variable Declarations ***************************/

/* A table of configuration structures containing the configuration information
 * for each timer core in the system. */
extern XTmrCtr_Config XTmrCtr_ConfigTable[XPAR_XTMRCTR_NUM_INSTANCES];

/**************************** Function Definitions ***************************/

/*****************************************************************************/
/**
* Looks up the device configuration based on the unique device ID. The table
* TmrCtr_ConfigTable contains the configuration info for each device in the
* system.
*
* @param	DeviceId is the unique device ID to search for in the config
*		table.
*
* @return	A pointer to the configuration that matches the given device
* 		ID, or NULL if no match is found.
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

/** @} */
