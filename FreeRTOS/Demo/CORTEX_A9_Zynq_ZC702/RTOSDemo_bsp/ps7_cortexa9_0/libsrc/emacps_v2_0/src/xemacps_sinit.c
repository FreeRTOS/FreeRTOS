/* $Id: xemacps_sinit.c,v 1.1.2.1 2011/01/20 03:39:02 sadanan Exp $ */
/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xemacps_sinit.c
*
* This file contains lookup method by device ID when success, it returns
* pointer to config table to be used to initialize the device.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a wsy  01/10/10 New
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xparameters.h"
#include "xemacps.h"

/************************** Constant Definitions *****************************/


/**************************** Type Definitions *******************************/


/***************** Macros (Inline Functions) Definitions *********************/


/************************** Function Prototypes ******************************/

/*****************************************************************************/
/**
* Lookup the device configuration based on the unique device ID.  The table
* contains the configuration info for each device in the system.
*
* @param DeviceId is the unique device ID of the device being looked up.
*
* @return
* A pointer to the configuration table entry corresponding to the given
* device ID, or NULL if no match is found.
*
******************************************************************************/
XEmacPs_Config *XEmacPs_LookupConfig(u16 DeviceId)
{
	extern XEmacPs_Config XEmacPs_ConfigTable[];
	XEmacPs_Config *CfgPtr = NULL;
	int i;

	for (i = 0; i < XPAR_XEMACPS_NUM_INSTANCES; i++) {
		if (XEmacPs_ConfigTable[i].DeviceId == DeviceId) {
			CfgPtr = &XEmacPs_ConfigTable[i];
			break;
		}
	}

	return (CfgPtr);
}
