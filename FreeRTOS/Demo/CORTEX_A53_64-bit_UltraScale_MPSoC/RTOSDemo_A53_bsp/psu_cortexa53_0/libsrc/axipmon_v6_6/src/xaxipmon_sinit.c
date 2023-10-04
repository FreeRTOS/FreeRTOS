/******************************************************************************
*
* Copyright (C) 2012 - 2015 Xilinx, Inc.  All rights reserved.
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
 * @file xaxipmon_sinit.c
 * @addtogroup axipmon_v6_6
 * @{
 *
 * This file contains the implementation of the XAxiPmon driver's static
 * initialization functionality.
 *
 * @note	None.
 *
 * <pre>
 *
 * MODIFICATION HISTORY:
 *
 * Ver   Who    Date     Changes
 * ----- -----  -------- -----------------------------------------------------
 * 1.00a bss  02/27/12 First release
 * 2.00a bss  06/23/12 Updated to support v2_00a version of IP.
 * 6.3   kvn  07/02/15 Modified code according to MISRA-C:2012 guidelines.
 * </pre>
 *
 ******************************************************************************/

/***************************** Include Files *********************************/

#include "xparameters.h"
#include "xaxipmon.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/
extern XAxiPmon_Config XAxiPmon_ConfigTable[];

/*****************************************************************************/

/**
 *
 * This function looks up the device configuration based on the unique device ID.
 * The table XAxiPmon_ConfigTable contains the configuration info for each device
 * in the system.
 *
 * @param	DeviceId contains the ID of the device for which the
 *		device configuration pointer is to be returned.
 *
 * @return
 *		- A pointer to the configuration found.
 *		- NULL if the specified device ID was not found.
 *
 * @note		None.
 *
 ******************************************************************************/
XAxiPmon_Config * XAxiPmon_LookupConfig( u16 DeviceId )
{
    XAxiPmon_Config * CfgPtr = NULL;
    u32 Index;

    for( Index = 0U; Index < ( u32 ) XPAR_XAXIPMON_NUM_INSTANCES; Index++ )
    {
        if( XAxiPmon_ConfigTable[ Index ].DeviceId == DeviceId )
        {
            CfgPtr = &XAxiPmon_ConfigTable[ Index ];
            break;
        }
    }

    return ( XAxiPmon_Config * ) CfgPtr;
}
/** @} */
