/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
 * @file xscuwdt_sinit.c
 * @addtogroup scuwdt_v2_1
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
 * 1.00a sdm 01/15/10 First release
 * 2.1  sk  02/26/15 Modified the code for MISRA-C:2012 compliance.
 * </pre>
 *
 ******************************************************************************/

/***************************** Include Files *********************************/

#include "xscuwdt.h"
#include "xparameters.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/
extern XScuWdt_Config XScuWdt_ConfigTable[ XPAR_XSCUWDT_NUM_INSTANCES ];

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
XScuWdt_Config * XScuWdt_LookupConfig( u16 DeviceId )
{
    XScuWdt_Config * CfgPtr = NULL;
    u32 Index;

    for( Index = 0U; Index < XPAR_XSCUWDT_NUM_INSTANCES; Index++ )
    {
        if( XScuWdt_ConfigTable[ Index ].DeviceId == DeviceId )
        {
            CfgPtr = &XScuWdt_ConfigTable[ Index ];
            break;
        }
    }

    return ( XScuWdt_Config * ) CfgPtr;
}
/** @} */
