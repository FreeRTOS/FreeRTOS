/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xplatform_info.c
*
* This file contains information about hardware for which the code is built
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date   Changes
* ----- ---- -------- -------------------------------------------------------
* 5.00  pkp  12/15/14 Initial release
* 5.04  pkp  01/12/16 Added platform information support for Cortex-A53 32bit
*					  mode
* 6.00  mus  17/08/16 Removed unused variable from XGetPlatform_Info
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_io.h"
#include "xplatform_info.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Variable Definitions *****************************/


/************************** Function Prototypes ******************************/

/*****************************************************************************/
/**
*
* This API is used to provide information about platform
*
* @param    None.
*
* @return   The information about platform defined in xplatform_info.h
*
* @note     None.
*
******************************************************************************/
u32 XGetPlatform_Info()
{

#if defined (ARMR5) || (__aarch64__) || (ARMA53_32)
	return XPLAT_ZYNQ_ULTRA_MP;
#elif (__microblaze__)
	return XPLAT_MICROBLAZE;
#else
	return XPLAT_ZYNQ;
#endif
}

/*****************************************************************************/
/**
*
* This API is used to provide information about zynq ultrascale MP platform
*
* @param    None.
*
* @return   The information about zynq ultrascale MP platform defined in
*			xplatform_info.h
*
* @note     None.
*
******************************************************************************/
#if defined (ARMR5) || (__aarch64__) || (ARMA53_32)
u32 XGet_Zynq_UltraMp_Platform_info()
{
	u32 reg;
	reg = ((Xil_In32(XPAR_CSU_BASEADDR + XPAR_CSU_VER_OFFSET) >> 12U )& XPLAT_INFO_MASK);
	return reg;
}
#endif

/*****************************************************************************/
/**
*
* This API is used to provide information about PS Silicon version
*
* @param    None.
*
* @return   The information about PS Silicon version.
*
* @note     None.
*
******************************************************************************/
#if defined (ARMR5) || (__aarch64__) || (ARMA53_32)
u32 XGetPSVersion_Info()
{
	u32 reg;
	reg = (Xil_In32(XPAR_CSU_BASEADDR + XPAR_CSU_VER_OFFSET)
			& XPS_VERSION_INFO_MASK);
	return reg;
}
#endif
