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
* @file xplatform_info.h
*
* This file contains definitions for various platforms available
*
******************************************************************************/

#ifndef XPLATFORM_INFO_H		/* prevent circular inclusions */
#define XPLATFORM_INFO_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"

/************************** Constant Definitions *****************************/

#define XPAR_CSU_BASEADDR 0xFFCA0000U
#define	XPAR_CSU_VER_OFFSET 0x00000044U

#define XPLAT_ZYNQ_ULTRA_MP 0x1
#define XPLAT_ZYNQ_ULTRA_MPVEL 0x2
#define XPLAT_ZYNQ_ULTRA_MPQEMU 0x3
#define XPLAT_ZYNQ 0x4
#define XPLAT_MICROBLAZE 0x5

#define XPLAT_INFO_MASK (0xF)
/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/


u32 XGetPlatform_Info();

#if defined (ARMR5) || (__aarch64__)
u32 XGet_Zynq_UltraMp_Platform_info();
#endif
/************************** Function Prototypes ******************************/


#ifdef __cplusplus
}
#endif

#endif /* end of protection macro */
