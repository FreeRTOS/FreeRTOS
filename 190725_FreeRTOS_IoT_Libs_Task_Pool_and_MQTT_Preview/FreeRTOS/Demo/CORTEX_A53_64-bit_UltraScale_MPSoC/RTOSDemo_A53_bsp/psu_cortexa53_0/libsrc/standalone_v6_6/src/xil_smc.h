/******************************************************************************
*
* Copyright (C) 2017 Xilinx, Inc. All rights reserved.
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
* @file xil_smc.h
*
* @addtogroup a53_64_smc_api Cortex A53 64bit EL1 Non-secure SMC Call
*
* Cortex A53 64bit EL1 Non-secure SMC Call provides a C wrapper for calling
* SMC from EL1 Non-secure application to request Secure monitor for secure
* services. SMC calling conventions should be followed.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who      Date     Changes
* ----- -------- -------- -----------------------------------------------
* 6.2 	pkp  	 02/16/17 First release
* 6.4   mus      08/17/17 Added constant define for SMC ID , which is
*                         intended to read the version/idcode of the
*                         platform
*
*
* </pre>
*
******************************************************************************/

#ifndef XIL_SMC_H /* prevent circular inclusions */
#define XIL_SMC_H /* by using protection macros */

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "bspconfig.h"

#ifdef __cplusplus
extern "C" {
#endif
#if EL1_NONSECURE
/************************** Constant Definitions ****************************/
#define SMC_FID_START	0xF2000000
#define SMC_FID_END	0xFF00FFFF

#define XILSP_INIT_DONE 0xF2000000
#define	ARITH_SMC_FID	0xF2000001

#define PM_ASSERT_SMC_FID       0xC2000011
#define PM_GETSTATUS_SMC_FID    0xC2000012
#define MMIO_WRITE_SMC_FID	0xC2000013
#define MMIO_READ_SMC_FID	0xC2000014
#define GET_CHIPID_SMC_FID      0xC2000018
/**************************** Type Definitions ******************************/
typedef struct {
	u64 Arg0;
	u64 Arg1;
	u64 Arg2;
	u64 Arg3;
} XSmc_OutVar;
/***************** Macros (Inline Functions) Definitions ********************/

#define XSave_X8toX17() \
	__asm__ __volatile__ ("stp X8, X9, [sp,#-0x10]!");\
	__asm__ __volatile__ ("stp X10, X11, [sp,#-0x10]!");\
	__asm__ __volatile__ ("stp X12, X13, [sp,#-0x10]!");\
	__asm__ __volatile__ ("stp X14, X15, [sp,#-0x10]!");\
	__asm__ __volatile__ ("stp X16, X17, [sp,#-0x10]!");

#define XRestore_X8toX17() \
	__asm__ __volatile__ ("ldp X16, X17, [sp], #0x10");\
	__asm__ __volatile__ ("ldp X14, X15, [sp], #0x10");\
	__asm__ __volatile__ ("ldp X12, X13, [sp], #0x10");\
	__asm__ __volatile__ ("ldp X10, X11, [sp], #0x10");\
	__asm__ __volatile__ ("ldp X8, X9, [sp], #0x10");

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/
XSmc_OutVar Xil_Smc(u64 FunctionID, u64 Arg1, u64 Arg2, u64 Arg3, u64 Arg4,
					u64 Arg5, u64 Arg6, u64 Arg7);
#endif
#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* XIL_SMC_H */
/**
* @} End of "addtogroup a53_64_smc_api".
*/
