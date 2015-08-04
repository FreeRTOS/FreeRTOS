/******************************************************************************
*
* Copyright (C) 2012 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file microblaze_exceptions_i.h
*
* This header file contains defines for structures used by the microblaze
* hardware exception handler.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Date     Changes
* ----- -------- -----------------------------------------------
* 1.00a 06/24/04 First release
* </pre>
*
******************************************************************************/

#ifndef MICROBLAZE_EXCEPTIONS_I_H /* prevent circular inclusions */
#define MICROBLAZE_EXCEPTIONS_I_H /* by using protection macros */

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_exception.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct
{
   Xil_ExceptionHandler Handler;
   void *CallBackRef;
} MB_ExceptionVectorTableEntry;

/* Exception IDs */
#define XEXC_ID_FSL                     0
#define XEXC_ID_UNALIGNED_ACCESS        1
#define XEXC_ID_ILLEGAL_OPCODE          2
#define XEXC_ID_M_AXI_I_EXCEPTION       3
#define XEXC_ID_IPLB_EXCEPTION          3
#define XEXC_ID_M_AXI_D_EXCEPTION       4
#define XEXC_ID_DPLB_EXCEPTION          4
#define XEXC_ID_DIV_BY_ZERO             5
#define XEXC_ID_FPU                     6
#define XEXC_ID_STACK_VIOLATION         7
#define XEXC_ID_MMU                     7

void microblaze_register_exception_handler(u32 ExceptionId, Xil_ExceptionHandler Handler, void *DataPtr);

#ifdef __cplusplus
}
#endif
#endif /* end of protection macro */
