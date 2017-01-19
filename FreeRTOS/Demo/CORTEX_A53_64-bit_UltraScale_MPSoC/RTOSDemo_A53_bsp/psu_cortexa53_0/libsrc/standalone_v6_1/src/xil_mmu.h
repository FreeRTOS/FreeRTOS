/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc. All rights reserved.
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
* @file xil_mmu.h
*
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 5.00 	pkp  05/29/14 First release
* </pre>
*
* @note
*
* None.
*
******************************************************************************/

#ifndef XIL_MMU_H
#define XIL_MMU_H

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

/***************************** Include Files *********************************/

#include "xil_types.h"

/***************** Macros (Inline Functions) Definitions *********************/

/**************************** Type Definitions *******************************/

/************************** Constant Definitions *****************************/

/* Memory type */
#define NORM_NONCACHE 0x401UL 	/* Normal Non-cacheable*/
#define STRONG_ORDERED 0x409UL	/* Strongly ordered (Device-nGnRnE)*/
#define DEVICE_MEMORY 0x40DUL	/* Device memory (Device-nGnRE)*/
#define RESERVED 0x0UL			/* reserved memory*/

/* Normal write-through cacheable inner shareable*/
#define NORM_WT_CACHE 0x711UL

/* Normal write back cacheable inner-shareable */
#define NORM_WB_CACHE 0x705UL

/*
 * shareability attribute only applicable to
 * normal cacheable memory
 */
#define INNER_SHAREABLE (0x3 << 8)
#define OUTER_SHAREABLE (0x2 << 8)
#define NON_SHAREABLE	(~(0x3 << 8))

/* Execution type */
#define EXECUTE_NEVER ((0x1 << 53) | (0x1 << 54))

/* Security type */
#define NON_SECURE	(0x1 << 5)

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

void Xil_SetTlbAttributes(INTPTR Addr, u64 attrib);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* XIL_MMU_H */
