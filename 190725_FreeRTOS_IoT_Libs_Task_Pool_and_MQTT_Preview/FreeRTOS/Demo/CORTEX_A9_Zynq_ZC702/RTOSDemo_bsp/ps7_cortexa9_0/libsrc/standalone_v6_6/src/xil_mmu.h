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
* @file xil_mmu.h
*
* @addtogroup a9_mmu_apis Cortex A9 Processor MMU Functions
*
* MMU functions equip users to enable MMU, disable MMU and modify default
* memory attributes of MMU table as per the need.
*
* @{
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 1.00a sdm  01/12/12 Initial version
* 4.2	pkp	 07/21/14 Included xil_types.h file which contains definition for
*					  u32 which resolves issue of CR#805869
* 5.4	pkp	 23/11/15 Added attribute definitions for Xil_SetTlbAttributes API
* </pre>
*
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
#define NORM_NONCACHE 0x11DE2 	/* Normal Non-cacheable */
#define STRONG_ORDERED 0xC02	/* Strongly ordered */
#define DEVICE_MEMORY 0xC06		/* Device memory */
#define RESERVED 0x0			/* reserved memory */

/* Normal write-through cacheable shareable */
#define NORM_WT_CACHE 0x16DEA

/* Normal write back cacheable shareable */
#define NORM_WB_CACHE 0x15DE6

/* shareability attribute */
#define SHAREABLE (0x1 << 16)
#define NON_SHAREABLE	(~(0x1 << 16))

/* Execution type */
#define EXECUTE_NEVER ((0x1 << 4) | (0x1 << 0))

/************************** Variable Definitions *****************************/

/************************** Function Prototypes ******************************/

void Xil_SetTlbAttributes(INTPTR Addr, u32 attrib);
void Xil_EnableMMU(void);
void Xil_DisableMMU(void);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* XIL_MMU_H */
/**
* @} End of "addtogroup a9_mmu_apis".
*/