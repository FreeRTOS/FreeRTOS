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
*
* @file xpseudo_asm.h
*
* @addtogroup r5_specific Cortex R5 Processor Specific Include Files
*
* The xpseudo_asm.h includes xreg_cortexr5.h and xpseudo_asm_gcc.h.
*
* The xreg_cortexr5.h file contains definitions for inline assembler code.
* It provides inline definitions for Cortex R5 GPRs, SPRs,co-processor
* registers and Debug register
*
* The xpseudo_asm_gcc.h contains the definitions for the most often used
* inline assembler instructions, available as macros. These can be very
* useful for tasks such as setting or getting special purpose registers,
* synchronization,or cache manipulation. These inline assembler instructions
* can be used from drivers and user applications written in C.
*
* @{
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 5.00  pkp  02/10/14 Initial version
* 6.2   mus  01/27/17 Updated to support IAR compiler
* </pre>
*
******************************************************************************/
#ifndef XPSEUDO_ASM_H /* prevent circular inclusions */
#define XPSEUDO_ASM_H /* by using protection macros */

#include "xreg_cortexr5.h"
#if defined (__GNUC__)
#include "xpseudo_asm_gcc.h"
#elif defined (__ICCARM__)
#include "xpseudo_asm_iccarm.h"
#endif
#endif /* XPSEUDO_ASM_H */
/**
* @} End of "addtogroup r5_specific".
*/