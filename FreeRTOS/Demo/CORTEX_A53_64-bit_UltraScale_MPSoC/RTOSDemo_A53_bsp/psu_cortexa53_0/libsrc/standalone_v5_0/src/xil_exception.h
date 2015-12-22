/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc. All rights reserved.
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
* @file xil_exception.h
*
* This header file contains ARM Cortex A53 specific exception related APIs.
* For exception related functions that can be used across all Xilinx supported
* processors, please use xil_exception.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who      Date     Changes
* ----- -------- -------- -----------------------------------------------
* 5.00 	pkp  05/29/14 First release
* </pre>
*
******************************************************************************/

#ifndef XIL_EXCEPTION_H /* prevent circular inclusions */
#define XIL_EXCEPTION_H /* by using protection macros */

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xpseudo_asm.h"

#ifdef __cplusplus
extern "C" {
#endif

/************************** Constant Definitions ****************************/

#define XIL_EXCEPTION_FIQ	XREG_CPSR_FIQ_ENABLE
#define XIL_EXCEPTION_IRQ	XREG_CPSR_IRQ_ENABLE
#define XIL_EXCEPTION_ALL	(XREG_CPSR_FIQ_ENABLE | XREG_CPSR_IRQ_ENABLE)

#define XIL_EXCEPTION_ID_FIRST			0U
#define XIL_EXCEPTION_ID_SYNC_INT		1U
#define XIL_EXCEPTION_ID_IRQ_INT		2U
#define XIL_EXCEPTION_ID_FIQ_INT		3U
#define XIL_EXCEPTION_ID_SERROR_ABORT_INT		4U
#define XIL_EXCEPTION_ID_LAST			5U

/*
 * XIL_EXCEPTION_ID_INT is defined for all Xilinx processors.
 */
#define XIL_EXCEPTION_ID_INT	XIL_EXCEPTION_ID_IRQ_INT

/**************************** Type Definitions ******************************/

/**
 * This typedef is the exception handler function.
 */
typedef void (*Xil_ExceptionHandler)(void *data);
typedef void (*Xil_InterruptHandler)(void *data);

/***************** Macros (Inline Functions) Definitions ********************/

/****************************************************************************/
/**
* Enable Exceptions.
*
* @param	Mask for exceptions to be enabled.
*
* @return	None.
*
* @note		If bit is 0, exception is enabled.
*		C-Style signature: void Xil_ExceptionEnableMask(Mask)
*
******************************************************************************/

#define Xil_ExceptionEnableMask(Mask)	\
		mtcpsr(mfcpsr() & ~ ((Mask) & XIL_EXCEPTION_ALL))

/****************************************************************************/
/**
* Enable the IRQ exception.
*
* @return   None.
*
* @note     None.
*
******************************************************************************/
#define Xil_ExceptionEnable() \
		Xil_ExceptionEnableMask(XIL_EXCEPTION_IRQ)

/****************************************************************************/
/**
* Disable Exceptions.
*
* @param	Mask for exceptions to be enabled.
*
* @return	None.
*
* @note		If bit is 1, exception is disabled.
*		C-Style signature: Xil_ExceptionDisableMask(Mask)
*
******************************************************************************/

#define Xil_ExceptionDisableMask(Mask)	\
		mtcpsr(mfcpsr() | ((Mask) & XIL_EXCEPTION_ALL))

/****************************************************************************/
/**
* Disable the IRQ exception.
*
* @return   None.
*
* @note     None.
*
******************************************************************************/
#define Xil_ExceptionDisable() \
		Xil_ExceptionDisableMask(XIL_EXCEPTION_IRQ)


/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/

extern void Xil_ExceptionRegisterHandler(u32 Exception_id,
					 Xil_ExceptionHandler Handler,
					 void *Data);

extern void Xil_ExceptionRemoveHandler(u32 Exception_id);

extern void Xil_ExceptionInit(void);

void Xil_SyncAbortHandler(void *CallBackRef);

void Xil_SErrorAbortHandler(void *CallBackRef);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* XIL_EXCEPTION_H */
