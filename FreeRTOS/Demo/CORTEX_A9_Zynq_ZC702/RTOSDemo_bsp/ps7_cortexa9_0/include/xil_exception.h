/******************************************************************************
*
* (c) Copyright 2009-13  Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xil_exception.h
*
* This header file contains ARM Cortex A9 specific exception related APIs.
* For exception related functions that can be used across all Xilinx supported
* processors, please use xil_exception.h.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who      Date     Changes
* ----- -------- -------- -----------------------------------------------
* 1.00a ecm/sdm  11/04/09 First release
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

#define XIL_EXCEPTION_ID_FIRST			0
#define XIL_EXCEPTION_ID_RESET			0
#define XIL_EXCEPTION_ID_UNDEFINED_INT		1
#define XIL_EXCEPTION_ID_SWI_INT		2
#define XIL_EXCEPTION_ID_PREFETCH_ABORT_INT	3
#define XIL_EXCEPTION_ID_DATA_ABORT_INT		4
#define XIL_EXCEPTION_ID_IRQ_INT		5
#define XIL_EXCEPTION_ID_FIQ_INT		6
#define XIL_EXCEPTION_ID_LAST			6

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
*		C-Style signature: void Xil_ExceptionEnableMask(Mask);
*
******************************************************************************/
#ifdef __GNUC__
#define Xil_ExceptionEnableMask(Mask)	\
		mtcpsr(mfcpsr() & ~ (Mask & XIL_EXCEPTION_ALL))
#else
#define Xil_ExceptionEnableMask(Mask)	\
		{ register unsigned int Reg __asm("cpsr"); \
		  mtcpsr(Reg & ~ (Mask & XIL_EXCEPTION_ALL)) }
#endif

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
*		C-Style signature: Xil_ExceptionDisableMask(Mask);
*
******************************************************************************/
#ifdef __GNUC__
#define Xil_ExceptionDisableMask(Mask)	\
		mtcpsr(mfcpsr() | (Mask & XIL_EXCEPTION_ALL))
#else
#define Xil_ExceptionDisableMask(Mask)	\
		{ register unsigned int Reg __asm("cpsr"); \
		  mtcpsr(Reg | (Mask & XIL_EXCEPTION_ALL)) }
#endif

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

/****************************************************************************/
/**
* Enable nested interrupts by clearing the I and F bits it CPSR
*
* @return   None.
*
* @note     This macro is supposed to be used from interrupt handlers. In the
*			interrupt handler the interrupts are disabled by default (I and F
*			are 1). To allow nesting of interrupts, this macro should be
*			used. It clears the I and F bits by changing the ARM mode to
*			system mode. Once these bits are cleared and provided the
*			preemption of interrupt conditions are met in the GIC, nesting of
*			interrupts will start happening.
*			Caution: This macro must be used with caution. Before calling this
*			macro, the user must ensure that the source of the current IRQ
*			is appropriately cleared. Otherwise, as soon as we clear the I and
*			F bits, there can be an infinite loop of interrupts with an
*			eventual crash (all the stack space getting consumed).
******************************************************************************/
#define Xil_EnableNestedInterrupts() \
		__asm__ __volatile__ ("mrs     lr, spsr");  \
		__asm__ __volatile__ ("stmfd   sp!, {lr}"); \
		__asm__ __volatile__ ("msr     cpsr_c, #0x1F"); \
		__asm__ __volatile__ ("stmfd   sp!, {lr}");

/****************************************************************************/
/**
* Disable the nested interrupts by setting the I and F bits.
*
* @return   None.
*
* @note     This macro is meant to be called in the interrupt service routines.
*			This macro cannot be used independently. It can only be used when
*			nesting of interrupts have been enabled by using the macro
*			Xil_EnableNestedInterrupts(). In a typical flow, the user first
*			calls the Xil_EnableNestedInterrupts in the ISR at the appropriate
*			point. The user then must call this macro before exiting the interrupt
*			service routine. This macro puts the ARM back in IRQ/FIQ mode and
*			hence sets back the I and F bits.
******************************************************************************/
#define Xil_DisableNestedInterrupts() \
		__asm__ __volatile__ ("ldmfd   sp!, {lr}");   \
		__asm__ __volatile__ ("msr     cpsr_c, #0x92"); \
		__asm__ __volatile__ ("ldmfd   sp!, {lr}"); \
		__asm__ __volatile__ ("msr     spsr_cxsf, lr");

/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/

extern void Xil_ExceptionRegisterHandler(u32 id,
					 Xil_ExceptionHandler handler,
					 void *data);

extern void Xil_ExceptionRemoveHandler(u32 id);

extern void Xil_ExceptionInit(void);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* XIL_EXCEPTION_H */
