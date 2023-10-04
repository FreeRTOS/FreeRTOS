/******************************************************************************
*
* Copyright (C) 2015 - 2016 Xilinx, Inc.  All rights reserved.
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
 * This header file contains ARM Cortex A53,A9,R5 specific exception related APIs.
 * For exception related functions that can be used across all Xilinx supported
 * processors, please use xil_exception.h.
 *
 * @addtogroup arm_exception_apis ARM Processor Exception Handling
 * @{
 * ARM processors specific exception related APIs for cortex A53,A9 and R5 can
 * utilized for enabling/disabling IRQ, registering/removing handler for
 * exceptions or initializing exception vector table with null handler.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who      Date     Changes
 * ----- -------- -------- -----------------------------------------------
 * 5.2	pkp      28/05/15 First release
 * 6.0   mus      27/07/16 Consolidated file for a53,a9 and r5 processors
 * </pre>
 *
 ******************************************************************************/

#ifndef XIL_EXCEPTION_H     /* prevent circular inclusions */
    #define XIL_EXCEPTION_H /* by using protection macros */

/***************************** Include Files ********************************/

    #include "xil_types.h"
    #include "xpseudo_asm.h"

    #ifdef __cplusplus
    extern "C" {
    #endif

/************************** Constant Definitions ****************************/

    #define XIL_EXCEPTION_FIQ                          XREG_CPSR_FIQ_ENABLE
    #define XIL_EXCEPTION_IRQ                          XREG_CPSR_IRQ_ENABLE
    #define XIL_EXCEPTION_ALL                          ( XREG_CPSR_FIQ_ENABLE | XREG_CPSR_IRQ_ENABLE )

    #define XIL_EXCEPTION_ID_FIRST                     0U
    #if defined( __aarch64__ )
        #define XIL_EXCEPTION_ID_SYNC_INT              1U
        #define XIL_EXCEPTION_ID_IRQ_INT               2U
        #define XIL_EXCEPTION_ID_FIQ_INT               3U
        #define XIL_EXCEPTION_ID_SERROR_ABORT_INT      4U
        #define XIL_EXCEPTION_ID_LAST                  5U
    #else
        #define XIL_EXCEPTION_ID_RESET                 0U
        #define XIL_EXCEPTION_ID_UNDEFINED_INT         1U
        #define XIL_EXCEPTION_ID_SWI_INT               2U
        #define XIL_EXCEPTION_ID_PREFETCH_ABORT_INT    3U
        #define XIL_EXCEPTION_ID_DATA_ABORT_INT        4U
        #define XIL_EXCEPTION_ID_IRQ_INT               5U
        #define XIL_EXCEPTION_ID_FIQ_INT               6U
        #define XIL_EXCEPTION_ID_LAST                  6U
    #endif /* if defined( __aarch64__ ) */

/*
 * XIL_EXCEPTION_ID_INT is defined for all Xilinx processors.
 */
    #define XIL_EXCEPTION_ID_INT    XIL_EXCEPTION_ID_IRQ_INT

/**************************** Type Definitions ******************************/

/**
 * This typedef is the exception handler function.
 */
    typedef void (* Xil_ExceptionHandler)( void * data );
    typedef void (* Xil_InterruptHandler)( void * data );

/***************** Macros (Inline Functions) Definitions ********************/

/****************************************************************************/

/**
 * @brief	Enable Exceptions.
 *
 * @param	Mask: Value for enabling the exceptions.
 *
 * @return	None.
 *
 * @note		If bit is 0, exception is enabled.
 *			C-Style signature: void Xil_ExceptionEnableMask(Mask)
 *
 ******************************************************************************/
    #if defined( __GNUC__ ) || defined( __ICCARM__ )
        #define Xil_ExceptionEnableMask( Mask ) \
    mtcpsr( mfcpsr() & ~( ( Mask ) & XIL_EXCEPTION_ALL ) )
    #else
        #define Xil_ExceptionEnableMask( Mask )                    \
    {                                                              \
        register u32 Reg __asm( "cpsr" );                          \
        mtcpsr( ( Reg ) & ( ~( ( Mask ) & XIL_EXCEPTION_ALL ) ) ); \
    }
    #endif
/****************************************************************************/

/**
 * @brief	Enable the IRQ exception.
 *
 * @return   None.
 *
 * @note     None.
 *
 ******************************************************************************/
    #define Xil_ExceptionEnable() \
    Xil_ExceptionEnableMask( XIL_EXCEPTION_IRQ )

/****************************************************************************/

/**
 * @brief	Disable Exceptions.
 *
 * @param	Mask: Value for disabling the exceptions.
 *
 * @return	None.
 *
 * @note		If bit is 1, exception is disabled.
 *			C-Style signature: Xil_ExceptionDisableMask(Mask)
 *
 ******************************************************************************/
    #if defined( __GNUC__ ) || defined( __ICCARM__ )
        #define Xil_ExceptionDisableMask( Mask ) \
    mtcpsr( mfcpsr() | ( ( Mask ) & XIL_EXCEPTION_ALL ) )
    #else
        #define Xil_ExceptionDisableMask( Mask )              \
    {                                                         \
        register u32 Reg __asm( "cpsr" );                     \
        mtcpsr( ( Reg ) | ( ( Mask ) & XIL_EXCEPTION_ALL ) ); \
    }
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
    Xil_ExceptionDisableMask( XIL_EXCEPTION_IRQ )

    #if !defined( __aarch64__ ) && !defined( ARMA53_32 )
/****************************************************************************/

/**
 * @brief	Enable nested interrupts by clearing the I and F bits in CPSR. This
 *          API is defined for cortex-a9 and cortex-r5.
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
        #define Xil_EnableNestedInterrupts()          \
    __asm__ __volatile__ ( "stmfd   sp!, {lr}" );     \
    __asm__ __volatile__ ( "mrs     lr, spsr" );      \
    __asm__ __volatile__ ( "stmfd   sp!, {lr}" );     \
    __asm__ __volatile__ ( "msr     cpsr_c, #0x1F" ); \
    __asm__ __volatile__ ( "stmfd   sp!, {lr}" );

/****************************************************************************/

/**
 * @brief	Disable the nested interrupts by setting the I and F bits. This API
 *			is defined for cortex-a9 and cortex-r5.
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
        #define Xil_DisableNestedInterrupts()         \
    __asm__ __volatile__ ( "ldmfd   sp!, {lr}" );     \
    __asm__ __volatile__ ( "msr     cpsr_c, #0x92" ); \
    __asm__ __volatile__ ( "ldmfd   sp!, {lr}" );     \
    __asm__ __volatile__ ( "msr     spsr_cxsf, lr" ); \
    __asm__ __volatile__ ( "ldmfd   sp!, {lr}" );     \

    #endif /* if !defined( __aarch64__ ) && !defined( ARMA53_32 ) */
/************************** Variable Definitions ****************************/

/************************** Function Prototypes *****************************/

    extern void Xil_ExceptionRegisterHandler( u32 Exception_id,
                                              Xil_ExceptionHandler Handler,
                                              void * Data );

    extern void Xil_ExceptionRemoveHandler( u32 Exception_id );

    extern void Xil_ExceptionInit( void );
    #if defined( __aarch64__ )
        void Xil_SyncAbortHandler( void * CallBackRef );
        void Xil_SErrorAbortHandler( void * CallBackRef );
    #else
        extern void Xil_DataAbortHandler( void * CallBackRef );
        extern void Xil_PrefetchAbortHandler( void * CallBackRef );
        extern void Xil_UndefinedExceptionHandler( void * CallBackRef );
    #endif

    #ifdef __cplusplus
}
    #endif /* __cplusplus */

#endif /* XIL_EXCEPTION_H */

/**
 * @} End of "addtogroup arm_exception_apis".
 */
