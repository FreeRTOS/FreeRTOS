/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/**
 * @file atomic.h
 * @brief FreeRTOS atomic operation support.
 *
 * Two implementations of atomic are given in this header file:
 * 1. Disabling interrupt globally.
 * 2. ISA native atomic support.
 * The former is available to all ports (compiler-architecture combination),
 * while the latter is only available to ports compiling with GCC (version at
 * least 4.7.0), which also have ISA atomic support.
 *
 * User can select which implementation to use by:
 * setting/clearing configUSE_ATOMIC_INSTRUCTION in FreeRTOSConfig.h.
 * Define AND set configUSE_ATOMIC_INSTRUCTION to 1 for ISA native atomic support.
 * Undefine OR clear configUSE_ATOMIC_INSTRUCTION for disabling global interrupt
 * implementation.
 *
 * @see GCC Built-in Functions for Memory Model Aware Atomic Operations
 *      https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
 */

#ifndef ATOMIC_H
#define ATOMIC_H

#ifndef INC_FREERTOS_H
    #error "include FreeRTOS.h must appear in source files before include atomic.h"
#endif

/* Standard includes. */
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    /* Needed for __atomic_compare_exchange() weak=false. */
    #include <stdbool.h>

    /* This branch is for GCC compiler and GCC compiler only. */
    #ifndef portFORCE_INLINE
        #define portFORCE_INLINE  inline __attribute__((always_inline))
    #endif

#else

    /* Port specific definitions -- entering/exiting critical section.
     * Refer template -- ./lib/FreeRTOS/portable/Compiler/Arch/portmacro.h
     *
     * Every call to ATOMIC_EXIT_CRITICAL() must be closely paired with
     * ATOMIC_ENTER_CRITICAL().
     */
    #if defined( portSET_INTERRUPT_MASK_FROM_ISR )

        /* Nested interrupt scheme is supported in this port. */
        #define ATOMIC_ENTER_CRITICAL()     \
            UBaseType_t uxCriticalSectionType = portSET_INTERRUPT_MASK_FROM_ISR()

        #define ATOMIC_EXIT_CRITICAL()      \
            portCLEAR_INTERRUPT_MASK_FROM_ISR( uxCriticalSectionType )

    #else

        /* Nested interrupt scheme is NOT supported in this port. */
        #define ATOMIC_ENTER_CRITICAL()     portENTER_CRITICAL()
        #define ATOMIC_EXIT_CRITICAL()      portEXIT_CRITICAL()

    #endif /* portSET_INTERRUPT_MASK_FROM_ISR() */

    /* Port specific definition -- "always inline". 
     * Inline is compiler specific, and may not always get inlined depending on your optimization level. 
     * Also, inline is considered as performance optimization for atomic. 
     * Thus, if portFORCE_INLINE is not provided by portmacro.h, instead of resulting error,
     * simply define it. 
     */
    #ifndef portFORCE_INLINE
        #define portFORCE_INLINE 
    #endif

#endif /* configUSE_GCC_BUILTIN_ATOMICS */

#define ATOMIC_COMPARE_AND_SWAP_SUCCESS     0x1U        /**< Compare and swap succeeded, swapped. */
#define ATOMIC_COMPARE_AND_SWAP_FAILURE     0x0U        /**< Compare and swap failed, did not swap. */

/*----------------------------- Swap && CAS ------------------------------*/

/**
 * Atomic compare-and-swap
 *
 * @brief Performs an atomic compare-and-swap operation on the specified values.
 *
 * @param[in, out] pDestination  Pointer to memory location from where value is
 *                               to be loaded and checked.
 * @param[in] ulExchange         If condition meets, write this value to memory.
 * @param[in] ulComparand        Swap condition.
 *
 * @return Unsigned integer of value 1 or 0. 1 for swapped, 0 for not swapped.
 *
 * @note This function only swaps *pDestination with ulExchange, if previous
 *       *pDestination value equals ulComparand.
 */
static portFORCE_INLINE uint32_t Atomic_CompareAndSwap_u32(
        uint32_t volatile * pDestination,
        uint32_t ulExchange,
        uint32_t ulComparand )
{

    uint32_t ulReturnValue = ATOMIC_COMPARE_AND_SWAP_FAILURE;

#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    if ( __atomic_compare_exchange( pDestination,
                                    &ulComparand,
                                    &ulExchange,
                                    false,
                                    __ATOMIC_SEQ_CST,
                                    __ATOMIC_SEQ_CST ) )
    {
        ulReturnValue = ATOMIC_COMPARE_AND_SWAP_SUCCESS;
    }

#else

    ATOMIC_ENTER_CRITICAL();

    if ( *pDestination == ulComparand )
    {
        *pDestination = ulExchange;
        ulReturnValue = ATOMIC_COMPARE_AND_SWAP_SUCCESS;
    }

    ATOMIC_EXIT_CRITICAL();

#endif

    return ulReturnValue;

}

/**
 * Atomic swap (pointers)
 *
 * @brief Atomically sets the address pointed to by *ppDestination to the value
 *        of *pExchange.
 *
 * @param[in, out] ppDestination  Pointer to memory location from where a pointer
 *                                value is to be loaded and written back to.
 * @param[in] pExchange           Pointer value to be written to *ppDestination.
 *
 * @return The initial value of *ppDestination.
 */
static portFORCE_INLINE void * Atomic_SwapPointers_p32(
        void * volatile * ppDestination,
        void * pExchange )
{
    void * pReturnValue;

#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    __atomic_exchange( ppDestination, &pExchange, &pReturnValue, __ATOMIC_SEQ_CST );

#else

    ATOMIC_ENTER_CRITICAL();

    pReturnValue = *ppDestination;

    *ppDestination = pExchange;

    ATOMIC_EXIT_CRITICAL();

#endif

    return pReturnValue;
}

/**
 * Atomic compare-and-swap (pointers)
 *
 * @brief Performs an atomic compare-and-swap operation on the specified pointer
 *        values.
 *
 * @param[in, out] ppDestination  Pointer to memory location from where a pointer
 *                                value is to be loaded and checked.
 * @param[in] pExchange           If condition meets, write this value to memory.
 * @param[in] pComparand          Swap condition.
 *
 * @return Unsigned integer of value 1 or 0. 1 for swapped, 0 for not swapped.
 *
 * @note This function only swaps *ppDestination with pExchange, if previous
 *       *ppDestination value equals pComparand.
 */
static portFORCE_INLINE uint32_t Atomic_CompareAndSwapPointers_p32(
        void * volatile * ppDestination,
        void * pExchange, void * pComparand )
{
    uint32_t ulReturnValue = ATOMIC_COMPARE_AND_SWAP_FAILURE;

#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )
    if ( __atomic_compare_exchange( ppDestination,
                                    &pComparand,
                                    &pExchange,
                                    false,
                                    __ATOMIC_SEQ_CST,
                                    __ATOMIC_SEQ_CST ) )
    {
        ulReturnValue = ATOMIC_COMPARE_AND_SWAP_SUCCESS;
    }

#else

    ATOMIC_ENTER_CRITICAL();

    if ( *ppDestination == pComparand )
    {
        *ppDestination = pExchange;
        ulReturnValue = ATOMIC_COMPARE_AND_SWAP_SUCCESS;
    }

    ATOMIC_EXIT_CRITICAL();

#endif

    return ulReturnValue;
}


/*----------------------------- Arithmetic ------------------------------*/

/**
 * Atomic add
 *
 * @brief Atomically adds count to the value of the specified pointer points to.
 *
 * @param[in,out] pAddend  Pointer to memory location from where value is to be
 *                         loaded and written back to.
 * @param[in] ulCount      Value to be added to *pAddend.
 *
 * @return previous *pAddend value.
 */
static portFORCE_INLINE uint32_t Atomic_Add_u32(
        uint32_t volatile * pAddend,
        uint32_t ulCount )
{
#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    return __atomic_fetch_add(pAddend, ulCount, __ATOMIC_SEQ_CST);

#else

    uint32_t ulCurrent;

    ATOMIC_ENTER_CRITICAL();

    ulCurrent = *pAddend;

    *pAddend += ulCount;

    ATOMIC_EXIT_CRITICAL();

    return ulCurrent;

#endif
}

/**
 * Atomic subtract
 *
 * @brief Atomically subtracts count from the value of the specified pointer
 *        pointers to.
 *
 * @param[in,out] pAddend  Pointer to memory location from where value is to be
 *                         loaded and written back to.
 * @param[in] ulCount      Value to be subtract from *pAddend.
 *
 * @return previous *pAddend value.
 */
static portFORCE_INLINE uint32_t Atomic_Subtract_u32(
        uint32_t volatile * pAddend,
        uint32_t ulCount )
{
#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    return __atomic_fetch_sub(pAddend, ulCount, __ATOMIC_SEQ_CST);

#else

    uint32_t ulCurrent;

    ATOMIC_ENTER_CRITICAL();

    ulCurrent = *pAddend;

    *pAddend -= ulCount;

    ATOMIC_EXIT_CRITICAL();

    return ulCurrent;

#endif
}

/**
 * Atomic increment
 *
 * @brief Atomically increments the value of the specified pointer points to.
 *
 * @param[in,out] pAddend  Pointer to memory location from where value is to be
 *                         loaded and written back to.
 *
 * @return *pAddend value before increment.
 */
static portFORCE_INLINE uint32_t Atomic_Increment_u32( uint32_t volatile * pAddend )
{
#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    return __atomic_fetch_add(pAddend, 1, __ATOMIC_SEQ_CST);

#else

    uint32_t ulCurrent;

    ATOMIC_ENTER_CRITICAL();

    ulCurrent = *pAddend;

    *pAddend += 1;

    ATOMIC_EXIT_CRITICAL();

    return ulCurrent;

#endif
}

/**
 * Atomic decrement
 *
 * @brief Atomically decrements the value of the specified pointer points to
 *
 * @param[in,out] pAddend  Pointer to memory location from where value is to be
 *                         loaded and written back to.
 *
 * @return *pAddend value before decrement.
 */
static portFORCE_INLINE uint32_t Atomic_Decrement_u32( uint32_t volatile * pAddend )
{
#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    return __atomic_fetch_sub(pAddend, 1, __ATOMIC_SEQ_CST);

#else

    uint32_t ulCurrent;

    ATOMIC_ENTER_CRITICAL();

    ulCurrent = *pAddend;

    *pAddend -= 1;

    ATOMIC_EXIT_CRITICAL();

    return ulCurrent;

#endif
}

/*----------------------------- Bitwise Logical ------------------------------*/

/**
 * Atomic OR
 *
 * @brief Performs an atomic OR operation on the specified values.
 *
 * @param [in, out] pDestination  Pointer to memory location from where value is
 *                                to be loaded and written back to.
 * @param [in] ulValue            Value to be ORed with *pDestination.
 *
 * @return The original value of *pDestination.
 */
static portFORCE_INLINE uint32_t Atomic_OR_u32(
        uint32_t volatile * pDestination,
        uint32_t ulValue )
{
#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    return __atomic_fetch_or(pDestination, ulValue, __ATOMIC_SEQ_CST);

#else

    uint32_t ulCurrent;

    ATOMIC_ENTER_CRITICAL();

    ulCurrent = *pDestination;

    *pDestination |= ulValue;

    ATOMIC_EXIT_CRITICAL();

    return ulCurrent;

#endif
}

/**
 * Atomic AND
 *
 * @brief Performs an atomic AND operation on the specified values.
 *
 * @param [in, out] pDestination  Pointer to memory location from where value is
 *                                to be loaded and written back to.
 * @param [in] ulValue            Value to be ANDed with *pDestination.
 *
 * @return The original value of *pDestination.
 */
static portFORCE_INLINE uint32_t Atomic_AND_u32(
        uint32_t volatile * pDestination,
        uint32_t ulValue )
{
#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    return __atomic_fetch_and(pDestination, ulValue, __ATOMIC_SEQ_CST);

#else

    uint32_t ulCurrent;

    ATOMIC_ENTER_CRITICAL();

    ulCurrent = *pDestination;

    *pDestination &= ulValue;

    ATOMIC_EXIT_CRITICAL();

    return ulCurrent;

#endif
}

/**
 * Atomic NAND
 *
 * @brief Performs an atomic NAND operation on the specified values.
 *
 * @param [in, out] pDestination  Pointer to memory location from where value is
 *                                to be loaded and written back to.
 * @param [in] ulValue            Value to be NANDed with *pDestination.
 *
 * @return The original value of *pDestination.
 */
static portFORCE_INLINE uint32_t Atomic_NAND_u32(
        uint32_t volatile * pDestination,
        uint32_t ulValue )
{
#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    return __atomic_fetch_nand(pDestination, ulValue, __ATOMIC_SEQ_CST);

#else

    uint32_t ulCurrent;

    ATOMIC_ENTER_CRITICAL();

    ulCurrent = *pDestination;

    *pDestination = ~(ulCurrent & ulValue);

    ATOMIC_EXIT_CRITICAL();

    return ulCurrent;

#endif
}

/**
 * Atomic XOR
 *
 * @brief Performs an atomic XOR operation on the specified values.
 *
 * @param [in, out] pDestination  Pointer to memory location from where value is
 *                                to be loaded and written back to.
 * @param [in] ulValue            Value to be XORed with *pDestination.
 *
 * @return The original value of *pDestination.
 */
static portFORCE_INLINE uint32_t Atomic_XOR_u32(
        uint32_t volatile * pDestination,
        uint32_t ulValue )
{
#if defined ( configUSE_GCC_BUILTIN_ATOMICS ) && ( configUSE_GCC_BUILTIN_ATOMICS == 1 )

    return __atomic_fetch_xor(pDestination, ulValue, __ATOMIC_SEQ_CST);

#else

    uint32_t ulCurrent;

    ATOMIC_ENTER_CRITICAL();

    ulCurrent = *pDestination;

    *pDestination ^= ulValue;

    ATOMIC_EXIT_CRITICAL();

    return ulCurrent;

#endif
}

#ifdef __cplusplus
}
#endif

#endif /* ATOMIC_H */
