/**
 * \file atomic.h
 *
 * \brief Macros used for atomic memory access.
 *
 *
 * Copyright (C) 2016 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 *
 */

#ifndef ATOMIC_H
#define ATOMIC_H

/**
 * \defgroup doc_driver_utils_atomic Atomic memory access and critical sections
 * \ingroup doc_driver_utils
 *
 * Atomic memory access and critical sections
 *
 * \{
 */

/* clang-format off */

#if defined(__GNUC__) || defined (__DOXYGEN__)

/**
 * \brief Enter a critical region
 * 
 * Saves the contents of the status register, including the Global 
 * Interrupt Enable bit, so that it can be restored upon leaving the 
 * critical region. Thereafter, clears the Global Interrupt Enable Bit.
 * This macro takes a parameter P that is unused for the GCC compiler,
 * but necessary for code compatibility with the IAR compiler. The IAR
 * compiler declares a variable with the name of the parameter for
 * holding the SREG value. Since a variable is declared in the macro,
 * this variable must have a name that is unique within the scope
 * that the critical region is declared within, otherwise compilation 
 * will fail.
 *
 * \param[in] UNUSED(GCC)/P(IAR) Name of variable storing SREG
 *
 */

#define ENTER_CRITICAL(UNUSED) __asm__ __volatile__ (   \
   "in __tmp_reg__, __SREG__"                    "\n\t" \
   "cli"                                         "\n\t" \
   "push __tmp_reg__"                            "\n\t" \
   ::: "memory"                                         \
   )

/**
 * \brief Exit a critical region
 * 
 * Restores the contents of the status register, including the Global 
 * Interrupt Enable bit, as it was when entering the critical region.
 * This macro takes a parameter P that is unused for the GCC compiler,
 * but necessary for code compatibility with the IAR compiler. The IAR
 * compiler uses this parameter as the name of a variable that holds 
 * the SREG value. The parameter must be identical to the parameter 
 * used in the corresponding ENTER_CRITICAL().
 *
 * \param[in] UNUSED(GCC)/P(IAR) Name of variable storing SREG
 *
 */

#define EXIT_CRITICAL(UNUSED)  __asm__ __volatile__ (   \
   "pop __tmp_reg__"                             "\n\t" \
   "out __SREG__, __tmp_reg__"                   "\n\t" \
   ::: "memory"                                         \
   )

#define DISABLE_INTERRUPTS()        __asm__ __volatile__ ( "cli" ::: "memory")
#define ENABLE_INTERRUPTS()         __asm__ __volatile__ ( "sei" ::: "memory")

#elif defined(__ICCAVR__)

#define ENTER_CRITICAL(P)  unsigned char P = __save_interrupt();__disable_interrupt();
#define EXIT_CRITICAL(P)  __restore_interrupt(P);

#define DISABLE_INTERRUPTS()   __disable_interrupt();
#define ENABLE_INTERRUPTS()    __enable_interrupt();

#else
#  error Unsupported compiler.
#endif

/* clang-format on */

#endif /* ATOMIC_H */
