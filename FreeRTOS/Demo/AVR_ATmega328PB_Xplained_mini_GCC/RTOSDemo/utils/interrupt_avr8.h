/**
 * \file interrupt_avr8.h
 *
 * \brief Global interrupt management for 8-bit AVR
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
 */

/**
 * \defgroup doc_driver_utils_interrupts ISR abstraction
 * \ingroup doc_driver_utils
 *
 * Interrupt-related functionality.
 *
 * \{
 */

#ifndef UTILS_INTERRUPT_AVR8_H
#define UTILS_INTERRUPT_AVR8_H

/**
 * \weakgroup interrupt_group
 *
 * @{
 */

#ifdef ISR_CUSTOM_H
#include ISR_CUSTOM_H
#else

/**
 * \def ISR
 * \brief Define service routine for specified interrupt vector
 *
 * Usage:
 * \code
    ISR(FOO_vect)
    {
        ...
    }
\endcode
 *
 * \param vect Interrupt vector name as found in the device header files.
 */
#if defined(__DOXYGEN__)
#define ISR(vect)
#elif defined(__GNUC__)
#include <avr/interrupt.h>
#elif defined(__ICCAVR__)
#define __ISR(x) _Pragma(#x)
#define ISR(vect) __ISR(vector = vect) __interrupt void handler_##vect(void)
#endif
#endif // ISR_CUSTOM_H

#ifdef __GNUC__
#define cpu_irq_enable() sei()
#define cpu_irq_disable() cli()
#else
#define cpu_irq_enable() __enable_interrupt()
#define cpu_irq_disable() __disable_interrupt()
#endif

//! @}

/**
 * \weakgroup interrupt_deprecated_group
 * @{
 */
// Deprecated definitions.
#define Enable_global_interrupt() cpu_irq_enable()
#define Disable_global_interrupt() cpu_irq_disable()
#define Is_global_interrupt_enabled() cpu_irq_is_enabled()
//! @}

#endif /* UTILS_INTERRUPT_AVR8_H */
