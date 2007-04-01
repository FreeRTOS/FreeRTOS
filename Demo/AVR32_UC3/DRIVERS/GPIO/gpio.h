/* This header file is part of the ATMEL FREERTOS-0.9.0 Release */

/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief GPIO header for AVR32 UC3.
 *
 * This file contains basic GPIO driver functions.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices with a GPIO module can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support email: avr32@atmel.com
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


#ifndef _GPIO_H_
#define _GPIO_H_

#if __GNUC__
#  include <avr32/io.h>
#elif __ICCAVR32__
#  include <avr32/iouc3a0512.h>
#else
#  error Unknown compiler
#endif


/*! \name General GPIO API defines
 * These values are returned by the GPIO API:
 */
//! @{
#define GPIO_SUCCESS            0 //!< Function successfully completed
#define GPIO_FAILURE           -1 //!< Function did not successfully complete for some unspecified reason
#define GPIO_INVALID_ARGUMENT   1 //!< Input paramters are out of range
//! @}


/*! \name Interrupt configuration defines
 * Configure the method used to trigger the interrupt:
 */
//! @{
#define GPIO_RISING_EDGE      1 //!< configure IT upon Rising Edge
#define GPIO_FALLING_EDGE     2 //!< configure IT upon Falling Edge
#define GPIO_INPUT_CHANGE     3 //!< configure IT upon Pin Change
//! @}


/*!
 * A type definitions of pins and module connectivity.
 * First column is the pin number, the second is gpio connectivity.
 */
typedef char avr32_gpiomap_t[][2];


/*!
 * \brief Enable a module pin for a given set of pins and respective modules.
 *
 * \param gpiomap A list of pins and pio connectivity
 * \param size The number of pins in \a gpiomap
 * \return \ref GPIO_SUCCESS or \ref GPIO_INVALID_ARGUMENT
 */
extern int gpio_enable_module(avr32_gpiomap_t gpiomap, int size);

/*!
 * \brief Enable a special module (function) for a pin (pin number).
 *
 * \param pin The pin number
 * \param function The pin function
 * \return \ref GPIO_SUCCESS or \ref GPIO_INVALID_ARGUMENT
 */
extern int gpio_enable_module_pin(int pin, int function);

/*!
 * \brief Enable pins of a module according gpiomap.
 *
 * \param gpiomap The pin map
 * \param size The number of pins in \a gpiomap
 */
extern void gpio_enable_gpio(avr32_gpiomap_t gpiomap, int size);

/*!
 * \brief Enable the GPIO module to control the pin.
 *
 * \param pin The pin number
 */
extern void gpio_enable_gpio_pin(int pin);

/*!
 * \brief Enable the GPIO glitch filter.
 *
 * When the glitch filter is enabled, a
 * glitch with duration of less than 1 clock cycle is automatically rejected, while a pulse with duration
 * of 2 clock cycles or more is accepted. For pulse durations between 1 clock cycle and 2 clock
 * cycles, the pulse may or may not be taken into account, depending on the precise timing of its
 * occurrence. Thus for a pulse to be guaranteed visible it must exceed 2 clock cycles, whereas for
 * a glitch to be reliably filtered out, its duration must not exceed 1 clock cycle. The filter introduces
 * 2 clock cycles latency.
 *
 * \param pin The pin number
 * \return \ref GPIO_SUCCESS
 */
extern void gpio_enable_gpio_glitch_filter(int pin);

/*!
 * \brief Disable the GPIO glitch filter.
 *
 * \param pin The pin number
 */
extern void gpio_disable_gpio_glitch_filter(int pin);

/*!
 * \brief Return the pin value
 *
 * \param pin The pin number
 * \return pin value
 */
extern int gpio_pin_value(int pin);

/*!
 * \brief Disable the GPIO module to control a set of pins according to gpiomap.
 *
 * \param gpiomap The pin map
 * \param size The number of pins in \a gpiomap
 */
extern void gpio_disable_module(avr32_gpiomap_t gpiomap, int size);

/*!
 * \brief Disable the GPIO module to control the pin.
 *
 * \param pin The pin number
 */
extern void gpio_disable_gpio_pin(int pin);

/*!
 * \brief Configure a pin to generate IT
 *
 * \param pin   GPIO pin number to configure.
 * \param level level to configure (\ref GPIO_RISING_EDGE, \ref GPIO_FALLING_EDGE, \ref GPIO_INPUT_CHANGE).
 */
extern void gpio_cfg_int_gpio_pin(int pin, int level);

/*!
 * \brief Drive a gpio pin value to 1.
 *
 * \param pin The pin number
 */
extern void gpio_set_gpio_pin(int pin);

/*!
 * \brief Drive a gpio pin value to 0.
 *
 * \param pin The pin number
 */
extern void gpio_clr_gpio_pin(int pin);

/*!
 * \brief This function toggle a gpio pin value.
 *
 * \param pin The pin number
 */
extern void gpio_tgl_gpio_pin(int pin);


#endif  // _GPIO_H_
