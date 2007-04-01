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


/*! \name Return Values of the GPIO API
 */
//! @{
#define GPIO_SUCCESS            0 //!< Function successfully completed.
#define GPIO_INVALID_ARGUMENT   1 //!< Input parameters are out of range.
//! @}


/*! \name Interrupt Trigger Modes
 */
//! @{
#define GPIO_PIN_CHANGE         0 //!< Interrupt triggered upon pin change.
#define GPIO_RISING_EDGE        1 //!< Interrupt triggered upon rising edge.
#define GPIO_FALLING_EDGE       2 //!< Interrupt triggered upon falling edge.
//! @}


//! A type definition of pins and modules connectivity.
typedef struct
{
  unsigned char pin;              //!< Module pin.
  unsigned char function;         //!< Module function.
} gpio_map_t[];


/*! \brief Enables specific module modes for a set of pins.
 *
 * \param gpiomap The pin map.
 * \param size The number of pins in \a gpiomap.
 *
 * \return \ref GPIO_SUCCESS or \ref GPIO_INVALID_ARGUMENT.
 */
extern int gpio_enable_module(const gpio_map_t gpiomap, unsigned int size);

/*! \brief Enables a specific module mode for a pin.
 *
 * \param pin The pin number.
 * \param function The pin function.
 *
 * \return \ref GPIO_SUCCESS or \ref GPIO_INVALID_ARGUMENT.
 */
extern int gpio_enable_module_pin(unsigned int pin, unsigned int function);

/*! \brief Enables the GPIO mode of a set of pins.
 *
 * \param gpiomap The pin map.
 * \param size The number of pins in \a gpiomap.
 */
extern void gpio_enable_gpio(const gpio_map_t gpiomap, unsigned int size);

/*! \brief Enables the GPIO mode of a pin.
 *
 * \param pin The pin number.
 */
extern void gpio_enable_gpio_pin(unsigned int pin);

/*! \brief Enables the open-drain mode of a pin.
 *
 * \param pin The pin number.
 */
extern void gpio_enable_pin_open_drain(unsigned int pin);

/*! \brief Disables the open-drain mode of a pin.
 *
 * \param pin The pin number.
 */
extern void gpio_disable_pin_open_drain(unsigned int pin);

/*! \brief Enables the pull-up resistor of a pin.
 *
 * \param pin The pin number.
 */
extern void gpio_enable_pin_pull_up(unsigned int pin);

/*! \brief Disables the pull-up resistor of a pin.
 *
 * \param pin The pin number.
 */
extern void gpio_disable_pin_pull_up(unsigned int pin);

/*! \brief Returns the value of a pin.
 *
 * \param pin The pin number.
 *
 * \return The pin value.
 */
extern int gpio_get_pin_value(unsigned int pin);

/*! \brief Returns the output value set for a GPIO pin.
 *
 * \param pin The pin number.
 *
 * \return The pin output value.
 */
extern int gpio_get_gpio_pin_output_value(unsigned int pin);

/*! \brief Drives a GPIO pin to 1.
 *
 * \param pin The pin number.
 */
extern void gpio_set_gpio_pin(unsigned int pin);

/*! \brief Drives a GPIO pin to 0.
 *
 * \param pin The pin number.
 */
extern void gpio_clr_gpio_pin(unsigned int pin);

/*! \brief Toggles a GPIO pin.
 *
 * \param pin The pin number.
 */
extern void gpio_tgl_gpio_pin(unsigned int pin);

/*! \brief Enables the glitch filter of a pin.
 *
 * When the glitch filter is enabled, a glitch with duration of less than 1
 * clock cycle is automatically rejected, while a pulse with duration of 2 clock
 * cycles or more is accepted. For pulse durations between 1 clock cycle and 2
 * clock cycles, the pulse may or may not be taken into account, depending on
 * the precise timing of its occurrence. Thus for a pulse to be guaranteed
 * visible it must exceed 2 clock cycles, whereas for a glitch to be reliably
 * filtered out, its duration must not exceed 1 clock cycle. The filter
 * introduces 2 clock cycles latency.
 *
 * \param pin The pin number.
 */
extern void gpio_enable_pin_glitch_filter(unsigned int pin);

/*! \brief Disables the glitch filter of a pin.
 *
 * \param pin The pin number.
 */
extern void gpio_disable_pin_glitch_filter(unsigned int pin);

/*! \brief Enables the interrupt of a pin with the specified settings.
 *
 * \param pin The pin number.
 * \param mode The trigger mode (\ref GPIO_PIN_CHANGE, \ref GPIO_RISING_EDGE or
 *             \ref GPIO_FALLING_EDGE).
 *
 * \return \ref GPIO_SUCCESS or \ref GPIO_INVALID_ARGUMENT.
 */
extern int gpio_enable_pin_interrupt(unsigned int pin, unsigned int mode);

/*! \brief Disables the interrupt of a pin.
 *
 * \param pin The pin number.
 */
extern void gpio_disable_pin_interrupt(unsigned int pin);

/*! \brief Gets the interrupt flag of a pin.
 *
 * \param pin The pin number.
 *
 * \return The pin interrupt flag.
 */
extern int gpio_get_pin_interrupt_flag(unsigned int pin);

/*! \brief Clears the interrupt flag of a pin.
 *
 * \param pin The pin number.
 */
extern void gpio_clear_pin_interrupt_flag(unsigned int pin);


#endif  // _GPIO_H_
