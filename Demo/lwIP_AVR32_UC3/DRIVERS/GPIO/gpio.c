/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief GPIO driver for AVR32 UC3.
 *
 * This file defines a useful set of functions for the GPIO.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices with a GPIO module can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
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


#include "gpio.h"


//! GPIO module instance.
#define GPIO  AVR32_GPIO


int gpio_enable_module(const gpio_map_t gpiomap, unsigned int size)
{
  int status = GPIO_SUCCESS;
  unsigned int i;

  for (i = 0; i < size; i++)
  {
    status |= gpio_enable_module_pin(gpiomap->pin, gpiomap->function);
    gpiomap++;
  }

  return status;
}


int gpio_enable_module_pin(unsigned int pin, unsigned int function)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];

  // Enable the correct function.
  switch (function)
  {
  case 0: // A function.
    gpio_port->pmr0c = 1 << (pin & 0x1F);
    gpio_port->pmr1c = 1 << (pin & 0x1F);
    break;

  case 1: // B function.
    gpio_port->pmr0s = 1 << (pin & 0x1F);
    gpio_port->pmr1c = 1 << (pin & 0x1F);
    break;

  case 2: // C function.
    gpio_port->pmr0c = 1 << (pin & 0x1F);
    gpio_port->pmr1s = 1 << (pin & 0x1F);
    break;

  default:
    return GPIO_INVALID_ARGUMENT;
  }

  // Disable GPIO control.
  gpio_port->gperc = 1 << (pin & 0x1F);

  return GPIO_SUCCESS;
}


void gpio_enable_gpio(const gpio_map_t gpiomap, unsigned int size)
{
  unsigned int i;

  for (i = 0; i < size; i++)
  {
    gpio_enable_gpio_pin(gpiomap->pin);
    gpiomap++;
  }
}


void gpio_enable_gpio_pin(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  gpio_port->oderc = 1 << (pin & 0x1F);
  gpio_port->gpers = 1 << (pin & 0x1F);
}


void gpio_enable_pin_open_drain(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  gpio_port->odmers = 1 << (pin & 0x1F);
}


void gpio_disable_pin_open_drain(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  gpio_port->odmerc = 1 << (pin & 0x1F);
}


void gpio_enable_pin_pull_up(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  gpio_port->puers = 1 << (pin & 0x1F);
}


void gpio_disable_pin_pull_up(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  gpio_port->puerc = 1 << (pin & 0x1F);
}


int gpio_get_pin_value(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  return (gpio_port->pvr >> (pin & 0x1F)) & 1;
}


int gpio_get_gpio_pin_output_value(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  return (gpio_port->ovr >> (pin & 0x1F)) & 1;
}


void gpio_set_gpio_pin(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];

  gpio_port->ovrs  = 1 << (pin & 0x1F); // Value to be driven on the I/O line: 1.
  gpio_port->oders = 1 << (pin & 0x1F); // The GPIO output driver is enabled for that pin.
  gpio_port->gpers = 1 << (pin & 0x1F); // The GPIO module controls that pin.
}


void gpio_clr_gpio_pin(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];

  gpio_port->ovrc  = 1 << (pin & 0x1F); // Value to be driven on the I/O line: 0.
  gpio_port->oders = 1 << (pin & 0x1F); // The GPIO output driver is enabled for that pin.
  gpio_port->gpers = 1 << (pin & 0x1F); // The GPIO module controls that pin.
}


void gpio_tgl_gpio_pin(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];

  gpio_port->ovrt  = 1 << (pin & 0x1F); // Toggle the I/O line.
  gpio_port->oders = 1 << (pin & 0x1F); // The GPIO output driver is enabled for that pin.
  gpio_port->gpers = 1 << (pin & 0x1F); // The GPIO module controls that pin.
}


void gpio_enable_pin_glitch_filter(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  gpio_port->gfers = 1 << (pin & 0x1F);
}


void gpio_disable_pin_glitch_filter(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  gpio_port->gferc = 1 << (pin & 0x1F);
}


int gpio_enable_pin_interrupt(unsigned int pin, unsigned int mode)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];

  // Enable the glitch filter.
  gpio_port->gfers = 1 << (pin & 0x1F);

  // Configure the edge detector.
  switch (mode)
  {
  case GPIO_PIN_CHANGE:
    gpio_port->imr0c = 1 << (pin & 0x1F);
    gpio_port->imr1c = 1 << (pin & 0x1F);
    break;

  case GPIO_RISING_EDGE:
    gpio_port->imr0s = 1 << (pin & 0x1F);
    gpio_port->imr1c = 1 << (pin & 0x1F);
    break;

  case GPIO_FALLING_EDGE:
    gpio_port->imr0c = 1 << (pin & 0x1F);
    gpio_port->imr1s = 1 << (pin & 0x1F);
    break;

  default:
    return GPIO_INVALID_ARGUMENT;
  }

  // Enable interrupt.
  gpio_port->iers = 1 << (pin & 0x1F);

  return GPIO_SUCCESS;
}


void gpio_disable_pin_interrupt(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  gpio_port->ierc = 1 << (pin & 0x1F);
}


int gpio_get_pin_interrupt_flag(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  return (gpio_port->ifr >> (pin & 0x1F)) & 1;
}


void gpio_clear_pin_interrupt_flag(unsigned int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin >> 5];
  gpio_port->ifrc = 1 << (pin & 0x1F);
}
