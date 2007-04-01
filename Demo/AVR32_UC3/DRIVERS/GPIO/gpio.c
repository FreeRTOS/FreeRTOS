/* This source file is part of the ATMEL FREERTOS-0.9.0 Release */

/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief GPIO driver for AVR32 UC3.
 *
 * This file defines a useful set of functions for the GPIO.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices with a PWM module can be used.
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


#include "gpio.h"


//! GPIO module instance.
#define GPIO  AVR32_GPIO


int gpio_enable_module(avr32_gpiomap_t gpiomap, int size)
{
  int i,status=GPIO_SUCCESS;

  for(i=0; i<size; i++) {
    status |= gpio_enable_module_pin(**gpiomap, *(*gpiomap+1) );
    gpiomap++;
  }

  return status;
}


int gpio_enable_module_pin(int pin, int function)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin/32];

  // Enable the correct function
  switch(function)
  {
  case 0: // A function
    gpio_port->pmr0c = (1<<(pin%32));
    gpio_port->pmr1c = (1<<(pin%32));
    break;
  case 1: // B function
    gpio_port->pmr0s = (1<<(pin%32));
    gpio_port->pmr1c = (1<<(pin%32));
    break;
  case 2: // C function
    gpio_port->pmr0c = (1<<(pin%32));
    gpio_port->pmr1s = (1<<(pin%32));
    break;
  default:
    return GPIO_INVALID_ARGUMENT;
  }

  // Disable gpio control
  gpio_port->gperc = (1<<(pin%32));

  return GPIO_SUCCESS;
}


void gpio_enable_gpio(avr32_gpiomap_t gpiomap, int size)
{
  int i;

  for(i=0; i<size; i++){
    gpio_enable_gpio_pin(**gpiomap);
    gpiomap++;
  }
}


void gpio_enable_gpio_pin(int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin/32];
  gpio_port->gpers = 1<<(pin%32);
}


void gpio_enable_gpio_glitch_filter(int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin/32];
  gpio_port->gfers = 1<<(pin%32);
}


void gpio_disable_gpio_glitch_filter(int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin/32];
  gpio_port->gferc = 1<<(pin%32);
}


void gpio_disable_module(avr32_gpiomap_t gpiomap, int size)
{
  int i;

  for(i=0; i<size; i++){
    gpio_disable_gpio_pin(**gpiomap);
    gpiomap++;
  }
}


void gpio_disable_gpio_pin(int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin/32];
  gpio_port->gperc = 1<<(pin%32);
}


int gpio_pin_value(int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin/32];
  return (gpio_port->pvr >>(pin%32))&1;
}


void gpio_set_gpio_pin(int pin)
{
  // The port holding that pin.
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin/32];

  gpio_port->ovrs  = (1<<(pin%32)); // Value to be driven on the I/O line: 1
  gpio_port->oders = (1<<(pin%32)); // The GPIO output driver is enabled for that pin.
  gpio_port->gpers = (1<<(pin%32)); // The GPIO module controls that pin.
}


void gpio_clr_gpio_pin(int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin/32]; // The port holding that pin.

  gpio_port->ovrc  = (1<<(pin%32)); // Value to be driven on the I/O line: 0
  gpio_port->oders = (1<<(pin%32)); // The GPIO output driver is enabled for that pin.
  gpio_port->gpers = (1<<(pin%32)); // The GPIO module controls that pin.
}


void gpio_tgl_gpio_pin(int pin)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin/32]; // The port holding that pin.

  gpio_port->ovrt  = (1<<(pin%32)); // Toggle the I/O line.
  gpio_port->oders = (1<<(pin%32)); // The GPIO output driver is enabled for that pin.
  gpio_port->gpers = (1<<(pin%32)); // The GPIO module controls that pin.
}


void gpio_cfg_int_gpio_pin(int pin, int level)
{
  volatile avr32_gpio_port_t *gpio_port = &GPIO.port[pin/32]; // The port holding that pin.

  gpio_port->gpers  = 1<<(pin%32); // GPIO controller enable
  gpio_port->gfers  = 1<<(pin%32); // GPIO glitch filter enable
  switch (level)
  {
    case GPIO_RISING_EDGE:
    {
      // mode rising edge
      gpio_port->imr0s  = 1<<(pin%32);
      gpio_port->imr1c  = 1<<(pin%32);
      break;
    }
    case GPIO_FALLING_EDGE:
    {
      // mode falling edge
      gpio_port->imr0c  = 1<<(pin%32);
      gpio_port->imr1s  = 1<<(pin%32);
      break;
    }
    default :
    {
      // mode pin change
      gpio_port->imr0c  = 1<<(pin%32);
      gpio_port->imr1c  = 1<<(pin%32);
      break;
    }
  }
  gpio_port->iers   = 1<<(pin%32); // GPIO interrupt enable
}
