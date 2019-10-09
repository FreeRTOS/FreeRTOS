/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_GPIO_LEDS_H
#define METAL__DRIVERS__SIFIVE_GPIO_LEDS_H

#include <metal/drivers/sifive_gpio0.h>
#include <metal/led.h>
#include <metal/compiler.h>

struct __metal_driver_vtable_sifive_led {
  struct metal_led_vtable led_vtable;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_led)

struct __metal_driver_sifive_gpio_led {
    struct metal_led led;
};

#endif
