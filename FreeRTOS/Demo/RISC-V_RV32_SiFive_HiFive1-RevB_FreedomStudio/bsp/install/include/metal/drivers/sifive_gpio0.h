/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_GPIO0_H
#define METAL__DRIVERS__SIFIVE_GPIO0_H

#include <metal/compiler.h>
#include <metal/gpio.h>

struct __metal_driver_vtable_sifive_gpio0 {
    const struct __metal_gpio_vtable gpio;
};

// struct __metal_driver_sifive_gpio0;

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_gpio0)

struct __metal_driver_sifive_gpio0 {
    struct metal_gpio gpio;
};

#endif
