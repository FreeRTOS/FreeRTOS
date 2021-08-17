/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_GPIO_SWITCHES_H
#define METAL__DRIVERS__SIFIVE_GPIO_SWITCHES_H

#include <metal/compiler.h>
#include <metal/drivers/sifive_gpio0.h>
#include <metal/switch.h>

struct __metal_driver_vtable_sifive_switch {
    struct metal_switch_vtable switch_vtable;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_switch)

struct __metal_driver_sifive_gpio_switch {
    struct metal_switch flip;
};

#endif
