/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_GPIO_BUTTONS_H
#define METAL__DRIVERS__SIFIVE_GPIO_BUTTONS_H

#include <string.h>
#include <metal/button.h>
#include <metal/compiler.h>

struct __metal_driver_vtable_sifive_button {
  struct metal_button_vtable button_vtable;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_button)

struct __metal_driver_sifive_gpio_button {
    struct metal_button button;
};

#endif
