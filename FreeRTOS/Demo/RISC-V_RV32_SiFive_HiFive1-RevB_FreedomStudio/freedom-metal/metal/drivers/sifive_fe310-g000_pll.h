/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifndef METAL__DRIVERS__SIFIVE_FE310_G000_PLL_H
#define METAL__DRIVERS__SIFIVE_FE310_G000_PLL_H

struct __metal_driver_sifive_fe310_g000_pll;

#include <metal/clock.h>
#include <metal/drivers/sifive_fe310-g000_prci.h>
#include <metal/machine.h>

struct __metal_driver_vtable_sifive_fe310_g000_pll {
    void (*init)(struct __metal_driver_sifive_fe310_g000_pll *pll);
    struct __metal_clock_vtable clock;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_fe310_g000_pll)

struct __metal_driver_sifive_fe310_g000_pll {
    struct metal_clock clock;
};

#endif
