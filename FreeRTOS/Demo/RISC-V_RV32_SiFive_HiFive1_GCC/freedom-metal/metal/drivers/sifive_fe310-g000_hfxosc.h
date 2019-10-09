/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_FE310_G000_HFXOSC_H
#define METAL__DRIVERS__SIFIVE_FE310_G000_HFXOSC_H

#include <metal/clock.h>
#include <metal/drivers/sifive_fe310-g000_prci.h>

struct __metal_driver_vtable_sifive_fe310_g000_hfxosc {
    struct __metal_clock_vtable clock;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_fe310_g000_hfxosc)

struct __metal_driver_sifive_fe310_g000_hfxosc {
    struct metal_clock clock;
};

#endif
