/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_FE310_G000_LFROSC_H
#define METAL__DRIVERS__SIFIVE_FE310_G000_LFROSC_H

#include <metal/compiler.h>
#include <metal/clock.h>
#include <metal/io.h>

struct __metal_driver_vtable_sifive_fe310_g000_lfrosc {
    struct __metal_clock_vtable clock;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_fe310_g000_lfrosc)

struct __metal_driver_sifive_fe310_g000_lfrosc {
    struct metal_clock clock;
};

#endif
