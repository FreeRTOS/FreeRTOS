/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_FE310_G000_HFROSC_H
#define METAL__DRIVERS__SIFIVE_FE310_G000_HFROSC_H

#include <metal/clock.h>
#include <metal/compiler.h>
#include <metal/drivers/sifive_fe310-g000_prci.h>
#include <metal/io.h>

struct __metal_driver_vtable_sifive_fe310_g000_hfrosc {
    struct __metal_clock_vtable clock;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_fe310_g000_hfrosc)

struct __metal_driver_sifive_fe310_g000_hfrosc {
    struct metal_clock clock;
};

#endif
