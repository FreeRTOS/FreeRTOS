/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_WDOG0_H
#define METAL__DRIVERS__SIFIVE_WDOG0_H

#include <metal/compiler.h>
#include <metal/io.h>

#include <metal/clock.h>
#include <metal/interrupt.h>
#include <metal/watchdog.h>

struct __metal_driver_vtable_sifive_wdog0 {
    const struct metal_watchdog_vtable watchdog;
};

struct __metal_driver_sifive_wdog0;

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_wdog0)

struct __metal_driver_sifive_wdog0 {
    const struct metal_watchdog watchdog;
};

#endif
