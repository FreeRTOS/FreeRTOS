/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_RTC0_H
#define METAL__DRIVERS__SIFIVE_RTC0_H

#include <metal/compiler.h>
#include <metal/io.h>

#include <metal/clock.h>
#include <metal/interrupt.h>
#include <metal/rtc.h>

struct __metal_driver_vtable_sifive_rtc0 {
    const struct metal_rtc_vtable rtc;
};

struct __metal_driver_sifive_rtc0;

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_rtc0)

struct __metal_driver_sifive_rtc0 {
    const struct metal_rtc rtc;
};

#endif
