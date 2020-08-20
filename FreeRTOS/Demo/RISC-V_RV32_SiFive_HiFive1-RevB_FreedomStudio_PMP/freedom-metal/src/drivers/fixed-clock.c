/* Copyright 2018 SiFive, Inc. */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_FIXED_CLOCK

#include <metal/drivers/fixed-clock.h>
#include <stddef.h>
#include <metal/machine.h>

long __metal_driver_fixed_clock_get_rate_hz(const struct metal_clock *gclk)
{
    return __metal_driver_fixed_clock_rate(gclk);
}

long __metal_driver_fixed_clock_set_rate_hz(struct metal_clock *gclk, long target_hz)
{
    return __metal_driver_fixed_clock_get_rate_hz(gclk);
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_fixed_clock) = {
    .clock.get_rate_hz = __metal_driver_fixed_clock_get_rate_hz,
    .clock.set_rate_hz = __metal_driver_fixed_clock_set_rate_hz,
};

#endif /* METAL_FIXED_CLOCK */

typedef int no_empty_translation_units;
