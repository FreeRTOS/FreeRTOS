/* Copyright 2018 SiFive, Inc. */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_FIXED_FACTOR_CLOCK

#include <metal/drivers/fixed-factor-clock.h>
#include <stddef.h>
#include <metal/machine.h>

long __metal_driver_fixed_factor_clock_get_rate_hz(const struct metal_clock *gclk)
{
    struct metal_clock *parent = __metal_driver_fixed_factor_clock_parent(gclk);
    long parent_rate = 1;
    if(parent) {
        parent_rate = parent->vtable->get_rate_hz(parent);
    }

    return __metal_driver_fixed_factor_clock_mult(gclk) * parent_rate / __metal_driver_fixed_factor_clock_div(gclk);
}

long __metal_driver_fixed_factor_clock_set_rate_hz(struct metal_clock *gclk, long target_hz)
{
    return __metal_driver_fixed_factor_clock_get_rate_hz(gclk);
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_fixed_factor_clock) = {
    .clock.get_rate_hz = __metal_driver_fixed_factor_clock_get_rate_hz,
    .clock.set_rate_hz = __metal_driver_fixed_factor_clock_set_rate_hz,
};
#endif /* METAL_FIXED_FACTOR_CLOCK */
