/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_I2C0_H
#define METAL__DRIVERS__SIFIVE_I2C0_H

#include <metal/clock.h>
#include <metal/i2c.h>

struct __metal_driver_vtable_sifive_i2c0 {
    const struct metal_i2c_vtable i2c;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_i2c0)

struct __metal_driver_sifive_i2c0 {
    struct metal_i2c i2c;
    unsigned int init_done;
    unsigned int baud_rate;
    metal_clock_callback pre_rate_change_callback;
    metal_clock_callback post_rate_change_callback;
};

#endif
