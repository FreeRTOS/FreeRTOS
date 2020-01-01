/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_SPI0_H
#define METAL__DRIVERS__SIFIVE_SPI0_H

#include <metal/drivers/sifive_gpio0.h>
#include <metal/clock.h>
#include <metal/compiler.h>
#include <metal/io.h>
#include <metal/spi.h>

struct __metal_driver_vtable_sifive_spi0 {
    const struct metal_spi_vtable spi;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_spi0)

struct __metal_driver_sifive_spi0 {
    struct metal_spi spi;
    unsigned long baud_rate;
};

#endif
