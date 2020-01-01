/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_TRACE_H
#define METAL__DRIVERS__SIFIVE_TRACE_H

#include <metal/compiler.h>
#include <metal/io.h>
#include <metal/uart.h>

struct __metal_driver_vtable_sifive_trace {
    const struct metal_uart_vtable uart;
};

struct __metal_driver_sifive_trace;

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_trace)

struct __metal_driver_sifive_trace {
    struct metal_uart uart;
};

#endif /* METAL__DRIVERS__SIFIVE_TRACE_H */
