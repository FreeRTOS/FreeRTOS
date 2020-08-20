/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_UART0_H
#define METAL__DRIVERS__SIFIVE_UART0_H

#include <metal/drivers/sifive_gpio0.h>
#include <metal/drivers/riscv_plic0.h>
#include <metal/clock.h>
#include <metal/io.h>
#include <metal/uart.h>
#include <metal/compiler.h>

struct __metal_driver_vtable_sifive_uart0 {
    const struct metal_uart_vtable uart;
};

struct __metal_driver_sifive_uart0;

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_uart0)

struct __metal_driver_sifive_uart0 {
    struct metal_uart uart;
    unsigned long baud_rate;
    metal_clock_callback pre_rate_change_callback;
    metal_clock_callback post_rate_change_callback;
};


#endif
