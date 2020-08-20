/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_GLOBAL_EXTERNAL_INTERRUPTS0_H
#define METAL__DRIVERS__SIFIVE_GLOBAL_EXTERNAL_INTERRUPTS0_H

#include <metal/compiler.h>
#include <metal/drivers/riscv_cpu.h>

struct __metal_driver_vtable_sifive_global_external_interrupts0 {
    struct metal_interrupt_vtable global0_vtable;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_global_external_interrupts0)

struct __metal_driver_sifive_global_external_interrupts0 {
    struct metal_interrupt irc;
    int init_done;
};

#endif
