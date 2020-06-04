/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__RISCV_CLINT0_H
#define METAL__DRIVERS__RISCV_CLINT0_H

#include <metal/compiler.h>
#include <metal/drivers/riscv_cpu.h>

struct __metal_driver_vtable_riscv_clint0 {
    struct metal_interrupt_vtable clint_vtable;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_riscv_clint0)

#define __METAL_MACHINE_MACROS
#include <metal/machine.h>
struct __metal_driver_riscv_clint0 {
    struct metal_interrupt controller;
    int init_done;
};
#undef __METAL_MACHINE_MACROS

#endif
