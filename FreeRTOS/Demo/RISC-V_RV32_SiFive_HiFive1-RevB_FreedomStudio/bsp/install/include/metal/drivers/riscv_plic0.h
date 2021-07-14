/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__RISCV_PLIC0_H
#define METAL__DRIVERS__RISCV_PLIC0_H

#include <metal/compiler.h>
#include <metal/drivers/riscv_cpu.h>

#define METAL_PLIC_SOURCE_MASK 0x1F
#define METAL_PLIC_SOURCE_SHIFT 5
#define METAL_PLIC_SOURCE_PRIORITY_SHIFT 2
#define METAL_PLIC_SOURCE_PENDING_SHIFT 0

struct __metal_driver_vtable_riscv_plic0 {
    struct metal_interrupt_vtable plic_vtable;
};

__METAL_DECLARE_VTABLE(__metal_driver_vtable_riscv_plic0)

#define __METAL_MACHINE_MACROS
#include <metal/machine.h>
struct __metal_driver_riscv_plic0 {
    struct metal_interrupt controller;
    int init_done;
    metal_interrupt_handler_t metal_exint_table[__METAL_PLIC_SUBINTERRUPTS];
    __metal_interrupt_data metal_exdata_table[__METAL_PLIC_SUBINTERRUPTS];
};
#undef __METAL_MACHINE_MACROS

#endif
