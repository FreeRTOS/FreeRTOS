/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_FE310_G000_PRCI

#include <metal/drivers/sifive_fe310-g000_prci.h>
#include <metal/machine.h>

long __metal_driver_sifive_fe310_g000_prci_get_reg(const struct __metal_driver_sifive_fe310_g000_prci *prci, long offset) {
    unsigned long base = __metal_driver_sifive_fe310_g000_prci_base();
    return __METAL_ACCESS_ONCE((__metal_io_u32 *)(base + offset));
}

long __metal_driver_sifive_fe310_g000_prci_set_reg(const struct __metal_driver_sifive_fe310_g000_prci *prci, long offset, long value) {
    unsigned long base = __metal_driver_sifive_fe310_g000_prci_base();
    return __METAL_ACCESS_ONCE((__metal_io_u32 *)(base + offset)) = value;
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_fe310_g000_prci) = {
    .get_reg = __metal_driver_sifive_fe310_g000_prci_get_reg,
    .set_reg = __metal_driver_sifive_fe310_g000_prci_set_reg,
};

#endif /* METAL_SIFIVE_FE310_G000_PRCI */
