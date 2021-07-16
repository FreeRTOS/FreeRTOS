/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_TEST0

#include <metal/machine.h>

#include <stdint.h>

#include <metal/drivers/sifive_test0.h>
#include <metal/io.h>

void __metal_driver_sifive_test0_exit(const struct __metal_shutdown *sd,
                                      int code) __attribute__((noreturn));
void __metal_driver_sifive_test0_exit(const struct __metal_shutdown *sd,
                                      int code) {
    long base = __metal_driver_sifive_test0_base(sd);
    uint32_t out = (code << 16) + (code == 0 ? 0x5555 : 0x3333);
    while (1) {
        __METAL_ACCESS_ONCE((
            __metal_io_u32 *)(base + METAL_SIFIVE_TEST0_FINISHER_OFFSET)) = out;
    }
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_test0) = {
    .shutdown.exit = &__metal_driver_sifive_test0_exit,
};
#endif /* METAL_SIFIVE_TEST0 */

typedef int no_empty_translation_units;
