/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_FE310_G000_LFROSC

#include <metal/drivers/sifive_fe310-g000_lfrosc.h>
#include <metal/machine.h>

/* LFROSCCFG */
#define METAL_LFROSCCFG_DIV_MASK 0x3F
#define METAL_LFROSCCFG_TRIM_SHIFT 16
#define METAL_LFROSCCFG_TRIM_MASK (0x1F << METAL_LFROSCCFG_TRIM_SHIFT)
#define METAL_LFROSCCFG_EN (1 << 30)
#define METAL_LFROSCCFG_RDY (1 << 31)

/* LFCLKMUX */
#define METAL_LFCLKMUX_SEL 1
#define METAL_LFCLKMUX_EXT_MUX_STATUS (1 << 31)

#define LFROSC_REGW(addr) (__METAL_ACCESS_ONCE((__metal_io_u32 *)addr))

long __metal_driver_sifive_fe310_g000_lfrosc_get_rate_hz(
    const struct metal_clock *clock) {
    struct metal_clock *internal_ref =
        __metal_driver_sifive_fe310_g000_lfrosc_lfrosc(clock);
    struct metal_clock *external_ref =
        __metal_driver_sifive_fe310_g000_lfrosc_psdlfaltclk(clock);

    unsigned long int cfg_reg =
        __metal_driver_sifive_fe310_g000_lfrosc_config_reg(clock);
    unsigned long int mux_reg =
        __metal_driver_sifive_fe310_g000_lfrosc_mux_reg(clock);

    if (LFROSC_REGW(mux_reg) & METAL_LFCLKMUX_EXT_MUX_STATUS) {
        return metal_clock_get_rate_hz(external_ref);
    }

    const unsigned long int div =
        (LFROSC_REGW(cfg_reg) & METAL_LFROSCCFG_DIV_MASK) + 1;

    return metal_clock_get_rate_hz(internal_ref) / div;
}

long __metal_driver_sifive_fe310_g000_lfrosc_set_rate_hz(
    struct metal_clock *clock, long rate) {
    return __metal_driver_sifive_fe310_g000_lfrosc_get_rate_hz(clock);
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_fe310_g000_lfrosc) = {
    .clock.get_rate_hz = &__metal_driver_sifive_fe310_g000_lfrosc_get_rate_hz,
    .clock.set_rate_hz = &__metal_driver_sifive_fe310_g000_lfrosc_set_rate_hz,
};
#endif /* METAL_SIFIVE_FE310_G000_LFROSC */

typedef int no_empty_translation_units;
