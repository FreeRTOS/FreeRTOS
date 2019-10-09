/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_FE310_G000_HFXOSC

#include <metal/drivers/sifive_fe310-g000_hfxosc.h>
#include <metal/machine.h>

#define CONFIG_ENABLE  0x40000000UL
#define CONFIG_READY   0x80000000UL

long __metal_driver_sifive_fe310_g000_hfxosc_get_rate_hz(const struct metal_clock *clock)
{
    struct metal_clock *ref = __metal_driver_sifive_fe310_g000_hfxosc_ref(clock);
    long config_offset = __metal_driver_sifive_fe310_g000_hfxosc_config_offset(clock);
    struct __metal_driver_sifive_fe310_g000_prci *config_base =
      __metal_driver_sifive_fe310_g000_hfxosc_config_base(clock);
    const struct __metal_driver_vtable_sifive_fe310_g000_prci *vtable =
      __metal_driver_sifive_fe310_g000_prci_vtable();
    long cfg = vtable->get_reg(config_base, config_offset);

    if (cfg & CONFIG_ENABLE == 0)
        return -1;
    if (cfg & CONFIG_READY == 0)
        return -1;
    return metal_clock_get_rate_hz(ref);
}

long __metal_driver_sifive_fe310_g000_hfxosc_set_rate_hz(struct metal_clock *clock, long rate)
{
    return __metal_driver_sifive_fe310_g000_hfxosc_get_rate_hz(clock);
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_fe310_g000_hfxosc) = {
    .clock.get_rate_hz = __metal_driver_sifive_fe310_g000_hfxosc_get_rate_hz,
    .clock.set_rate_hz = __metal_driver_sifive_fe310_g000_hfxosc_set_rate_hz,
};

#endif /* METAL_SIFIVE_FE310_G000_HFXOSC */
