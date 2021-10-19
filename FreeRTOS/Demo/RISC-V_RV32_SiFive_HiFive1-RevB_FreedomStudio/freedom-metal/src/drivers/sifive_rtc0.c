/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_RTC0

#include <metal/drivers/sifive_rtc0.h>
#include <metal/machine.h>

#include <limits.h>

/* RTCCFG */
#define METAL_RTCCFG_RTCSCALE_MASK 0xF
#define METAL_RTCCFG_ENALWAYS (1 << 12)
#define METAL_RTCCFG_IP0 (1 << 28)

/* RTCCMP0 */
#define METAL_RTCCMP0_MAX UINT32_MAX

#define RTC_REG(base, offset) (((unsigned long)base + offset))
#define RTC_REGW(base, offset)                                                 \
    (__METAL_ACCESS_ONCE((__metal_io_u32 *)RTC_REG(base, offset)))

uint64_t
__metal_driver_sifive_rtc0_get_rate(const struct metal_rtc *const rtc) {
    const struct metal_clock *const clock =
        __metal_driver_sifive_rtc0_clock(rtc);
    return metal_clock_get_rate_hz(clock);
}

uint64_t __metal_driver_sifive_rtc0_set_rate(const struct metal_rtc *const rtc,
                                             const uint64_t rate) {
    const struct metal_clock *const clock =
        __metal_driver_sifive_rtc0_clock(rtc);
    return metal_clock_get_rate_hz(clock);
}

uint64_t
__metal_driver_sifive_rtc0_get_compare(const struct metal_rtc *const rtc) {
    const uint64_t base = __metal_driver_sifive_rtc0_control_base(rtc);

    const uint32_t shift =
        RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCFG) & METAL_RTCCFG_RTCSCALE_MASK;

    return ((uint64_t)RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCMP0) << shift);
}

uint64_t
__metal_driver_sifive_rtc0_set_compare(const struct metal_rtc *const rtc,
                                       const uint64_t compare) {
    const uint64_t base = __metal_driver_sifive_rtc0_control_base(rtc);

    /* Determine the bit shift and shifted value to store in
     * rtccmp0/rtccfg.scale */
    uint32_t shift = 0;
    uint64_t comp_shifted = compare;
    while (comp_shifted > METAL_RTCCMP0_MAX) {
        shift += 1;
        comp_shifted = comp_shifted >> shift;
    }

    /* Set the value of rtccfg.scale */
    uint32_t cfg = RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCFG);
    cfg &= ~(METAL_RTCCFG_RTCSCALE_MASK);
    cfg |= (METAL_RTCCFG_RTCSCALE_MASK & shift);
    RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCFG) = cfg;

    /* Set the value of rtccmp0 */
    RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCMP0) = (uint32_t)comp_shifted;

    return __metal_driver_sifive_rtc0_get_compare(rtc);
}

uint64_t
__metal_driver_sifive_rtc0_get_count(const struct metal_rtc *const rtc) {
    const uint64_t base = __metal_driver_sifive_rtc0_control_base(rtc);

    uint64_t count = RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCOUNTHI);
    count <<= 32;
    count |= RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCOUNTLO);

    return count;
}

uint64_t __metal_driver_sifive_rtc0_set_count(const struct metal_rtc *const rtc,
                                              const uint64_t count) {
    const uint64_t base = __metal_driver_sifive_rtc0_control_base(rtc);

    RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCOUNTHI) = (UINT_MAX & (count >> 32));
    RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCOUNTLO) = (UINT_MAX & count);

    return __metal_driver_sifive_rtc0_get_count(rtc);
}

int __metal_driver_sifive_rtc0_run(const struct metal_rtc *const rtc,
                                   const enum metal_rtc_run_option option) {
    const uint64_t base = __metal_driver_sifive_rtc0_control_base(rtc);

    switch (option) {
    default:
    case METAL_RTC_STOP:
        RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCFG) &= ~(METAL_RTCCFG_ENALWAYS);
        break;
    case METAL_RTC_RUN:
        RTC_REGW(base, METAL_SIFIVE_RTC0_RTCCFG) |= METAL_RTCCFG_ENALWAYS;
        break;
    }

    return 0;
}

struct metal_interrupt *
__metal_driver_sifive_rtc0_get_interrupt(const struct metal_rtc *const rtc) {
    return __metal_driver_sifive_rtc0_interrupt_parent(rtc);
}

int __metal_driver_sifive_rtc0_get_interrupt_id(
    const struct metal_rtc *const rtc) {
    return __metal_driver_sifive_rtc0_interrupt_line(rtc);
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_rtc0) = {
    .rtc.get_rate = __metal_driver_sifive_rtc0_get_rate,
    .rtc.set_rate = __metal_driver_sifive_rtc0_set_rate,
    .rtc.get_compare = __metal_driver_sifive_rtc0_get_compare,
    .rtc.set_compare = __metal_driver_sifive_rtc0_set_compare,
    .rtc.get_count = __metal_driver_sifive_rtc0_get_count,
    .rtc.set_count = __metal_driver_sifive_rtc0_set_count,
    .rtc.run = __metal_driver_sifive_rtc0_run,
    .rtc.get_interrupt = __metal_driver_sifive_rtc0_get_interrupt,
    .rtc.get_interrupt_id = __metal_driver_sifive_rtc0_get_interrupt_id,
};

#endif

typedef int no_empty_translation_units;
