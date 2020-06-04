/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_WDOG0

#include <metal/drivers/sifive_uart0.h>
#include <metal/machine.h>

#include <limits.h>

/* WDOGCFG */
#define METAL_WDOGCFG_SCALE_MASK 7
#define METAL_WDOGCFG_RSTEN (1 << 8)
#define METAL_WDOGCFG_ZEROCMP (1 << 9)
#define METAL_WDOGCFG_ENALWAYS (1 << 12)
#define METAL_WDOGCFG_COREAWAKE (1 << 13)
#define METAL_WDOGCFG_IP (1 << 28)

/* WDOGCMP */
#define METAL_WDOGCMP_MASK 0xFFFF

#define WDOG_REG(base, offset)   (((unsigned long)base + offset))
#define WDOG_REGB(base, offset)  (__METAL_ACCESS_ONCE((__metal_io_u8  *)WDOG_REG(base, offset)))
#define WDOG_REGW(base, offset)  (__METAL_ACCESS_ONCE((__metal_io_u32 *)WDOG_REG(base, offset)))

/* All writes to watchdog registers must be precedded by a write of
 * a magic number to WDOGKEY */
#define WDOG_UNLOCK(base) (WDOG_REGW(base, METAL_SIFIVE_WDOG0_WDOGKEY) = METAL_SIFIVE_WDOG0_MAGIC_KEY)

/* Unlock the watchdog and then perform a register access */
#define WDOG_UNLOCK_REGW(base, offset) \
    WDOG_UNLOCK(base);\
    WDOG_REGW(base, offset)

int __metal_driver_sifive_wdog0_feed(const struct metal_watchdog *const wdog)
{
    const uintptr_t base = (uintptr_t)__metal_driver_sifive_wdog0_control_base(wdog);

    WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGFEED) = METAL_SIFIVE_WDOG0_MAGIC_FOOD;

    return 0;
}

long int __metal_driver_sifive_wdog0_get_rate(const struct metal_watchdog *const wdog)
{
    const uintptr_t base = (uintptr_t)__metal_driver_sifive_wdog0_control_base(wdog);
    const struct metal_clock *const clock = __metal_driver_sifive_wdog0_clock(wdog);
    
    const long int clock_rate = metal_clock_get_rate_hz(clock);

    if (clock_rate == 0)
        return -1;

    const unsigned int scale = (WDOG_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) & METAL_WDOGCFG_SCALE_MASK);

    return clock_rate / (1 << scale);
}

long int __metal_driver_sifive_wdog0_set_rate(const struct metal_watchdog *const wdog, const long int rate)
{
    const uintptr_t base = (uintptr_t)__metal_driver_sifive_wdog0_control_base(wdog);
    const struct metal_clock *const clock = __metal_driver_sifive_wdog0_clock(wdog);
    
    const long int clock_rate = metal_clock_get_rate_hz(clock);

    if (rate >= clock_rate) {
        /* We can't scale the rate above the driving clock. Clear the scale
         * field and return the driving clock rate */
        WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) &= ~(METAL_WDOGCFG_SCALE_MASK);
        return clock_rate;
    }

    /* Look for the closest scale value */
    long min_diff = LONG_MAX;
    unsigned int min_scale = 0;
    for (int i = 0; i < METAL_WDOGCFG_SCALE_MASK; i++) {
        const long int new_rate = clock_rate / (1 << i);

        long int diff = rate - new_rate;
        if (diff < 0)
            diff *= -1;

        if (diff < min_diff) {
            min_diff = diff;
            min_scale = i;
        }
    }

    WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) &= ~(METAL_WDOGCFG_SCALE_MASK);
    WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) |= (METAL_WDOGCFG_SCALE_MASK & min_scale);

    return clock_rate / (1 << min_scale);
}

long int __metal_driver_sifive_wdog0_get_timeout(const struct metal_watchdog *const wdog)
{
    const uintptr_t base = (uintptr_t)__metal_driver_sifive_wdog0_control_base(wdog);

    return (WDOG_REGW(base, METAL_SIFIVE_WDOG0_WDOGCMP) & METAL_WDOGCMP_MASK);
}

long int __metal_driver_sifive_wdog0_set_timeout(const struct metal_watchdog *const wdog, const long int timeout)
{
    const uintptr_t base = (uintptr_t)__metal_driver_sifive_wdog0_control_base(wdog);

    /* Cap the timeout at the max value */
    const long int set_timeout = timeout > METAL_WDOGCMP_MASK ? METAL_WDOGCMP_MASK : timeout;

    /* If we edit the timeout value in-place by masking the compare value to 0 and
     * then writing it, we cause a spurious interrupt because the compare value
     * is temporarily 0. Instead, read the value into a local variable, modify it
     * there, and then write the whole register back */
    uint32_t wdogcmp = WDOG_REGW(base, METAL_SIFIVE_WDOG0_WDOGCMP);

    wdogcmp &= ~(METAL_WDOGCMP_MASK);
    wdogcmp |= set_timeout;

    WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCMP) = wdogcmp;

    return set_timeout;
}

int __metal_driver_sifive_wdog0_set_result(const struct metal_watchdog *const wdog,
                                           const enum metal_watchdog_result result)
{
    const uintptr_t base = (uintptr_t)__metal_driver_sifive_wdog0_control_base(wdog);

    /* Turn off reset enable and counter reset */
    WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) &= ~(METAL_WDOGCFG_RSTEN | METAL_WDOGCFG_ZEROCMP);

    switch (result) {
    default:
    case METAL_WATCHDOG_NO_RESULT:
        break;
    case METAL_WATCHDOG_INTERRUPT:
        /* Reset counter to zero after match */
        WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) |= METAL_WDOGCFG_ZEROCMP;
        break;
    case METAL_WATCHDOG_FULL_RESET:
        WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) |= METAL_WDOGCFG_RSTEN;
        break;
    }

    return 0;
}

int __metal_driver_sifive_wdog0_run(const struct metal_watchdog *const wdog,
                                    const enum metal_watchdog_run_option option)
{
    const uintptr_t base = (uintptr_t)__metal_driver_sifive_wdog0_control_base(wdog);

    WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) &= ~(METAL_WDOGCFG_ENALWAYS | METAL_WDOGCFG_COREAWAKE);

    switch (option) {
    default:
    case METAL_WATCHDOG_STOP:
        break;
    case METAL_WATCHDOG_RUN_ALWAYS:
        /* Feed the watchdog before starting to reset counter */
        __metal_driver_sifive_wdog0_feed(wdog);

        WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) |= METAL_WDOGCFG_ENALWAYS;
        break;
    case METAL_WATCHDOG_RUN_AWAKE:
        /* Feed the watchdog before starting to reset counter */
        __metal_driver_sifive_wdog0_feed(wdog);

        WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) |= METAL_WDOGCFG_COREAWAKE;
        break;
    }

    return 0;
}

struct metal_interrupt *__metal_driver_sifive_wdog0_get_interrupt(const struct metal_watchdog *const wdog)
{
    return __metal_driver_sifive_wdog0_interrupt_parent(wdog);
}

int __metal_driver_sifive_wdog0_get_interrupt_id(const struct metal_watchdog *const wdog)
{
    return __metal_driver_sifive_wdog0_interrupt_line(wdog);
}

int __metal_driver_sifive_wdog0_clear_interrupt(const struct metal_watchdog *const wdog)
{
    const uintptr_t base = (uintptr_t)__metal_driver_sifive_wdog0_control_base(wdog);

    /* Clear the interrupt pending bit */
    WDOG_UNLOCK_REGW(base, METAL_SIFIVE_WDOG0_WDOGCFG) &= ~(METAL_WDOGCFG_IP);

    return 0;
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_wdog0) = {
    .watchdog.feed = __metal_driver_sifive_wdog0_feed,
    .watchdog.get_rate = __metal_driver_sifive_wdog0_get_rate,
    .watchdog.set_rate = __metal_driver_sifive_wdog0_set_rate,
    .watchdog.get_timeout = __metal_driver_sifive_wdog0_get_timeout,
    .watchdog.set_timeout = __metal_driver_sifive_wdog0_set_timeout,
    .watchdog.set_result = __metal_driver_sifive_wdog0_set_result,
    .watchdog.run = __metal_driver_sifive_wdog0_run,
    .watchdog.get_interrupt = __metal_driver_sifive_wdog0_get_interrupt,
    .watchdog.get_interrupt_id = __metal_driver_sifive_wdog0_get_interrupt_id,
    .watchdog.clear_interrupt = __metal_driver_sifive_wdog0_clear_interrupt,
};

#endif /* METAL_SIFIVE_WDOG0 */

typedef int no_empty_translation_units;

