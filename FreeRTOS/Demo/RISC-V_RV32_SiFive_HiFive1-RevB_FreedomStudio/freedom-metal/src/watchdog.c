/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine.h>
#include <metal/watchdog.h>

extern inline int metal_watchdog_feed(const struct metal_watchdog *const wdog);
extern inline long int
metal_watchdog_get_rate(const struct metal_watchdog *const wdog);
extern inline long int
metal_watchdog_set_rate(const struct metal_watchdog *const wdog,
                        const long int rate);
extern inline long int
metal_watchdog_get_timeout(const struct metal_watchdog *const wdog);
extern inline long int
metal_watchdog_set_timeout(const struct metal_watchdog *const wdog,
                           const long int timeout);
extern inline int
metal_watchdog_set_result(const struct metal_watchdog *const wdog,
                          const enum metal_watchdog_result result);
extern inline int
metal_watchdog_run(const struct metal_watchdog *const wdog,
                   const enum metal_watchdog_run_option option);
extern inline struct metal_interrupt *
metal_watchdog_get_interrupt(const struct metal_watchdog *const wdog);
extern inline int
metal_watchdog_get_interrupt_id(const struct metal_watchdog *const wdog);
extern inline int
metal_watchdog_clear_interrupt(const struct metal_watchdog *const wdog);

struct metal_watchdog *metal_watchdog_get_device(const int index) {
    if (index > __METAL_DT_MAX_WDOGS) {
        return NULL;
    }

    return (struct metal_watchdog *)__metal_wdog_table[index];
}
