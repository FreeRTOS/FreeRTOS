/* Copyright 2019 SiFive, Inc. */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine.h>
#include <metal/rtc.h>

#include <stddef.h>

extern inline uint64_t metal_rtc_get_rate(const struct metal_rtc *const rtc);
extern inline uint64_t metal_rtc_set_rate(const struct metal_rtc *const rtc, const uint64_t rate);
extern inline uint64_t metal_rtc_get_compare(const struct metal_rtc *const rtc);
extern inline uint64_t metal_rtc_set_compare(const struct metal_rtc *const rtc, const uint64_t compare);
extern inline uint64_t metal_rtc_get_count(const struct metal_rtc *const rtc);
extern inline uint64_t metal_rtc_set_count(const struct metal_rtc *const rtc, const uint64_t count);
extern inline int metal_rtc_run(const struct metal_rtc *const rtc, const enum metal_rtc_run_option option);
extern inline struct metal_interrupt *metal_rtc_get_interrupt(const struct metal_rtc *const rtc);
extern inline int metal_rtc_get_interrupt_id(const struct metal_rtc *const rtc);

struct metal_rtc *metal_rtc_get_device(int index) {
#ifdef __METAL_DT_MAX_RTCS
    if (index < __METAL_DT_MAX_RTCS) {
        return (struct metal_rtc *) __metal_rtc_table[index];
    }
#endif
    return NULL;
}

