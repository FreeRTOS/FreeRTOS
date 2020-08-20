/* Copyright 2019 SiFive, Inc. */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__RTC_H
#define METAL__RTC_H

#include <stdint.h>

/*!
 * @file rtc.h
 * @brief API for Real-Time Clocks
 */

struct metal_rtc;

/*!
 * @brief List of RTC run behaviors
 */
enum metal_rtc_run_option {
    METAL_RTC_STOP = 0,
    METAL_RTC_RUN,
};

struct metal_rtc_vtable {
    uint64_t (*get_rate)(const struct metal_rtc *const rtc);
    uint64_t (*set_rate)(const struct metal_rtc *const rtc, const uint64_t rate);
    uint64_t (*get_compare)(const struct metal_rtc *const rtc);
    uint64_t (*set_compare)(const struct metal_rtc *const rtc, const uint64_t compare);
    uint64_t (*get_count)(const struct metal_rtc *const rtc);
    uint64_t (*set_count)(const struct metal_rtc *const rtc, const uint64_t count);
    int (*run)(const struct metal_rtc *const rtc, const enum metal_rtc_run_option option);
    struct metal_interrupt *(*get_interrupt)(const struct metal_rtc *const rtc);
    int (*get_interrupt_id)(const struct metal_rtc *const rtc);
};

/*!
 * @brief Handle for a Real-Time Clock
 */
struct metal_rtc {
    const struct metal_rtc_vtable *vtable;
};

/*!
 * @brief Get the rate of the RTC
 * @return The rate in Hz
 */
inline uint64_t metal_rtc_get_rate(const struct metal_rtc *const rtc) {
    return rtc->vtable->get_rate(rtc);
}

/*!
 * @brief Set (if possible) the rate of the RTC
 * @return The new rate of the RTC (not guaranteed to be the same as requested)
 */
inline uint64_t metal_rtc_set_rate(const struct metal_rtc *const rtc, const uint64_t rate) {
    return rtc->vtable->set_rate(rtc, rate);
}

/*!
 * @brief Get the compare value of the RTC
 * @return The compare value
 */
inline uint64_t metal_rtc_get_compare(const struct metal_rtc *const rtc) {
    return rtc->vtable->get_compare(rtc);
}

/*!
 * @brief Set the compare value of the RTC
 * @return The set compare value (not guaranteed to be exactly the requested value)
 *
 * The RTC device might impose limits on the maximum compare value or the granularity
 * of the compare value.
 */
inline uint64_t metal_rtc_set_compare(const struct metal_rtc *const rtc, const uint64_t compare) {
    return rtc->vtable->set_compare(rtc, compare);
}

/*!
 * @brief Get the current count of the RTC
 * @return The count
 */
inline uint64_t metal_rtc_get_count(const struct metal_rtc *const rtc) {
    return rtc->vtable->get_count(rtc);
}

/*!
 * @brief Set the current count of the RTC
 * @return The set value of the count (not guaranteed to be exactly the requested value)
 *
 * The RTC device might impose limits on the maximum value of the count
 */
inline uint64_t metal_rtc_set_count(const struct metal_rtc *const rtc, const uint64_t count) {
    return rtc->vtable->set_count(rtc, count);
}

/*!
 * @brief Start or stop the RTC
 * @return 0 if the RTC was successfully started/stopped
 */
inline int metal_rtc_run(const struct metal_rtc *const rtc, const enum metal_rtc_run_option option) {
    return rtc->vtable->run(rtc, option);
}

/*!
 * @brief Get the interrupt handle for the RTC compare
 * @return The interrupt handle
 */
inline struct metal_interrupt *metal_rtc_get_interrupt(const struct metal_rtc *const rtc) {
    return rtc->vtable->get_interrupt(rtc);
}

/*!
 * @brief Get the interrupt ID for the RTC compare
 * @return The interrupt ID
 */
inline int metal_rtc_get_interrupt_id(const struct metal_rtc *const rtc) {
    return rtc->vtable->get_interrupt_id(rtc);
}

/*!
 * @brief Get the handle for an RTC by index
 * @return The RTC handle, or NULL if none is available at that index
 */
struct metal_rtc *metal_rtc_get_device(int index);

#endif

