/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__WATCHDOG_H
#define METAL__WATCHDOG_H

/*!
 * @file watchdog.h
 *
 * @brief API for configuring watchdog timers
 */

#include <metal/interrupt.h>

struct metal_watchdog;

/*!
 * @brief List of watchdog timer count behaviors
 */
enum metal_watchdog_run_option {
    METAL_WATCHDOG_STOP = 0,   /*!< Stop the watchdog */
    METAL_WATCHDOG_RUN_ALWAYS, /*!< Run the watchdog continuously, even during
                                  sleep */
    METAL_WATCHDOG_RUN_AWAKE,  /*!< Run the watchdog only while the CPU is awake
                                */
};

/*!
 * @brief List of behaviors when a watchdog triggers
 */
enum metal_watchdog_result {
    METAL_WATCHDOG_NO_RESULT = 0, /*!< When the watchdog triggers, do nothing */
    METAL_WATCHDOG_INTERRUPT, /*!< When the watchdog triggers, fire an interrupt
                               */
    METAL_WATCHDOG_FULL_RESET, /*!< When the watchdog triggers, cause a full
                                  system reset */
};

struct metal_watchdog_vtable {
    int (*feed)(const struct metal_watchdog *const wdog);
    long int (*get_rate)(const struct metal_watchdog *const wdog);
    long int (*set_rate)(const struct metal_watchdog *const wdog,
                         const long int rate);
    long int (*get_timeout)(const struct metal_watchdog *const wdog);
    long int (*set_timeout)(const struct metal_watchdog *const wdog,
                            const long int timeout);
    int (*set_result)(const struct metal_watchdog *const wdog,
                      const enum metal_watchdog_result result);
    int (*run)(const struct metal_watchdog *const wdog,
               const enum metal_watchdog_run_option option);
    struct metal_interrupt *(*get_interrupt)(
        const struct metal_watchdog *const wdog);
    int (*get_interrupt_id)(const struct metal_watchdog *const wdog);
    int (*clear_interrupt)(const struct metal_watchdog *const wdog);
};

/*!
 * @brief Handle for a Watchdog Timer
 */
struct metal_watchdog {
    const struct metal_watchdog_vtable *vtable;
};

/*!
 * @brief Feed the watchdog timer
 */
inline int metal_watchdog_feed(const struct metal_watchdog *const wdog) {
    return wdog->vtable->feed(wdog);
}

/*!
 * @brief Get the rate of the watchdog timer in Hz
 *
 * @return the rate of the watchdog timer
 */
inline long int
metal_watchdog_get_rate(const struct metal_watchdog *const wdog) {
    return wdog->vtable->get_rate(wdog);
}

/*!
 * @brief Set the rate of the watchdog timer in Hz
 *
 * There is no guarantee that the new rate will match the requested rate.
 *
 * @return the new rate of the watchdog timer
 */
inline long int metal_watchdog_set_rate(const struct metal_watchdog *const wdog,
                                        const long int rate) {
    return wdog->vtable->set_rate(wdog, rate);
}

/*!
 * @brief Get the timeout of the watchdog timer
 *
 * @return the watchdog timeout value
 */
inline long int
metal_watchdog_get_timeout(const struct metal_watchdog *const wdog) {
    return wdog->vtable->get_timeout(wdog);
}

/*!
 * @brief Set the timeout of the watchdog timer
 *
 * The set rate will be the minimimum of the requested and maximum supported
 * rates.
 *
 * @return the new watchdog timeout value
 */
inline long int
metal_watchdog_set_timeout(const struct metal_watchdog *const wdog,
                           const long int timeout) {
    return wdog->vtable->set_timeout(wdog, timeout);
}

/*!
 * @brief Sets the result behavior of a watchdog timer timeout
 *
 * @return 0 if the requested result behavior is supported
 */
inline int metal_watchdog_set_result(const struct metal_watchdog *const wdog,
                                     const enum metal_watchdog_result result) {
    return wdog->vtable->set_result(wdog, result);
}

/*!
 * @brief Set the run behavior of the watchdog
 *
 * Used to enable/disable the watchdog timer
 *
 * @return 0 if the watchdog was successfully started/stopped
 */
inline int metal_watchdog_run(const struct metal_watchdog *const wdog,
                              const enum metal_watchdog_run_option option) {
    return wdog->vtable->run(wdog, option);
}

/*!
 * @brief Get the interrupt controller for the watchdog interrupt
 */
inline struct metal_interrupt *
metal_watchdog_get_interrupt(const struct metal_watchdog *const wdog) {
    return wdog->vtable->get_interrupt(wdog);
}

/*!
 * @Brief Get the interrupt id for the watchdog interrupt
 */
inline int
metal_watchdog_get_interrupt_id(const struct metal_watchdog *const wdog) {
    return wdog->vtable->get_interrupt_id(wdog);
}

/*!
 * @brief Clear the watchdog interrupt
 */
inline int
metal_watchdog_clear_interrupt(const struct metal_watchdog *const wdog) {
    return wdog->vtable->clear_interrupt(wdog);
}

/*!
 * @brief Get a watchdog handle
 */
struct metal_watchdog *metal_watchdog_get_device(const int index);

#endif /* METAL__WATCHDOG_H */
