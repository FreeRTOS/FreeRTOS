/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__CLOCK_H
#define METAL__CLOCK_H

/*!
 * @file clock.h
 * @brief API for manipulating clock sources
 *
 * The clock interface allows for controlling the rate of various clocks in the
 * system.
 */

struct metal_clock;

#include <stddef.h>

/* The generic interface to all clocks. */
struct __metal_clock_vtable {
    long (*get_rate_hz)(const struct metal_clock *clk);
    long (*set_rate_hz)(struct metal_clock *clk, long hz);
};

/*!
 * @brief Function signature of clock rate change callbacks
 */
typedef void (*metal_clock_rate_change_callback)(void *priv);

struct _metal_clock_callback_t;
struct _metal_clock_callback_t {
    /* The callback function */
    metal_clock_rate_change_callback callback;

    /* Private data for the callback function */
    void *priv;

    struct _metal_clock_callback_t *_next;
};

/*!
 * @brief Type for the linked list of callbacks for clock rate changes
 */
typedef struct _metal_clock_callback_t metal_clock_callback;

/*!
 * @brief Call all callbacks in the linked list, if any are registered
 */
__inline__ void
_metal_clock_call_all_callbacks(const metal_clock_callback *const list) {
    const metal_clock_callback *current = list;
    while (current) {
        current->callback(current->priv);
        current = current->_next;
    }
}

/*!
 * @brief Append a callback to the linked list and return the head of the list
 */
__inline__ metal_clock_callback *
_metal_clock_append_to_callbacks(metal_clock_callback *list,
                                 metal_clock_callback *const cb) {
    cb->_next = NULL;

    if (!list) {
        return cb;
    }

    metal_clock_callback *current = list;

    while ((current->_next) != NULL) {
        current = current->_next;
    }

    current->_next = cb;

    return list;
}

/*!
 * @struct metal_clock
 * @brief The handle for a clock
 *
 * Clocks are defined as a pointer to a `struct metal_clock`, the contents of
 * which are implementation defined. Users of the clock interface must call
 * functions which accept a `struct metal_clock *` as an argument to interract
 * with the clock.
 *
 * Note that no mechanism for obtaining a pointer to a `struct metal_clock` has
 * been defined, making it impossible to call any of these functions without
 * invoking implementation-defined behavior.
 */
struct metal_clock {
    const struct __metal_clock_vtable *vtable;

    /* Pre-rate change callback linked list */
    metal_clock_callback *_pre_rate_change_callback;

    /* Post-rate change callback linked list */
    metal_clock_callback *_post_rate_change_callback;
};

/*!
 * @brief Returns the current rate of the given clock
 *
 * @param clk The handle for the clock
 * @return The current rate of the clock in Hz
 */
__inline__ long metal_clock_get_rate_hz(const struct metal_clock *clk) {
    return clk->vtable->get_rate_hz(clk);
}

/*!
 * @brief Set the current rate of a clock
 *
 * @param clk The handle for the clock
 * @param hz The desired rate in Hz
 * @return The new rate of the clock in Hz.
 *
 * Attempts to set the current rate of the given clock to as close as possible
 * to the given rate in Hz. Returns the actual value that's been selected, which
 * could be anything!
 *
 * Prior to and after the rate change of the clock, this will call the
 * registered pre- and post-rate change callbacks.
 */
__inline__ long metal_clock_set_rate_hz(struct metal_clock *clk, long hz) {
    _metal_clock_call_all_callbacks(clk->_pre_rate_change_callback);

    long out = clk->vtable->set_rate_hz(clk, hz);

    _metal_clock_call_all_callbacks(clk->_post_rate_change_callback);

    return out;
}

/*!
 * @brief Register a callback that must be called before a rate change
 *
 * @param clk The handle for the clock
 * @param cb The callback to be registered
 */
__inline__ void
metal_clock_register_pre_rate_change_callback(struct metal_clock *clk,
                                              metal_clock_callback *cb) {
    clk->_pre_rate_change_callback =
        _metal_clock_append_to_callbacks(clk->_pre_rate_change_callback, cb);
}

/*!
 * @brief Registers a callback that must be called after a rate change
 *
 * @param clk The handle for the clock
 * @param cb The callback to be registered
 */
__inline__ void
metal_clock_register_post_rate_change_callback(struct metal_clock *clk,
                                               metal_clock_callback *cb) {
    clk->_post_rate_change_callback =
        _metal_clock_append_to_callbacks(clk->_post_rate_change_callback, cb);
}

#endif
