/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__BUTTON_H
#define METAL__BUTTON_H

/*!
 * @file button.h
 * API for interfacing with physical buttons
 */

#include <metal/interrupt.h>

struct metal_button;

struct metal_button_vtable {
    int (*button_exist)(struct metal_button *button, char *label);
    struct metal_interrupt* (*interrupt_controller)(struct metal_button *button);
    int (*get_interrupt_id)(struct metal_button *button);
};

/*!
 * @brief A button device handle
 *
 * A `struct metal_button` is an implementation-defined object which represents
 * a button on a development board.
 */
struct metal_button {
    const struct metal_button_vtable *vtable;
};

/*!
 * @brief Get a reference to a button
 *
 * @param label The DeviceTree label for the button
 * @return A handle for the button
 */
struct metal_button* metal_button_get(char *label);


/*!
 * @brief Get the interrupt controller for a button
 *
 * @param button The handle for the button
 * @return A pointer to the interrupt controller responsible for handling
 * button interrupts.
 */
__inline__ struct metal_interrupt*
    metal_button_interrupt_controller(struct metal_button *button) { return button->vtable->interrupt_controller(button); }

/*!
 * @brief Get the interrupt id for a button
 *
 * @param button The handle for the button
 * @return The interrupt id corresponding to a button.
 */
__inline__ int metal_button_get_interrupt_id(struct metal_button *button) { return button->vtable->get_interrupt_id(button); }

#endif
