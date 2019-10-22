/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__SWITCH_H
#define METAL__SWITCH_H

/*!
 * @file switch.h
 * @brief API for reading toggle switches
 */

#include <metal/interrupt.h>

struct metal_switch;

struct metal_switch_vtable {
    int (*switch_exist)(struct metal_switch *sw, char *label);
    struct metal_interrupt* (*interrupt_controller)(struct metal_switch *sw);
    int (*get_interrupt_id)(struct metal_switch *sw);
};

/*!
 * @brief A handle for a switch
 */
struct metal_switch {
    const struct metal_switch_vtable *vtable;
};

/*!
 * @brief Get a handle for a switch
 * @param label The DeviceTree label for the desired switch
 * @return A handle to the switch, or NULL if none is found for the requested label
 */
struct metal_switch* metal_switch_get(char *label);

/*!
 * @brief Get the interrupt controller for a switch
 * @param sw The handle for the switch
 * @return The interrupt controller handle
 */
inline struct metal_interrupt*
    metal_switch_interrupt_controller(struct metal_switch *sw) { return sw->vtable->interrupt_controller(sw); }

/*!
 * @brief Get the interrupt id for a switch
 * @param sw The handle for the switch
 * @return The interrupt ID for the switch
 */
inline int metal_switch_get_interrupt_id(struct metal_switch *sw) { return sw->vtable->get_interrupt_id(sw); }

#endif
