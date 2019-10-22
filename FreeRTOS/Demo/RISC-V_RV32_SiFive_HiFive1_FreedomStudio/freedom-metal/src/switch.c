/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/switch.h>
#include <metal/machine.h>

struct metal_switch* metal_switch_get (char *label)
{
    int i;
    struct metal_switch *flip;

    if ((__METAL_DT_MAX_BUTTONS == 0) || (label == NULL)) {
        return NULL;
    }

    for (i = 0; i < __METAL_DT_MAX_BUTTONS; i++) {
        flip = (struct metal_switch*)__metal_switch_table[i];
        if (flip->vtable->switch_exist(flip, label)) {
            return flip;
        }
    }
    return NULL;
}

extern inline struct metal_interrupt*
    metal_switch_interrupt_controller(struct metal_switch *flip);
extern inline int metal_switch_get_interrupt_id(struct metal_switch *flip);
