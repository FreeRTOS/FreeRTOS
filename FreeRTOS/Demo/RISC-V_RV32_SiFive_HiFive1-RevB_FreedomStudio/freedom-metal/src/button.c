/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/button.h>
#include <metal/machine.h>

struct metal_button *metal_button_get(char *label) {
    int i;
    struct metal_button *button;

    if ((__METAL_DT_MAX_BUTTONS == 0) || (label == NULL)) {
        return NULL;
    }

    for (i = 0; i < __METAL_DT_MAX_BUTTONS; i++) {
        button = (struct metal_button *)__metal_button_table[i];
        if (button->vtable->button_exist(button, label)) {
            return button;
        }
    }
    return NULL;
}

extern __inline__ struct metal_interrupt *
metal_button_interrupt_controller(struct metal_button *button);
extern __inline__ int
metal_button_get_interrupt_id(struct metal_button *button);
