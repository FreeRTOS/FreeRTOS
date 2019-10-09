/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_GPIO_BUTTONS

#include <string.h>
#include <metal/drivers/riscv_cpu.h>
#include <metal/drivers/sifive_gpio-buttons.h>
#include <metal/machine.h>

int  __metal_driver_button_exist (struct metal_button *button, char *label)
{
    if (strcmp(__metal_driver_sifive_gpio_button_label(button), label) == 0) {
        return 1;
    }
    return 0;
}

struct metal_interrupt *
__metal_driver_button_interrupt_controller(struct metal_button *button)
{
    return __metal_driver_sifive_gpio_button_interrupt_controller(button);
}

int __metal_driver_button_get_interrupt_id(struct metal_button *button)
{
    int irq, max_irq;
    struct metal_interrupt *irc;

    irq = __metal_driver_sifive_gpio_button_interrupt_line(button);
    irc =  __metal_driver_sifive_gpio_button_interrupt_controller(button);

    if (irc != NULL) {
        max_irq = _metal_interrupt_command_request(irc,
                                                   METAL_MAX_INTERRUPT_GET,
                                                   NULL);

        if (irq < max_irq) {
            return _metal_interrupt_command_request(irc,
                                                 METAL_INDEX_INTERRUPT_GET,
                                                 (void *)&irq);
        }
    }
    return METAL_INTERRUPT_ID_LCMX;
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_button) = {
    .button_vtable.button_exist   = __metal_driver_button_exist,
    .button_vtable.interrupt_controller = __metal_driver_button_interrupt_controller,
    .button_vtable.get_interrupt_id = __metal_driver_button_get_interrupt_id,
};

#endif
