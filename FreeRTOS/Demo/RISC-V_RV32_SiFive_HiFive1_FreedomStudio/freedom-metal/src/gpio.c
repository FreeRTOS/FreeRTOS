/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine.h>
#include <metal/gpio.h>

extern __inline__ int metal_gpio_disable_input(struct metal_gpio *gpio, int pin);
extern __inline__ int metal_gpio_enable_input(struct metal_gpio *gpio, int pin);
extern __inline__ int metal_gpio_enable_output(struct metal_gpio *gpio, int pin);
extern __inline__ int metal_gpio_disable_output(struct metal_gpio *gpio, int pin);
extern __inline__ int metal_gpio_get_output_pin(struct metal_gpio *gpio, int pin);
extern __inline__ int metal_gpio_get_input_pin(struct metal_gpio *gpio, int pin);
extern __inline__ int metal_gpio_set_pin(struct metal_gpio *, int pin, int value);
extern __inline__ int metal_gpio_clear_pin(struct metal_gpio *, int pin);
extern __inline__ int metal_gpio_toggle_pin(struct metal_gpio *, int pin);
extern __inline__ int metal_gpio_enable_pinmux(struct metal_gpio *, int pin, int io_function);
extern __inline__ int metal_gpio_disable_pinmux(struct metal_gpio *, int pin);
extern __inline__ struct metal_interrupt* metal_gpio_interrupt_controller(struct metal_gpio *gpio);
extern __inline__ int metal_gpio_get_interrupt_id(struct metal_gpio *gpio, int pin);
extern __inline__ int metal_gpio_config_interrupt(struct metal_gpio *gpio, int pin, int intr_type);
extern __inline__ int metal_gpio_clear_interrupt(struct metal_gpio *gpio, int pin, int intr_type);

struct metal_gpio *metal_gpio_get_device(unsigned int device_num)
{
    if(device_num > __MEE_DT_MAX_GPIOS) {
	return NULL;
    }

    return (struct metal_gpio *) __metal_gpio_table[device_num];
}
