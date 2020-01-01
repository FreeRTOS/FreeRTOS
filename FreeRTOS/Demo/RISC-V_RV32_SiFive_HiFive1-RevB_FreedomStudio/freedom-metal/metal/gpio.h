/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__GPIO_H
#define METAL__GPIO_H

#include <metal/compiler.h>
#include <metal/interrupt.h>

/*!
 * @file gpio.h
 * @brief API for manipulating general-purpose input/output
 */

struct metal_gpio;

struct __metal_gpio_vtable {
    int (*disable_input)(struct metal_gpio *, long pins);
    int (*enable_input)(struct metal_gpio *, long pins);
    long (*input)(struct metal_gpio *);
    long (*output)(struct metal_gpio *);
    int (*disable_output)(struct metal_gpio *, long pins);
    int (*enable_output)(struct metal_gpio *, long pins);
    int (*output_set)(struct metal_gpio *, long value);
    int (*output_clear)(struct metal_gpio *, long value);
    int (*output_toggle)(struct metal_gpio *, long value);
    int (*enable_io)(struct metal_gpio *, long pins, long dest);
    int (*disable_io)(struct metal_gpio *, long pins);
    int (*config_int)(struct metal_gpio *, long pins, int intr_type);
    int (*clear_int)(struct metal_gpio *, long pins, int intr_type);
    struct metal_interrupt* (*interrupt_controller)(struct metal_gpio *gpio);
    int (*get_interrupt_id)(struct metal_gpio *gpio, int pin);
};

#define METAL_GPIO_INT_DISABLE       0
#define METAL_GPIO_INT_RISING        1
#define METAL_GPIO_INT_FALLING       2
#define METAL_GPIO_INT_BOTH_EDGE     3
#define METAL_GPIO_INT_LOW           4
#define METAL_GPIO_INT_HIGH          5
#define METAL_GPIO_INT_BOTH_LEVEL    6
#define METAL_GPIO_INT_MAX           7

/*!
 * @struct metal_gpio
 * @brief The handle for a GPIO interface
 */
struct metal_gpio {
	const struct __metal_gpio_vtable *vtable;
};

/*!
 * @brief Get a GPIO device handle
 * @param device_num The GPIO device index
 * @return The GPIO device handle, or NULL if there is no device at that index
 */
struct metal_gpio *metal_gpio_get_device(unsigned int device_num);

/*!
 * @brief enable input on a pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @return 0 if the input is successfully enabled
 */
__inline__ int metal_gpio_enable_input(struct metal_gpio *gpio, int pin) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->enable_input(gpio, (1 << pin));
}

/*!
 * @brief Disable input on a pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @return 0 if the input is successfully disabled
 */
__inline__ int metal_gpio_disable_input(struct metal_gpio *gpio, int pin) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->disable_input(gpio, (1 << pin));
}

/*!
 * @brief Enable output on a pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @return 0 if the output is successfully enabled
 */
__inline__ int metal_gpio_enable_output(struct metal_gpio *gpio, int pin) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->enable_output(gpio, (1 << pin));
}

/*!
 * @brief Disable output on a pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @return 0 if the output is successfully disabled
 */
__inline__ int metal_gpio_disable_output(struct metal_gpio *gpio, int pin) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->disable_output(gpio, (1 << pin));
}

/*!
 * @brief Set the output value of a GPIO pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @param value The value to set the pin to
 * @return 0 if the output is successfully set
 */
__inline__ int metal_gpio_set_pin(struct metal_gpio *gpio, int pin, int value) {
    if(!gpio) {
	return 1;
    }

    if(value == 0) {
	return gpio->vtable->output_clear(gpio, (1 << pin));
    } else {
	return gpio->vtable->output_set(gpio, (1 << pin));
    }
}

/*!
 * @brief Get the value of the GPIO pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @return The value of the GPIO pin
 */
__inline__ int metal_gpio_get_input_pin(struct metal_gpio *gpio, int pin) {
    if(!gpio) {
	return 0;
    }

    long value = gpio->vtable->input(gpio);

    if(value & (1 << pin)) {
	    return 1;
    } else {
	    return 0;
    }
}

/*!
 * @brief Get the value of the GPIO pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @return The value of the GPIO pin
 */
__inline__ int metal_gpio_get_output_pin(struct metal_gpio *gpio, int pin) {
    if(!gpio) {
	return 0;
    }

    long value = gpio->vtable->output(gpio);

    if(value & (1 << pin)) {
	return 1;
    } else {
	return 0;
    }
}

/*!
 * @brief Clears the value of the GPIO pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @return 0 if the pin is successfully cleared
 */
__inline__ int metal_gpio_clear_pin(struct metal_gpio *gpio, int pin) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->output_clear(gpio, (1 << pin));
}

/*!
 * @brief Toggles the value of the GPIO pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @return 0 if the pin is successfully toggled
 */
__inline__ int metal_gpio_toggle_pin(struct metal_gpio *gpio, int pin) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->output_toggle(gpio, (1 << pin));
}

/*!
 * @brief Enables and sets the pinmux for a GPIO pin
 * @param gpio The handle for the GPIO interface
 * @param pin The bitmask for the pin to enable pinmux on
 * @param io_function The IO function to set
 * @return 0 if the pinmux is successfully set
 */
__inline__ int metal_gpio_enable_pinmux(struct metal_gpio *gpio, int pin, int io_function) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->enable_io(gpio, (1 << pin), (io_function << pin));
}

/*!
 * @brief Disables the pinmux for a GPIO pin
 * @param gpio The handle for the GPIO interface
 * @param pin The bitmask for the pin to disable pinmux on
 * @return 0 if the pinmux is successfully set
 */
__inline__ int metal_gpio_disable_pinmux(struct metal_gpio *gpio, int pin) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->disable_io(gpio, (1 << pin));
}

/*!
 * @brief Config gpio interrupt type
 * @param gpio The handle for the GPIO interface
 * @param pin The bitmask for the pin to enable gpio interrupt
 * @param intr_type The interrupt type
 * @return 0 if the interrupt mode is setup properly
 */
__inline__ int metal_gpio_config_interrupt(struct metal_gpio *gpio, int pin, int intr_type) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->config_int(gpio, (1 << pin), intr_type);
}

/*!
 * @brief Clear gpio interrupt status
 * @param gpio The handle for the GPIO interface
 * @param pin The bitmask for the pin to clear gpio interrupt
 * @param intr_type The interrupt type to be clear
 * @return 0 if the interrupt is cleared
 */
__inline__ int metal_gpio_clear_interrupt(struct metal_gpio *gpio, int pin, int intr_type) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->clear_int(gpio, (1 << pin), intr_type);
}

/*!
 * @brief Get the interrupt controller for a gpio
 *
 * @param gpio The handle for the gpio
 * @return A pointer to the interrupt controller responsible for handling
 * gpio interrupts.
 */
__inline__ struct metal_interrupt*
    metal_gpio_interrupt_controller(struct metal_gpio *gpio) {
    return gpio->vtable->interrupt_controller(gpio);
}

/*!
 * @brief Get the interrupt id for a gpio
 *
 * @param gpio The handle for the gpio
 * @param pin The bitmask for the pin to get gpio interrupt id
 * @return The interrupt id corresponding to a gpio.
 */
__inline__ int metal_gpio_get_interrupt_id(struct metal_gpio *gpio, int pin) {
    return gpio->vtable->get_interrupt_id(gpio, pin);
}

#endif
