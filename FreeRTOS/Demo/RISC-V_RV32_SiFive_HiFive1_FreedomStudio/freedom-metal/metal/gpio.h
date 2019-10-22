/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__GPIO_H
#define METAL__GPIO_H

#include <metal/compiler.h>

/*!
 * @file gpio.h
 * @brief API for manipulating general-purpose input/output
 */

struct metal_gpio;

struct __metal_gpio_vtable {
    int (*disable_input)(struct metal_gpio *, long pins);
    long (*output)(struct metal_gpio *);
    int (*enable_output)(struct metal_gpio *, long pins);
    int (*output_set)(struct metal_gpio *, long value);
    int (*output_clear)(struct metal_gpio *, long value);
    int (*output_toggle)(struct metal_gpio *, long value);
    int (*enable_io)(struct metal_gpio *, long pins, long dest);
};

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
struct metal_gpio *metal_gpio_get_device(int device_num);

/*!
 * @brief Disable input on a pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @return 0 if the input is successfully disabled
 */
inline int metal_gpio_disable_input(struct metal_gpio *gpio, int pin) {
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
inline int metal_gpio_enable_output(struct metal_gpio *gpio, int pin) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->enable_output(gpio, (1 << pin));
}

/*!
 * @brief Set the output value of a GPIO pin
 * @param gpio The handle for the GPIO interface
 * @param pin The pin number indexed from 0
 * @param value The value to set the pin to
 * @return 0 if the output is successfully set
 */
inline int metal_gpio_set_pin(struct metal_gpio *gpio, int pin, int value) {
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
inline int metal_gpio_get_pin(struct metal_gpio *gpio, int pin) {
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
inline int metal_gpio_clear_pin(struct metal_gpio *gpio, int pin) {
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
inline int metal_gpio_toggle_pin(struct metal_gpio *gpio, int pin) {
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
inline int metal_gpio_enable_pinmux(struct metal_gpio *gpio, int pin, int io_function) {
    if(!gpio) {
	return 1;
    }

    return gpio->vtable->enable_io(gpio, (1 << pin), (io_function << pin));
}

#endif
