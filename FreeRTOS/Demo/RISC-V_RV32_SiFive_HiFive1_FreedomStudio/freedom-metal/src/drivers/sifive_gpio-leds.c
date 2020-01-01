/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_GPIO_LEDS

#include <string.h>
#include <metal/gpio.h>
#include <metal/drivers/sifive_gpio-leds.h>
#include <metal/machine.h>

int  __metal_driver_led_exist (struct metal_led *led, char *label)
{
    if (strcmp(__metal_driver_sifive_gpio_led_label(led), label) == 0) {
        return 1;
    }
    return 0;
}

void __metal_driver_led_enable (struct metal_led *led)
{
    int pin;
    struct metal_gpio *gpio;

    pin = __metal_driver_sifive_gpio_led_pin(led);
    gpio =  __metal_driver_sifive_gpio_led_gpio(led);

    if (gpio != NULL) {
        /* Configure LED as output */
        metal_gpio_disable_input((struct metal_gpio *) gpio, pin);
        metal_gpio_enable_output((struct metal_gpio *) gpio, pin);
    }
}

void __metal_driver_led_on (struct metal_led *led)
{
    int pin;
    struct metal_gpio *gpio;

    pin = __metal_driver_sifive_gpio_led_pin(led);
    gpio =  __metal_driver_sifive_gpio_led_gpio(led);

    if (gpio != NULL) {
        metal_gpio_set_pin((struct metal_gpio *) gpio, pin, 1);
    }
}

void __metal_driver_led_off (struct metal_led *led)
{
    int pin;
    struct metal_gpio *gpio;

    pin = __metal_driver_sifive_gpio_led_pin(led);
    gpio =  __metal_driver_sifive_gpio_led_gpio(led);

    if (gpio != NULL) {
        metal_gpio_set_pin((struct metal_gpio *) gpio, pin, 0);
    }
}

void __metal_driver_led_toggle (struct metal_led *led)
{
    int pin;
    struct metal_gpio *gpio;

    pin = __metal_driver_sifive_gpio_led_pin(led);
    gpio =  __metal_driver_sifive_gpio_led_gpio(led);

    if (gpio != NULL) {
        metal_gpio_toggle_pin((struct metal_gpio *) gpio, pin);
    }
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_led) = {
    .led_vtable.led_exist   = __metal_driver_led_exist,
    .led_vtable.led_enable  = __metal_driver_led_enable,
    .led_vtable.led_on      = __metal_driver_led_on,
    .led_vtable.led_off     = __metal_driver_led_off,
    .led_vtable.led_toggle  = __metal_driver_led_toggle,
};

#endif

typedef int no_empty_translation_units;
