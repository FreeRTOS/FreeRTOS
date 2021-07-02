/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "types.h"
#include "gpio.h"
#include "iobank0.h"

static gpio_irq_callback_t _callbacks[NUM_CORES];

// Get the raw value from the pin, bypassing any muxing or overrides.
int gpio_get_pad(uint32_t gpio) {
    hw_set_bits(&padsbank0_hw->io[gpio], PADS_BANK0_GPIO0_IE_BITS);
    return (iobank0_hw->io[gpio].status & IO_BANK0_GPIO0_STATUS_INFROMPAD_BITS)
            >> IO_BANK0_GPIO0_STATUS_INFROMPAD_LSB;
}

/// \tag::gpio_set_function[]
// Select function for this GPIO, and ensure input/output are enabled at the pad.
// This also clears the input/output/irq override bits.
void gpio_set_function(uint32_t gpio, enum gpio_function fn) {
    // Set input enable on, output disable off
    hw_write_masked(&padsbank0_hw->io[gpio],
                   PADS_BANK0_GPIO0_IE_BITS,
                   PADS_BANK0_GPIO0_IE_BITS | PADS_BANK0_GPIO0_OD_BITS
    );
    // Zero all fields apart from fsel; we want this IO to do what the peripheral tells it.
    // This doesn't affect e.g. pullup/pulldown, as these are in pad controls.
    iobank0_hw->io[gpio].ctrl = fn << IO_BANK0_GPIO0_CTRL_FUNCSEL_LSB;
}
/// \end::gpio_set_function[]

enum gpio_function gpio_get_function(uint32_t gpio) {
    return (enum gpio_function) ((iobank0_hw->io[gpio].ctrl & IO_BANK0_GPIO0_CTRL_FUNCSEL_BITS) >> IO_BANK0_GPIO0_CTRL_FUNCSEL_LSB);
}

// Note that, on RP2040, setting both pulls enables a "bus keep" function,
// i.e. weak pull to whatever is current high/low state of GPIO.
void gpio_set_pulls(uint32_t gpio, bool up, bool down) {
    hw_write_masked(
            &padsbank0_hw->io[gpio],
            (!!up << PADS_BANK0_GPIO0_PUE_LSB) | (!!down << PADS_BANK0_GPIO0_PDE_LSB),
            PADS_BANK0_GPIO0_PUE_BITS | PADS_BANK0_GPIO0_PDE_BITS
    );
}

// Direct overrides for pad controls
void gpio_set_inover(uint32_t gpio, uint32_t value) {
    hw_write_masked(&iobank0_hw->io[gpio].ctrl,
                   value << IO_BANK0_GPIO0_CTRL_INOVER_LSB,
                   IO_BANK0_GPIO0_CTRL_INOVER_BITS
    );
}

void gpio_set_outover(uint32_t gpio, uint32_t value) {
    hw_write_masked(&iobank0_hw->io[gpio].ctrl,
                   value << IO_BANK0_GPIO0_CTRL_OUTOVER_LSB,
                   IO_BANK0_GPIO0_CTRL_OUTOVER_BITS
    );
}

void gpio_set_oeover(uint32_t gpio, uint32_t value) {
    hw_write_masked(&iobank0_hw->io[gpio].ctrl,
                   value << IO_BANK0_GPIO0_CTRL_OEOVER_LSB,
                   IO_BANK0_GPIO0_CTRL_OEOVER_BITS
    );
}

#define DEBUG_PIN_MASK (((1u << PICO_DEBUG_PIN_COUNT)-1) << PICO_DEBUG_PIN_BASE)

void gpio_debug_pins_init() {
    gpio_init_mask(DEBUG_PIN_MASK);
    gpio_set_dir_masked(DEBUG_PIN_MASK, DEBUG_PIN_MASK);
}

void gpio_set_input_enabled(uint32_t gpio, bool enabled) {
    if (enabled)
        hw_set_bits(&padsbank0_hw->io[gpio], PADS_BANK0_GPIO0_IE_BITS);
    else
        hw_clear_bits(&padsbank0_hw->io[gpio], PADS_BANK0_GPIO0_IE_BITS);
}

void gpio_init(uint32_t gpio) {
    sio_hw->gpio_oe_clr = 1ul << gpio;
    sio_hw->gpio_clr = 1ul << gpio;
    gpio_set_function(gpio, GPIO_FUNC_SIO);
}

void gpio_init_mask(uint32_t gpio_mask) {
    for(uint32_t i=0;i<32;i++) {
        if (gpio_mask & 1) {
            gpio_init(i);
        }
        gpio_mask >>= 1;
    }
}
