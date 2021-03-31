/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <assert.h>

#include "types.h"
#include "address_mapped.h"
// For MHZ definitions etc
#include "clocks.h"
#include "platform_defs.h"
#include "regs/xosc.h"

/// \tag::xosc_hw[]
typedef struct {
    io_rw_32 ctrl;
    io_rw_32 status;
    io_rw_32 dormant;
    io_rw_32 startup;
    io_rw_32 _reserved[3];
    io_rw_32 count;
} xosc_hw_t;

#define xosc_hw ((xosc_hw_t *const)XOSC_BASE)
/// \end::xosc_hw[]


void xosc_init(void) {
    // Assumes 1-15 MHz input
    assert(XOSC_MHZ <= 15);
    xosc_hw->ctrl = XOSC_CTRL_FREQ_RANGE_VALUE_1_15MHZ;

    // Set xosc startup delay
    uint32_t startup_delay = (((12 * MHZ) / 1000) + 128) / 256;
    xosc_hw->startup = startup_delay;

    // Set the enable bit now that we have set freq range and startup delay
    hw_set_bits(&xosc_hw->ctrl, XOSC_CTRL_ENABLE_VALUE_ENABLE << XOSC_CTRL_ENABLE_LSB);

    // Wait for XOSC to be stable
    while(!(xosc_hw->status & XOSC_STATUS_STABLE_BITS));
}

void xosc_disable(void) {
    uint32_t tmp = xosc_hw->ctrl;
    tmp &= (~XOSC_CTRL_ENABLE_BITS);
    tmp |= (XOSC_CTRL_ENABLE_VALUE_DISABLE << XOSC_CTRL_ENABLE_LSB);
    xosc_hw->ctrl = tmp;
    // Wait for stable to go away
    while(xosc_hw->status & XOSC_STATUS_STABLE_BITS);
}

void xosc_dormant(void) {
    // WARNING: This stops the xosc until woken up by an irq
    xosc_hw->dormant = XOSC_DORMANT_VALUE_DORMANT;
    // Wait for it to become stable once woken up
    while(!(xosc_hw->status & XOSC_STATUS_STABLE_BITS));
}