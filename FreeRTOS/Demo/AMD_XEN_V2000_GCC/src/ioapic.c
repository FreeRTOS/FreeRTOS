/* toapic
 *
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 *
 */


#include "ioapic.h"

#define IOAPIC_BASE       0xFEC00000
#define IOREGSEL          (IOAPIC_BASE + 0x00)
#define IOWIN             (IOAPIC_BASE + 0x10)

#define IOAPIC_RED_TBL_BASE 0x10

uint32_t ioapic_read(uint32_t reg) {
    *(volatile uint32_t *)(IOREGSEL) = reg;
    return *(volatile uint32_t *)(IOWIN);
}
void ioapic_write(uint32_t reg, uint32_t value) {
    *(volatile uint32_t *)(IOREGSEL) = reg;
    *(volatile uint32_t *)(IOWIN) = value;
}
void set_ioapic_irq_mask(uint8_t irq, int mask) {
    uint32_t red_tbl_low = IOAPIC_RED_TBL_BASE + (irq * 2);
    uint32_t red_tbl_high = red_tbl_low + 1;
    uint32_t low_value = (uint8_t)32+irq;
    if (irq == (uint8_t)9) {
        low_value |= 1<<13;
        low_value |= 1<<15;
    }
    ioapic_write(red_tbl_low, low_value);
    uint32_t low = ioapic_read(red_tbl_low);
    low &= ~(1 << 16);
    ioapic_write(red_tbl_low, low);
}

