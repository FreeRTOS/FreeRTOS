/* IRQ 
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


#include "IRQ.h"
#include "ioapic.h"
#include "stdio.h"
#define MAX_IRQS 128
void init_irq_handlers(void);
INT_HANDLER irq_handler[MAX_IRQS];

void int_disable(unsigned int irq) {
    set_ioapic_irq_mask(irq, 1);
}
void int_enable(unsigned int irq) {
    set_ioapic_irq_mask(irq, 0);
}

void int_handler_install(unsigned int irq, INT_HANDLER int_handler) {
    if (irq < (unsigned int)MAX_IRQS){
        irq_handler[irq] = int_handler;

    }	
}

INT_HANDLER get_int_handler(unsigned int irq) {
    if (irq < (unsigned int)MAX_IRQS) {
        return irq_handler[irq];
    } 
    return 0;
}

void init_irq_handlers(void) {
    for (int irq=0;irq<MAX_IRQS;irq++) {
        irq_handler[irq] = 0;
    }
}
