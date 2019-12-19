/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include <vic.h>
#include <stdint.h>
#include "portmacro.h"

void vic_enable_irq(int irq)
{
    uint32_t flags;

    flags = portSET_INTERRUPT_MASK_FROM_ISR();
    *(VIC_ISER) |= (1 << (irq - 32));
    *(VIC_ISNR) |= (1 << (irq - 32));
    *(VIC_ISFR) &= ~(1 << (irq - 32));
    portCLEAR_INTERRUPT_MASK_FROM_ISR(flags);
}

void vic_init(void)
{
    int i;
    *(VIC_ICR) = 0;
    for (i = 0; i < 56; i++) {
        VIC_PR[i] = 0x0;
    }

    return;
}
