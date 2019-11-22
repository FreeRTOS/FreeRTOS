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

#include <stdint.h>
#include "chip.h"


extern void Board_SystemInit(void);
extern void vic_init(void);
extern void coretim_init(uint32_t hz);
extern void vic_enable_irq(int irq);
extern int  yunos_bsp_uart_init(uint8_t * count);

/* Set up and initialize hardware prior to call to main */
void SystemInit(void)
{
    uint8_t count;
    volatile int *uart_reg = (volatile int *)0x50010400;

    Board_SystemInit();
    vic_init();
    vic_enable_irq(33);
    coretim_init(OS_TICK_FREQ);

    yunos_bsp_uart_init(&count);

    /* FIXME */
    *(uart_reg + 1) = 0x1;
    *(uart_reg + 2) = 0xc1;
    *(uart_reg + 3) = 0x3;
    *(uart_reg + 5) = 0x60;
    *(uart_reg + 6) = 0x11;
}
