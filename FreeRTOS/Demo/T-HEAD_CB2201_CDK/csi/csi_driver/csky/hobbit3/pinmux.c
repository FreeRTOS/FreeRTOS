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

/******************************************************************************
 * @file     pinmux.c
 * @brief    source file for the pinmux
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include <stdint.h>
#include "pinmux.h"
#include "pin_name.h"

#define readl(addr) \
    ({ unsigned int __v = (*(volatile unsigned int *) (addr)); __v; })

#define writel(b,addr) (void)((*(volatile unsigned int *) (addr)) = (b))

/*******************************************************************************
 * function: hobbit_ioreuse_inital
 *
 * description:
 *   initial hobbit_pinmux
 *******************************************************************************/

extern int32_t target_qspi_init(pin_name_t mosi, pin_name_t miso, pin_name_t sclk, pin_name_t ssel, pin_name_t wp, pin_name_t hold, uint32_t *base, uint32_t *irq);

void hobbit_ioreuse_initial(void)
{
    unsigned int value;

    /* gpio data source select */
    value = readl(HOBBIT_GIPO0_PORTCTL_REG);
    value |= GPIO0_REUSE_EN;
    writel(value, HOBBIT_GIPO0_PORTCTL_REG);

    value = readl(HOBBIT_GIPO1_PORTCTL_REG);
    value |= GPIO1_REUSE_EN;
    writel(value, HOBBIT_GIPO1_PORTCTL_REG);

    /* reuse function select */
    value = readl(HOBBIT_IOMUX0L_REG);
    value |= IOMUX0L_FUNCTION_SEL;
    writel(value, HOBBIT_IOMUX0H_REG);

    value = readl(HOBBIT_IOMUX0H_REG);
    value |= IOMUX1L_FUNCTION_SEL;
    writel(value, HOBBIT_IOMUX0H_REG);

    value = readl(HOBBIT_IOMUX1L_REG);
    value |= IOMUX1L_FUNCTION_SEL;
    writel(value, HOBBIT_IOMUX1L_REG);

    target_qspi_init(PA4_QSPI0MOSI_XX_XX_XX, PA3_QSPI0MISO_XX_XX_XX, PA2_QSPI0CLK_XX_XX_XX, PA7_QSPI0CS0_XX_XX_XX, PA6_QSPI0WP_XX_XX_XX, PA5_QSPI0HOLD_XX_XX_XX, 0, 0);
}

int32_t pin_mux(pin_name_t pin, uint16_t function)
{
    unsigned int val = 0;
    unsigned int reg_val = 0;

    uint8_t offset;

    if (function > 3) {
        if (pin < PB0_UART2TX_XX_XX_SIROUT2) {
            offset = pin;
            /* gpio data source select */
            val = readl(HOBBIT_GIPO0_PORTCTL_REG);
            val &= ~(1 << offset);
            writel(val, HOBBIT_GIPO0_PORTCTL_REG);
            return 0;
        } else if (pin >= PB0_UART2TX_XX_XX_SIROUT2) {
            offset = pin - 32;
            /* gpio data source select */
            val = readl(HOBBIT_GIPO1_PORTCTL_REG);
            val &= ~(1 << offset);
            writel(val, HOBBIT_GIPO1_PORTCTL_REG);
            return 0;
        } else {
            return -1;
        }
    }

    if (pin >= PB0_UART2TX_XX_XX_SIROUT2) {
        offset = pin - 32;

        /* gpio data source select */
        val = readl(HOBBIT_GIPO1_PORTCTL_REG);
        val |= (1 << offset);
        writel(val, HOBBIT_GIPO1_PORTCTL_REG);

        reg_val = (0x3 << (offset * 2));
        /* reuse function select */
        val = readl(HOBBIT_IOMUX1L_REG);
        val &= ~(reg_val);
        val |= (function << (2 * offset));
        writel(val, HOBBIT_IOMUX1L_REG);
        return 0;
    }

    offset = pin;
    /* gpio data source select */
    val = readl(HOBBIT_GIPO0_PORTCTL_REG);
    val |= (1 << offset);
    writel(val, HOBBIT_GIPO0_PORTCTL_REG);

    if (pin >= PA16_SPI0CS0_PWMTRIG0_XX_USI1SCLK) {
        offset = pin - 16;
        reg_val = (0x3 << (offset * 2));
        /* reuse function select */
        val = readl(HOBBIT_IOMUX0H_REG);
        val &= ~(reg_val);
        val |= (function << (2 * offset));
        writel(val, HOBBIT_IOMUX0H_REG);
        return 0;
    }

    reg_val = (0x3 << (offset * 2));
    /* reuse function select */
    val = readl(HOBBIT_IOMUX0L_REG);
    val &= ~(reg_val);
    val |= (function << (2 * offset));
    writel(val, HOBBIT_IOMUX0L_REG);
    return 0;
}
