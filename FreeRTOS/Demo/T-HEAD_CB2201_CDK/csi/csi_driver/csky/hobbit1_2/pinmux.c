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

void hobbit_ioreuse_initial(void)
{
    unsigned int value;

    value = readl(HOBBIT1_2_GIPO0_PORTCTL_REG);
    value &= ~(GPIO0_REUSE_DIS);
    writel(value, HOBBIT1_2_GIPO0_PORTCTL_REG);
}

int32_t pin_mux(pin_name_t pin, uint16_t function)
{
    unsigned int val = 0;
    unsigned int reg_val = 0;

    uint8_t offset;

    if (function > 3) {
        if (pin <= PB3_SPI0MISO_PWM5_I2SSD) {
            if (pin <= PA5_RTS0_PWM1_SPI0SSN_TRIG1) {
                offset = pin;
                /* gpio data source select */
                val = readl(HOBBIT1_2_GIPO0_PORTCTL_REG);
                val &= ~(1 << offset);
                writel(val, HOBBIT1_2_GIPO0_PORTCTL_REG);
                return 0;
            } else if (pin >= PB0_SCL0_PWM2_I2SMCLK) {
                offset = pin - 6;
                /* gpio data source select */
                val = readl(HOBBIT1_2_GIPO1_PORTCTL_REG);
                val &= ~(1 << offset);
                writel(val, HOBBIT1_2_GIPO1_PORTCTL_REG);
                return 0;
            }
        }
        if ((pin >= PA6_SPI0MOSI_PWM6_SCL0) && (pin <= PA27_RTS2_I2SSD_ADC13)) {
            offset = pin - 4;
            /* gpio data source select */
            val = readl(HOBBIT1_2_GIPO0_PORTCTL_REG);
            val &= ~(1 << offset);
            writel(val, HOBBIT1_2_GIPO0_PORTCTL_REG);
            return 0;
        }
        return -1;
    }

    if ((pin >= PA6_SPI0MOSI_PWM6_SCL0) && (pin <= PA27_RTS2_I2SSD_ADC13)) {
        offset = pin - 4;

        /* gpio data source select */
        val = readl(HOBBIT1_2_GIPO0_PORTCTL_REG);
        val |= (1 << offset);
        writel(val, HOBBIT1_2_GIPO0_PORTCTL_REG);

        if (pin <= PA11_ACMP0N_ADC3_RXD0) {
            offset = pin;
            reg_val = (0x3 << (offset * 2));
            /* reuse function select */
            val = readl(HOBBIT1_2_IOMUX0L_REG);
            val &= ~(reg_val);
            val |= (function << (2 * offset));
            writel(val, HOBBIT1_2_IOMUX0L_REG);
            return 0;
        } else {
            offset = pin - 16;
            reg_val = (0x3 << (offset * 2));
            /* reuse function select */
            val = readl(HOBBIT1_2_IOMUX0H_REG);
            val &= ~(reg_val);
            val |= (function << (2 * offset));
            writel(val, HOBBIT1_2_IOMUX0H_REG);
            return 0;
        }
    }

    if ((pin >= PA0_TRIG0_ACMP1P_TCK) && (pin <= PB3_SPI0MISO_PWM5_I2SSD)) {
        if (pin >= PB0_SCL0_PWM2_I2SMCLK) {
            offset = pin - 6;
            val = readl(HOBBIT1_2_GIPO1_PORTCTL_REG);
            val |= (1 << offset);
            writel(val, HOBBIT1_2_GIPO1_PORTCTL_REG);

            offset = pin;
            reg_val = (0x3 << (offset * 2));
            /* reuse function select */
            val = readl(HOBBIT1_2_IOMUX0L_REG);
            val &= ~(reg_val);
            val |= (function << (2 * offset));
            writel(val, HOBBIT1_2_IOMUX0L_REG);
            return 0;
        }

        if (pin <= PA5_RTS0_PWM1_SPI0SSN_TRIG1) {
            offset = pin;
            /* gpio data source select */
            val = readl(HOBBIT1_2_GIPO0_PORTCTL_REG);
            val |= (1 << offset);
            writel(val, HOBBIT1_2_GIPO0_PORTCTL_REG);

            reg_val = (0x3 << (offset * 2));
            /* reuse function select */
            val = readl(HOBBIT1_2_IOMUX0L_REG);
            val &= ~(reg_val);
            val |= (function << (2 * offset));
            writel(val, HOBBIT1_2_IOMUX0L_REG);
            return 0;
        }
    }

    if (pin > PA27_RTS2_I2SSD_ADC13) {
        offset = pin - PC0_SCL1_CTS1_PWM10_ADC14;
        reg_val = (0x3 << (offset *2));
        val = readl(HOBBIT1_2_IOMUX1L_REG);
        val &= ~(reg_val);
        val |= (function << (2 * offset));
        writel(val, HOBBIT1_2_IOMUX1L_REG);
    }

    return -1;
}
