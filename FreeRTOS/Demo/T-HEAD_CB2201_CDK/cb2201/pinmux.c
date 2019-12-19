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

#include "pinmux.h"

#include <fcntl.h>
#include <stdio.h>
#include <string.h>


#define readl(addr) \
    ({ unsigned int __v = (*(volatile unsigned int *) (addr)); __v; })

#define writel(b,addr) (void)((*(volatile unsigned int *) (addr)) = (b))


void hobbit_ioreuse_initial(void)
{
    unsigned int value;

    /*gpio data source select*/
    value = readl(HOBBIT_GIPO0_PORTCTL_REG);
    value |= GPIO0_REUSE_EN;
    writel(value, HOBBIT_GIPO0_PORTCTL_REG);

    value = readl(HOBBIT_GIPO1_PORTCTL_REG);
    value |= GPIO1_REUSE_EN;
    writel(value, HOBBIT_GIPO1_PORTCTL_REG);

    /*reuse function select*/
    value = readl(HOBBIT_IOMUX0L_REG);
    value |= IOMUX0L_FUNCTION_SEL;
    writel(value, HOBBIT_IOMUX0L_REG);

    value = readl(HOBBIT_IOMUX0H_REG);
    value |= IOMUX1L_FUNCTION_SEL;
    writel(value, HOBBIT_IOMUX0H_REG);

    value = readl(HOBBIT_IOMUX1L_REG);
    value |= IOMUX1L_FUNCTION_SEL;
    writel(value, HOBBIT_IOMUX1L_REG);

    writel(PA5_ETB_TRIG1, HOBBIT_GIPO0_PORTCTL_REG);
}

