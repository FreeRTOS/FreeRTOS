/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited. All rights reserved.
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
 * @file     devices.c
 * @brief    source file for the devices
 * @version  V1.0
 * @date     07. Mar 2019
 ******************************************************************************/

#include <stdio.h>
#include <csi_config.h>
#include <soc.h>
#include <drv_usart.h>
#include <drv_timer.h>
#include <drv_gpio.h>
#include <pin_name.h>

extern void TIM0_IRQHandler(void);
extern void TIM1_IRQHandler(void);
extern void TIM2_IRQHandler(void);
extern void TIM3_IRQHandler(void);
extern void TIM4_NMIHandler(void);
extern void TIM6_IRQHandler(void);
extern void TIM7_IRQHandler(void);
extern void TIM8_IRQHandler(void);
extern void TIM9_IRQHandler(void);
extern void TIM10_IRQHandler(void);
extern void TIM11_IRQHandler(void);

extern void USART_IRQHandler(void);
extern void GPIO0_IRQHandler(void);
extern void GPIO1_IRQHandler(void);
extern void GPIO2_IRQHandler(void);
extern void GPIO3_IRQHandler(void);
extern void GPIO4_IRQHandler(void);
extern void GPIO5_IRQHandler(void);
extern void GPIO6_IRQHandler(void);
extern void GPIO7_IRQHandler(void);

struct {
    uint32_t base;
    uint32_t irq;
    void *handler;
}
const sg_usart_config[CONFIG_USART_NUM] = {
    {CSKY_UART_BASE, UART_IRQn, USART_IRQHandler},
};

int32_t target_usart_init(int32_t idx, uint32_t *base, uint32_t *irq, void **handler)
{
    if (idx >= CONFIG_USART_NUM) {
        return -1;
    }

    if (base != NULL) {
        *base = sg_usart_config[idx].base;
    }

    if (irq != NULL) {
        *irq = sg_usart_config[idx].irq;
    }

    if (handler != NULL) {
        *handler = sg_usart_config[idx].handler;
    }

    return idx;
}

struct {
    uint32_t base;
    uint32_t irq;
    void *handler;
}
const sg_timer_config[CONFIG_TIMER_NUM] = {
    {CSKY_TIMER0_BASE, TIM0_IRQn, TIM0_IRQHandler},
    {CSKY_TIMER1_BASE, TIM1_IRQn, TIM1_IRQHandler},
    {CSKY_TIMER2_BASE, TIM2_IRQn, TIM2_IRQHandler},
    {CSKY_TIMER3_BASE, TIM3_IRQn, TIM3_IRQHandler},
    {CSKY_TIMER4_BASE, NMI_EXPn, TIM4_NMIHandler},
    {CSKY_TIMER5_BASE, -1, NULL},
    {CSKY_TIMER6_BASE, TIM6_IRQn, TIM6_IRQHandler},
    {CSKY_TIMER7_BASE, TIM7_IRQn, TIM7_IRQHandler},
    {CSKY_TIMER8_BASE, TIM8_IRQn, TIM8_IRQHandler},
    {CSKY_TIMER9_BASE, TIM9_IRQn, TIM9_IRQHandler},
    {CSKY_TIMER10_BASE, TIM10_IRQn, TIM10_IRQHandler},
    {CSKY_TIMER11_BASE, TIM11_IRQn, TIM11_IRQHandler},

};

int32_t target_get_timer_count(void)
{
    return CONFIG_TIMER_NUM;
}

int32_t target_get_timer(int32_t idx, uint32_t *base, uint32_t *irq, void **handler)
{
    if (idx >= target_get_timer_count()) {
        return -1;
    }

    if (base != NULL) {
        *base = sg_timer_config[idx].base;
    }

    if (irq != NULL) {
        *irq = sg_timer_config[idx].irq;
    }

    if (handler != NULL) {
        *handler = sg_timer_config[idx].handler;
    }

    return idx;
}

struct {
    uint32_t base;
    uint32_t irq;
    uint32_t pin_num;
    port_name_e port;
}
const sg_gpio_config[CONFIG_GPIO_NUM] = {
    {CSKY_GPIOA_BASE, GPIO0_IRQn, 0, PORTA},
    {CSKY_GPIOA_BASE, GPIO1_IRQn, 0, PORTB},
    {CSKY_GPIOA_BASE, GPIO2_IRQn, 0, PORTC},
    {CSKY_GPIOA_BASE, GPIO3_IRQn, 0, PORTD},
    {CSKY_GPIOA_BASE, GPIO4_IRQn, 0, PORTE},
    {CSKY_GPIOA_BASE, GPIO5_IRQn, 0, PORTF},
    {CSKY_GPIOA_BASE, GPIO6_IRQn, 0, PORTG},
    {CSKY_GPIOA_BASE, GPIO7_IRQn, 0, PORTH},
};

typedef struct {
    int32_t    gpio_pin;
    uint32_t cfg_idx;
} gpio_pin_map_t;
const static gpio_pin_map_t s_gpio_pin_map[] = {
    {PA0, 0},
    {PA1, 1},
    {PA2, 2},
    {PA3, 3},
    {PA4, 4},
    {PA5, 5},
    {PA6, 6},
    {PA7, 7}
};

int32_t target_gpio_port_init(port_name_e port, uint32_t *base, uint32_t *irq, void **handler, uint32_t *pin_num)
{
    int i;

    for (i = 0; i < CONFIG_GPIO_NUM; i++) {
        if (sg_gpio_config[i].port == port) {
            if (base != NULL) {
                *base = sg_gpio_config[i].base;
            }

            if (irq != NULL) {
                *irq = sg_gpio_config[i].irq;
            }

            if (pin_num != NULL) {
                *pin_num = sg_gpio_config[i].pin_num;
            }

            if (handler != NULL) {
                switch (i) {
                    case 0:
                        *handler = (void *)GPIO0_IRQHandler;
                        break;

                    case 1:
                        *handler = (void *)GPIO1_IRQHandler;
                        break;

                    case 2:
                        *handler = (void *)GPIO2_IRQHandler;
                        break;

                    case 3:
                        *handler = (void *)GPIO3_IRQHandler;
                        break;

                    case 4:
                        *handler = (void *)GPIO4_IRQHandler;
                        break;

                    case 5:
                        *handler = (void *)GPIO5_IRQHandler;
                        break;

                    case 6:
                        *handler = (void *)GPIO6_IRQHandler;
                        break;

                    case 7:
                        *handler = (void *)GPIO7_IRQHandler;
                        break;
                }
            }

            return i;
        }
    }

    return -1;
}

int32_t target_gpio_pin_init(int32_t gpio_pin, uint32_t *port_idx)
{
    uint32_t idx;

    for (idx = 0; idx < sizeof(s_gpio_pin_map) / sizeof(gpio_pin_map_t); idx++) {
        if (s_gpio_pin_map[idx].gpio_pin == gpio_pin) {
            if (port_idx != NULL) {
                *port_idx = s_gpio_pin_map[idx].cfg_idx;
            }

            return idx;
        }
    }

    return -1;
}
