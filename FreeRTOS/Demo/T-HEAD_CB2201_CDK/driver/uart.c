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
#include <stdio.h>
#include <stdint.h>
#include "soc.h"
#include "pin_name.h"
#include "drv_usart.h"
#include "ck_sys_freq.h"

#define CONSOLE_TXD PA10_ADC2_TXD0
#define CONSOLE_RXD PA11_ACMP0N_ADC3_RXD0
static usart_handle_t console_handle = NULL;
extern int32_t csi_usart_putchar(usart_handle_t handle, uint8_t ch);

int putchar(int ch)
{
    if (ch == '\n') {
        csi_usart_putchar(console_handle, '\r');
    }

    csi_usart_putchar(console_handle, ch);

    return 0;
}

int fputc(int ch, FILE *fp)
{
    if (ch == '\n') {
        csi_usart_putchar(console_handle, '\r');
    }

    csi_usart_putchar(console_handle, ch);

    return 0;
}


void usart_event_cb(usart_event_e event, void *cb_arg)
{
    //do nothing
}

void console_init()
{
    int ret;

    console_handle = csi_usart_initialize(CONSOLE_TXD, CONSOLE_RXD, usart_event_cb, 0);

    if (!console_handle) {
        return;
    }

    ret = csi_usart_config(console_handle,
                           SYSTEM_CLOCK,
                           115200,
                           USART_MODE_ASYNCHRONOUS,
                           USART_PARITY_NONE,
                           USART_STOP_BITS_1,
                           USART_DATA_BITS_8);

    if (ret < 0) {
        return;
    }
}

void console_init_ree(uint32_t sysclk)
{
    int ret;


    console_handle = csi_usart_initialize(CONSOLE_TXD, CONSOLE_RXD, usart_event_cb, 0);

    if (!console_handle) {
        return;
    }

    ret = csi_usart_config(console_handle,
                           sysclk,
                           115200,
                           USART_MODE_ASYNCHRONOUS,
                           USART_PARITY_NONE,
                           USART_STOP_BITS_1,
                           USART_DATA_BITS_8);

    if (ret < 0) {
        return;
    }
}
