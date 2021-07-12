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
 * @file     pin.h
 * @brief    header File for pin definition
 * @version  V1.0
 * @date     02. June 2018
 ******************************************************************************/
#ifndef _PIN_H_
#define _PIN_H_

#include <stdint.h>
#include "pin_name.h"
#include "pinmux.h"

#ifdef __cplusplus
extern "C" {
#endif

#define CLOCK_GETTIME_USE_TIMER_ID 0
#define UART_TXD0       1
#define UART_RXD0       2

#define CONSOLE_TXD     PAD_UART0_SIN
#define CONSOLE_RXD     PAD_UART0_SOUT
#define CONSOLE_IDX     0

/* example pin manager */
#define EXAMPLE_USART_IDX       0
#define EXAMPLE_PIN_USART_TX    PAD_UART0_SIN
#define EXAMPLE_PIN_USART_RX    PAD_UART0_SOUT
#define EXAMPLE_PIN_USART_TX_FUNC   0
#define EXAMPLE_PIN_USART_RX_FUNC   0

#define EXAMPLE_GPIO_PIN    PA1
#define EXAMPLE_BOARD_GPIO_PIN_NAME "A1"
#define EXAMPLE_GPIO_PIN_FUNC   0

/* tests pin manager */
#define TEST_USART_IDX       0
#define TEST_PIN_USART_TX    PAD_UART0_SIN
#define TEST_PIN_USART_RX    PAD_UART0_SOUT
#define TEST_PIN_USART_TX_FUNC      0
#define TEST_PIN_USART_RX_FUNC      0

#define TEST_GPIO_PIN    PA0
#define TEST_BOARD_GPIO_PIN_NAME "A0"
#define TEST_GPIO_PIN_FUNC   0

#define UART_TXD2       3
#define UART_RXD2       4

#define UART_TXD3       5
#define UART_RXD3       6

#define UART_PINs  { {PA0, PA1},\
        {PA10, PA11},\
        {PA23, PA22},\
        {PA26, PA27} }

#define GPIO_EXAMPLE_PORT   PORTB
#define GPIO_EXAMPLE_PIN    PA1
#define CTS_GPIO_TEST_PORT  PORTA
#define CTS_GPIO_TEST_PIN   PA0
#define EXAMPLE_BOARD_GPIO_PIN_NAME "A1"
#define CTS_BOARD_GPIO_PIN_NAME     "A0"
#define SENSOR_UART_DIR     PA3

#ifdef __cplusplus
}
#endif

#endif /* _PIN_H_ */

