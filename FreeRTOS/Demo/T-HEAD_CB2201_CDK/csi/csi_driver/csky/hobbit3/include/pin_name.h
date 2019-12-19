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
 * @file     pin_name.h
 * @brief    header file for the pin_name
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#ifndef _PINNAMES_H
#define _PINNAMES_H


#ifdef __cplusplus
extern "C" {
#endif


typedef enum {
        PA0_I2C0SCL_SPI1CS1_SPU0_UART1TX = 0,
        PA1_I2C0SDA_SPI1CS2_SPU1_UART1RX,
        PA2_QSPI0CLK_XX_XX_XX,
        PA3_QSPI0MISO_XX_XX_XX,
        PA4_QSPI0MOSI_XX_XX_XX,
        PA5_QSPI0HOLD_XX_XX_XX,
        PA6_QSPI0WP_XX_XX_XX,
        PA7_QSPI0CS0_XX_XX_XX,
        PA8_UART0TX_XX_SPU2_SIROUT0,
        PA9_UART0RX_XX_SPU3_SIRIN0,
        PA10_UART0CTS_USI0SCLK_SPU4_I2C0SCL,
        PA11_UART0RTS_USI0SD0_SPU5_I2C0SDA,
        PA12_XX_USI0SD1_XX_UART2RX,
        PA13_XX_USI0NSS_XX_UART2TX,
        PA14_SPI0CS2_FAULT_I2C1SDA_XX,
        PA15_SPI0CS1_XX_I2C1SCL_XX,
        PA16_SPI0CS0_PWMTRIG0_XX_USI1SCLK,
        PA17_SPI0MOSI_PWMTRIG1_XX_USI1SD0,
        PA18_SPI0MISO_XX_SPU6_USI1SD1,
        PA19_SPI0SCK_FAULT_SPU7_USI1NSS,
        PA20_UART1RX_PWM0_SPU8_SIRIN1,
        PA21_UART1TX_PWM1_SPU9_SIROUT1,
        PA22_UART1CTS_PWM2_SPU10_XX,
        PA23_UART1RTS_PWM3_SPU11_XX,
        PA24_USI1NSS_PWM4_SPU12_XX,
        PA25_USI1SD1_PWM5_SPU13_XX,
        PA26_USI1SD0_PWM6_SPU14_XX,
        PA27_USI1SCLK_PWM7_SPU15_XX,
        PA28_I2C1SCL_PWM8_SPU16_XX,
        PA29_I2C1SDA_PWM9_SPU17_XX,
        PA30_I2C0SDA_PWM10_SPU18_XX,
        PA31_I2C0SCL_PWM11_SPU19_XX,
        PB0_UART2TX_XX_XX_SIROUT2,
        PB1_UART2RX_XX_XX_SIRIN2,
        PB2_UART2RTS_XX_XX_XX,
        PB3_UART2CTS_XX_XX_XX,
        PB4_XX_XX_SPU20_UART3TX,
        PB5_QSPI1CS1_XX_SPU21_UART3RX,
        PB6_QSPI1WP_XX_SPU22_XX,
        PB7_QSPI1HOLD_XX_SPU23_XX,
        PB8_QSPI1CS0_PWMTRIG0_SPU24_XX,
        PB9_QSPI1MOSI_PWMTRIG1_SPU25_XX,
        PB10_QSPI1MISO_XX_SPU26_I2C1SDA,
        PB11_QSPI1CLK_XX_SPU27_I2C1SCL,
        PB12_UART3RX_SPI1CS0_SPU28_SIRIN3,
        PB13_UART3TX_SPI1MISO_SPU29_SIROUT3,
        PB14_UART3RTS_SPI1MOSI_SPU30_XX,
        PB15_UART3CTS_SPI1SCK_SPU31_XX,
}
pin_name_t;

typedef enum {
    PORTA = 0,
    PORTB = 1
} port_name_t;

#ifdef __cplusplus
}
#endif

#endif
