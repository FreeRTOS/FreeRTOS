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
 * @date     23. August 2017
 ******************************************************************************/
#ifndef _PINNAMES_H
#define _PINNAMES_H


#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
        PA0_TRIG0_ACMP1P_TCK = 0,
        PA1_TRIG1_ACMP1N_TMS,
        PA2_TXD0_SPI0MISO,
        PA3_RXD0_SPI0MOSI,
        PA4_CTS0_PWM0_SPI0SCK_TRIG0,
        PA5_RTS0_PWM1_SPI0SSN_TRIG1,

        PB0_SCL0_PWM2_I2SMCLK,
        PB1_SDA0_PWM3_I2SSCK,
        PB2_SPI0SCK_PWM4_I2SWS,
        PB3_SPI0MISO_PWM5_I2SSD,

        PA6_SPI0MOSI_PWM6_SCL0,
        PA7_SPI0SSN_PWM7_SDA0,
        PA8_WKUP_ADC0_ACMP0P,
        PA9_BOOT_ADC1_PWMFAULT,
        PA10_ADC2_TXD0,
        PA11_ACMP0N_ADC3_RXD0,

        PA12_PWM8_TCK_ADC4,
        PA13_PWM9_TMS_ADC5,
        PA14_PWM10_ADC6,
        PA15_PWM11_ADC7,
        PA16_RXD1_ADC8,
        PA17_TXD1_ADC9,
        PA18_SPI1SSN0_ACMP0O,
        PA19_SPI1SSN1_ACMP1O,
        PA20_SPI1SSN2_TRIG0_RXD1,
        PA21_SPI1SCK_TRIG1_TXD1,
        PA22_SPI1MISO_PWM0_ADC10,
        PA23_SPI1MOSI_PWM1_ADC11,
        PA24_TXD2_I2SMCLK_SPI1SSN0,
        PA25_RXD2_I2SSCK_SPI1SSN1,
        PA26_CTS2_I2SWS_ADC12,
        PA27_RTS2_I2SSD_ADC13,

        PC0_SCL1_CTS1_PWM10_ADC14,
        PC1_SDA1_RTS1_PWM11_ADC15,

}
pin_name_t;

typedef enum {
    PORTA = 0,
    PORTB = 1,
} port_name_t;

#ifdef __cplusplus
}
#endif

#endif
