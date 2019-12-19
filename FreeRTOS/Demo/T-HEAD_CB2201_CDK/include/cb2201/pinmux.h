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

#ifndef __INCLUDE_HOBBIT_PINMUX_H
#define __INCLUDE_HOBBIT_PINMUX_H

/****************************************************************************************************
 * Included Files
 ****************************************************************************************************/

#include <stdint.h>


void hobbit_ioreuse_initial(void);

/*IOMUX0L function definition */
#define PA0_ETBT_RIG0                 0x00000000
#define PA0_JTAG_TCK                  0x00000002
#define PA1_ETB_TRIG1                 0x00000000
#define PA1_JTAG_TMS                  0x00000008
#define PA2_UART0_TX                  0x00000000
#define PA2_SPI0_MISO                 0x00000020
#define PA2_UART0_SIROUT              0x00000030
#define PA3_UART0_RX                  0x00000000
#define PA3_SPI0_MOSI                 0x00000080
#define PA3_UART0_SIRIN               0x000000C0
#define PA4_UART0_CTS                 0x00000000
#define PA4_PWM_CH0                   0x00000100
#define PA4_SPI0_CLK                  0x00000200
#define PA4_ETB_TRIG0                 0x00000300
#define PA5_UART0_TRS                 0x00000000
#define PA5_PWM_CH1                   0x00000400
#define PA5_SPI0_CS                   0x00000800
#define PA5_ETB_TRIG1                 0x00000C00
#define PB0_I2C0_SCL                  0x00000000
#define PB0_PWM_CH2                   0x00001000
#define PB0_I2S_MCLK                  0x00002000
#define PB1_I2C0_SDA                  0x00000000
#define PB1_PWM_CH3                   0x00004000
#define PB1_I2S_SCLK                  0x00008000
#define PB2_SPI0_CLK                  0x00000000
#define PB2_PWM_CH4                   0x00010000
#define PB2_I2S_WSCLK                 0x00020000
#define PB3_SPI0_MISO                 0x00000000
#define PB3_PWM_CH5                   0x00040000
#define PB3_I2S_SDA                   0x00080000
#define PA6_SPI0_MOSI                 0x00000000
#define PA6_PWM_CH6                   0x00100000
#define PA6_I2C0_SCL                  0x00200000
#define PA7_SPIO_CS                   0x00000000
#define PA7_PWM_CH7                   0x00400000
#define PA7_I2C0_SDA                  0x00800000
#define PA8_SYS_WKUP                  0x00000000
#define PA8_ADC_A0                    0x01000000
#define PA8_ACMP_P0                   0x02000000
#define PA9_BOOT                      0x00000000
#define PA9_ADC_A1                    0x04000000
#define PA9_PWM_FAULT                 0x08000000
#define PA10_ADC_A2                   0x10000000
#define PA10_UART0_TX                 0x20000000
#define PA10_UART0_SIROUT             0x30000000
#define PA11_ACMP_N0                  0x00000000
#define PA11_ADC_A3                   0x40000000
#define PA11_UART0_RX                 0x80000000
#define PA11_UART0_SIRIN              0xC0000000

/*IOMUX0H function definition*/
#define PA12_PWM_CH8                  0x00000000
#define PA12_JTAG_TCK                 0x00000001
#define PA12_ADC_A4                   0x00000002
#define PA13_PWM_CH9                  0x00000000
#define PA13_JTAG_TMS                 0x00000004
#define PA13_ADC_A5                   0x00000008
#define PA14_PWM_CH10                 0x00000000
#define PA14_ADC_A6                   0x00000010
#define PA15_PWM_CH11                 0x00000000
#define PA15_ADC_A7                   0x00000020
#define PA16_UART1_RX                 0x00000000
#define PA16_ADC_A8                   0x00000100
#define PA16_UART1_SIRIN              0x00000300
#define PA17_UART1_TX                 0x00000000
#define PA17_ADC_A9                   0x00000400
#define PA17_UART1_SIROUT             0x00000C00
#define PA18_SPI1_CS0                 0x00000000
#define PA18_ACMP_O0                  0x00001000
#define PA19_SPI_CS1                  0x00000000
#define PA20_SPI1_CS2                 0x00000000
#define PA20_ETB_TRIG0                0x00010000
#define PA20_UART1_RX                 0x00020000
#define PA20_UART1_SIRIN              0x00030000
#define PA21_SPI1_SCK                 0x00000000
#define PA21_ETB_TRIG1                0x00040000
#define PA21_UART1_TX                 0x00080000
#define PA21_UART1_SIROUT             0x000C0000
#define PA22_SPI1_MISO                0x00000000
#define PA22_PWM_CH0                  0x00100000
#define PA22_ADC_A10                  0x00200000
#define PA23_SPI_MOSI                 0x00000000
#define PA23_PWM_CH1                  0x00400000
#define PA23_ADC_A11                  0x00800000
#define PA24_UART2_TX                 0x00000000
#define PA24_I2S_MCLK                 0x01000000
#define PA24_SPI1_CS0                 0x02000000
#define PA24_UART2_SIROUT             0x03000000
#define PA25_UART2_RX                 0x00000000
#define PA25_I2C_SCLK                 0x04000000
#define PA25_SPI1_CS1                 0x08000000
#define PA25_UART2_SIRIN              0x0C000000
#define PA26_UART2_CTS                0x00000000
#define PA26_I2S_WSCLK                0x10000000
#define PA26_ADC_AD12                 0x20000000
#define PA27_UART2_RTS                0x00000000
#define PA27_I2S_SDA                  0x40000000
#define PA27_ADC_AD13                 0x80000000

/*IOMUX1L function definition*/
#define PC0_ICC1_SCL                  0x00000000
#define PC0_UART1_CTS                 0x00000001
#define PC0_PWM_CH10                  0x00000002
#define PC0_ADC_A14                   0x00000003
#define PC1_I2C1_SDA                  0x00000000
#define PC1_UART1_RTS                 0x00000004
#define PC1_PWM_CH11                  0x00000008
#define PC1_ADC_AD15                  0x0000000C

/*flag as identification*/
#define GPIO_SET_BIT0                 0x00000001
#define GPIO_SET_BIT1                 0x00000002
#define GPIO_SET_BIT2                 0x00000004
#define GPIO_SET_BIT3                 0x00000008
#define GPIO_SET_BIT4                 0x00000010
#define GPIO_SET_BIT5                 0x00000020
#define GPIO_SET_BIT6                 0x00000040
#define GPIO_SET_BIT7                 0x00000080
#define GPIO_SET_BIT8                 0x00000100
#define GPIO_SET_BIT9                 0x00000200
#define GPIO_SET_BIT10                0x00000400
#define GPIO_SET_BIT11                0x00000800
#define GPIO_SET_BIT12                0x00001000
#define GPIO_SET_BIT13                0x00002000
#define GPIO_SET_BIT14                0x00004000
#define GPIO_SET_BIT15                0x00008000
#define GPIO_SET_BIT16                0x00010000
#define GPIO_SET_BIT17                0x00020000
#define GPIO_SET_BIT18                0x00040000
#define GPIO_SET_BIT19                0x00080000
#define GPIO_SET_BIT20                0x00100000
#define GPIO_SET_BIT21                0x00200000
#define GPIO_SET_BIT22                0x00400000
#define GPIO_SET_BIT23                0x00800000
#define GPIO_SET_BIT24                0x01000000
#define GPIO_SET_BIT25                0x02000000
#define GPIO_SET_BIT26                0x04000000
#define GPIO_SET_BIT27                0x08000000
#define GPIO_SET_BIT28                0x10000000
#define GPIO_SET_BIT29                0x20000000
#define GPIO_SET_BIT30                0x40000000
#define GPIO_SET_BIT31                0x80000000

/*hobbit gpio control and gpio reuse function
selecting regester adddress
***********************************************/
#if defined  CONFIG_HOBBIT_NBIOT
#define HOBBIT_GIPO0_PORTCTL_REG      0xB0006008
#define HOBBIT_GIPO1_PORTCTL_REG      0xB0009008
#define HOBBIT_IOMUX0L_REG            0xB0006100
#define HOBBIT_IOMUX0H_REG            0xB0006104
#define HOBBIT_IOMUX1L_REG            0xB0006108
#else
#define HOBBIT_GIPO0_PORTCTL_REG      0x50018008
#define HOBBIT_GIPO1_PORTCTL_REG      0x60018008
#define HOBBIT_IOMUX0L_REG            0x50018100
#define HOBBIT_IOMUX0H_REG            0x50018104
#define HOBBIT_IOMUX1L_REG            0x50018108
#endif

#define BOARD_TYPE_HOBBIT_XJ_1
#if defined(BOARD_TYPE_HOBBIT_NG_1) || defined(BOARD_TYPE_HOBBIT_XJ_1)
/*************basic gpio reuse v1.0*************
UART0(PA2,PA3)
UART1(PA16,PA17)
UART2(PA24,PA25,PA26,PA27) either UART2 or IIS
//IIS(PA24,PA25,PA26,PA27)
SPI1(PA18,PA21,PA22,PA23)
IIC0(PB0,PB1)
PWM0(PA4)
ADC0((PA8)
ETB.TRIG0(PA20)
JTAG(PA0,PA1)
***********************************************/
#define GPIO0_REUSE_EN                (GPIO_SET_BIT0|GPIO_SET_BIT1|GPIO_SET_BIT2|GPIO_SET_BIT3|GPIO_SET_BIT4|GPIO_SET_BIT8|GPIO_SET_BIT16|GPIO_SET_BIT17|GPIO_SET_BIT18|GPIO_SET_BIT20|GPIO_SET_BIT21|GPIO_SET_BIT22|GPIO_SET_BIT23|GPIO_SET_BIT24|GPIO_SET_BIT25|GPIO_SET_BIT26|GPIO_SET_BIT27)
#define GPIO1_REUSE_EN                (GPIO_SET_BIT0|GPIO_SET_BIT1)
#define IOMUX0L_FUNCTION_SEL          (PA0_JTAG_TCK|PA1_JTAG_TMS|PA4_PWM_CH0|PA8_ADC_A0)
#define IOMUX0H_FUNCTION_SEL          (PA16_UART1_RX|PA17_UART1_TX|PA18_SPI1_CS0|PA20_ETB_TRIG0|PA21_SPI1_SCK|PA22_SPI1_MISO|PA23_SPI_MOSI|PA24_UART2_TX|PA25_UART2_RX|PA26_UART2_CTS|PA27_UART2_RTS)
#define IOMUX1L_FUNCTION_SEL          0x00000000
#else
#error board type has not been defined
#endif

#endif

