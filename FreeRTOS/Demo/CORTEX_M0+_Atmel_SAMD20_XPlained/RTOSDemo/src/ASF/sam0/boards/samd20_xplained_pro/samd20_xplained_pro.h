/**
 * \file
 *
 * \brief SAM D20 Xplained Pro board definition
 *
 * Copyright (c) 2013 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

#ifndef SAMD20_XPLAINED_PRO_H_INCLUDED
#define SAMD20_XPLAINED_PRO_H_INCLUDED

#include <conf_board.h>
#include <compiler.h>

/**
 * \ingroup group_common_boards
 * \defgroup samd20_xplained_pro_group SAM D20 Xplained Pro board
 *
 * @{
 */

void system_board_init(void);

/**
 * \defgroup samd20_xplained_pro_features_group Features
 *
 * Symbols that describe features and capabilities of the board.
 *
 * @{
 */

/** Name string macro */
#define BOARD_NAME                "SAMD20_XPLAINED_PRO"

/** \name Resonator definitions
 *  @{ */
#define BOARD_FREQ_SLCK_XTAL      (32768U)
#define BOARD_FREQ_SLCK_BYPASS    (32768U)
#define BOARD_FREQ_MAINCK_XTAL    0 /* Not Mounted */
#define BOARD_FREQ_MAINCK_BYPASS  0 /* Not Mounted */
#define BOARD_MCK                 CHIP_FREQ_CPU_MAX
#define BOARD_OSC_STARTUP_US      15625
/** @} */

/** \name LED0 definitions
 *  @{ */
#define LED0_PIN                  PIN_PA14
#define LED0_ACTIVE               false
#define LED0_INACTIVE             !LED0_ACTIVE
/** @} */

/** \name SW0 definitions
 *  @{ */
#define SW0_PIN                   PIN_PA15
#define SW0_ACTIVE                false
#define SW0_INACTIVE              !SW0_ACTIVE
#define SW0_EIC_PIN               PIN_PA15A_EIC_EXTINT15
#define SW0_EIC_MUX               MUX_PA15A_EIC_EXTINT15
#define SW0_EIC_PINMUX            PINMUX_PA15A_EIC_EXTINT15
#define SW0_EIC_LINE              15
/** @} */

/**
 * \name LED #0 definitions
 *
 * Wrapper macros for LED0, to ensure common naming across all Xplained Pro
 * boards.
 *
 *  @{ */
#define LED_0_NAME                "LED0 (yellow)"
#define LED_0_PIN                 LED0_PIN
#define LED_0_ACTIVE              LED0_ACTIVE
#define LED_0_INACTIVE            LED0_INACTIVE
/** @} */

/** Number of on-board LEDs */
#define LED_COUNT                 1

/**
 * \name Button #0 definitions
 *
 * Wrapper macros for SW0, to ensure common naming across all Xplained Pro
 * boards.
 *
 *  @{ */
#define BUTTON_0_NAME             "SW0"
#define BUTTON_0_PIN              SW0_PIN
#define BUTTON_0_ACTIVE           SW0_ACTIVE
#define BUTTON_0_INACTIVE         SW0_INACTIVE
#define BUTTON_0_EIC_PIN          SW0_EIC_PIN
#define BUTTON_0_EIC_MUX          SW0_EIC_MUX
#define BUTTON_0_EIC_PINMUX       SW0_EIC_PINMUX
#define BUTTON_0_EIC_LINE         SW0_EIC_LINE
/** @} */

/** Number of on-board buttons */
#define BUTTON_COUNT 1

/** \name Extension header #1 pin definitions
 *  @{
 */
#define EXT1_PIN_3                PIN_PB00
#define EXT1_PIN_4                PIN_PB01
#define EXT1_PIN_5                PIN_PB06
#define EXT1_PIN_6                PIN_PB07
#define EXT1_PIN_7                PIN_PB02
#define EXT1_PIN_8                PIN_PB03
#define EXT1_PIN_9                PIN_PB04
#define EXT1_PIN_10               PIN_PB05
#define EXT1_PIN_11               PIN_PA08
#define EXT1_PIN_12               PIN_PA09
#define EXT1_PIN_13               PIN_PB09
#define EXT1_PIN_14               PIN_PB08
#define EXT1_PIN_15               PIN_PA05
#define EXT1_PIN_16               PIN_PA06
#define EXT1_PIN_17               PIN_PA04
#define EXT1_PIN_18               PIN_PA07
/** @} */

/** \name Extension header #1 pin definitions by function
 *  @{
 */
#define EXT1_PIN_ADC_0            EXT1_PIN_3
#define EXT1_PIN_ADC_1            EXT1_PIN_4
#define EXT1_PIN_GPIO_0           EXT1_PIN_5
#define EXT1_PIN_GPIO_1           EXT1_PIN_6
#define EXT1_PIN_PWM_0            EXT1_PIN_7
#define EXT1_PIN_PWM_1            EXT1_PIN_8
#define EXT1_PIN_IRQ              EXT1_PIN_9
#define EXT1_PIN_I2C_SDA          EXT1_PIN_11
#define EXT1_PIN_I2C_SCL          EXT1_PIN_12
#define EXT1_PIN_UART_RX          EXT1_PIN_13
#define EXT1_PIN_UART_TX          EXT1_PIN_14
#define EXT1_PIN_SPI_SS_1         EXT1_PIN_10
#define EXT1_PIN_SPI_SS_0         EXT1_PIN_15
#define EXT1_PIN_SPI_MOSI         EXT1_PIN_16
#define EXT1_PIN_SPI_MISO         EXT1_PIN_17
#define EXT1_PIN_SPI_SCK          EXT1_PIN_18
/** @} */

/** \name Extension header #1 ADC definitions
 *  @{
 */
#define EXT1_ADC_MODULE           ADC
#define EXT1_ADC_0_CHANNEL        8
#define EXT1_ADC_0_PIN            PIN_PB00B_ADC_AIN8
#define EXT1_ADC_0_MUX            MUX_PB00B_ADC_AIN8
#define EXT1_ADC_0_PINMUX         PINMUX_PB00B_ADC_AIN8
#define EXT1_ADC_1_CHANNEL        9
#define EXT1_ADC_1_PIN            PIN_PB01B_ADC_AIN9
#define EXT1_ADC_1_MUX            MUX_PB01B_ADC_AIN9
#define EXT1_ADC_1_PINMUX         PINMUX_PB01B_ADC_AIN9
/** @} */

/** \name Extension header #1 PWM definitions
 *  @{
 */
#define EXT1_PWM_MODULE           TC6
#define EXT1_PWM_0_CHANNEL        0
#define EXT1_PWM_0_PIN            PIN_PB02F_TC6_WO0
#define EXT1_PWM_0_MUX            MUX_PB02F_TC6_WO0
#define EXT1_PWM_0_PINMUX         PINMUX_PB02F_TC6_WO0
#define EXT1_PWM_1_CHANNEL        1
#define EXT1_PWM_1_PIN            PIN_PB03F_TC6_WO1
#define EXT1_PWM_1_MUX            MUX_PB03F_TC6_WO1
#define EXT1_PWM_1_PINMUX         PINMUX_PB03F_TC6_WO1
/** @} */

/** \name Extension header #1 IRQ/External interrupt definitions
 *  @{
 */
#define EXT1_IRQ_MODULE           EIC
#define EXT1_IRQ_INPUT            4
#define EXT1_IRQ_PIN              PIN_PB04A_EIC_EXTINT4
#define EXT1_IRQ_MUX              MUX_PB04A_EIC_EXTINT4
#define EXT1_IRQ_PINMUX           PINMUX_PB04A_EIC_EXTINT4
/** @} */

/** \name Extension header #1 I2C definitions
 *  @{
 */
#define EXT1_I2C_MODULE              SERCOM2
#define EXT1_I2C_SERCOM_PINMUX_PAD0  PINMUX_PA08D_SERCOM2_PAD0
#define EXT1_I2C_SERCOM_PINMUX_PAD1  PINMUX_PA09D_SERCOM2_PAD1
/** @} */

/** \name Extension header #1 UART definitions
 *  @{
 */
#define EXT1_UART_MODULE              SERCOM4
#define EXT1_UART_SERCOM_MUX_SETTING  USART_RX_1_TX_0_XCK_1
#define EXT1_UART_SERCOM_PINMUX_PAD0  PINMUX_PB08D_SERCOM4_PAD0
#define EXT1_UART_SERCOM_PINMUX_PAD1  PINMUX_PB09D_SERCOM4_PAD1
#define EXT1_UART_SERCOM_PINMUX_PAD2  PINMUX_UNUSED
#define EXT1_UART_SERCOM_PINMUX_PAD3  PINMUX_UNUSED
/** @} */

/** \name Extension header #1 SPI definitions
 *  @{
 */
#define EXT1_SPI_MODULE              SERCOM0
#define EXT1_SPI_SERCOM_MUX_SETTING  SPI_SIGNAL_MUX_SETTING_E
#define EXT1_SPI_SERCOM_PINMUX_PAD0  PINMUX_PA04D_SERCOM0_PAD0
#define EXT1_SPI_SERCOM_PINMUX_PAD1  PINMUX_PA05D_SERCOM0_PAD1
#define EXT1_SPI_SERCOM_PINMUX_PAD2  PINMUX_PA06D_SERCOM0_PAD2
#define EXT1_SPI_SERCOM_PINMUX_PAD3  PINMUX_PA07D_SERCOM0_PAD3
/** @} */

/** \name Extension header #2 pin definitions
 *  @{
 */
#define EXT2_PIN_3                PIN_PA10
#define EXT2_PIN_4                PIN_PA11
#define EXT2_PIN_5                PIN_PA20
#define EXT2_PIN_6                PIN_PA21
#define EXT2_PIN_7                PIN_PA22
#define EXT2_PIN_8                PIN_PA23
#define EXT2_PIN_9                PIN_PB14
#define EXT2_PIN_10               PIN_PB15
#define EXT2_PIN_11               PIN_PA08
#define EXT2_PIN_12               PIN_PA09
#define EXT2_PIN_13               PIN_PB13
#define EXT2_PIN_14               PIN_PB12
#define EXT2_PIN_15               PIN_PA17
#define EXT2_PIN_16               PIN_PA18
#define EXT2_PIN_17               PIN_PA16
#define EXT2_PIN_18               PIN_PA19
/** @} */

/** \name Extension header #2 pin definitions by function
 *  @{
 */
#define EXT2_PIN_ADC_0            EXT2_PIN_3
#define EXT2_PIN_ADC_1            EXT2_PIN_4
#define EXT2_PIN_GPIO_0           EXT2_PIN_5
#define EXT2_PIN_GPIO_1           EXT2_PIN_6
#define EXT2_PIN_PWM_0            EXT2_PIN_7
#define EXT2_PIN_PWM_1            EXT2_PIN_8
#define EXT2_PIN_IRQ              EXT2_PIN_9
#define EXT2_PIN_I2C_SDA          EXT2_PIN_11
#define EXT2_PIN_I2C_SCL          EXT2_PIN_12
#define EXT2_PIN_UART_RX          EXT2_PIN_13
#define EXT2_PIN_UART_TX          EXT2_PIN_14
#define EXT2_PIN_SPI_SS_1         EXT2_PIN_10
#define EXT2_PIN_SPI_SS_0         EXT2_PIN_15
#define EXT2_PIN_SPI_MOSI         EXT2_PIN_16
#define EXT2_PIN_SPI_MISO         EXT2_PIN_17
#define EXT2_PIN_SPI_SCK          EXT2_PIN_18
/** @} */

/** \name Extension header #2 ADC definitions
 *  @{
 */
#define EXT2_ADC_MODULE           ADC
#define EXT2_ADC_0_CHANNEL        18
#define EXT2_ADC_0_PIN            PIN_PA10B_ADC_AIN18
#define EXT2_ADC_0_MUX            MUX_PA10B_ADC_AIN18
#define EXT2_ADC_0_PINMUX         PINMUX_PA10B_ADC_AIN18
#define EXT2_ADC_1_CHANNEL        19
#define EXT2_ADC_1_PIN            PIN_PA11B_ADC_AIN19
#define EXT2_ADC_1_MUX            MUX_PA11B_ADC_AIN19
#define EXT2_ADC_1_PINMUX         PINMUX_PA11B_ADC_AIN19
/** @} */

/** \name Extension header #2 PWM definitions
 *  @{
 */
#define EXT2_PWM_MODULE           TC4
#define EXT2_PWM_0_CHANNEL        0
#define EXT2_PWM_0_PIN            PIN_PA22F_TC4_WO0
#define EXT2_PWM_0_MUX            MUX_PA22F_TC4_WO0
#define EXT2_PWM_0_PINMUX         PINMUX_PA22F_TC4_WO0
#define EXT2_PWM_1_CHANNEL        1
#define EXT2_PWM_1_PIN            PIN_PA23F_TC4_WO1
#define EXT2_PWM_1_MUX            MUX_PA23F_TC4_WO1
#define EXT2_PWM_1_PINMUX         PINMUX_PA23F_TC4_WO1
/** @} */

/** \name Extension header #2 IRQ/External interrupt definitions
 *  @{
 */
#define EXT2_IRQ_MODULE           EIC
#define EXT2_IRQ_INPUT            14
#define EXT2_IRQ_PIN              PIN_PB14A_EIC_EXTINT14
#define EXT2_IRQ_MUX              MUX_PB14A_EIC_EXTINT14
#define EXT2_IRQ_PINMUX           PINMUX_PB14A_EIC_EXTINT14
/** @} */

 /** \name Extension header #2 I2C definitions
 *  @{
 */
#define EXT2_I2C_MODULE              SERCOM2
#define EXT2_I2C_SERCOM_PINMUX_PAD0  PINMUX_PA08D_SERCOM2_PAD0
#define EXT2_I2C_SERCOM_PINMUX_PAD1  PINMUX_PA09D_SERCOM2_PAD1
/** @} */

/** \name Extension header #2 UART definitions
 *  @{
 */
#define EXT2_UART_MODULE              SERCOM4
#define EXT2_UART_SERCOM_MUX_SETTING  USART_RX_1_TX_0_XCK_1
#define EXT2_UART_SERCOM_PINMUX_PAD0  PINMUX_PB12C_SERCOM4_PAD0
#define EXT2_UART_SERCOM_PINMUX_PAD1  PINMUX_PB13C_SERCOM4_PAD1
#define EXT2_UART_SERCOM_PINMUX_PAD2  PINMUX_UNUSED
#define EXT2_UART_SERCOM_PINMUX_PAD3  PINMUX_UNUSED
/** @} */

/** \name Extension header #2 SPI definitions
 *  @{
 */
#define EXT2_SPI_MODULE              SERCOM1
#define EXT2_SPI_SERCOM_MUX_SETTING  SPI_SIGNAL_MUX_SETTING_E
#define EXT2_SPI_SERCOM_PINMUX_PAD0  PINMUX_PA16C_SERCOM1_PAD0
#define EXT2_SPI_SERCOM_PINMUX_PAD1  PINMUX_PA17C_SERCOM1_PAD1
#define EXT2_SPI_SERCOM_PINMUX_PAD2  PINMUX_PA18C_SERCOM1_PAD2
#define EXT2_SPI_SERCOM_PINMUX_PAD3  PINMUX_PA19C_SERCOM1_PAD3
/** @} */

/** \name Extension header #3 pin definitions
 *  @{
 */
#define EXT3_PIN_3                PIN_PA02
#define EXT3_PIN_4                PIN_PA03
#define EXT3_PIN_5                PIN_PB30
#define EXT3_PIN_6                PIN_PA15
#define EXT3_PIN_7                PIN_PA12
#define EXT3_PIN_8                PIN_PA13
#define EXT3_PIN_9                PIN_PA28
#define EXT3_PIN_10               PIN_PA27
#define EXT3_PIN_11               PIN_PA08
#define EXT3_PIN_12               PIN_PA09
#define EXT3_PIN_13               PIN_PB11
#define EXT3_PIN_14               PIN_PB10
#define EXT3_PIN_15               PIN_PB17
#define EXT3_PIN_16               PIN_PB22
#define EXT3_PIN_17               PIN_PB16
#define EXT3_PIN_18               PIN_PB23
/** @} */

/** \name Extension header #3 pin definitions by function
 *  @{
 */
#define EXT3_PIN_ADC_0            EXT3_PIN_3
#define EXT3_PIN_ADC_1            EXT3_PIN_4
#define EXT3_PIN_GPIO_0           EXT3_PIN_5
#define EXT3_PIN_GPIO_1           EXT3_PIN_6
#define EXT3_PIN_PWM_0            EXT3_PIN_7
#define EXT3_PIN_PWM_1            EXT3_PIN_8
#define EXT3_PIN_IRQ              EXT3_PIN_9
#define EXT3_PIN_I2C_SDA          EXT3_PIN_11
#define EXT3_PIN_I2C_SCL          EXT3_PIN_12
#define EXT3_PIN_UART_RX          EXT3_PIN_13
#define EXT3_PIN_UART_TX          EXT3_PIN_14
#define EXT3_PIN_SPI_SS_1         EXT3_PIN_10
#define EXT3_PIN_SPI_SS_0         EXT3_PIN_15
#define EXT3_PIN_SPI_MOSI         EXT3_PIN_16
#define EXT3_PIN_SPI_MISO         EXT3_PIN_17
#define EXT3_PIN_SPI_SCK          EXT3_PIN_18
/** @} */

/** \name Extension header #3 ADC definitions
 *  @{
 */
#define EXT3_ADC_MODULE           ADC
#define EXT3_ADC_0_CHANNEL        0
#define EXT3_ADC_0_PIN            PIN_PA02B_ADC_AIN0
#define EXT3_ADC_0_MUX            MUX_PA02B_ADC_AIN0
#define EXT3_ADC_0_PINMUX         PINMUX_PA02B_ADC_AIN0
#define EXT3_ADC_1_CHANNEL        1
#define EXT3_ADC_1_PIN            PIN_PA03B_ADC_AIN1
#define EXT3_ADC_1_MUX            MUX_PA03B_ADC_AIN1
#define EXT3_ADC_1_PINMUX         PINMUX_PA03B_ADC_AIN1
/** @} */

/** \name Extension header #3 PWM definitions
 *  @{
 */
#define EXT3_PWM_MODULE           TC2
#define EXT3_PWM_0_CHANNEL        0
#define EXT3_PWM_0_PIN            PIN_PA12E_TC2_WO0
#define EXT3_PWM_0_MUX            MUX_PA12E_TC2_WO0
#define EXT3_PWM_0_PINMUX         PINMUX_PA12E_TC2_WO0
#define EXT3_PWM_1_CHANNEL        1
#define EXT3_PWM_1_PIN            PIN_PA13E_TC2_WO1
#define EXT3_PWM_1_MUX            MUX_PA13E_TC2_WO1
#define EXT3_PWM_1_PINMUX         PINMUX_PA13E_TC2_WO1
/** @} */

/** \name Extension header #3 IRQ/External interrupt definitions
 *  @{
 */
#define EXT3_IRQ_MODULE           EIC
#define EXT3_IRQ_INPUT            8
#define EXT3_IRQ_PIN              PIN_PA28A_EIC_EXTINT8
#define EXT3_IRQ_MUX              MUX_PA28A_EIC_EXTINT8
#define EXT3_IRQ_PINMUX           PINMUX_PA28A_EIC_EXTINT8
/** @} */

/** \name Extension header #3 I2C definitions
 *  @{
 */
#define EXT3_I2C_MODULE              SERCOM2
#define EXT3_I2C_SERCOM_PINMUX_PAD0  PINMUX_PA08D_SERCOM2_PAD0
#define EXT3_I2C_SERCOM_PINMUX_PAD1  PINMUX_PA09D_SERCOM2_PAD1
/** @} */

/** \name Extension header #3 UART definitions
 *  @{
 */
#define EXT3_UART_MODULE              SERCOM4
#define EXT3_UART_SERCOM_MUX_SETTING  USART_RX_3_TX_2_XCK_3
#define EXT3_UART_SERCOM_PINMUX_PAD0  PINMUX_UNUSED
#define EXT3_UART_SERCOM_PINMUX_PAD1  PINMUX_UNUSED
#define EXT3_UART_SERCOM_PINMUX_PAD2  PINMUX_PB10D_SERCOM4_PAD2
#define EXT3_UART_SERCOM_PINMUX_PAD3  PINMUX_PB11D_SERCOM4_PAD3
/** @} */

/** \name Extension header #3 SPI definitions
 *  @{
 */
#define EXT3_SPI_MODULE              SERCOM5
#define EXT3_SPI_SERCOM_MUX_SETTING  SPI_SIGNAL_MUX_SETTING_E
#define EXT3_SPI_SERCOM_PINMUX_PAD0  PINMUX_PB16C_SERCOM5_PAD0
#define EXT3_SPI_SERCOM_PINMUX_PAD1  PINMUX_PB17C_SERCOM5_PAD1
#define EXT3_SPI_SERCOM_PINMUX_PAD2  PINMUX_PB22D_SERCOM5_PAD2
#define EXT3_SPI_SERCOM_PINMUX_PAD3  PINMUX_PB23D_SERCOM5_PAD3
/** @} */

/** \name Embedded debugger GPIO interface definitions
 * @{
 */
#define EDBG_GPIO0_PIN            PIN_PA27
#define EDBG_GPIO1_PIN            PIN_PA28
#define EDBG_GPIO2_PIN            PIN_PA20
#define EDBG_GPIO3_PIN            PIN_PA21
/** @} */

/** \name Embedded debugger USART interface definitions
 * @{
 */
#define EDBG_UART_MODULE          -1 /* Not available on this board */
#define EDBG_UART_RX_PIN          -1 /* Not available on this board */
#define EDBG_UART_RX_MUX          -1 /* Not available on this board */
#define EDBG_UART_RX_PINMUX       -1 /* Not available on this board */
#define EDBG_UART_RX_SERCOM_PAD   -1 /* Not available on this board */
#define EDBG_UART_TX_PIN          -1 /* Not available on this board */
#define EDBG_UART_TX_MUX          -1 /* Not available on this board */
#define EDBG_UART_TX_PINMUX       -1 /* Not available on this board */
#define EDBG_UART_TX_SERCOM_PAD   -1 /* Not available on this board */
/** @} */

/** \name Embedded debugger I2C interface definitions
 * @{
 */
#define EDBG_I2C_MODULE              SERCOM2
#define EDBG_I2C_SERCOM_PINMUX_PAD0  PINMUX_PA08D_SERCOM2_PAD0
#define EDBG_I2C_SERCOM_PINMUX_PAD1  PINMUX_PA09D_SERCOM2_PAD1
/** @} */

/** \name Embedded debugger SPI interface definitions
 * @{
 */
#define EDBG_SPI_MODULE              SERCOM5
#define EDBG_SPI_SERCOM_MUX_SETTING  SPI_SIGNAL_MUX_SETTING_E
#define EDBG_SPI_SERCOM_PINMUX_PAD0  PINMUX_PB16C_SERCOM5_PAD0
#define EDBG_SPI_SERCOM_PINMUX_PAD1  PINMUX_PB31D_SERCOM5_PAD1
#define EDBG_SPI_SERCOM_PINMUX_PAD2  PINMUX_PB22D_SERCOM5_PAD2
#define EDBG_SPI_SERCOM_PINMUX_PAD3  PINMUX_PB23D_SERCOM5_PAD3
/** @} */

/** \name Embedded debugger CDC Gateway USART interface definitions
 * @{
 */
#define EDBG_CDC_MODULE              SERCOM3
#define EDBG_CDC_SERCOM_MUX_SETTING  USART_RX_3_TX_2_XCK_3
#define EDBG_CDC_SERCOM_PINMUX_PAD0  PINMUX_UNUSED
#define EDBG_CDC_SERCOM_PINMUX_PAD1  PINMUX_UNUSED
#define EDBG_CDC_SERCOM_PINMUX_PAD2  PINMUX_PA24C_SERCOM3_PAD2
#define EDBG_CDC_SERCOM_PINMUX_PAD3  PINMUX_PA25C_SERCOM3_PAD3
/** @} */

/** @} */

/** @} */

#endif  /* SAMD20_XPLAINED_PRO_H_INCLUDED */
