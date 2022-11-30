/**
 * \file
 *
 * \brief SAM4L-EK Board header file.
 *
 * This file contains definitions and services related to the features of the
 * SAM4L-EK Board.
 *
 * To use this board define BOARD=SAM4L_EK.
 *
 * Copyright (c) 2012 - 2013 Atmel Corporation. All rights reserved.
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
#ifndef SAM4L_EK_INCLUDED
#define SAM4L_EK_INCLUDED

#include "compiler.h"

/** Name of the board */
#define BOARD_NAME "SAM4L-EK"

/**
 * \defgroup sam4l_ek_group SAM4L-EK Board
 * @{
 */

/**
 * \defgroup sam4l_ek_feature_group Feature definitions
 * @{
 */

//! \name Miscellaneous data
//@{
//@}

//! Osc frequency (Hz.) and startup time (RCOsc periods).
#define FOSC0                       (12000000)

//! Osc32 frequency (Hz.) and startup time (RCOsc periods).
#define FOSC32                      (32768)

/**
 * \name Board oscillator configuration
 *
 */
//@{
#define BOARD_OSC32_IS_XTAL         true
#define BOARD_OSC32_HZ              FOSC32
#define BOARD_OSC32_STARTUP_US      (1100000)
#define BOARD_OSC32_SELCURR         BSCIF_OSCCTRL32_SELCURR(10)
#define BOARD_OSC0_IS_XTAL          true
#define BOARD_OSC0_HZ               FOSC0
#define BOARD_OSC0_STARTUP_US       (1100)
//@}

/*! \name Number of LEDs.
 */
//! @{
#define LED_COUNT   1
//! @}

/**
 * \name LEDs
 *
 * LED0 is a single yellow LED that is active low.
 */
//@{
#define LED0                            PC10
#define LED0_GPIO                       PIN_PC10
#define LED0_GPIO_MASK                  GPIO_PC10
#if defined(SAM4L_EK_REV1)
#  define LED0_ACTIVE_LEVEL             IOPORT_PIN_LEVEL_LOW
#  define LED0_INACTIVE_LEVEL           IOPORT_PIN_LEVEL_HIGH
#else
#  define LED0_ACTIVE_LEVEL             IOPORT_PIN_LEVEL_HIGH
#  define LED0_INACTIVE_LEVEL           IOPORT_PIN_LEVEL_LOW
#endif
//@}

/**
 * \name LCD Backlight
 */
//@{
#if defined(SAM4L_EK_REV1)
#  define LCD_BL                        PA02
#  define LCD_BL_GPIO                   PIN_PA02
#  define LCD_BL_GPIO_MASK              GPIO_PA02
#else
#  define LCD_BL                        PC14
#  define LCD_BL_GPIO                   PIN_PC14
#  define LCD_BL_GPIO_MASK              GPIO_PC14
#endif
#define LCD_BL_ACTIVE_LEVEL             IOPORT_PIN_LEVEL_HIGH
#define LCD_BL_INACTIVE_LEVEL           IOPORT_PIN_LEVEL_LOW
//@}

/*! \name GPIO Connections of Push Buttons
 */
//! @{
#define GPIO_PUSH_BUTTON_0              PIN_PC03
#define GPIO_PUSH_BUTTON_0_MASK         GPIO_PC03
#define PUSH_BUTTON_0_DOWN_LEVEL        IOPORT_PIN_LEVEL_LOW
#define PUSH_BUTTON_0_UP_LEVEL          IOPORT_PIN_LEVEL_HIGH
//! @}

/*! \name Push Button Connection on External Interrupt line
 */
//! @{
#define GPIO_PUSH_BUTTON_EIC_PIN        PIN_PC03B_EIC_EXTINT5
#define GPIO_PUSH_BUTTON_EIC_PIN_MASK   GPIO_PC03B_EIC_EXTINT5
#define GPIO_PUSH_BUTTON_EIC_PIN_MUX    MUX_PC03B_EIC_EXTINT5
#define GPIO_PUSH_BUTTON_EIC_LINE       5

#define GPIO_UNIT_TEST_EIC_PIN        PIN_PA06C_EIC_EXTINT1
#define GPIO_UNIT_TEST_EIC_PIN_MASK   GPIO_PA06C_EIC_EXTINT1
#define GPIO_UNIT_TEST_EIC_PIN_MUX    MUX_PA06C_EIC_EXTINT1
#define GPIO_UNIT_TEST_EIC_LINE       1

#define GPIO_EIC_TRIG_PIN       PIN_PB05
//! @}


/*! \name GPIO Connections of Touch sensors
 */
//! @{
#define GPIO_QTOUCH_SLIDER_0            PIN_PB02
#define GPIO_QTOUCH_SLIDER_0_MASK       GPIO_PB02
#define GPIO_QTOUCH_SLIDER_0_MUX        MUX_PB02G_CATB_SENSE23
#define GPIO_QTOUCH_SLIDER_1            PIN_PA04
#define GPIO_QTOUCH_SLIDER_1_MASK       GPIO_PA04
#define GPIO_QTOUCH_SLIDER_1_MUX       	MUX_PA04G_CATB_SENSE0
#define GPIO_QTOUCH_SLIDER_2            PIN_PA05
#define GPIO_QTOUCH_SLIDER_2_MASK       GPIO_PA05
#define GPIO_QTOUCH_SLIDER_2_MUX        MUX_PA05G_CATB_SENSE1
#define GPIO_QTOUCH_DISCHARGE           PIN_PB03
#define GPIO_QTOUCH_DISCHARGE_MASK      GPIO_PB03
#define GPIO_QTOUCH_DISCHARGE_MUX       MUX_PB03G_CATB_DIS
#define GPIO_QTOUCH_BUTTON              PIN_PB04
#define GPIO_QTOUCH_BUTTON_MASK         GPIO_PB04
#define GPIO_QTOUCH_BUTTON_MUX          MUX_PB04G_CATB_SENSE24
//! @}

/*! \name Touch sensors pin assignements
 */
//! @{
#define QTOUCH_PINSEL_SLIDER_0          23
#define QTOUCH_PINSEL_SLIDER_1          0
#define QTOUCH_PINSEL_SLIDER_2          1
#define QTOUCH_PINSEL_BUTTON            24
//! @}

/*! \name GPIO Connections of SAM4L4C VBUS monitoring
 */
//! @{
#if defined(SAM4L_EK_REV1)
#define USB_VBUS_FLAGS           IOPORT_MODE_GLITCH_FILTER
#define USB_VBUS_PIN             PIN_PC14  /* As IO pin input */
/* No EIC for VBus pin */
#elif 0 // The Vbus monitoring can not be used on SAM4L_EK Rev. 2
#define USB_VBUS_FLAGS           IOPORT_MODE_GLITCH_FILTER
#define USB_VBUS_EIC             PIN_PA06C_EIC_EXTINT1 /* As EIC input */
#define USB_VBUS_EIC_MUX         IOPORT_MODE_MUX_C
#define USB_VBUS_EIC_LINE        1
#define USB_VBUS_EIC_IRQn        EIC_1_IRQn
#endif
//! @}

/*! \name GPIO Connections of SAM4L4C VBUS Power Control
 */
//! @{
#define USB_VBOF_PIN            PIN_PC08 /* As IO pin output */
#define USB_VBOF_ACTIVE_LEVEL   0
#define USB_VBOF_INACTIVE_LEVEL 1
//! @}

/*! \name GPIO Connections of SAM4L4C VBUS error detecting
 */
//! @{
#define USB_VBERR_FLAGS          IOPORT_MODE_PULLUP | IOPORT_MODE_GLITCH_FILTER
#define USB_VBERR_PIN            PIN_PC07 /* As IO pin input */
/* No EIC for VBErr pin */
//! @}

/*! \name GPIO Connections of SAM4L4C ID detecting
 */
//! @{
#define USB_ID_FLAGS             IOPORT_MODE_PULLUP | IOPORT_MODE_GLITCH_FILTER
#define USB_ID_PIN               PIN_PB05 /* As IO pin input */
/* No EIC for ID pin */
//! @}


//! \name USART connections to GPIO for Virtual Com Port
// @{
#define COM_PORT_USART                 USART2
#define COM_PORT_USART_ID              ID_USART2
#define COM_PORT_RX_PIN                PIN_PC11B_USART2_RXD
#define COM_PORT_RX_GPIO               GPIO_PC11B_USART2_RXD
#define COM_PORT_RX_MUX                MUX_PC11B_USART2_RXD
#define COM_PORT_TX_PIN                PIN_PC12B_USART2_TXD
#define COM_PORT_TX_GPIO               GPIO_PC12B_USART2_TXD
#define COM_PORT_TX_MUX                MUX_PC12B_USART2_TXD
// @}

//! \name USART connections to the Board Monitor
// @{
#define BM_USART_USART                 USART0
#define BM_USART_USART_ID              ID_USART0
#define BM_USART_RX_PIN                PIN_PC02C_USART0_RXD
#define BM_USART_RX_GPIO               GPIO_PC02C_USART0_RXD
#define BM_USART_RX_MUX                MUX_PC02C_USART0_RXD
#define BM_USART_TX_PIN                PIN_PA07B_USART0_TXD
#define BM_USART_TX_GPIO               GPIO_PA07B_USART0_TXD
#define BM_USART_TX_MUX                MUX_PA07B_USART0_TXD
// @}

//! \name USART connections to the RS485
// @{
#define RS485_USART_USART              USART0
#define RS485_USART_USART_ID           ID_USART0
#define RS485_USART_RX_PIN             PIN_PC02C_USART0_RXD
#define RS485_USART_RX_GPIO            GPIO_PC02C_USART0_RXD
#define RS485_USART_RX_MUX             MUX_PC02C_USART0_RXD
#define RS485_USART_TX_PIN             PIN_PA07B_USART0_TXD
#define RS485_USART_TX_GPIO            GPIO_PA07B_USART0_TXD
#define RS485_USART_TX_MUX             MUX_PA07B_USART0_TXD
#define RS485_USART_RTS_PIN            PIN_PA06B_USART0_RTS
#define RS485_USART_RTS_GPIO           GPIO_PA06B_USART0_RTS
#define RS485_USART_RTS_MUX            MUX_PA06B_USART0_RTS
#define RS485_USART_CTS_PIN            PIN_PC08E_USART2_CTS
#define RS485_USART_CTS_GPIO           GPIO_PC08E_USART2_CTS
#define RS485_USART_CTS_MUX            MUX_PC08E_USART2_CTS
// @}

//! \name TWIMS1 pins
// @{
#define TWIMS1_TWI_SDA_PIN   PIN_PB00A_TWIMS1_TWD
#define TWIMS1_TWI_SDA_GPIO  GPIO_PB00A_TWIMS1_TWD
#define TWIMS1_TWI_SDA_MUX   MUX_PB00A_TWIMS1_TWD
#define TWIMS1_TWI_SCL_PIN   PIN_PB01A_TWIMS1_TWCK
#define TWIMS1_TWI_SCL_GPIO  GPIO_PB01A_TWIMS1_TWCK
#define TWIMS1_TWI_SCL_MUX   MUX_PB01A_TWIMS1_TWCK
// @}

//! \name USART0 pins
// @{
#define USART0_RX_PIN   PIN_PC02C_USART0_RXD
#define USART0_RX_MUX   MUX_PC02C_USART0_RXD
#define USART0_RX_GPIO  GPIO_PC02C_USART0_RXD
#define USART0_TX_PIN   PIN_PA07B_USART0_TXD
#define USART0_TX_MUX   MUX_PA07B_USART0_TXD
#define USART0_TX_GPIO  GPIO_PA07B_USART0_TXD
// @}

//! \name DACC pins
// @{
#define DACC_EXT_TRIG0_PIN             PIN_PB04E_DACC_EXT_TRIG0
#define DACC_EXT_TRIG0_GPIO            GPIO_PB04E_DACC_EXT_TRIG0
#define DACC_EXT_TRIG0_MUX             MUX_PB04E_DACC_EXT_TRIG0
#define DACC_VOUT_PIN                  PIN_PA06A_DACC_VOUT
#define DACC_VOUT_GPIO                 GPIO_PA06A_DACC_VOUT
#define DACC_VOUT_MUX                  MUX_PA06A_DACC_VOUT
// @}

/* Select the SPI module that AT25DFx is connected to */
#define AT25DFX_SPI_MODULE          SPI

/* Chip select used by AT25DFx components on the SPI module instance */
#define AT25DFX_CS      2

/**
 * @}
 */

#endif /* SAM4L_EK_INCLUDED */
