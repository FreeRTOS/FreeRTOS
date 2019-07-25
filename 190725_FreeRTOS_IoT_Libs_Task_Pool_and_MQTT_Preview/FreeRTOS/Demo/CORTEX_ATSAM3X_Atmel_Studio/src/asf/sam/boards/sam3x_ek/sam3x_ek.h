/**
 * \file
 *
 * \brief SAM3X-EK Board Definition.
 *
 * Copyright (c) 2011 - 2012 Atmel Corporation. All rights reserved.
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

#ifndef _SAM3X_EK_H_
#define _SAM3X_EK_H_

#include "compiler.h"
#include "system_sam3x.h"
#include "exceptions.h"

/*#define BOARD_REV_A */
#define BOARD_REV_B

/* ------------------------------------------------------------------------ */

/**
 *  \page sam3x_ek_opfreq "SAM3X-EK - Operating frequencies"
 *  This page lists several definition related to the board operating frequency
 *
 *  \section Definitions
 *  - \ref BOARD_FREQ_*
 *  - \ref BOARD_MCK
 */

/*! Board oscillator settings */
#define BOARD_FREQ_SLCK_XTAL            (32768U)
#define BOARD_FREQ_SLCK_BYPASS          (32768U)
#define BOARD_FREQ_MAINCK_XTAL          (12000000U)
#define BOARD_FREQ_MAINCK_BYPASS        (12000000U)

/*! Master clock frequency */
#define BOARD_MCK                       CHIP_FREQ_CPU_MAX

/* ------------------------------------------------------------------------ */

/**
 * \page sam3x_ek_board_info "SAM3X-EK - Board informations"
 * This page lists several definition related to the board description.
 *
 * \section Definitions
 * - \ref BOARD_NAME
 */

/*! Name of the board */
#define BOARD_NAME "SAM3X-EK"
/*! Board definition */
#define sam3xek
/*! Family definition (already defined) */
#define sam3x
/*! Core definition */
#define cortexm3

/* ------------------------------------------------------------------------ */

/**
 * \page sam3x_ek_piodef "SAM3X-EK - PIO definitions"
 * This pages lists all the pio definitions. The constants
 * are named using the following convention: PIN_* for a constant which defines
 * a single Pin instance (but may include several PIOs sharing the same
 * controller), and PINS_* for a list of Pin instances.
 *
 */

/**
 * \file
 * ADC
 * - \ref PIN_ADC0_AD1
 * - \ref PINS_ADC
 *
 */

/*! ADC_AD1 pin definition. */
#define PIN_ADC0_AD1 {PIO_PA3X1_AD1, PIOA, ID_PIOA, PIO_INPUT, PIO_DEFAULT}
#define PINS_ADC_TRIG  PIO_PA11_IDX
#define PINS_ADC_TRIG_FLAG  (PIO_PERIPH_B | PIO_DEFAULT)
/*! Pins ADC */
#define PINS_ADC PIN_ADC0_AD1

/**
 * \file
 * EBI
 * - \ref PIN_EBI_DATA_BUS
 * - \ref PIN_EBI_NRD
 * - \ref PIN_EBI_NWE
 * - \ref PIN_EBI_NCS0
 * - \ref PIN_EBI_PSRAM_ADDR_BUS
 * - \ref PIN_EBI_PSRAM_NBS
 * - \ref PIN_EBI_A1
 * - \ref PIN_EBI_NCS1
 * - \ref PIN_EBI_LCD_RS
 *
 */

/* ------------------------------------------------------------------------ */
/* EBI */
/* ------------------------------------------------------------------------ */
/*! EBI Data Bus pins */
#define PIN_EBI_DATA_BUS_D0       PIO_PC2_IDX
#define PIN_EBI_DATA_BUS_D1       PIO_PC3_IDX
#define PIN_EBI_DATA_BUS_D2       PIO_PC4_IDX
#define PIN_EBI_DATA_BUS_D3       PIO_PC5_IDX
#define PIN_EBI_DATA_BUS_D4       PIO_PC6_IDX
#define PIN_EBI_DATA_BUS_D5       PIO_PC7_IDX
#define PIN_EBI_DATA_BUS_D6       PIO_PC8_IDX
#define PIN_EBI_DATA_BUS_D7       PIO_PC9_IDX
#define PIN_EBI_DATA_BUS_D8       PIO_PC10_IDX
#define PIN_EBI_DATA_BUS_D9       PIO_PC11_IDX
#define PIN_EBI_DATA_BUS_D10      PIO_PC12_IDX
#define PIN_EBI_DATA_BUS_D11      PIO_PC13_IDX
#define PIN_EBI_DATA_BUS_D12      PIO_PC14_IDX
#define PIN_EBI_DATA_BUS_D13      PIO_PC15_IDX
#define PIN_EBI_DATA_BUS_D14      PIO_PC16_IDX
#define PIN_EBI_DATA_BUS_D15      PIO_PC17_IDX
#define PIN_EBI_DATA_BUS_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)
/*! EBI NRD pin */
#define PIN_EBI_NRD            PIO_PA29_IDX
#define PIN_EBI_NRD_FLAGS      (PIO_PERIPH_B | PIO_PULLUP)
#define PIN_EBI_NRD_MASK       (1 << 29)
#define PIN_EBI_NRD_PIO        PIOB
#define PIN_EBI_NRD_ID         ID_PIOB
#define PIN_EBI_NRD_TYPE       PIO_PERIPH_B
#define PIN_EBI_NRD_ATTR       PIO_PULLUP
/*! EBI NWE pin */
#define PIN_EBI_NWE            PIO_PC18_IDX
#define PIN_EBI_NWE_FLAGS      (PIO_PERIPH_A | PIO_PULLUP)
#define PIN_EBI_NWE_MASK       (1 << 18)
#define PIN_EBI_NWE_PIO        PIOC
#define PIN_EBI_NWE_ID         ID_PIOC
#define PIN_EBI_NWE_TYPE       PIO_PERIPH_A
#define PIN_EBI_NWE_ATTR       PIO_PULLUP
/*! EBI NCS0 pin */
#define PIN_EBI_NCS0           PIO_PA6_IDX
#define PIN_EBI_NCS0_FLAGS     (PIO_PERIPH_B | PIO_PULLUP)
#define PIN_EBI_NCS0_MASK      (1 << 6)
#define PIN_EBI_NCS0_PIO       PIOA
#define PIN_EBI_NCS0_ID        ID_PIOA
#define PIN_EBI_NCS0_TYPE      PIO_PERIPH_B
#define PIN_EBI_NCS0_ATTR      PIO_PULLUP
/*! EBI address bus pins */
#define PIN_EBI_ADDR_BUS_A0    PIO_PC21_IDX
#define PIN_EBI_ADDR_BUS_NBS0  PIO_PC21_IDX
#define PIN_EBI_ADDR_BUS_A1    PIO_PC22_IDX
#define PIN_EBI_ADDR_BUS_NBS1  PIO_PD10_IDX
#define PIN_EBI_ADDR_BUS_A2    PIO_PC23_IDX
#define PIN_EBI_ADDR_BUS_A3    PIO_PC24_IDX
#define PIN_EBI_ADDR_BUS_A4    PIO_PC25_IDX
#define PIN_EBI_ADDR_BUS_A5    PIO_PC26_IDX
#define PIN_EBI_ADDR_BUS_A6    PIO_PC27_IDX
#define PIN_EBI_ADDR_BUS_A7    PIO_PC28_IDX
#define PIN_EBI_ADDR_BUS_A8    PIO_PC29_IDX
#define PIN_EBI_ADDR_BUS_A9    PIO_PC30_IDX
#define PIN_EBI_ADDR_BUS_A10   PIO_PD0_IDX
#define PIN_EBI_ADDR_BUS_A11   PIO_PD1_IDX
#define PIN_EBI_ADDR_BUS_A12   PIO_PD2_IDX
#define PIN_EBI_ADDR_BUS_A13   PIO_PD3_IDX
#define PIN_EBI_ADDR_BUS_A14   PIO_PD4_IDX
#define PIN_EBI_ADDR_BUS_A15   PIO_PD5_IDX
#define PIN_EBI_ADDR_BUS_A16   PIO_PD6_IDX
#define PIN_EBI_ADDR_BUS_A17   PIO_PD7_IDX
#define PIN_EBI_ADDR_BUS_FLAG1 (PIO_PERIPH_A | PIO_PULLUP)
#define PIN_EBI_ADDR_BUS_A18   PIO_PA25_IDX
#define PIN_EBI_ADDR_BUS_A19   PIO_PA26_IDX
#define PIN_EBI_ADDR_BUS_A20   PIO_PA27_IDX
#define PIN_EBI_ADDR_BUS_FLAG2 (PIO_PERIPH_B | PIO_PULLUP)
/*! EBI pin for LCD CS */
#define PIN_EBI_NCS2           PIO_PB24_IDX
#define PIN_EBI_NCS2_FLAGS     (PIO_PERIPH_B | PIO_PULLUP)
#define PIN_EBI_NCS2_MASK      (1 << 24)
#define PIN_EBI_NCS2_PIO       PIOB
#define PIN_EBI_NCS2_ID        ID_PIOB
#define PIN_EBI_NCS2_TYPE      PIO_PERIPH_B
#define PIN_EBI_NCS2_ATTR      PIO_PULLUP
/*! EBI pin for LCD RS */
#define PIN_EBI_LCD_RS         PIO_PC22_IDX
#define PIN_EBI_LCD_RS_FLAGS   (PIO_PERIPH_A | PIO_PULLUP)
#define PIN_EBI_LCD_RS_MASK    (1 << 22)
#define PIN_EBI_LCD_RS_PIO     PIOC
#define PIN_EBI_LCD_RS_ID      ID_PIOC
#define PIN_EBI_LCD_RS_TYPE    PIO_PERIPH_A
#define PIN_EBI_LCD_RS_ATTR    PIO_PULLUP

/**
 * \file
 * LEDs
 * - \ref PIN_USER_LED1
 * - \ref PIN_USER_LED2
 * - \ref PIN_USER_LED3
 * - \ref PIN_POWER_LED
 * - \ref PINS_LEDS
 *
 */

/* ------------------------------------------------------------------------ */
/* LEDS                                                                     */
/* ------------------------------------------------------------------------ */
/*! LED #0 pin definition (GREEN). D4 */
#define PIN_USER_LED1   {PIO_PB13, PIOB, ID_PIOB, PIO_OUTPUT_1, PIO_DEFAULT}
/*! LED #1 pin definition (AMBER). D3 */
#define PIN_USER_LED2   {PIO_PB12, PIOB, ID_PIOB, PIO_OUTPUT_1, PIO_DEFAULT}
/*! LED #1 pin definition (BLUE).  D2 */
#define PIN_USER_LED3   {PIO_PA12, PIOA, ID_PIOA, PIO_OUTPUT_1, PIO_DEFAULT}
/*! LED #2 pin definition (RED).   D5 */
#define PIN_POWER_LED   {PIO_PA13, PIOA, ID_PIOA, PIO_OUTPUT_1, PIO_DEFAULT}

#define LED_GREEN     0
#define LED_AMBER     1
#define LED_BLUE      2
#define LED_RED       3

/*! List of all LEDs definitions. */
#define PINS_LEDS   PIN_USER_LED1, PIN_USER_LED2, PIN_USER_LED3, PIN_POWER_LED

/*! LED #0 pin definition (BLUE). */
#define LED_0_NAME      "blue LED D2"
#define LED0_GPIO       (PIO_PA12_IDX)
#define LED0_FLAGS      (PIO_TYPE_PIO_OUTPUT_1 | PIO_DEFAULT)

#define PIN_LED_0       {1 << 12, PIOA, ID_PIOA, PIO_OUTPUT_0, PIO_DEFAULT}
#define PIN_LED_0_MASK  (1 << 12)
#define PIN_LED_0_PIO   PIOA
#define PIN_LED_0_ID    ID_PIOA
#define PIN_LED_0_TYPE  PIO_OUTPUT_0
#define PIN_LED_0_ATTR  PIO_DEFAULT

/*! LED #1 pin definition (GREEN). */
#define LED_1_NAME      "green LED D4"
#define LED1_GPIO       (PIO_PB13_IDX)
#define LED1_FLAGS      (PIO_TYPE_PIO_OUTPUT_1 | PIO_DEFAULT)

#define PIN_LED_1       {1 << 13, PIOB, ID_PIOB, PIO_OUTPUT_1, PIO_DEFAULT}
#define PIN_LED_1_MASK  (1 << 13)
#define PIN_LED_1_PIO   PIOB
#define PIN_LED_1_ID    ID_PIOB
#define PIN_LED_1_TYPE  PIO_OUTPUT_1
#define PIN_LED_1_ATTR  PIO_DEFAULT

/*! LED #2 pin detection (AMBER). */
#define LED2_GPIO       (PIO_PB12_IDX)
#define LED2_FLAGS      (PIO_TYPE_PIO_OUTPUT_1 | PIO_DEFAULT)

/*! LED #3 pin detection (power) */
#define LED3_GPIO       (PIO_PA13_IDX)
#define LED3_FLAGS      (PIO_TYPE_PIO_OUTPUT_0 | PIO_DEFAULT)

/**
 * \file
 * Push buttons
 * - \ref PIN_PB_LEFT_CLICK
 * - \ref PIN_PB_RIGHT_CLICK
 * - \ref PINS_PUSHBUTTONS
 * - \ref PUSHBUTTON_BP1
 * - \ref PUSHBUTTON_BP2
 *
 */

/* ------------------------------------------------------------------------ */
/* PUSHBUTTONS                                                              */
/* ------------------------------------------------------------------------ */

/** Push button LEFT CLICK definition.
 *  Attributes = pull-up + debounce + interrupt on falling edge. */
#define PIN_PB_LEFT_CLICK    {PIO_PE7, PIOE, ID_PIOE, PIO_INPUT,\
	PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE}

/** Push button RIGHT CLICK definition.
 *  Attributes = pull-up + debounce + interrupt on falling edge. */
#define PIN_PB_RIGHT_CLICK    {PIO_PB23, PIOB, ID_PIOB, PIO_INPUT,\
	PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE}

/*! List of all push button definitions. */
#define PINS_PUSHBUTTONS    PIN_PB_LEFT_CLICK, PIN_PB_RIGHT_CLICK

/*! Push button #1 index. */
#define PUSHBUTTON_BP1   0
/*! Push button #2 index. */
#define PUSHBUTTON_BP2   1

/*! Push button LEFT CLICK index. */
#define PUSHBUTTON_LEFT     0
/*! Push button RIGHT CLICK index. */
#define PUSHBUTTON_RIGHT    1

/** Push button #0 definition.
 *  Attributes = pull-up + debounce + interrupt on rising edge. */
#define PUSHBUTTON_1_NAME    "LEFT CLICK"
#define GPIO_PUSH_BUTTON_1           (PIO_PE7_IDX)
#define GPIO_PUSH_BUTTON_1_FLAGS\
	(PIO_INPUT | PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_RISE_EDGE)

#define PIN_PUSHBUTTON_1    {PIO_PE7, PIOE, ID_PIOE, PIO_INPUT,\
	PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE}
#define PIN_PUSHBUTTON_1_MASK PIO_PE7
#define PIN_PUSHBUTTON_1_PIO PIOE
#define PIN_PUSHBUTTON_1_ID ID_PIOE
#define PIN_PUSHBUTTON_1_TYPE PIO_INPUT
#define PIN_PUSHBUTTON_1_ATTR (PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_RISE_EDGE)

/** Push button #1 definition.
 *  Attributes = pull-up + debounce + interrupt on falling edge. */
#define PUSHBUTTON_2_NAME    "RIGHT CLICK"
#define GPIO_PUSH_BUTTON_2           (PIO_PB23_IDX)
#define GPIO_PUSH_BUTTON_2_FLAGS\
	(PIO_INPUT | PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE)

#define PIN_PUSHBUTTON_2    {PIO_PB23, PIOB, ID_PIOB, PIO_INPUT,\
	PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE}
#define PIN_PUSHBUTTON_2_MASK PIO_PB23
#define PIN_PUSHBUTTON_2_PIO PIOB
#define PIN_PUSHBUTTON_2_ID ID_PIOB
#define PIN_PUSHBUTTON_2_TYPE PIO_INPUT
#define PIN_PUSHBUTTON_2_ATTR (PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE)

#define PIN_TC0_TIOA0           (PIO_PB25_IDX)
#define PIN_TC0_TIOA0_FLAGS     (PIO_PERIPH_B | PIO_DEFAULT)

#define PIN_TC0_TIOA1           (PIO_PA2_IDX)
#define PIN_TC0_TIOA1_FLAGS     (PIO_PERIPH_A | PIO_DEFAULT)

#define PIN_TC0_TIOA1_PIO     PIOA
#define PIN_TC0_TIOA1_MASK    PIO_PA2
#define PIN_TC0_TIOA1_ID      ID_PIOA
#define PIN_TC0_TIOA1_TYPE    PIO_PERIPH_A
#define PIN_TC0_TIOA1_ATTR    PIO_DEFAULT

#define PIN_TC0_TIOA2         (PIO_PA5_IDX)
#define PIN_TC0_TIOA2_FLAGS   (PIO_INPUT | PIO_DEFAULT)

#define PIN_TC0_TIOA2_PIO     PIOA
#define PIN_TC0_TIOA2_MASK    PIO_PA5
#define PIN_TC0_TIOA2_ID      ID_PIOA
#define PIN_TC0_TIOA2_TYPE    PIO_INPUT
#define PIN_TC0_TIOA2_ATTR    PIO_DEFAULT

/**
 * \file
 * PWMC
 * - \ref PIN_PWMC_PWMH0
 * - \ref PIN_PWMC_PWML0
 * - \ref PIN_PWMC_PWMH1
 * - \ref PIN_PWMC_PWML1
 * - \ref PIN_PWMC_PWMH2
 * - \ref PIN_PWMC_PWML2
 * - \ref PIN_PWMC_PWMH3
 * - \ref PIN_PWMC_PWML3
 * - \ref PIN_PWM_LED0
 * - \ref PIN_PWM_LED1
 * - \ref PIN_PWM_LED2
 * - \ref CHANNEL_PWM_LED0
 * - \ref CHANNEL_PWM_LED1
 * - \ref CHANNEL_PWM_LED2
 *
 */

/* ------------------------------------------------------------------------ */
/* PWM                                                                      */
/* ------------------------------------------------------------------------ */
/*! PWMC PWM0 pin definition: Output High. */
#define PIN_PWMC_PWMH0\
	{PIO_PB12B_PWMH0, PIOB, ID_PIOB, PIO_PERIPH_B, PIO_DEFAULT}
#define PIN_PWMC_PWMH0_TRIG   PIO_PB12_IDX
#define PIN_PWMC_PWMH0_TRIG_FLAG   PIO_PERIPH_B | PIO_DEFAULT
/*! PWMC PWM0 pin definition: Output Low. */
#define PIN_PWMC_PWML0\
	{PIO_PA21B_PWML0, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
/*! PWMC PWM1 pin definition: Output High. */
#define PIN_PWMC_PWMH1\
	{PIO_PB13B_PWMH1, PIOB, ID_PIOB, PIO_PERIPH_B, PIO_DEFAULT}
/*! PWMC PWM1 pin definition: Output Low. */
#define PIN_PWMC_PWML1\
	{PIO_PB17B_PWML1, PIOB, ID_PIOB, PIO_PERIPH_B, PIO_DEFAULT}
/*! PWMC PWM2 pin definition: Output High. */
#define PIN_PWMC_PWMH2\
	{PIO_PA13B_PWMH2, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
/*! PWMC PWM2 pin definition: Output Low. */
#define PIN_PWMC_PWML2\
	{PIO_PA20B_PWML2, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
/*! PWMC PWM3 pin definition: Output High. */
#define PIN_PWMC_PWMH3\
	{PIO_PA9B_PWMH3, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
/*! PWMC PWM3 pin definition: Output Low. */
#define PIN_PWMC_PWML3\
	{PIO_PC8B_PWML3, PIOC, ID_PIOC, PIO_PERIPH_B, PIO_DEFAULT}
/*! PWM pins definition for LED0 */
#define PIN_PWM_LED0 PIN_PWMC_PWMH0, PIN_PWMC_PWML0
/*! PWM pins definition for LED1 */
#define PIN_PWM_LED1 PIN_PWMC_PWMH1, PIN_PWMC_PWML1
/*! PWM pins definition for LED2 */
#define PIN_PWM_LED2 PIN_PWMC_PWMH2, PIN_PWMC_PWML2
/*! PWM channel for LED0 */
#define CHANNEL_PWM_LED0 0
/*! PWM channel for LED1 */
#define CHANNEL_PWM_LED1 1
/*! PWM channel for LED2 */
#define CHANNEL_PWM_LED2 2

/*! PWM LED0 pin definitions. */
#define PIN_PWM_LED0_GPIO    PIO_PB13_IDX
#define PIN_PWM_LED0_FLAGS   (PIO_PERIPH_B | PIO_DEFAULT)
#define PIN_PWM_LED0_CHANNEL PWM_CHANNEL_1

/*! PWM LED1 pin definitions. */
#define PIN_PWM_LED1_GPIO    PIO_PB12_IDX
#define PIN_PWM_LED1_FLAGS   (PIO_PERIPH_B | PIO_DEFAULT)
#define PIN_PWM_LED1_CHANNEL PWM_CHANNEL_0

/*! PWM LED2 pin definitions. */
#define PIN_PWM_LED2_GPIO    PIO_PA12_IDX
#define PIN_PWM_LED2_FLAGS   (PIO_PERIPH_B | PIO_DEFAULT)

/**
 * \file
 * SPI
 * - \ref PIN_SPI_MISO
 * - \ref PIN_SPI_MOSI
 * - \ref PIN_SPI_SPCK
 * - \ref PINS_SPI
 * - \ref PIN_SPI_NPCS0
 * - \ref PIN_SPI1_MISO
 * - \ref PIN_SPI1_MOSI
 * - \ref PIN_SPI1_SPCK
 * - \ref PINS_SPI1
 * - \ref PIN_SPI1_NPCS0
 *
 */

/* ------------------------------------------------------------------------ */
/* SPI                                                                      */
/* ------------------------------------------------------------------------ */
/*! SPI MISO pin definition. */
#define PIN_SPI0_MISO\
	{PIO_PA25A_SPI0_MISO, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/*! SPI MOSI pin definition. */
#define PIN_SPI0_MOSI\
	{PIO_PA26A_SPI0_MOSI, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/*! SPI SPCK pin definition. */
#define PIN_SPI0_SPCK\
	{PIO_PA27A_SPI0_SPCK, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/*! SPI chip select pin definition. */
#define PIN_SPI0_NPCS0\
	{PIO_PA28A_SPI0_NPCS0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/*! List of SPI pin definitions (MISO, MOSI & SPCK). */
#define PINS_SPI0        PIN_SPI0_MISO, PIN_SPI0_MOSI, PIN_SPI0_SPCK

/*! SPI0 MISO pin definition. */
#define SPI0_MISO_GPIO        (PIO_PA25_IDX)
#define SPI0_MISO_FLAGS       (PIO_PERIPH_A | PIO_DEFAULT)
/*! SPI0 MOSI pin definition. */
#define SPI0_MOSI_GPIO        (PIO_PA26_IDX)
#define SPI0_MOSI_FLAGS       (PIO_PERIPH_A | PIO_DEFAULT)
/*! SPI0 SPCK pin definition. */
#define SPI0_SPCK_GPIO        (PIO_PA27_IDX)
#define SPI0_SPCK_FLAGS       (PIO_PERIPH_A | PIO_DEFAULT)

/*! SPI0 chip select 0 pin definition. (Only one configuration is possible) */
#define SPI0_NPCS0_GPIO            (PIO_PA28_IDX)
#define SPI0_NPCS0_FLAGS           (PIO_PERIPH_A | PIO_DEFAULT)
/*! SPI0 chip select 1 pin definition. (multiple configurations are possible) */
#define SPI0_NPCS1_PA29_GPIO       (PIO_PA29_IDX)
#define SPI0_NPCS1_PA29_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
#define SPI0_NPCS1_PB20_GPIO       (PIO_PB20_IDX)
#define SPI0_NPCS1_PB20_FLAGS      (PIO_PERIPH_B | PIO_DEFAULT)
/*! SPI0 chip select 2 pin definition. (multiple configurations are possible) */
#define SPI0_NPCS2_PA30_GPIO       (PIO_PA30_IDX)
#define SPI0_NPCS2_PA30_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
#define SPI0_NPCS2_PB21_GPIO       (PIO_PB21_IDX)
#define SPI0_NPCS2_PB21_FLAGS      (PIO_PERIPH_B | PIO_DEFAULT)
/*! SPI0 chip select 3 pin definition. (multiple configurations are possible) */
#define SPI0_NPCS3_PA31_GPIO       (PIO_PA31_IDX)
#define SPI0_NPCS3_PA31_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
#define SPI0_NPCS3_PB23_GPIO       (PIO_PB23_IDX)
#define SPI0_NPCS3_PB23_FLAGS      (PIO_PERIPH_B | PIO_DEFAULT)

/*! SPI1 MISO pin definition. */
#define PIN_SPI1_MISO\
	{PIO_PE28A_SPI1_MISO, PIOE, ID_PIOE, PIO_PERIPH_A, PIO_DEFAULT}
/*! SPI1 MOSI pin definition. */
#define PIN_SPI1_MOSI\
	{PIO_PE29A_SPI1_MOSI, PIOE, ID_PIOE, PIO_PERIPH_A, PIO_DEFAULT}
/*! SPI1 SPCK pin definition. */
#define PIN_SPI1_SPCK\
	{PIO_PE30A_SPI1_SPCK, PIOE, ID_PIOE, PIO_PERIPH_A, PIO_DEFAULT}
/*! SPI1 chip select pin definition. */
#define PIN_SPI1_NPCS0\
	{PIO_PE31A_SPI1_NPCS0, PIOE, ID_PIOE, PIO_PERIPH_A, PIO_DEFAULT}
/*! List of SPI1 pin definitions (MISO, MOSI & SPCK). */
#define PINS_SPI1        PIN_SPI1_MISO, PIN_SPI1_MOSI, PIN_SPI1_SPCK

/*! SPI1 MISO pin definition. */
#define SPI1_MISO_GPIO             (PIO_PE28_IDX)
#define SPI1_MISO_FLAGS            (PIO_PERIPH_A | PIO_DEFAULT)
/*! SPI1 MOSI pin definition. */
#define SPI1_MOSI_GPIO             (PIO_PE29_IDX)
#define SPI1_MOSI_FLAGS            (PIO_PERIPH_A | PIO_DEFAULT)
/*! SPI1 SPCK pin definition. */
#define SPI1_SPCK_GPIO             (PIO_PE30_IDX)
#define SPI1_SPCK_FLAGS            (PIO_PERIPH_A | PIO_DEFAULT)
/*! SPI1 chip select 0 pin definition. (Only one configuration is possible) */
#define SPI1_NPCS0_GPIO            (PIO_PE31_IDX)
#define SPI1_NPCS0_FLAGS           (PIO_PERIPH_A | PIO_DEFAULT)
/*! SPI1 chip select 1 pin definition. (Only one configuration is possible) */
#define SPI1_NPCS1_GPIO            (PIO_PF0_IDX)
#define SPI1_NPCS1_FLAGS           (PIO_PERIPH_A | PIO_DEFAULT)
/*! SPI1 chip select 2 pin definition. (Only one configuration is possible) */
#define SPI1_NPCS2_GPIO            (PIO_PF1_IDX)
#define SPI1_NPCS2_FLAGS           (PIO_PERIPH_A | PIO_DEFAULT)
/*! SPI1 chip select 3 pin definition. (Only one configuration is possible) */
#define SPI1_NPCS3_GPIO            (PIO_PF2_IDX)
#define SPI1_NPCS3_FLAGS           (PIO_PERIPH_A | PIO_DEFAULT)

/**
 * \file
 * SSC
 * - \ref PIN_SSC_TD
 * - \ref PIN_SSC_TK
 * - \ref PIN_SSC_TF
 * - \ref PINS_SSC_CODEC
 *
 */

/* ------------------------------------------------------------------------ */
/* SSC                                                                      */
/* ------------------------------------------------------------------------ */
/*! SSC pin Transmitter Data (TD) */
#define PIN_SSC_TD      {PIO_PA16B_TD, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
/*! SSC pin Transmitter Clock (TK) */
#define PIN_SSC_TK      {PIO_PA14B_TK, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
/*! SSC pin Transmitter FrameSync (TF) */
#define PIN_SSC_TF      {PIO_PA15B_TF, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}

/*! SSC pin Receiver Data (RD) */
#define PIN_SSC_RD      {PIO_PB18A_RD, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! SSC pin Receiver Clock (RK) */
#define PIN_SSC_RK      {PIO_PB19A_RK, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! SSC pin Receiver FrameSync (RF) */
#define PIN_SSC_RF      {PIO_PB17A_RF, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}

/*! SSC pins definition for codec. */
#define PINS_SSC_CODEC  PIN_SSC_TD, PIN_SSC_TK, PIN_SSC_TF,\
	PIN_SSC_RD, PIN_SSC_RK, PIN_SSC_RF

/**
 * \file
 * PCK0
 * - \ref PIN_PCK0
 *
 */

/* ------------------------------------------------------------------------ */
/* PCK                                                                      */
/* ------------------------------------------------------------------------ */
/*! PCK0 */
#define PIN_PCK0        (PIO_PB22_IDX)
#define PIN_PCK0_FLAGS  (PIO_PERIPH_B | PIO_DEFAULT)

#define PIN_PCK_0_MASK  PIO_PB22
#define PIN_PCK_0_PIO   PIOB
#define PIN_PCK_0_ID    ID_PIOB
#define PIN_PCK_0_TYPE  PIO_PERIPH_B
#define PIN_PCK_0_ATTR  PIO_DEFAULT

/**
 * \file
 * HSMCI
 * - \ref PINS_HSMCI
 *
 */

/* ------------------------------------------------------------------------ */
/* HSMCI                                                                      */
/* ------------------------------------------------------------------------ */
/*! HSMCI pins definition. */
#define PINS_HSMCI\
	{ PIO_PA20A_MCCDA | PIO_PA19A_MCCK | PIO_PA21A_MCDA0 | PIO_PA22A_MCDA1\
	| PIO_PA23A_MCDA2 | PIO_PA24A_MCDA3,\
	PIOA, ID_PIOA, PIO_PERIPH_A, PIO_PULLUP },\
	{ PIO_PD0B_MCDA4 | PIO_PD1B_MCDA5 | PIO_PD2B_MCDA6 | PIO_PD3B_MCDA7,\
	PIOD, ID_PIOD, PIO_PERIPH_B, PIO_PULLUP},\
	{ PIO_PE20B_MCCDB | PIO_PE22B_MCDB0 | PIO_PE24B_MCDB1 | PIO_PE26B_MCDB2\
	| PIO_PE27B_MCDB3,\
	PIOE, ID_PIOE, PIO_PERIPH_B, PIO_PULLUP }
/*! HSMCI pin Card Detect. */
#define PIN_HSMCI_CD {PIO_PE6, PIOE, ID_PIOE, PIO_INPUT, PIO_PULLUP}

/**
 * \file
 * UART
 * - \ref PINS_UART
 *
 */

/* ------------------------------------------------------------------------ */
/* UART                                                                     */
/* ------------------------------------------------------------------------ */
/*! UART pins (UTXD0 and URXD0) definitions, PA8,9. */
#define PINS_UART        (PIO_PA8A_URXD | PIO_PA9A_UTXD)
#define PINS_UART_FLAGS  (PIO_PERIPH_A | PIO_DEFAULT)

#define PINS_UART_MASK (PIO_PA8A_URXD | PIO_PA9A_UTXD)
#define PINS_UART_PIO  PIOA
#define PINS_UART_ID   ID_PIOA
#define PINS_UART_TYPE PIO_PERIPH_A
#define PINS_UART_ATTR PIO_DEFAULT

/**
 * \file
 * USART0
 * - \ref PIN_USART0_RXD
 * - \ref PIN_USART0_TXD
 * - \ref PIN_USART0_CTS
 * - \ref PIN_USART0_RTS
 * - \ref PIN_USART0_SCK
 *
 * - \ref PIN_USART0_EN
 */

/* ------------------------------------------------------------------------ */
/* USART0                                                                   */
/* ------------------------------------------------------------------------ */
/*! USART0 pin RX */
#define PIN_USART0_RXD\
	{PIO_PA10A_RXD0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART0_RXD_IDX        (PIO_PA10_IDX)
#define PIN_USART0_RXD_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
/*! USART0 pin TX */
#define PIN_USART0_TXD\
	{PIO_PA11A_TXD0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART0_TXD_IDX        (PIO_PA11_IDX)
#define PIN_USART0_TXD_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
/*! USART0 pin CTS */
#define PIN_USART0_CTS\
	{PIO_PB26A_CTS0, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART0_CTS_IDX        (PIO_PB26_IDX)
#define PIN_USART0_CTS_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
/*! USART0 pin RTS */
#define PIN_USART0_RTS\
	{PIO_PB25A_RTS0, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART0_RTS_IDX        (PIO_PB25_IDX)
#define PIN_USART0_RTS_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
/*! USART0 pin SCK */
#define PIN_USART0_SCK\
	{PIO_PA17B_SCK0, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
#define PIN_USART0_SCK_IDX        (PIO_PA17_IDX)
#define PIN_USART0_SCK_FLAGS      (PIO_PERIPH_B | PIO_DEFAULT)

/*! USART0 pin ENABLE */
#define PIN_USART0_EN\
	{PIO_PE14, PIOE, ID_PIOE, PIO_OUTPUT_0, PIO_DEFAULT}
#define PIN_USART0_EN_IDX         (PIO_PE14_IDX)
#define PIN_USART0_EN_FLAGS       (PIO_OUTPUT_0 | PIO_DEFAULT)

/**
 * \file
 * USART1
 * - \ref PIN_USART1_RXD
 * - \ref PIN_USART1_TXD
 * - \ref PIN_USART1_CTS
 * - \ref PIN_USART1_RTS
 * - \ref PIN_USART1_SCK
 *
 */

/* ------------------------------------------------------------------------ */
/* USART1                                                                   */
/* ------------------------------------------------------------------------ */
/*! USART1 pin RX */
#define PIN_USART1_RXD\
	{PIO_PA12A_RXD1, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART1_RXD_IDX        (PIO_PA12_IDX)
#define PIN_USART1_RXD_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
/*! USART1 pin TX */
#define PIN_USART1_TXD\
	{PIO_PA13A_TXD1, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART1_TXD_IDX        (PIO_PA13_IDX)
#define PIN_USART1_TXD_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
/*! USART1 pin CTS */
#define PIN_USART1_CTS\
	{PIO_PA15A_CTS1, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART1_CTS_IDX        (PIO_PA15_IDX)
#define PIN_USART1_CTS_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
/*! USART1 pin RTS */
#define PIN_USART1_RTS\
	{PIO_PA14A_RTS1, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART1_RTS_IDX        (PIO_PA14_IDX)
#define PIN_USART1_RTS_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
/*! USART1 pin SCK */
#define PIN_USART1_SCK\
	{PIO_PA16A_SCK1, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART1_SCK_IDX        (PIO_PA16_IDX)
#define PIN_USART1_SCK_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)

/**
 * \file
 * USART3
 * - \ref PIN_USART3_RXD
 * - \ref PIN_USART3_TXD
 * - \ref PIN_USART3_CTS
 * - \ref PIN_USART3_RTS
 * - \ref PIN_USART3_SCK
 *
 */

/* ------------------------------------------------------------------------ */
/* USART3                                                                   */
/* ------------------------------------------------------------------------ */
/*! USART1 pin RX */
#define PIN_USART3_RXD\
	{PIO_PD5B_RXD3, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
#define PIN_USART3_RXD_IDX        (PIO_PD5_IDX)
#define PIN_USART3_RXD_FLAGS      (PIO_PERIPH_B | PIO_DEFAULT)
/*! USART1 pin TX */
#define PIN_USART3_TXD\
	{PIO_PD4B_TXD3, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
#define PIN_USART3_TXD_IDX        (PIO_PD4_IDX)
#define PIN_USART3_TXD_FLAGS      (PIO_PERIPH_B | PIO_DEFAULT)
/*! USART1 pin CTS */
#define PIN_USART3_CTS\
	{PIO_PF4A_CTS3, PIOF, ID_PIOF, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART3_CTS_IDX        (PIO_PF4_IDX)
#define PIN_USART3_CTS_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
/*! USART1 pin RTS */
#define PIN_USART3_RTS\
	{PIO_PF5A_RTS3, PIOF, ID_PIOF, PIO_PERIPH_A, PIO_DEFAULT}
#define PIN_USART3_RTS_IDX        (PIO_PF5_IDX)
#define PIN_USART3_RTS_FLAGS      (PIO_PERIPH_A | PIO_DEFAULT)
/*! USART1 pin SCK */
#define PIN_USART3_SCK\
	{PIO_PE16B_SCK3, PIOE, ID_PIOE, PIO_PERIPH_B, PIO_DEFAULT}
#define PIN_USART3_SCK_IDX        (PIO_PE16_IDX)
#define PIN_USART3_SCK_FLAGS      (PIO_PERIPH_B | PIO_DEFAULT)

/**
 * \file
 * USB
 * - \ref PIN_USBOTG_VBOF
 * - \ref PIN_USB_FAULT
 *
 */

/* ------------------------------------------------------------------------ */
/* USB                                                                      */
/* ------------------------------------------------------------------------ */
/*! USB OTG VBus On/Off: Bus Power Control Port. */
#define PIN_UOTGHS_VBOF  { PIO_PB10, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_PULLUP }
/*! USB OTG Identification: Mini Connector Identification Port. */
#define PIN_UOTGHS_ID    { PIO_PB11, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_PULLUP }
/*! USB Fault monitoring pin definition. */
#define PIN_UOTGHS_FAULT { PIO_PE5, PIOE, ID_PIOE, PIO_INPUT, PIO_PULLUP }

/*! Multiplexed pin used for USB ID pin: */
#define USB_ID_GPIO                 (PIO_PB11_IDX)
#define USB_ID_FLAGS                (PIO_PERIPH_A | PIO_PULLUP)
/*! Multiplexed pin used for USB_VBOF: */
#define USB_VBOF_GPIO               (PIO_PB10_IDX)
#define USB_VBOF_FLAGS              (PIO_PERIPH_A | PIO_DEFAULT)
/*! Active level of the USB_VBOF output pin. */
#define USB_VBOF_ACTIVE_LEVEL       LOW
/*! USB overcurrent detection pin. */
#define USB_OVERCURRENT_DETECT_PIN     PIO_PE5_IDX
#define USB_OVERCURRENT_DETECT_GPIO    (PIO_PE5_IDX)
#define USB_OVERCURRENT_DETECT_FLAGS   (PIO_INPUT | PIO_PULLUP)

/* ------------------------------------------------------------------------ */

/**
 * \page sam3x_ek_usb "SAM3X-EK - USB device"
 *
 * \section Definitions
 * - \ref BOARD_USB_BMATTRIBUTES
 * - \ref CHIP_USB_UDP
 * - \ref CHIP_USB_PULLUP_INTERNAL
 * - \ref CHIP_USB_NUMENDPOINTS
 * - \ref CHIP_USB_ENDPOINTS_MAXPACKETSIZE
 * - \ref CHIP_USB_ENDPOINTS_BANKS
 */

/*! USB attributes configuration descriptor (bus or self powered, remote wakeup) */
#define BOARD_USB_BMATTRIBUTES\
	USBConfigurationDescriptor_SELFPOWERED_RWAKEUP

/*! Indicates chip has an internal pull-up. */
#define CHIP_USB_PULLUP_INTERNAL

/*! Number of USB endpoints */
#define CHIP_USB_NUMENDPOINTS 10

/*! Endpoints max packet size */
#define CHIP_USB_ENDPOINTS_MAXPACKETSIZE(i)\
	((i == 0) ? 64 : 1024)

/*! Endpoints Number of Bank */
#define CHIP_USB_ENDPOINTS_BANKS(i)\
	((i == 0) ? 1 :\
	((i == 1) ? 3 :\
	((i == 2) ? 3 : 2)))

/**
 * \file
 * CAN
 * \ref PIN_CAN0_TRANSCEIVER_RXEN
 * \ref PIN_CAN0_TRANSCEIVER_RS
 * \ref PIN_CAN0_TXD
 * \ref PIN_CAN0_RXD
 * \ref PINS_CAN0
 *
 * \ref PIN_CAN1_TRANSCEIVER_RXEN
 * \ref PIN_CAN1_TRANSCEIVER_RS
 * \ref PIN_CAN1_TXD
 * \ref PIN_CAN1_RXD
 * \ref PINS_CAN1
 */

/* ------------------------------------------------------------------------ */
/* CAN                                                                      */
/* ------------------------------------------------------------------------ */

/*! CAN0 RXEN: Select input for high speed mode or ultra low current sleep mode */
#define PIN_CAN0_TRANSCEIVER_RXEN\
	{ PIO_PB21, PIOB, ID_PIOB, PIO_OUTPUT_1, PIO_DEFAULT }

/*! CAN0 RS: Select input for high speed mode or low-current standby mode */
#define PIN_CAN0_TRANSCEIVER_RS\
	{ PIO_PB20, PIOB, ID_PIOB, PIO_OUTPUT_0, PIO_DEFAULT }

/*! CAN0 TXD: Transmit data input */
#define PIN_CAN0_TXD\
	{ PIO_PA0A_CANTX0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT }

/*! CAN0 RXD: Receive data output */
#define PIN_CAN0_RXD\
	{ PIO_PA1A_CANRX0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT }

/*! List of all CAN0 definitions. */
#define PINS_CAN0    PIN_CAN0_TXD, PIN_CAN0_RXD

/** CAN0 transceiver PIN RS. */
#define PIN_CAN0_TR_RS_IDX        PIO_PB20_IDX
#define PIN_CAN0_TR_RS_FLAGS      (PIO_TYPE_PIO_OUTPUT_0 | PIO_DEFAULT)

/** CAN0 transceiver PIN EN. */
#define PIN_CAN0_TR_EN_IDX        PIO_PB21_IDX
#define PIN_CAN0_TR_EN_FLAGS      (PIO_TYPE_PIO_OUTPUT_0 | PIO_DEFAULT)

/** CAN0 PIN RX. */
#define PIN_CAN0_RX_IDX           (PIO_PA1_IDX)
#define PIN_CAN0_RX_FLAGS         (PIO_PERIPH_A | PIO_DEFAULT)

/** CAN0 PIN TX. */
#define PIN_CAN0_TX_IDX           (PIO_PA0_IDX)
#define PIN_CAN0_TX_FLAGS         (PIO_PERIPH_A | PIO_DEFAULT)

/*! CAN1 RXEN: Select input for high speed mode or ultra low current sleep mode */
#define PIN_CAN1_TRANSCEIVER_RXEN\
	{ PIO_PE16, PIOE, ID_PIOE, PIO_OUTPUT_1, PIO_DEFAULT }

/*! CAN1 RS: Select input for high speed mode or low-current standby mode */
#define PIN_CAN1_TRANSCEIVER_RS\
	{ PIO_PE15, PIOE, ID_PIOE, PIO_OUTPUT_0, PIO_DEFAULT }

/*! CAN1 TXD: Transmit data input */
#define PIN_CAN1_TXD\
	{ PIO_PB14A_CANTX1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT }

/*! CAN1 RXD: Receive data output */
#define PIN_CAN1_RXD\
	{ PIO_PB15A_CANRX1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT }

/*! List of all CAN1 definitions. */
#define PINS_CAN1    PIN_CAN1_TXD, PIN_CAN1_RXD

/** CAN1 transceiver PIN RS. */
#define PIN_CAN1_TR_RS_IDX        PIO_PE15_IDX
#define PIN_CAN1_TR_RS_FLAGS      (PIO_TYPE_PIO_OUTPUT_0 | PIO_DEFAULT)

/** CAN1 transceiver PIN EN. */
#define PIN_CAN1_TR_EN_IDX        PIO_PE16_IDX
#define PIN_CAN1_TR_EN_FLAGS      (PIO_TYPE_PIO_OUTPUT_0 | PIO_DEFAULT)

/** CAN1 PIN RX. */
#define PIN_CAN1_RX_IDX           (PIO_PB15_IDX)
#define PIN_CAN1_RX_FLAGS         (PIO_PERIPH_A | PIO_DEFAULT)

/** CAN1 PIN TX. */
#define PIN_CAN1_TX_IDX           (PIO_PB14_IDX)
#define PIN_CAN1_TX_FLAGS         (PIO_PERIPH_A | PIO_DEFAULT)

/**
 * \file
 * QTouch
 * PIO definitions for Slider
 * \ref SLIDER_IOMASK_SNS
 * \ref SLIDER_IOMASK_SNSK
 * \ref PINS_SLIDER_SNS
 * \ref PINS_SLIDER_SNSK
 *
 * PIO definitions for keys
 * \ref KEY_IOMASK_SNS
 * \ref KEY_IOMASK_SNSK
 * \ref PINS_KEY_SNS
 * \ref PINS_KEY_SNSK
 *
 * PIOS for QTouch
 * \ref PINS_QTOUCH
 *
 */

/* ------------------------------------------------------------------------ */
/* QTOUCH                                                                   */
/* ------------------------------------------------------------------------ */
/*! PIO definitions for Slider */
#define SLIDER_IOMASK_SNS   (uint32_t)(PIO_PF0 | PIO_PF2 | PIO_PF4)
#define SLIDER_IOMASK_SNSK  (uint32_t)(PIO_PF1 | PIO_PF3 | PIO_PF5)
#define PINS_SLIDER_SNS\
	{SLIDER_IOMASK_SNS, PIOF, ID_PIOF, PIO_INPUT, PIO_DEFAULT}
#define PINS_SLIDER_SNSK\
	{SLIDER_IOMASK_SNSK, PIOF, ID_PIOF, PIO_INPUT, PIO_DEFAULT}

/*! PIO definitions for keys */
#define KEY_IOMASK_SNS\
	(uint32_t)(PIO_PE21 | PIO_PE27 | PIO_PE25 | PIO_PE19 | PIO_PE23)
#define KEY_IOMASK_SNSK\
	(uint32_t)(PIO_PE20 | PIO_PE26 | PIO_PE24 | PIO_PE18 | PIO_PE22)
#define PINS_KEY_SNS\
	{KEY_IOMASK_SNS, PIOE, ID_PIOE, PIO_INPUT, PIO_DEFAULT}
#define PINS_KEY_SNSK\
	{KEY_IOMASK_SNSK, PIOE, ID_PIOE, PIO_INPUT, PIO_DEFAULT}

/*! PIOS for QTouch */
#define PINS_QTOUCH     PINS_SLIDER_SNS, PINS_SLIDER_SNSK,\
	PINS_KEY_SNS, PINS_KEY_SNSK

/**
 * \file
 * TWI
 * - \ref PIN_TWI_TWD0
 * - \ref PIN_TWI_TWCK0
 * - \ref PINS_TWI0
 * - \ref PIN_TWI_TWD1
 * - \ref PIN_TWI_TWCK1
 * - \ref PINS_TWI1
 *
 */

/* ------------------------------------------------------------------------ */
/* TWI                                                                      */
/* ------------------------------------------------------------------------ */
/*! TWI0 data pin */
#define PIN_TWI_TWD0\
	{PIO_PA17A_TWD0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/*! TWI0 clock pin */
#define PIN_TWI_TWCK0\
	{PIO_PA18A_TWCK0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/*! TWI0 pins */
#define PINS_TWI0      PIN_TWI_TWD0, PIN_TWI_TWCK0

/*! TWI0 pins definition */
#define TWI0_DATA_GPIO   PIO_PA17_IDX
#define TWI0_DATA_FLAGS  (PIO_PERIPH_A | PIO_DEFAULT)
#define TWI0_CLK_GPIO    PIO_PA18_IDX
#define TWI0_CLK_FLAGS   (PIO_PERIPH_A | PIO_DEFAULT)

/*! TWI1 data pin */
#define PIN_TWI_TWD1\
	{PIO_PB12A_TWD1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! TWI1 clock pin */
#define PIN_TWI_TWCK1\
	{PIO_PB13A_TWCK1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! TWI1 pins */
#define PINS_TWI1      PIN_TWI_TWD1, PIN_TWI_TWCK1

/*! TWI1 pins definition */
#define TWI1_DATA_GPIO   PIO_PB12_IDX
#define TWI1_DATA_FLAGS  (PIO_PERIPH_A | PIO_DEFAULT)
#define TWI1_CLK_GPIO    PIO_PB13_IDX
#define TWI1_CLK_FLAGS   (PIO_PERIPH_A | PIO_DEFAULT)

/* ------------------------------------------------------------------------ */

/**
 * \page sam3x_ek_extcomp "SAM3X-EK - External components"
 * This page lists the definitions related to external on-board components
 * located in the board.h file for the SAM3X-EK.
 *
 */

/**
 * \file
 * LCD
 *
 * - \ref BOARD_LCD_PINS
 * - \ref BOARD_BACKLIGHT_PIN
 * - \ref BOARD_LCD_BASE
 * - \ref BOARD_LCD_RS
 *
 */

/*! LCD Base Address */
#define BOARD_LCD_BASE              0x62000000
/*! LCD pins definition. */
#define BOARD_LCD_PINS              PIN_EBI_DATA_BUS, PIN_EBI_NRD,\
	PIN_EBI_NWE, PIN_EBI_NCS2, PIN_EBI_LCD_RS
/*! Board chip select */
#define BOARD_LCD_NCS 2
/*! Board LCD SMC setup timings */
#define BOARD_TIMING_NS(ns)\
	(((uint32_t)((ns * (BOARD_MCK / 1000000)) / 1000)) + 1)

#define BOARD_LCD_SETUP\
	SMC_SETUP_NWE_SETUP(BOARD_TIMING_NS(10)) |\
	SMC_SETUP_NCS_WR_SETUP(BOARD_TIMING_NS(10)) |\
	SMC_SETUP_NRD_SETUP(BOARD_TIMING_NS(90)) |\
	SMC_SETUP_NCS_RD_SETUP(BOARD_TIMING_NS(90))
/*! Board LCD SMC pulse timings */
#define BOARD_LCD_PULSE\
	SMC_PULSE_NWE_PULSE(BOARD_TIMING_NS(35)) |\
	SMC_PULSE_NCS_WR_PULSE(BOARD_TIMING_NS(35)) |\
	SMC_PULSE_NRD_PULSE(BOARD_TIMING_NS(355)) |\
	SMC_PULSE_NCS_RD_PULSE(BOARD_TIMING_NS(355))
/*! Board LCD SMC cycle timings */
#define BOARD_LCD_CYCLE\
	SMC_CYCLE_NWE_CYCLE(BOARD_TIMING_NS(100)) |\
	SMC_CYCLE_NRD_CYCLE(BOARD_TIMING_NS(460))
/*! Board LCD SMC mode */
#define BOARD_LCD_MODE\
	SMC_MODE_WRITE_MODE |\
	SMC_MODE_READ_MODE |\
	SMC_MODE_DBW_BIT_16

/*! Define HX8347A register select signal. */
#define BOARD_LCD_RS                   (1 << 1)

/*! Backlight pin definition. */
#define BOARD_BACKLIGHT                PIO_PB27_IDX
#define BOARD_BACKLIGHT_FLAG           PIO_OUTPUT_0 | PIO_DEFAULT

/** Definition of MMA7341L x,y,z axis channel number */
#define MMA7341L_ADC_CHANNEL_X  2
#define MMA7341L_ADC_CHANNEL_Y  6
#define MMA7341L_ADC_CHANNEL_Z  7

/** MMA7341L mode set pin definition. */
#define PIN_MMA7341L_MODE                PIO_PC13_IDX
#define PIN_MMA7341L_MODE_FLAG       PIO_OUTPUT_1 | PIO_DEFAULT

/** MMA7341L X,Y,Z axis pin definition. */
#define PIN_MMA7341L_X_AXIS                PIO_PB3_IDX
#define PIN_MMA7341L_X_AXIS_FLAG       PIO_INPUT | PIO_DEFAULT
#define PIN_MMA7341L_Y_AXIS                PIO_PC17_IDX
#define PIN_MMA7341L_Y_AXIS_FLAG       PIO_INPUT | PIO_DEFAULT
#define PIN_MMA7341L_Z_AXIS                PIO_PC18_IDX
#define PIN_MMA7341L_Z_AXIS_FLAG       PIO_INPUT | PIO_DEFAULT

/**
 * \file
 * TouchScreen
 *
 * - \ref PIN_TSC_IRQ
 * - \ref PIN_TSC_BUSY
 * - \ref BOARD_TSC_SPI_BASE
 * - \ref BOARD_TSC_SPI_ID
 * - \ref BOARD_TSC_SPI_PINS
 * - \ref BOARD_TSC_NPCS
 * - \ref BOARD_TSC_NPCS_PIN
 *
 */

/* ------------------------------------------------------------------------ */
/* Touchscreen                                                              */
/* ------------------------------------------------------------------------ */
/*! Touchscreen controller IRQ pin definition. */
#define PIN_TSC_IRQ  {PIO_PA31, PIOA, ID_PIOA, PIO_INPUT, PIO_PULLUP}
/*! Touchscreen controller Busy pin definition. */
#define PIN_TSC_BUSY {PIO_PA30, PIOA, ID_PIOA, PIO_INPUT, PIO_PULLUP}

/*! Base address of SPI peripheral connected to the touchscreen controller. */
#define BOARD_TSC_SPI_BASE         SPI0
/*! Identifier of SPI peripheral connected to the touchscreen controller. */
#define BOARD_TSC_SPI_ID           ID_SPI0
/*! Pins of the SPI peripheral connected to the touchscreen controller. */
#define BOARD_TSC_SPI_PINS         PINS_SPI0
/*! Chip select connected to the touchscreen controller. */
#define BOARD_TSC_NPCS             0
/*! Chip select pin connected to the touchscreen controller. */
/* We use PIO mode for chip select to meet ADS7843's timing specification */
#define BOARD_TSC_NPCS_PIN\
	{PIO_PA28A_SPI0_NPCS0, PIOA, ID_PIOA, PIO_OUTPUT_1, PIO_PULLUP}

/**
 * \file
 * EMAC
 *
 * - BOARD_EMAC_EREFCK
 * - BOARD_EMAC_ETXEN
 * - BOARD_EMAC_ETX0
 * - BOARD_EMAC_ETX1
 * - BOARD_EMAC_ECRSDV
 * - BOARD_EMAC_ERX0
 * - BOARD_EMAC_ERX1
 * - BOARD_EMAC_ERXER
 * - BOARD_EMAC_EMDC
 * - BOARD_EMAC_EMDIO
 *
 * - BOARD_EMAC_PINS: One single define for all MACB pins
 * - BOARD_EMAC_PHY_ADDR: Phy MAC address
 * - BOARD_EMAC_MODE_RMII: Enable RMII connection with the PHY
 */

/*! EMAC pin EREFCK */
#define BOARD_EMAC_EREFCK  {PIO_PB0, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! EMAC pin ETXEN */
#define BOARD_EMAC_ETXEN\
	{PIO_PB1A_ETXEN, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! EMAC pin ETX0 */
#define BOARD_EMAC_ETX0\
	{PIO_PB2A_ETX0, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! EMAC pin ETX1 */
#define BOARD_EMAC_ETX1\
	{PIO_PB3A_ETX1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! EMAC pin ECRSDV */
#define BOARD_EMAC_ECRSDV\
	{PIO_PB4A_ECRSDV_ERXDV, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! EMAC pin ERX0 */
#define BOARD_EMAC_ERX0\
	{PIO_PB5A_ERX0, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! EMAC pin ERX1 */
#define BOARD_EMAC_ERX1\
	{PIO_PB6A_ERX1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! EMAC pin ERXER */
#define BOARD_EMAC_ERXER\
	{PIO_PB7A_ERXER, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! EMAC pin EMDC */
#define BOARD_EMAC_EMDC\
	{PIO_PB8A_EMDC, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/*! EMAC pin EMDIO */
#define BOARD_EMAC_EMDIO\
	{PIO_PB9A_EMDIO, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}

/*! EMAC pins */
#define BOARD_EMAC_PINS\
	BOARD_EMAC_EREFCK,\
	BOARD_EMAC_ETX0,\
	BOARD_EMAC_ETX1,\
	BOARD_EMAC_ETXEN,\
	BOARD_EMAC_ECRSDV,\
	BOARD_EMAC_ERX0,\
	BOARD_EMAC_ERX1,\
	BOARD_EMAC_ERXER,\
	BOARD_EMAC_EMDC,\
	BOARD_EMAC_EMDIO

#define PIN_EEMAC_EREFCK      PIO_PB0_IDX
#define PIN_EMAC_ETXEN        PIO_PB1_IDX
#define PIN_EMAC_ETX0         PIO_PB2_IDX
#define PIN_EMAC_ETX1         PIO_PB3_IDX
#define PIN_EMAC_ECRSDV       PIO_PB4_IDX
#define PIN_EMAC_ERX0         PIO_PB5_IDX
#define PIN_EMAC_ERX1         PIO_PB6_IDX
#define PIN_EMAC_ERXER        PIO_PB7_IDX
#define PIN_EMAC_EMDC         PIO_PB8_IDX
#define PIN_EMAC_EMDIO        PIO_PB9_IDX
#define PIN_EMAC_FLAGS        PIO_PERIPH_A | PIO_DEFAULT

/** EMAC PHY address */
#define BOARD_EMAC_PHY_ADDR  0
/*! EMAC RMII mode */
#define BOARD_EMAC_MODE_RMII 1

/**
 * \file
 * SD Card
 * - \ref BOARD_SD_PINS
 * - \ref BOARD_SD_PIN_CD
 *
 */

/*! HSMCI pins that shall be configured to access the SD card. */
#define BOARD_SD_PINS               PINS_HSMCI
/*! HSMCI Card Detect pin. */
#define BOARD_SD_PIN_CD             PIN_HSMCI_CD
/*! Total number of HSMCI interface */
#define BOARD_NUM_HSMCI               1

/**
 * \file
 * SmartCard
 * - \ref SMARTCARD_CONNECT_PIN
 * - \ref PIN_ISO7816_RSTMC
 * - \ref PINS_ISO7816
 *
 */

/* ------------------------------------------------------------------------ */
/* SMARTCARD                                                                */
/* ------------------------------------------------------------------------ */
/* Smartcard detection pin */
/*#define SMARTCARD_CONNECT_PIN {1 << 13, PIOA, ID_PIOA, PIO_INPUT, PIO_DEFAULT} */

/*/ PIN used for reset the smartcard */
#define PIN_ISO7816_RSTMC  {1 << 11, PIOA, ID_PIOA, PIO_OUTPUT_0, PIO_DEFAULT}
/*/ Pins used for connect the smartcard */
#define PINS_ISO7816        PIN_USART1_TXD, PIN_USART1_SCK, PIN_ISO7816_RSTMC

/* ------------------------------------------------------------------------ */

/**
 * \page sam3x_ek_mem "SAM3X-EK - Memories"
 * This page lists definitions related to internal & external on-board memories.
 *
 *
 */

/**
 * \file
 * NandFlash
 * - \ref PIN_EBI_NANDOE
 * - \ref PIN_EBI_NANDWE
 * - \ref PIN_EBI_NANDCLE
 * - \ref PIN_EBI_NANDALE
 * - \ref PIN_EBI_NANDIO
 * - \ref BOARD_NF_CE_PIN
 * - \ref BOARD_NF_RB_PIN
 * - \ref PINS_NANDFLASH
 *
 */

/* ------------------------------------------------------------------------ */
/* NAND FLASH                                                               */
/* ------------------------------------------------------------------------ */
/** NandFlash pins definition: OE. */
#define PIN_EBI_NANDOE    (PIO_PC19_IDX)
#define PIN_EBI_NANDOE_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

/** NandFlash pins definition: WE. */
#define PIN_EBI_NANDWE    (PIO_PC20_IDX)
#define PIN_EBI_NANDWE_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

/** NandFlash pins definition: CLE. */
#define PIN_EBI_NANDCLE    (PIO_PD9_IDX)
#define PIN_EBI_NANDCLE_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

/** NandFlash pins definition: ALE. */
#define PIN_EBI_NANDALE    (PIO_PD8_IDX)
#define PIN_EBI_NANDALE_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

/** NandFlash pins definition: DATA. */
#define PIN_EBI_NANDIO_0    (PIO_PC2_IDX)
#define PIN_EBI_NANDIO_0_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

#define PIN_EBI_NANDIO_1    (PIO_PC3_IDX)
#define PIN_EBI_NANDIO_1_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

#define PIN_EBI_NANDIO_2    (PIO_PC4_IDX)
#define PIN_EBI_NANDIO_2_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

#define PIN_EBI_NANDIO_3    (PIO_PC5_IDX)
#define PIN_EBI_NANDIO_3_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

#define PIN_EBI_NANDIO_4    (PIO_PC6_IDX)
#define PIN_EBI_NANDIO_4_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

#define PIN_EBI_NANDIO_5    (PIO_PC7_IDX)
#define PIN_EBI_NANDIO_5_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

#define PIN_EBI_NANDIO_6    (PIO_PC8_IDX)
#define PIN_EBI_NANDIO_6_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

#define PIN_EBI_NANDIO_7    (PIO_PC9_IDX)
#define PIN_EBI_NANDIO_7_FLAGS    (PIO_PERIPH_A | PIO_PULLUP)

/** Nandflash chip enable pin definition. */
#define PIN_NF_CE_IDX    (PIO_PA6_IDX)
#define PIN_NF_CE_FLAGS    (PIO_PERIPH_B | PIO_PULLUP)

/** Nandflash ready/busy pin definition. */
#define PIN_NF_RB_IDX    (PIO_PA2_IDX)
#define PIN_NF_RB_FLAGS    (PIO_PERIPH_B | PIO_PULLUP)

/* Chip select number for nand */
#define BOARD_NAND_CS      0

/*
 * \addtopage sam3x_ek_mem
 * \section NandFlash
 * - \ref BOARD_NF_COMMAND_ADDR
 * - \ref BOARD_NF_ADDRESS_ADDR
 * - \ref BOARD_NF_DATA_ADDR
 *
 */

/* ------------------------------------------------------------------------ */
/* NAND FLASH                                                               */
/* ------------------------------------------------------------------------ */
/*! Address for transferring command bytes to the nandflash. */
#define BOARD_NF_COMMAND_ADDR   0x60400000
/*! Address for transferring address bytes to the nandflash. */
#define BOARD_NF_ADDRESS_ADDR   0x60200000
/*! Address for transferring data bytes to the nandflash. */
#define BOARD_NF_DATA_ADDR      0x60000000
/* Bus width for NAND */
#define CONF_NF_BUSWIDTH    8
/* SMC NFC using five address cycle */
#define CONF_NF_NEED_FIVE_ADDRESS_CYCLES  1
/* Access timing for NAND */
#define CONF_NF_SETUP_TIMING (SMC_SETUP_NWE_SETUP(0) \
		| SMC_SETUP_NCS_WR_SETUP(0) \
		| SMC_SETUP_NRD_SETUP(0) \
		| SMC_SETUP_NCS_RD_SETUP(0))
#define CONF_NF_PULSE_TIMING (SMC_PULSE_NWE_PULSE(2) \
		| SMC_PULSE_NCS_WR_PULSE(3) \
		| SMC_PULSE_NRD_PULSE(2) \
		| SMC_PULSE_NCS_RD_PULSE(3))
#define CONF_NF_CYCLE_TIMING (SMC_CYCLE_NWE_CYCLE(3) \
		| SMC_CYCLE_NRD_CYCLE(3))
#define CONF_NF_TIMING (SMC_TIMINGS_TCLR(1) \
		| SMC_TIMINGS_TADL(6) \
		| SMC_TIMINGS_TAR(4) \
		| SMC_TIMINGS_TRR(2) \
		| SMC_TIMINGS_TWB(9) \
		| SMC_TIMINGS_RBNSEL(7) \
		| (SMC_TIMINGS_NFSEL))
/* Support DMA */
#define CONF_NF_USE_DMA
#ifdef CONF_NF_USE_DMA
/* DMA channel used for NF */
#define CONF_NF_DMA_CHANNEL    0
#endif

/**
 * \file
 * \section SDRAM
 * - \ref BOARD_SDRAM_SIZE
 * - \ref PIN_SDRAM
 * - \ref BOARD_SDRAM_BUSWIDTH
 *
 */

/* ------------------------------------------------------------------------ */
/* SDRAM                                                                    */
/* ------------------------------------------------------------------------ */
/*!  Board SDRAM size for MT48LC16M16A2 */
#define BOARD_SDRAM_SIZE        (32 * 1024 * 1024)  /* 32 MB */

/** Address for transferring command bytes to the SDRAM. */
#define BOARD_SDRAM_ADDR     0x70000000

/**  List of all SDRAM pins definitions */
#define PIO_SDRAM_SDCKE PIO_PD13
#define PIO_SDRAM_SDCS PIO_PD12
#define PIO_SDRAM_RAS PIO_PD15
#define PIO_SDRAM_CAS PIO_PD16
#define PIO_SDRAM_BA0 PIO_PD6
#define PIO_SDRAM_BA1 PIO_PD7
#define PIO_SDRAM_SDWE PIO_PD14
#define PIO_SDRAM_NBS0 PIO_PC21
#define PIO_SDRAM_NBS1 PIO_PD10
#define PIO_SDRAM_DATA (0xffff << 2)    //PIO_PC2--PIO_PC17
#define PIO_SDRAM_SDA0_A7 (0xff << 23)    //PIO_PC23--PIO_PC30
#define PIO_SDRAM_SDA8 PIO_PD22
#define PIO_SDRAM_SDA9 PIO_PD23
#define PIO_SDRAM_SDA11 PIO_PD25
#define PIO_SDRAM_SDA12 PIO_PD4
#define PIO_SDRAM_SDA10 PIO_PD11

#define PIN_SDRAM_SDCKE PIO_PD13_IDX
#define PIN_SDRAM_SDCS PIO_PD12_IDX
#define PIN_SDRAM_RAS PIO_PD15_IDX
#define PIN_SDRAM_CAS PIO_PD16_IDX
#define PIN_SDRAM_BA0 PIO_PD6_IDX
#define PIN_SDRAM_BA1 PIO_PD7_IDX
#define PIN_SDRAM_SDWE PIO_PD14_IDX
#define PIN_SDRAM_NBS0 PIO_PC21_IDX
#define PIN_SDRAM_NBS1 PIO_PD10_IDX
#define PIN_SDRAM_DATA0 PIO_PC2_IDX
#define PIN_SDRAM_DATA1 PIO_PC3_IDX
#define PIN_SDRAM_DATA2 PIO_PC4_IDX
#define PIN_SDRAM_DATA3 PIO_PC5_IDX
#define PIN_SDRAM_DATA4 PIO_PC6_IDX
#define PIN_SDRAM_DATA5 PIO_PC7_IDX
#define PIN_SDRAM_DATA6 PIO_PC8_IDX
#define PIN_SDRAM_DATA7 PIO_PC9_IDX
#define PIN_SDRAM_DATA8 PIO_PC10_IDX
#define PIN_SDRAM_DATA9 PIO_PC11_IDX
#define PIN_SDRAM_DATA10 PIO_PC12_IDX
#define PIN_SDRAM_DATA11 PIO_PC13_IDX
#define PIN_SDRAM_DATA12 PIO_PC14_IDX
#define PIN_SDRAM_DATA13 PIO_PC15_IDX
#define PIN_SDRAM_DATA14 PIO_PC16_IDX
#define PIN_SDRAM_DATA15 PIO_PC17_IDX
#define PIN_SDRAM_SDA1 PIO_PC23_IDX
#define PIN_SDRAM_SDA2 PIO_PC24_IDX
#define PIN_SDRAM_SDA3 PIO_PC25_IDX
#define PIN_SDRAM_SDA4 PIO_PC26_IDX
#define PIN_SDRAM_SDA5 PIO_PC27_IDX
#define PIN_SDRAM_SDA6 PIO_PC28_IDX
#define PIN_SDRAM_SDA7 PIO_PC29_IDX
#define PIN_SDRAM_SDA0 PIO_PC30_IDX
#define PIN_SDRAM_SDA8 PIO_PD22_IDX
#define PIN_SDRAM_SDA9 PIO_PD23_IDX
#define PIN_SDRAM_SDA11 PIO_PD25_IDX
#define PIN_SDRAM_SDA12 PIO_PD4_IDX
#define PIN_SDRAM_SDA10 PIO_PD11_IDX

#define PIN_SDRAM_FLAGS        PIO_PERIPH_A | PIO_PULLUP

#define PIN_SDRAM_EN PIO_PD18_IDX
#define PIN_SDRAM_EN_FLAGS  PIO_OUTPUT_1 | PIO_DEFAULT

/**  List of all SDRAM pins definitions */
#define PINS_SDRAM_PIOC              { PIO_SDRAM_DATA | PIO_SDRAM_NBS0 | PIO_SDRAM_SDA0_A7, \
                                      PIOC, ID_PIOC, PIO_PERIPH_A, PIO_PULLUP }

#define PINS_SDRAM_PIOD\
	{ PIO_SDRAM_SDCKE | PIO_SDRAM_SDCS |\
	PIO_SDRAM_RAS | PIO_SDRAM_CAS |\
	PIO_SDRAM_BA0 | PIO_SDRAM_BA1 |\
	PIO_SDRAM_SDWE | PIO_SDRAM_NBS1 |\
	PIO_SDRAM_SDA10 |\
	PIO_SDRAM_SDA8 | PIO_SDRAM_SDA9 |\
	PIO_SDRAM_SDA11 | PIO_SDRAM_SDA12,\
	PIOD, ID_PIOD, PIO_PERIPH_A, PIO_PULLUP }

/* PIO18 is used as SDRAM Enable on EK-REVB board */
#define PINS_SDRAM_EN\
	{ (1 << 18), PIOD, ID_PIOD, PIO_OUTPUT_1, PIO_DEFAULT }

#define PINS_SDRAM        PINS_SDRAM_PIOC, PINS_SDRAM_PIOD, PINS_SDRAM_EN

/*!  SDRAM bus width */
#define BOARD_SDRAM_BUSWIDTH    16

/* SDRAMC clock speed */
#define SDRAMC_CLK (BOARD_MCK)

/**
 * \file
 * \section NorFlash
 * - \ref BOARD_NORFLASH_ADDR
 *
 */

/* ------------------------------------------------------------------------ */
/* NOR FLASH                                                                */
/* ------------------------------------------------------------------------ */
/*! Address for transferring command bytes to the norflash. */
#define BOARD_NORFLASH_ADDR     0x60000000

/* ------------------------------------------------------------------------ */

/**
 * \page sam3x_ek_chipdef "SAM3X-EK - Individual chip definition"
 * This page lists the definitions related to different chip's definition
 * located in the board.h file for the SAM3X-EK.
 *
 * \section USART
 * - \ref BOARD_PIN_USART_RXD
 * - \ref BOARD_PIN_USART_TXD
 * - \ref BOARD_PIN_USART_CTS
 * - \ref BOARD_PIN_USART_RTS
 * - \ref BOARD_PIN_USART_EN
 * - \ref BOARD_USART_BASE
 * - \ref BOARD_ID_USART
 */

/*! Rtc */
#define BOARD_RTC_ID                ID_RTC

/* AT24CXX device address */
#define BOARD_AT24C_ADDRESS                 0x50
/** Define MCP980X TWI instance. */
#define BOARD_AT24C_TWI_INSTANCE    (TWI0)

/*! TWI ID for EEPROM application to use */
#define BOARD_ID_TWI_EEPROM         ID_TWI0
/*! TWI Base for TWI EEPROM application to use */
#define BOARD_BASE_TWI_EEPROM       TWI0
/*! TWI pins for EEPROM application to use */
#define BOARD_PINS_TWI_EEPROM       PINS_TWI0

/*! USART RX pin for application */
#define BOARD_PIN_USART_RXD        PIN_USART0_RXD
/*! USART TX pin for application */
#define BOARD_PIN_USART_TXD        PIN_USART0_TXD
/*! USART CTS pin for application */
#define BOARD_PIN_USART_CTS        PIN_USART0_CTS
/*! USART RTS pin for application */
#define BOARD_PIN_USART_RTS        PIN_USART0_RTS
/*! USART ENABLE pin for application */
#define BOARD_PIN_USART_EN         PIN_USART0_EN
/*! USART Base for application */
#define BOARD_USART_BASE           USART0
/*! USART ID for application */
#define BOARD_ID_USART             ID_USART0
/*! USART1 Base for application */
#define BOARD_USART1_BASE          USART1
/*! USART1 ID for application */
#define BOARD_ID_USART1            ID_USART1
/*! USART3 Base for application */
#define BOARD_USART3_BASE          USART3
/*! USART3 ID for application */
#define BOARD_ID_USART3            ID_USART3

#define CONSOLE_UART               UART
#define CONSOLE_UART_ID            ID_UART

/* RE pin. */
#define PIN_RE_IDX                 PIN_USART0_CTS_IDX
#define PIN_RE_FLAGS               (PIO_OUTPUT_0 | PIO_DEFAULT)

/* IRDA SD pin. */
#define PIN_IRDA_SD_IDX            PIN_USART0_CTS_IDX
#define PIN_IRDA_SD_FLAGS          (PIO_OUTPUT_1 | PIO_DEFAULT)

/* TXD pin configuration. */
#define PIN_USART_TXD_IDX          PIN_USART0_TXD_IDX
#define PIN_USART_TXD_FLAGS        (PIO_PERIPH_A | PIO_DEFAULT)
#define PIN_USART_TXD_IO_FLAGS     (PIO_OUTPUT_0 | PIO_DEFAULT)

/* ISO7816 example relate PIN definition. */
#define ISO7816_USART_ID           ID_USART0
#define ISO7816_USART              USART0
#define PIN_ISO7816_RST_IDX        PIO_PA15_IDX
#define PIN_ISO7816_RST_FLAG       (PIO_OUTPUT_0 | PIO_DEFAULT)

#endif  /* _SAM3X_EK_H_ */
