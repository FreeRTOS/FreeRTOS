/**
 * \file
 *
 * \brief SAM4E-EK Board Definition.
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

#ifndef _SAM4E_EK_H_
#define _SAM4E_EK_H_

#include "compiler.h"
#include "system_sam4e.h"
#include "exceptions.h"

/*----------------------------------------------------------------------------*/
/**
 *  \page sam4e_ek_opfreq "SAM4E-EK - Operating frequencies"
 *  This page lists several definition related to the board operating frequency
 *
 *  \section Definitions
 *  - \ref BOARD_FREQ_*
 *  - \ref BOARD_MCK
 */

/** Board oscillator settings */
#define BOARD_FREQ_SLCK_XTAL            (32768U)
#define BOARD_FREQ_SLCK_BYPASS          (32768U)
#define BOARD_FREQ_MAINCK_XTAL          (12000000U)
#define BOARD_FREQ_MAINCK_BYPASS        (12000000U)

/** Master clock frequency */
#define BOARD_MCK                       CHIP_FREQ_CPU_MAX

/** board main clock xtal statup time */
#define BOARD_OSC_STARTUP_US            15625

/*----------------------------------------------------------------------------*/
/**
 * \page sam4e_ek_board_info "SAM4E-EK - Board informations"
 * This page lists several definition related to the board description.
 *
 * \section Definitions
 * - \ref BOARD_NAME
 */

/** Name of the board */
#define BOARD_NAME "SAM4E-EK"
/** Board definition */
#define sam4eek
/** Family definition (already defined) */
#define sam4e
/** Core definition */
#define cortexm4

/*----------------------------------------------------------------------------*/

/** UART0 pins (UTXD0 and URXD0) definitions, PA10,9. */
#define PINS_UART0        (PIO_PA9A_URXD0 | PIO_PA10A_UTXD0)
#define PINS_UART0_FLAGS  (IOPORT_MODE_MUX_A)

#define PINS_UART0_PORT   IOPORT_PIOA
#define PINS_UART0_MASK   (PIO_PA9A_URXD0 | PIO_PA10A_UTXD0)
#define PINS_UART0_PIO    PIOA
#define PINS_UART0_ID     ID_PIOA
#define PINS_UART0_TYPE   PIO_PERIPH_A
#define PINS_UART0_ATTR   PIO_DEFAULT

/** UART1 pins (UTXD1 and URXD1) definitions, PA6,5. */
#define PINS_UART1        (PIO_PA6C_URXD1 | PIO_PA5C_UTXD1)
#define PINS_UART1_FLAGS  (IOPORT_MODE_MUX_C)

#define PINS_UART1_PORT   IOPORT_PIOA
#define PINS_UART1_MASK   (PIO_PA6C_URXD1 | PIO_PA5C_UTXD1)
#define PINS_UART1_PIO    PIOA
#define PINS_UART1_ID     ID_PIOA
#define PINS_UART1_TYPE   PIO_PERIPH_C
#define PINS_UART1_ATTR   PIO_DEFAULT

/** LED #0 pin definition (Blue). */
#define LED_0_NAME      "Blue LED D2"
#define PIN_LED_0       {PIO_PA0, PIOA, ID_PIOA, PIO_OUTPUT_1, PIO_DEFAULT}
#define PIN_LED_0_MASK  PIO_PA0
#define PIN_LED_0_PIO   PIOA
#define PIN_LED_0_ID    ID_PIOA
#define PIN_LED_0_TYPE  PIO_OUTPUT_1
#define PIN_LED_0_ATTR  PIO_DEFAULT

#define LED0_GPIO            (PIO_PA0_IDX)
#define LED0_FLAGS           (0)
#define LED0_ACTIVE_LEVEL    IOPORT_PIN_LEVEL_LOW
#define LED0_INACTIVE_LEVEL  IOPORT_PIN_LEVEL_HIGH

/** LED #1 pin definition (Amber). */
#define LED_1_NAME      "Amber LED D3"
#define PIN_LED_1       {PIO_PD20, PIOD, ID_PIOD, PIO_OUTPUT_1, PIO_DEFAULT}
#define PIN_LED_1_MASK  PIO_PD20
#define PIN_LED_1_PIO   PIOD
#define PIN_LED_1_ID    ID_PIOD
#define PIN_LED_1_TYPE  PIO_OUTPUT_1
#define PIN_LED_1_ATTR  PIO_DEFAULT

#define LED1_GPIO            (PIO_PD20_IDX)
#define LED1_FLAGS           (0)
#define LED1_ACTIVE_LEVEL    IOPORT_PIN_LEVEL_LOW
#define LED1_INACTIVE_LEVEL  IOPORT_PIN_LEVEL_HIGH

/** LED #2 pin definition (Green). */
#define LED_2_NAME      "Green LED D4"
#define PIN_LED_2_MASK  PIO_PD21
#define PIN_LED_2_PIO   PIOD
#define PIN_LED_2_ID    ID_PIOD
#define PIN_LED_2_TYPE  PIO_OUTPUT_1
#define PIN_LED_2_ATTR  PIO_DEFAULT

#define LED2_GPIO            (PIO_PD21_IDX)
#define LED2_FLAGS           (0)
#define LED2_ACTIVE_LEVEL    IOPORT_PIN_LEVEL_LOW
#define LED2_INACTIVE_LEVEL  IOPORT_PIN_LEVEL_HIGH

/** LED #3 pin definition (Red). */
#define LED_3_NAME      "Red LED D5"
#define PIN_LED_3_MASK  PIO_PD22
#define PIN_LED_3_PIO   PIOD
#define PIN_LED_3_ID    ID_PIOD
#define PIN_LED_3_TYPE  PIO_OUTPUT_0
#define PIN_LED_3_ATTR  PIO_DEFAULT

#define LED3_GPIO            (PIO_PD22_IDX)
#define LED3_FLAGS           (0)
#define LED3_ACTIVE_LEVEL    IOPORT_PIN_LEVEL_HIGH
#define LED3_INACTIVE_LEVEL  IOPORT_PIN_LEVEL_LOW

#define BOARD_NUM_OF_LED 4

/** HSMCI pins definition. */
/*! Number of slot connected on HSMCI interface */
#define SD_MMC_HSMCI_MEM_CNT      1
#define SD_MMC_HSMCI_SLOT_0_SIZE  4
#define PINS_HSMCI   {0x3fUL << 26, PIOA, ID_PIOA, PIO_PERIPH_C, PIO_PULLUP}
/** HSMCI MCCDA pin definition. */
#define PIN_HSMCI_MCCDA_GPIO            (PIO_PA28_IDX)
#define PIN_HSMCI_MCCDA_FLAGS           (IOPORT_MODE_MUX_C)
/** HSMCI MCCK pin definition. */
#define PIN_HSMCI_MCCK_GPIO             (PIO_PA29_IDX)
#define PIN_HSMCI_MCCK_FLAGS            (IOPORT_MODE_MUX_C)
/** HSMCI MCDA0 pin definition. */
#define PIN_HSMCI_MCDA0_GPIO            (PIO_PA30_IDX)
#define PIN_HSMCI_MCDA0_FLAGS           (IOPORT_MODE_MUX_C)
/** HSMCI MCDA1 pin definition. */
#define PIN_HSMCI_MCDA1_GPIO            (PIO_PA31_IDX)
#define PIN_HSMCI_MCDA1_FLAGS           (IOPORT_MODE_MUX_C)
/** HSMCI MCDA2 pin definition. */
#define PIN_HSMCI_MCDA2_GPIO            (PIO_PA26_IDX)
#define PIN_HSMCI_MCDA2_FLAGS           (IOPORT_MODE_MUX_C)
/** HSMCI MCDA3 pin definition. */
#define PIN_HSMCI_MCDA3_GPIO            (PIO_PA27_IDX)
#define PIN_HSMCI_MCDA3_FLAGS           (IOPORT_MODE_MUX_C)

/** SD/MMC card detect pin definition. */
#define PIN_HSMCI_CD             {PIO_PA6, PIOA, ID_PIOA, PIO_INPUT, PIO_PULLUP}
#define SD_MMC_0_CD_GPIO         (PIO_PA6_IDX)
#define SD_MMC_0_CD_PIO_ID       ID_PIOA
#define SD_MMC_0_CD_FLAGS        (IOPORT_MODE_PULLUP)
#define SD_MMC_0_CD_DETECT_VALUE 0

/**
 * Push button #0 definition. Attributes = pull-up + debounce + interrupt on
 * rising edge.
 */
#define PUSHBUTTON_1_NAME        "BP2 WAKU"
#define PUSHBUTTON_1_WKUP_LINE   (9)
#define PUSHBUTTON_1_WKUP_FSTT   (PMC_FSMR_FSTT9)
#define GPIO_PUSH_BUTTON_1       (PIO_PA19_IDX)
#define GPIO_PUSH_BUTTON_1_FLAGS (IOPORT_MODE_PULLUP | IOPORT_MODE_DEBOUNCE)
#define GPIO_PUSH_BUTTON_1_SENSE (IOPORT_SENSE_RISING)

#define PIN_PUSHBUTTON_1       {PIO_PA19, PIOA, ID_PIOA, PIO_INPUT, \
		PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_RISE_EDGE}
#define PIN_PUSHBUTTON_1_MASK  PIO_PA19
#define PIN_PUSHBUTTON_1_PIO   PIOA
#define PIN_PUSHBUTTON_1_ID    ID_PIOA
#define PIN_PUSHBUTTON_1_TYPE  PIO_INPUT
#define PIN_PUSHBUTTON_1_ATTR  (PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_RISE_EDGE)
#define PIN_PUSHBUTTON_1_IRQn  PIOA_IRQn

/**
 * Push button #1 definition. Attributes = pull-up + debounce + interrupt on
 * falling edge.
 */
#define PUSHBUTTON_2_NAME        "BP3 TAMP"
#define PUSHBUTTON_2_WKUP_LINE   (10)
#define PUSHBUTTON_2_WKUP_FSTT   (PMC_FSMR_FSTT10)
#define GPIO_PUSH_BUTTON_2       (PIO_PA20_IDX)
#define GPIO_PUSH_BUTTON_2_FLAGS (IOPORT_MODE_PULLUP | IOPORT_MODE_DEBOUNCE)
#define GPIO_PUSH_BUTTON_2_SENSE (IOPORT_SENSE_FALLING)

#define PIN_PUSHBUTTON_2       {PIO_PA20, PIOA, ID_PIOA, PIO_INPUT, \
		PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE}
#define PIN_PUSHBUTTON_2_MASK  PIO_PA20
#define PIN_PUSHBUTTON_2_PIO   PIOA
#define PIN_PUSHBUTTON_2_ID    ID_PIOA
#define PIN_PUSHBUTTON_2_TYPE  PIO_INPUT
#define PIN_PUSHBUTTON_2_ATTR  (PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE)
#define PIN_PUSHBUTTON_2_IRQn  PIOA_IRQn

/**
 * Push button #2 definition. Attributes = pull-up + debounce + interrupt on
 * both edges.
 */
#define PUSHBUTTON_3_NAME        "BP4 SCROLL-UP"
#define PUSHBUTTON_3_WKUP_LINE   (1)
#define PUSHBUTTON_3_WKUP_FSTT   (PMC_FSMR_FSTT1)
#define GPIO_PUSH_BUTTON_3       (PIO_PA1_IDX)
#define GPIO_PUSH_BUTTON_3_FLAGS (IOPORT_MODE_PULLUP | IOPORT_MODE_DEBOUNCE)
#define GPIO_PUSH_BUTTON_3_SENSE (IOPORT_SENSE_BOTHEDGES)

#define PIN_PUSHBUTTON_3       {PIO_PA1, PIOA, ID_PIOA, PIO_INPUT, \
		PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_RISE_EDGE}
#define PIN_PUSHBUTTON_3_MASK  PIO_PA1
#define PIN_PUSHBUTTON_3_PIO   PIOA
#define PIN_PUSHBUTTON_3_ID    ID_PIOA
#define PIN_PUSHBUTTON_3_TYPE  PIO_INPUT
#define PIN_PUSHBUTTON_3_ATTR  (PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_RISE_EDGE)
#define PIN_PUSHBUTTON_3_IRQn  PIOA_IRQn

/**
 * Push button #3 definition. Attributes = pull-up + debounce + interrupt on
 * rising edge.
 */
#define PUSHBUTTON_4_NAME        "BP5 SCROLL-DOWN"
#define PUSHBUTTON_4_WKUP_LINE   (2)
#define PUSHBUTTON_4_WKUP_FSTT   (PMC_FSMR_FSTT2)
#define GPIO_PUSH_BUTTON_4       (PIO_PA2_IDX)
#define GPIO_PUSH_BUTTON_4_FLAGS (IOPORT_MODE_PULLUP | IOPORT_MODE_DEBOUNCE)
#define GPIO_PUSH_BUTTON_4_SENSE (IOPORT_SENSE_RISING)

#define PIN_PUSHBUTTON_4       {PIO_PA2, PIOA, ID_PIOA, PIO_INPUT, \
		PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_RISE_EDGE}
#define PIN_PUSHBUTTON_4_MASK  PIO_PA2
#define PIN_PUSHBUTTON_4_PIO   PIOA
#define PIN_PUSHBUTTON_4_ID    ID_PIOA
#define PIN_PUSHBUTTON_4_TYPE  PIO_INPUT
#define PIN_PUSHBUTTON_4_ATTR  (PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_RISE_EDGE)
#define PIN_PUSHBUTTON_4_IRQn  PIOA_IRQn

/** List of all push button definitions. */
#define PINS_PUSHBUTTONS    {PIN_PUSHBUTTON_1, PIN_PUSHBUTTON_2,\
		PIN_PUSHBUTTON_3, PIN_PUSHBUTTON_4}

#define PIN_TC0_TIOA0        (PIO_PA0_IDX)
#define PIN_TC0_TIOA0_MUX    (IOPORT_MODE_MUX_B)
#define PIN_TC0_TIOA0_FLAGS  (IOPORT_MODE_MUX_B)

#define PIN_TC0_TIOA1        (PIO_PA15_IDX)
#define PIN_TC0_TIOA1_MUX    (IOPORT_MODE_MUX_B)
#define PIN_TC0_TIOA1_FLAGS  (IOPORT_MODE_MUX_B)

#define PIN_TC0_TIOA1_PIO    PIOA
#define PIN_TC0_TIOA1_MASK   PIO_PA15
#define PIN_TC0_TIOA1_ID     ID_PIOA
#define PIN_TC0_TIOA1_TYPE   PIO_PERIPH_B
#define PIN_TC0_TIOA1_ATTR   PIO_DEFAULT

#define PIN_TC0_TIOA2        (PIO_PA26_IDX)
#define PIN_TC0_TIOA2_MUX    (IOPORT_MODE_MUX_B)
#define PIN_TC0_TIOA2_FLAGS  (IOPORT_MODE_MUX_B)

#define PIN_TC0_TIOA2_PIO    PIOA
#define PIN_TC0_TIOA2_MASK   PIO_PA26
#define PIN_TC0_TIOA2_ID     ID_PIOA
#define PIN_TC0_TIOA2_TYPE   PIO_PERIPH_B
#define PIN_TC0_TIOA2_ATTR   PIO_DEFAULT

/** PWM LED0 pin definitions. */
#define PIN_PWM_LED0_GPIO     PIO_PD20_IDX
#define PIN_PWM_LED0_FLAGS    (IOPORT_MODE_MUX_A)
#define PIN_PWM_LED0_CHANNEL  PWM_CHANNEL_0

/** PWM LED1 pin definitions. */
#define PIN_PWM_LED1_GPIO     PIO_PD21_IDX
#define PIN_PWM_LED1_FLAGS    (IOPORT_MODE_MUX_A)
#define PIN_PWM_LED1_CHANNEL  PWM_CHANNEL_1

/** PWM LED2 pin definitions. */
#define PIN_PWM_LED2_GPIO     PIO_PD22_IDX
#define PIN_PWM_LED2_FLAGS    (IOPORT_MODE_MUX_A)
#define PIN_PWM_LED2_CHANNEL  PWM_CHANNEL_2

/** PWM LED3 pin definitions. */
#define PIN_PWM_LED3_GPIO     PIO_PA0_IDX
#define PIN_PWM_LED3_FLAGS    (IOPORT_MODE_MUX_A)
#define PIN_PWM_LED3_CHANNEL  PWM_CHANNEL_0


/** SPI MISO pin definition. */
#define SPI_MISO_GPIO         (PIO_PA12_IDX)
#define SPI_MISO_FLAGS        (IOPORT_MODE_MUX_A)
/** SPI MOSI pin definition. */
#define SPI_MOSI_GPIO         (PIO_PA13_IDX)
#define SPI_MOSI_FLAGS        (IOPORT_MODE_MUX_A)
/** SPI SPCK pin definition. */
#define SPI_SPCK_GPIO         (PIO_PA14_IDX)
#define SPI_SPCK_FLAGS        (IOPORT_MODE_MUX_A)

/** SPI chip select 0 pin definition. (Only one configuration is possible) */
#define SPI_NPCS0_GPIO        (PIO_PA11_IDX)
#define SPI_NPCS0_FLAGS       (IOPORT_MODE_MUX_A)
/** SPI chip select 1 pin definition. (multiple configurations are possible) */
#define SPI_NPCS1_PA9_GPIO    (PIO_PA9_IDX)
#define SPI_NPCS1_PA9_FLAGS   (IOPORT_MODE_MUX_B)
#define SPI_NPCS1_PA31_GPIO   (PIO_PA31_IDX)
#define SPI_NPCS1_PA31_FLAGS  (IOPORT_MODE_MUX_A)
#define SPI_NPCS1_PB14_GPIO   (PIO_PB14_IDX)
#define SPI_NPCS1_PB14_FLAGS  (IOPORT_MODE_MUX_A)
#define SPI_NPCS1_PC4_GPIO    (PIO_PC4_IDX)
#define SPI_NPCS1_PC4_FLAGS   (IOPORT_MODE_MUX_B)
/** SPI chip select 2 pin definition. (multiple configurations are possible) */
#define SPI_NPCS2_PA10_GPIO   (PIO_PA10_IDX)
#define SPI_NPCS2_PA10_FLAGS  (IOPORT_MODE_MUX_B)
#define SPI_NPCS2_PA30_GPIO   (PIO_PA30_IDX)
#define SPI_NPCS2_PA30_FLAGS  (IOPORT_MODE_MUX_B)
#define SPI_NPCS2_PB2_GPIO    (PIO_PB2_IDX)
#define SPI_NPCS2_PB2_FLAGS   (IOPORT_MODE_MUX_B)
/** SPI chip select 3 pin definition. (multiple configurations are possible) */
#define SPI_NPCS3_PA3_GPIO    (PIO_PA3_IDX)
#define SPI_NPCS3_PA3_FLAGS   (IOPORT_MODE_MUX_B)
#define SPI_NPCS3_PA5_GPIO    (PIO_PA5_IDX)
#define SPI_NPCS3_PA5_FLAGS   (IOPORT_MODE_MUX_B)
#define SPI_NPCS3_PA22_GPIO   (PIO_PA22_IDX)
#define SPI_NPCS3_PA22_FLAGS  (IOPORT_MODE_MUX_B)

/* Select the SPI module that AT25DFx is connected to */
#define AT25DFX_SPI_MODULE          SPI

/* Chip select used by AT25DFx components on the SPI module instance */
#define AT25DFX_CS      3

/* Touch screen IRQ & Busy pin definition */
#define BOARD_ADS7843_IRQ_GPIO  (PIO_PA16_IDX)
#define BOARD_ADS7843_IRQ_FLAGS  IOPORT_MODE_PULLUP
#define BOARD_ADS7843_BUSY_GPIO  (PIO_PA17_IDX)
#define BOARD_ADS7843_BUSY_FLAGS  IOPORT_MODE_PULLUP
/**
* SPI instance, which can be SPI, SPI0 or SPI1, depends on which SPI
* channel is used.
*/
#define BOARD_ADS7843_SPI_BASE    SPI
/* SPI chip select NO., depends on which SPI CS pin is used by ADS7843. */
#define BOARD_ADS7843_SPI_NPCS    0

/** TWI0 pins definition */
#define TWI0_DATA_GPIO   PIO_PA3_IDX
#define TWI0_DATA_FLAGS  (IOPORT_MODE_MUX_A)
#define TWI0_CLK_GPIO    PIO_PA4_IDX
#define TWI0_CLK_FLAGS   (IOPORT_MODE_MUX_A)

/** TWI1 pins definition */
#define TWI1_DATA_GPIO   PIO_PB4_IDX
#define TWI1_DATA_FLAGS  (IOPORT_MODE_MUX_A)
#define TWI1_CLK_GPIO    PIO_PB5_IDX
#define TWI1_CLK_FLAGS   (IOPORT_MODE_MUX_A)

/** PCK0 pin definition (PA6) */
#define PIN_PCK0         (PIO_PA6_IDX)
#define PIN_PCK0_MUX     (IOPORT_MODE_MUX_B)
#define PIN_PCK0_FLAGS   (IOPORT_MODE_MUX_B)
#define PIN_PCK0_PORT    IOPORT_PIOA
#define PIN_PCK0_MASK    PIO_PA6B_PCK0
#define PIN_PCK0_PIO     PIOA
#define PIN_PCK0_ID      ID_PIOA
#define PIN_PCK0_TYPE    PIO_PERIPH_B
#define PIN_PCK0_ATTR    PIO_DEFAULT

/** USART0 pin RX */
#define PIN_USART0_RXD        {PIO_PB0C_RXD0, PIOB, ID_PIOB, PIO_PERIPH_C, \
		PIO_DEFAULT}
#define PIN_USART0_RXD_IDX    (PIO_PB0_IDX)
#define PIN_USART0_RXD_FLAGS  (IOPORT_MODE_MUX_C)
/** USART0 pin TX */
#define PIN_USART0_TXD        {PIO_PB1C_TXD0, PIOB, ID_PIOB, PIO_PERIPH_C, \
		PIO_DEFAULT}
#define PIN_USART0_TXD_IDX    (PIO_PB1_IDX)
#define PIN_USART0_TXD_FLAGS  (IOPORT_MODE_MUX_C)
/** USART0 pin CTS */
#define PIN_USART0_CTS        {PIO_PB2C_CTS0, PIOB, ID_PIOB, PIO_PERIPH_C, \
		PIO_DEFAULT}
#define PIN_USART0_CTS_IDX    (PIO_PB2_IDX)
#define PIN_USART0_CTS_FLAGS  (IOPORT_MODE_MUX_C)
/** USART0 pin RTS */
#define PIN_USART0_RTS        {PIO_PB3C_RTS0, PIOB, ID_PIOB, PIO_PERIPH_C, \
		PIO_DEFAULT}
#define PIN_USART0_RTS_IDX    (PIO_PB3_IDX)
#define PIN_USART0_RTS_FLAGS  (IOPORT_MODE_MUX_C)
/** USART0 pin SCK */
#define PIN_USART0_SCK        {PIO_PB13C_SCK0, PIOB, ID_PIOB, PIO_PERIPH_C, \
		PIO_DEFAULT}
#define PIN_USART0_SCK_IDX    (PIO_PB13_IDX)
#define PIN_USART0_SCK_FLAGS  (IOPORT_MODE_MUX_C)

/** USART1 pin RX */
#define PIN_USART1_RXD        {PIO_PA21A_RXD1, PIOA, ID_PIOA, PIO_PERIPH_A, \
		PIO_DEFAULT}
#define PIN_USART1_RXD_IDX    (PIO_PA21_IDX)
#define PIN_USART1_RXD_FLAGS  (IOPORT_MODE_MUX_A)
/** USART1 pin TX */
#define PIN_USART1_TXD        {PIO_PA22A_TXD1, PIOA, ID_PIOA, PIO_PERIPH_A, \
		PIO_DEFAULT}
#define PIN_USART1_TXD_IDX    (PIO_PA22_IDX)
#define PIN_USART1_TXD_FLAGS  (IOPORT_MODE_MUX_A)
/** USART1 pin CTS */
#define PIN_USART1_CTS        {PIO_PA25A_CTS1, PIOA, ID_PIOA, PIO_PERIPH_A, \
		PIO_DEFAULT}
#define PIN_USART1_CTS_IDX    (PIO_PA25_IDX)
#define PIN_USART1_CTS_FLAGS  (IOPORT_MODE_MUX_A)
/** USART1 pin RTS */
#define PIN_USART1_RTS        {PIO_PA24A_RTS1, PIOA, ID_PIOA, PIO_PERIPH_A, \
		PIO_DEFAULT}
#define PIN_USART1_RTS_IDX    (PIO_PA24_IDX)
#define PIN_USART1_RTS_FLAGS  (IOPORT_MODE_MUX_A)
/** USART1 pin SCK */
#define PIN_USART1_SCK        {PIO_PA23A_SCK1, PIOA, ID_PIOA, PIO_PERIPH_A, \
		PIO_DEFAULT}
#define PIN_USART1_SCK_IDX    (PIO_PA23_IDX)
#define PIN_USART1_SCK_FLAGS  (IOPORT_MODE_MUX_A)
/** USART1 pin ENABLE */
#define PIN_USART1_EN         {PIO_PA23, PIOA, ID_PIOA, PIO_OUTPUT_0, \
		PIO_DEFAULT}
#define PIN_USART1_EN_IDX     (PIO_PA23_IDX)
#define PIN_USART1_EN_FLAGS   (0)
#define PIN_USART1_EN_ACTIVE_LEVEL   IOPORT_PIN_LEVEL_LOW
#define PIN_USART1_EN_INACTIVE_LEVEL IOPORT_PIN_LEVEL_HIGH

/** USB VBus monitoring pin definition. */
#define PIN_USB_VBUS    {PIO_PC21, PIOC, ID_PIOC, PIO_INPUT, PIO_PULLUP}
#define USB_VBUS_FLAGS    (PIO_INPUT | PIO_DEBOUNCE | PIO_IT_EDGE)
#define USB_VBUS_PIN_IRQn (PIOC_IRQn)
#define USB_VBUS_PIN      (PIO_PC21_IDX)
#define USB_VBUS_PIO_ID   (ID_PIOC)
#define USB_VBUS_PIO_MASK (PIO_PC21)
/* This pin can not be used as fast wakeup source such as
 * USB_VBUS_WKUP PMC_FSMR_FSTT7 */

/** USB D- pin (System function) */
#define PIN_USB_DM      {PIO_PB10}
/** USB D+ pin (System function) */
#define PIN_USB_DP      {PIO_PB11}

/** EBI Data Bus pins */
#define PIN_EBI_DATA_BUS_D0        PIO_PC0_IDX
#define PIN_EBI_DATA_BUS_D1        PIO_PC1_IDX
#define PIN_EBI_DATA_BUS_D2        PIO_PC2_IDX
#define PIN_EBI_DATA_BUS_D3        PIO_PC3_IDX
#define PIN_EBI_DATA_BUS_D4        PIO_PC4_IDX
#define PIN_EBI_DATA_BUS_D5        PIO_PC5_IDX
#define PIN_EBI_DATA_BUS_D6        PIO_PC6_IDX
#define PIN_EBI_DATA_BUS_D7        PIO_PC7_IDX
#define PIN_EBI_DATA_BUS_FLAGS     (IOPORT_MODE_MUX_A | IOPORT_MODE_PULLUP)

#define PIN_EBI_NRD                PIO_PC11_IDX
#define PIN_EBI_NRD_FLAGS          (IOPORT_MODE_MUX_A | IOPORT_MODE_PULLUP)
#define PIN_EBI_NWE                PIO_PC8_IDX
#define PIN_EBI_NWE_FLAGS          (IOPORT_MODE_MUX_A | IOPORT_MODE_PULLUP)

/** EBI pin for LCD CS and RS **/
#define PIN_EBI_NCS1               PIO_PD18_IDX
#define PIN_EBI_NCS1_FLAGS         (IOPORT_MODE_MUX_A | IOPORT_MODE_PULLUP)
#define PIN_EBI_LCD_RS             PIO_PC19_IDX
#define PIN_EBI_LCD_RS_FLAGS       (IOPORT_MODE_MUX_A | IOPORT_MODE_PULLUP)

/** Indicates board has an ILI9325 external component to manage LCD. */
#define BOARD_LCD_ILI93XX

/** Backlight pin definition. */
#define BOARD_AAT31XX_SET_GPIO      PIO_PC13_IDX
/** Define ILI93xx base address. */
#define BOARD_ILI93XX_ADDR          0x61000000
/** Define ILI9325 register select signal. */
#define BOARD_ILI93XX_RS            (1 << 1)
/** Display width in pixels. */
#define BOARD_LCD_WIDTH             240
/** Display height in pixels. */
#define BOARD_LCD_HEIGHT            320

/* KSZ8051MNL relate PIN definition */
#define PIN_KSZ8051MNL_RXC_IDX                PIO_PD14_IDX
#define PIN_KSZ8051MNL_RXC_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_TXC_IDX                PIO_PD0_IDX
#define PIN_KSZ8051MNL_TXC_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_TXEN_IDX                PIO_PD1_IDX
#define PIN_KSZ8051MNL_TXEN_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_TXD3_IDX                PIO_PD16_IDX
#define PIN_KSZ8051MNL_TXD3_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_TXD2_IDX                PIO_PD15_IDX
#define PIN_KSZ8051MNL_TXD2_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_TXD1_IDX                PIO_PD3_IDX
#define PIN_KSZ8051MNL_TXD1_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_TXD0_IDX                PIO_PD2_IDX
#define PIN_KSZ8051MNL_TXD0_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_RXD3_IDX                PIO_PD12_IDX
#define PIN_KSZ8051MNL_RXD3_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_RXD2_IDX                PIO_PD11_IDX
#define PIN_KSZ8051MNL_RXD2_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_RXD1_IDX                PIO_PD6_IDX
#define PIN_KSZ8051MNL_RXD1_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_RXD0_IDX                PIO_PD5_IDX
#define PIN_KSZ8051MNL_RXD0_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_RXER_IDX                PIO_PD7_IDX
#define PIN_KSZ8051MNL_RXER_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_RXDV_IDX                PIO_PD4_IDX
#define PIN_KSZ8051MNL_RXDV_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_CRS_IDX                PIO_PD10_IDX
#define PIN_KSZ8051MNL_CRS_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_COL_IDX                PIO_PD13_IDX
#define PIN_KSZ8051MNL_COL_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_MDC_IDX          PIO_PD8_IDX
#define PIN_KSZ8051MNL_MDC_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_MDIO_IDX                PIO_PD9_IDX
#define PIN_KSZ8051MNL_MDIO_FLAGS            (IOPORT_MODE_MUX_A)
#define PIN_KSZ8051MNL_INTRP_IDX                PIO_PD28_IDX

/** NandFlash pins definition: OE. */
#define PIN_EBI_NANDOE    (PIO_PC9_IDX)
#define PIN_EBI_NANDOE_FLAGS    (IOPORT_MODE_MUX_A)

/** NandFlash pins definition: WE. */
#define PIN_EBI_NANDWE    (PIO_PC10_IDX)
#define PIN_EBI_NANDWE_FLAGS    (IOPORT_MODE_MUX_A)

/** NandFlash pins definition: CLE. */
#define PIN_EBI_NANDCLE    (PIO_PC17_IDX)
#define PIN_EBI_NANDCLE_FLAGS    (IOPORT_MODE_MUX_A)

/** NandFlash pins definition: ALE. */
#define PIN_EBI_NANDALE    (PIO_PC16_IDX)
#define PIN_EBI_NANDALE_FLAGS    (IOPORT_MODE_MUX_A)

/** NandFlash pins definition: DATA. */
#define PIN_EBI_NANDIO_0    (PIO_PC0_IDX)
#define PIN_EBI_NANDIO_0_FLAGS    (IOPORT_MODE_MUX_A)

#define PIN_EBI_NANDIO_1    (PIO_PC1_IDX)
#define PIN_EBI_NANDIO_1_FLAGS    (IOPORT_MODE_MUX_A)

#define PIN_EBI_NANDIO_2    (PIO_PC2_IDX)
#define PIN_EBI_NANDIO_2_FLAGS    (IOPORT_MODE_MUX_A)

#define PIN_EBI_NANDIO_3    (PIO_PC3_IDX)
#define PIN_EBI_NANDIO_3_FLAGS    (IOPORT_MODE_MUX_A)

#define PIN_EBI_NANDIO_4    (PIO_PC4_IDX)
#define PIN_EBI_NANDIO_4_FLAGS    (IOPORT_MODE_MUX_A)

#define PIN_EBI_NANDIO_5    (PIO_PC5_IDX)
#define PIN_EBI_NANDIO_5_FLAGS    (IOPORT_MODE_MUX_A)

#define PIN_EBI_NANDIO_6    (PIO_PC6_IDX)
#define PIN_EBI_NANDIO_6_FLAGS    (IOPORT_MODE_MUX_A)

#define PIN_EBI_NANDIO_7    (PIO_PC7_IDX)
#define PIN_EBI_NANDIO_7_FLAGS    (IOPORT_MODE_MUX_A)

/** Nandflash chip enable pin definition. */
#define PIN_NF_CE_IDX    (PIO_PC14_IDX)

/** Nandflash ready/busy pin definition. */
#define PIN_NF_RB_IDX    (PIO_PC18_IDX)

/* Chip select number for nand */
#define BOARD_NAND_CS    0

/*----------------------------------------------------------------------------*/
/**
 * \page sam4e_ek_usb "SAM4E-EK - USB device"
 *
 * \section Definitions
 * - \ref BOARD_USB_BMATTRIBUTES
 * - \ref CHIP_USB_UDP
 * - \ref CHIP_USB_PULLUP_INTERNAL
 * - \ref CHIP_USB_NUMENDPOINTS
 * - \ref CHIP_USB_ENDPOINTS_MAXPACKETSIZE
 * - \ref CHIP_USB_ENDPOINTS_BANKS
 */

/**
 * USB attributes configuration descriptor (bus or self powered,
 * remote wakeup)
 */
#define BOARD_USB_BMATTRIBUTES  USBConfigurationDescriptor_SELFPOWERED_RWAKEUP

/** Indicates chip has an UDP Full Speed. */
#define CHIP_USB_UDP

/** Indicates chip has an internal pull-up. */
#define CHIP_USB_PULLUP_INTERNAL

/** Number of USB endpoints */
#define CHIP_USB_NUMENDPOINTS 8

/** Endpoints max packet size */
#define CHIP_USB_ENDPOINTS_MAXPACKETSIZE(i) \
   ((i == 0) ? 64 : \
   ((i == 1) ? 64 : \
   ((i == 2) ? 64 : \
   ((i == 3) ? 64 : \
   ((i == 4) ? 512 : \
   ((i == 5) ? 512 : \
   ((i == 6) ? 64 : \
   ((i == 7) ? 64 : 0 ))))))))

/** Endpoints Number of Bank */
#define CHIP_USB_ENDPOINTS_BANKS(i) \
   ((i == 0) ? 1 : \
   ((i == 1) ? 2 : \
   ((i == 2) ? 2 : \
   ((i == 3) ? 1 : \
   ((i == 4) ? 2 : \
   ((i == 5) ? 2 : \
   ((i == 6) ? 2 : \
   ((i == 7) ? 2 : 0 ))))))))

/*----------------------------------------------------------------------------*/
/**
 * \page sam4e_ek_extcomp "SAM4E-EK - External components"
 * This page lists the definitions related to external on-board components
 * located in the board.h file for the SAM4E-EK.
 *
 * SD Card
 * - \ref BOARD_SD_PINS
 * - \ref BOARD_SD_PIN_CD
 *
 * QTouch component (QT2160)
 * - \ref BOARD_QT_TWI_INSTANCE
 * - \ref BOARD_QT_DEVICE_ADDRESS
 * - \ref BOARD_QT_CHANGE_PIN_IDX
 * - \ref BOARD_QT_CHANGE_PIN_FLAGS
 * - \ref BOARD_QT_CHANGE_PIN_SENSE
 */

/** HSMCI pins that shall be configured to access the SD card. */
#define BOARD_SD_PINS               PINS_HSMCI
/** HSMCI Card Detect pin. */
#define BOARD_SD_PIN_CD             PIN_HSMCI_CD

/** TWI instance for QTouch device */
#define BOARD_QT_TWI_INSTANCE       TWI0
/* QTouch device address (I2CA1 = I2CA0 = 0) */
#define BOARD_QT_DEVICE_ADDRESS     0x0D
/** QTouch component pin definition */
#define BOARD_QT_CHANGE_PIN_IDX     (PIO_PE4_IDX)
#define BOARD_QT_CHANGE_PIN_FLAGS   (IOPORT_MODE_PULLUP | IOPORT_MODE_DEBOUNCE)
#define BOARD_QT_CHANGE_PIN_SENSE   (IOPORT_SENSE_FALLING)

/*----------------------------------------------------------------------------*/
/**
 * \page sam4e_ek_mem "SAM4E-EK - Memories"
 * This page lists definitions related to internal & external on-board memories.
 *
 * \section NandFlash
 * - \ref BOARD_NF_COMMAND_ADDR
 * - \ref BOARD_NF_ADDRESS_ADDR
 * - \ref BOARD_NF_DATA_ADDR
 *
 * \section NorFlash
 * - \ref BOARD_NORFLASH_ADDR
 * - \ref BOARD_NORFLASH_DFT_BUS_SIZE
 */

/** Address for transferring command bytes to the nandflash. */
#define BOARD_NF_COMMAND_ADDR   0x60400000
/** Address for transferring address bytes to the nandflash. */
#define BOARD_NF_ADDRESS_ADDR   0x60200000
/** Address for transferring data bytes to the nandflash. */
#define BOARD_NF_DATA_ADDR      0x60000000
/* Bus width for NAND */
#define CONF_NF_BUSWIDTH    8
/* Access timing for NAND */
#define CONF_NF_SETUP_TIMING (SMC_SETUP_NWE_SETUP(0) \
		| SMC_SETUP_NCS_WR_SETUP(1) \
		| SMC_SETUP_NRD_SETUP(0) \
		| SMC_SETUP_NCS_RD_SETUP(1))
#define CONF_NF_PULSE_TIMING (SMC_PULSE_NWE_PULSE(2) \
		| SMC_PULSE_NCS_WR_PULSE(3) \
		| SMC_PULSE_NRD_PULSE(4) \
		| SMC_PULSE_NCS_RD_PULSE(4))
#define CONF_NF_CYCLE_TIMING (SMC_CYCLE_NWE_CYCLE(4) \
		| SMC_CYCLE_NRD_CYCLE(7))

/** Address for transferring command bytes to the norflash. */
#define BOARD_NORFLASH_ADDR     0x63000000
/** Default NOR bus size after power up reset */
#define BOARD_NORFLASH_DFT_BUS_SIZE 8

/*----------------------------------------------------------------------------*/

#define CONSOLE_UART               UART0
#define CONSOLE_UART_ID            ID_UART0

/* RE pin. */
#define PIN_RE_IDX                 PIN_USART1_CTS_IDX
#define PIN_RE_FLAGS               (0)

/* IRDA SD pin. */
#define PIN_IRDA_SD_IDX            PIN_USART1_CTS_IDX
#define PIN_IRDA_SD_FLAGS          (0)

/* TXD pin configuration. */
#define PIN_USART_TXD_IDX          PIN_USART1_TXD_IDX
#define PIN_USART_TXD_FLAGS        (IOPORT_MODE_MUX_A)
#define PIN_USART_TXD_IO_FLAGS     (0)

/* ISO7816 example relate PIN definition. */
#define ISO7816_USART_ID           ID_USART1
#define ISO7816_USART              USART1
#define PIN_ISO7816_RST_IDX        PIO_PA15_IDX
#define PIN_ISO7816_RST_FLAG       (0)

/*----------------------------------------------------------------------------*/
/* GMAC HW configurations */
#define BOARD_GMAC_PHY_ADDR 0

/*----------------------------------------------------------------------------*/
/**
 * \page sam4e_ek_CAN "SAM4E-EK - CAN"
 * This page lists definitions related to CAN0 and CAN1.
 *
 * CAN
 * - \ref PIN_CAN0_TRANSCEIVER_RXEN
 * - \ref PIN_CAN0_TRANSCEIVER_RS
 * - \ref PIN_CAN0_TXD
 * - \ref PIN_CAN0_RXD
 * - \ref PINS_CAN0
 *
 * - \ref PIN_CAN1_TRANSCEIVER_RXEN
 * - \ref PIN_CAN1_TRANSCEIVER_RS
 * - \ref PIN_CAN1_TXD
 * - \ref PIN_CAN1_RXD
 * - \ref PINS_CAN1
 */
/** CAN0 transceiver PIN RS. */
#define PIN_CAN0_TR_RS_IDX        PIO_PE0_IDX
#define PIN_CAN0_TR_RS_FLAGS      IOPORT_DIR_OUTPUT

/** CAN0 transceiver PIN EN. */
#define PIN_CAN0_TR_EN_IDX        PIO_PE1_IDX
#define PIN_CAN0_TR_EN_FLAGS      IOPORT_DIR_OUTPUT

/** CAN0 PIN RX. */
#define PIN_CAN0_RX_IDX           PIO_PB3_IDX
#define PIN_CAN0_RX_FLAGS         IOPORT_MODE_MUX_A

/** CAN0 PIN TX. */
#define PIN_CAN0_TX_IDX           PIO_PB2_IDX
#define PIN_CAN0_TX_FLAGS         IOPORT_MODE_MUX_A

/** CAN1 transceiver PIN RS. */
#define PIN_CAN1_TR_RS_IDX        PIO_PE2_IDX
#define PIN_CAN1_TR_RS_FLAGS      IOPORT_DIR_OUTPUT

/** CAN1 transceiver PIN EN. */
#define PIN_CAN1_TR_EN_IDX        PIO_PE3_IDX
#define PIN_CAN1_TR_EN_FLAGS      IOPORT_DIR_OUTPUT

/** CAN1 PIN RX. */
#define PIN_CAN1_RX_IDX           PIO_PC12_IDX
#define PIN_CAN1_RX_FLAGS         IOPORT_MODE_MUX_C

/** CAN1 PIN TX. */
#define PIN_CAN1_TX_IDX           PIO_PC15_IDX
#define PIN_CAN1_TX_FLAGS         IOPORT_MODE_MUX_C

/** AFEC channel for potentiometer */
#define AFEC_CHANNEL_POTENTIOMETER  AFEC_CHANNEL_5

/*----------------------------------------------------------------------------*/
#endif  /* _SAM4E_EK_H_ */
