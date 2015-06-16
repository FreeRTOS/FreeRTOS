/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \page samv7_Xplained_ultra_board_desc SAM V71 Xplained Ultra - Board 
 * Description
 *
 * \section Purpose
 *
 * This file is dedicated to describe the SAM V71 Xplained Ultra board.
 *
 * \section Contents
 *
 *  - For SAM V71 Xplained Ultra board information, see 
 *    \subpage samv7_Xplained_ultra_board_info.
 *  - For operating frequency information, see \subpage samv7_Xplained_ultra_opfreq.
 *  - For using portable PIO definitions, see \subpage samv7_Xplained_ultra_piodef.
 *  - For using GMAC PIO definitions, see \subpage samv7_Xplained_ultra_gmac.
 *  - For using ISI definitions, see \subpage samv7_Xplained_ultra_isi.
 *  - For on-board memories, see \subpage samv7_Xplained_ultra_mem.
 *  - Several USB definitions are included here, 
 *    see \subpage samv7_Xplained_ultra_usb.
 *  - For External components, see \subpage samv7_Xplained_ultra_extcomp.
 *  - For Individual chip definition, see \subpage samv7_Xplained_ultra_chipdef.
 *
 * To get more software details and the full list of parameters related to the
 * SAM V71 Xplained Ultra board configuration, please have a look at the source
 * file:
 * \ref board.h\n
 *
 * \section Usage
 *
 *  - The code for booting the board is provided by board_cstartup_xxx.c and
 *    board_lowlevel.c.
 *  - For using board PIOs, board characteristics (clock, etc.) and external
 *    components, see board.h.
 *  - For manipulating memories, see board_memories.h.
 *
 * This file can be used as a template and modified to fit a custom board, with
 * specific PIOs usage or memory connections.
 */

/**
 *  \file board.h
 *
 *  Definition of SAM V71 Xplained Ultra board characteristics, PIOs and
 *  external components interface.
 */

#ifndef _BOARD_H_
#define _BOARD_H_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include "include/board_lowlevel.h"
#include "include/board_memories.h"
#include "include/led.h"
#include "include/gmii.h"
#include "include/gmacb_phy.h"
#include "include/dbg_console.h"
#include "include/bmp.h"
#include "include/lcdd.h"
#include "include/ili9488.h"
#include "include/ili9488_reg.h"
#include "include/ili9488_spi.h"
#include "include/ili9488_ebi.h"
#include "include/ili9488_dma.h"
#include "include/ili9488_spi_dma.h"
#include "include/ili9488_ebi_dma.h"
#include "include/frame_buffer.h"
#include "include/lcd_color.h"
#include "include/lcd_draw.h"
#include "include/lcd_font10x14.h"
#include "include/lcd_font.h"
#include "include/lcd_gimp_image.h"
#include "include/rtc_calib.h"
#include "include/wm8904.h"
#include "include/cs2100.h"
#include "include/s25fl1.h"
#include "include/omnivision.h"
#include "include/ovyuv.h"
#include "include/ov.h"
#include "include/iso7816_4.h"
   
#if defined (  __GNUC__  )
#include "include/syscalls.h"
#endif
/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------*/
/**
 * \page samv7_Xplained_ultra_board_info "SAM V71 Xplained Ultra - Board informations"
 * This page lists several definition related to the board description.
 *
 * \section Definitions
 * - \ref BOARD_NAME
 */

/** Name of the board */
#define BOARD_NAME "SAM V71 Xplained Ultra"
#define NO_PUSHBUTTON
/*----------------------------------------------------------------------------*/
/**
 *  \page samv7_Xplained_ultra_opfreq "SAM V71 Xplained Ultra - Operating frequencies"
 *  This page lists several definition related to the board operating frequency
 *  (when using the initialization done by board_lowlevel.c).
 *
 *  \section Definitions
 *  - \ref BOARD_MAINOSC
 *  - \ref BOARD_MCK
 */

/** Frequency of the board main oscillator */
#define BOARD_MAINOSC    12000000

/** Master clock frequency (when using board_lowlevel.c) */

#define BOARD_MCK    150000000 

#if (BOARD_MCK==132000000 )

#define PLL_MUL    0x16
#define PLL_DIV    0x01

#else   // 300MHz(PCK) and 150MHz(MCK) by default

#define PLL_MUL    0x19
#define PLL_DIV    0x01

#endif

/*----------------------------------------------------------------------------*/
/**
 * \page samv7_Xplained_ultra_piodef "SAM V71 Xplained Ultra - PIO definitions"
 * This pages lists all the PIOs definitions contained in board.h. The constants
 * are named using the following convention: PIN_* for a constant which defines
 * a single Pin instance (but may include several PIOs sharing the same
 * controller), and PINS_* for a list of Pin instances.
 *
 * UART0
 * - \ref PINS_UART0
 *
 * UART4
 * - \ref PINS_UART4
 *
 * LEDs
 * - \ref PIN_LED_0
 * - \ref PIN_LED_1
 * - \ref PINS_LEDS
 *
 * Push buttons
 * - \ref PIN_PUSHBUTTON_0
 * - \ref PIN_PUSHBUTTON_1
 * - \ref PINS_PUSHBUTTONS
 * - \ref PUSHBUTTON_BP0
 * - \ref PUSHBUTTON_BP1
 *
 * PWMC
 * - \ref PIN_PWMC_PWMH0
 * - \ref PIN_PWMC_PWMH1
 * - \ref PIN_PWM_LED0
 * - \ref PIN_PWM_LED1
 * - \ref CHANNEL_PWM_LED0
 * - \ref CHANNEL_PWM_LED1
 *
 * SPI
 * - \ref PIN_SPI_MISO
 * - \ref PIN_SPI_MOSI
 * - \ref PIN_SPI_SPCK
 * - \ref PINS_SPI
 *
 * PCK0
 * - \ref PIN_PCK0
 * - \ref PIN_PCK1
 * - \ref PIN_PCK2
 *
 * PIO PARALLEL CAPTURE
 * - \ref PIN_PIODCEN1
 * - \ref PIN_PIODCEN2
 *
 * TWI
 * - \ref TWI_V3XX
 * - \ref PIN_TWI_TWD0
 * - \ref PIN_TWI_TWCK0
 * - \ref PINS_TWI0
 * - \ref PIN_TWI_TWD1
 * - \ref PIN_TWI_TWCK1
 * - \ref PINS_TWI1
 *
 * USART0
 * - \ref PIN_USART0_RXD
 * - \ref PIN_USART0_TXD
 * - \ref PIN_USART0_CTS
 * - \ref PIN_USART0_RTS
 * - \ref PIN_USART0_SCK
 *
 * USART1
 * - \ref PIN_USART1_RXD
 * - \ref PIN_USART1_TXD
 * - \ref PIN_USART1_CTS
 * - \ref PIN_USART1_RTS
 * - \ref PIN_USART1_SCK
 *
 * USART2
 * - \ref PIN_USART2_RXD
 * - \ref PIN_USART2_TXD
 * - \ref PIN_USART2_CTS
 * - \ref PIN_USART2_RTS
 * - \ref PIN_USART2_SCK
 *
 * SSC
 * - \ref PIN_SSC_TD
 * - \ref PIN_SSC_TK
 * - \ref PIN_SSC_TF
 * - \ref PIN_SSC_RD
 * - \ref PIN_SSC_RK
 * - \ref PIN_SSC_RF
 * - \ref PIN_SSC_TD
 * - \ref PINS_SSC_CODEC
 *
 * MCAN
 * - \ref PIN_MCAN0_TXD
 * - \ref PIN_MCAN0_RXD
 * - \ref PIN_MCAN1_TXD
 * - \ref PIN_MCAN1_RXD
 */
 
/** SSC pin Transmitter Data (TD) */
#define PIN_SSC_TD  {PIO_PD26B_TD, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** SSC pin Transmitter Clock (TK) */
#define PIN_SSC_TK  {PIO_PB1D_TK, PIOB, ID_PIOB, PIO_PERIPH_D, PIO_DEFAULT}
/** SSC pin Transmitter FrameSync (TF) */
#define PIN_SSC_TF  {PIO_PB0D_TF, PIOB, ID_PIOB, PIO_PERIPH_D, PIO_DEFAULT}
/** SSC pin RD */
#define PIN_SSC_RD  {PIO_PA10C_RD, PIOA, ID_PIOA, PIO_PERIPH_C, PIO_DEFAULT}
/** SSC pin RK */
#define PIN_SSC_RK  {PIO_PA22A_RK, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** SSC pin RF */
#define PIN_SSC_RF  {PIO_PD24B_RF, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}

/** SSC pins definition for codec. */
#define PINS_SSC_CODEC \
		{PIN_SSC_TD,  PIN_SSC_TK, PIN_SSC_TF, PIN_SSC_RD,  PIN_SSC_RK, PIN_SSC_RF}

/** UART pins (UTXD0 and URXD0) definitions, PA9,10. */
#define PINS_UART0  \
		{PIO_PA9A_URXD0 | PIO_PA10A_UTXD0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** UART pins (UTXD4 and URXD4) definitions, PD19,18. */
#define PINS_UART4 \
		{PIO_PD18C_URXD4 | PIO_PD19C_UTXD4, PIOD, ID_PIOD, PIO_PERIPH_C, PIO_DEFAULT}

/* LED pins definitions */
#define LED_YELLOW0  0
#define LED_YELLOW1  1

/** LED #0 pin definition (YELLOW). */
#define PIN_LED_0  {PIO_PA23, PIOA, ID_PIOA, PIO_OUTPUT_0, PIO_DEFAULT}
/** LED #0 pin definition (YELLOW). */
#define PIN_LED_1  {PIO_PC9, PIOC, ID_PIOC, PIO_OUTPUT_0, PIO_DEFAULT}

/** List of all LEDs definitions. */
#define PINS_LEDS  {PIN_LED_0, PIN_LED_1}

/** 
 * Push button #0 definition. 
 * Attributes = pull-up + debounce + interrupt on rising edge.
 */
#define PIN_PUSHBUTTON_0 \
		{PIO_PA9, PIOA, ID_PIOA, PIO_INPUT, PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE}
/** 
 * Push button #1 definition. 
 * Attributes = pull-up + debounce + interrupt on rising edge.
 */
#define PIN_PUSHBUTTON_1 \
		{PIO_PB12, PIOB, ID_PIOB, PIO_INPUT, PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE}

/** List of all push button definitions. */
#define PINS_PUSHBUTTONS {PIN_PUSHBUTTON_0, PIN_PUSHBUTTON_1}

/** Push button #0 index. */
#define PUSHBUTTON_BP0  0
/** Push button #1 index. */
#define PUSHBUTTON_BP1  1

/** PWMC PWM0 pin definition: Output High. */
#define PIN_PWMC_PWMH0  {PIO_PD20A_PWMH0, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** PWMC PWM1 pin definition: Output High. */
#define PIN_PWMC_PWMH1  {PIO_PD21A_PWMH1, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** PWM pins definition for LED0 */
#define PIN_PWM_LED0  PIN_PWMC_PWMH0
/** PWM pins definition for LED1 */
#define PIN_PWM_LED1  PIN_PWMC_PWMH1
/** PWM channel for LED0 */
#define CHANNEL_PWM_LED0 0
/** PWM channel for LED1 */
#define CHANNEL_PWM_LED1 1

/** SPI MISO pin definition. */
#define PIN_SPI_MISO {PIO_PD20B_SPI0_MISO, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** SPI MOSI pin definition. */
#define PIN_SPI_MOSI {PIO_PD21B_SPI0_MOSI, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** SPI SPCK pin definition. */
#define PIN_SPI_SPCK {PIO_PD22B_SPI0_SPCK, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** SPI chip select pin definition. */
#define PIN_SPI_NPCS0 {PIO_PB2D_SPI0_NPCS0, PIOB, ID_PIOB, PIO_PERIPH_D, PIO_DEFAULT}
#define PIN_SPI_NPCS1 {PIO_PD25B_SPI0_NPCS1, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
#define PIN_SPI_NPCS3 {PIO_PD27B_SPI0_NPCS3, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}

/** List of SPI pin definitions (MISO, MOSI & SPCK). */
#define PINS_SPI  PIN_SPI_MISO, PIN_SPI_MOSI, PIN_SPI_SPCK

/** PCK0 */
#define PIN_PCK0  {PIO_PB13B_PCK0, PIOB, ID_PIOB, PIO_PERIPH_B, PIO_DEFAULT}
/** PCK1 */
#define PIN_PCK1  {PIO_PA17B_PCK1, PIOB, ID_PIOB, PIO_PERIPH_B, PIO_DEFAULT}
/** PCK2 */
#define PIN_PCK2   {PIO_PA18B_PCK2, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}


/** PIO PARALLEL CAPTURE */
/** Parallel Capture Mode Data Enable1 */
#define PIN_PIODCEN1 PIO_PA15
/** Parallel Capture Mode Data Enable2 */
#define PIN_PIODCEN2 PIO_PA16

/** TWI version 3.xx */
#define TWI_V3XX
/** TWI0 data pin */
#define PIN_TWI_TWD0 {PIO_PA3A_TWD0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** TWI0 clock pin */
#define PIN_TWI_TWCK0 {PIO_PA4A_TWCK0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** TWI0 pins */
#define PINS_TWI0  {PIN_TWI_TWD0, PIN_TWI_TWCK0}

/** TWI1 data pin */
#define PIN_TWI_TWD1 {PIO_PB4A_TWD1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/** TWI1 clock pin */
#define PIN_TWI_TWCK1 {PIO_PB5A_TWCK1, PIOB, ID_PIOB, PIO_PERIPH_A,PIO_DEFAULT}
/** TWI1 pins */
#define PINS_TWI1  {PIN_TWI_TWD1, PIN_TWI_TWCK1}

/** USART0 pin RX */
#define PIN_USART0_RXD {PIO_PB0C_RXD0, PIOB, ID_PIOB, PIO_PERIPH_C, PIO_DEFAULT}
/** USART0 pin TX */
#define PIN_USART0_TXD {PIO_PB1C_TXD0, PIOB, ID_PIOB, PIO_PERIPH_C, PIO_DEFAULT}
/** USART0 pin CTS */
#define PIN_USART0_CTS {PIO_PB2C_CTS0, PIOB, ID_PIOB, PIO_PERIPH_C, PIO_DEFAULT}
/** USART0 pin RTS */
#define PIN_USART0_RTS {PIO_PB3C_RTS0, PIOB, ID_PIOB, PIO_PERIPH_C, PIO_DEFAULT}
/** USART0 pin SCK */
#define PIN_USART0_SCK {PIO_PB13C_SCK0, PIOB, ID_PIOB, PIO_PERIPH_C,PIO_DEFAULT}

/** USART1 pin RX */
#define PIN_USART1_RXD {PIO_PA21A_RXD1, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** USART1 pin TX */
#define PIN_USART1_TXD {1<<22, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** USART1 pin CTS */
#define PIN_USART1_CTS {PIO_PA25A_CTS1, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** USART1 pin RTS */
#define PIN_USART1_RTS {PIO_PA24A_RTS1, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** USART1 pin ENABLE */
#define PIN_USART1_EN {PIO_PA23A_SCK1, PIOA, ID_PIOA, PIO_OUTPUT_0, PIO_DEFAULT}
/** USART1 pin SCK */
#define PIN_USART1_SCK {PIO_PA23A_SCK1, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}

/** USART2 pin RX */
#define PIN_USART2_RXD {PIO_PD15B_RXD2, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** USART2 pin TX */
#define PIN_USART2_TXD {PIO_PD16B_TXD2, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** USART2 pin CTS */
#define PIN_USART2_CTS {PIO_PD19B_CTS2, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** USART2 pin RTS */
#define PIN_USART2_RTS {PIO_PD18B_RTS2, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** USART2 pin SCK */
#define PIN_USART2_SCK {PIO_PD17B_SCK2, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}

/*Pins for USART0 as 7816 mode*/
/** PIN used for reset the smartcard */
#define PIN_ISO7816_RSTMC  {PIO_PB2C_CTS0, PIOB, ID_PIOB, PIO_OUTPUT_0, PIO_DEFAULT}
/** Pins used for connect the smartcard */
#define PINS_ISO7816        PIN_USART0_TXD, PIN_USART0_SCK,PIN_ISO7816_RSTMC

/** MCAN0 pin Transmit Data (TXD) */
#define PIN_MCAN0_TXD {PIO_PB2A_CANTX0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** MCAN0 pin Receive Data (RXD) */
#define PIN_MCAN0_RXD {PIO_PB3A_CANRX0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}

/** MCAN1 pin Transmit Data (TXD) */
#define PIN_MCAN1_TXD {PIO_PC14C_CANTX1, PIOC, ID_PIOC, PIO_PERIPH_C, PIO_DEFAULT}
/** MCAN1 pin Receive Data (RXD) */
#define PIN_MCAN1_RXD {PIO_PC12C_CANRX1, PIOC, ID_PIOC, PIO_PERIPH_C, PIO_DEFAULT}

/*----------------------------------------------------------------------------*/
/**
 * \page samv7_Xplained_ultra_gmac "SAM V71 Xplained Ultra - GMAC"
 * \section GMAC
 * - \ref BOARD_GMAC_PHY_ADDR
 * - \ref BOARD_GMAC_PHY_COMP_KSZ8061RNB
 * - \ref BOARD_GMAC_MODE_RMII
 * - \ref BOARD_GMAC_PINS
 * - \ref BOARD_GMAC_RESET_PIN
 *
 */
/** PHY address */
#define BOARD_GMAC_PHY_ADDR             1
/** PHY Component */
#define BOARD_GMAC_PHY_COMP_KSZ8061RNB  1
/** Board GMAC power control - ALWAYS ON */
#define BOARD_GMAC_POWER_ALWAYS_ON
/** Board GMAC work mode - RMII/MII ( 1 / 0 ) */
#define BOARD_GMAC_MODE_RMII            1

/** The PIN list of PIO for GMAC */
#define BOARD_GMAC_PINS \
		{ (PIO_PD0A_GTXCK | PIO_PD1A_GTXEN | PIO_PD2A_GTX0 | PIO_PD3A_GTX1 \
		| PIO_PD4A_GRXDV | PIO_PD5A_GRX0 | PIO_PD6A_GRX1 | PIO_PD7A_GRXER \
		| PIO_PD8A_GMDC | PIO_PD9A_GMDIO ),PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}, \
		{PIO_PC30, PIOC, ID_PIOC, PIO_INPUT,    PIO_PULLUP},\
		{PIO_PA29, PIOA, ID_PIOA, PIO_INPUT,    PIO_DEFAULT}

/** The PIN list of PIO for GMAC */
#define BOARD_GMAC_RESET_PIN {PIO_PC10, PIOC, ID_PIOC, PIO_OUTPUT_1, PIO_PULLUP}

/** The runtime pin configure list for GMAC */
#define BOARD_GMAC_RUN_PINS  BOARD_GMAC_PINS


/*----------------------------------------------------------------------------*/
/**
 * \page samv7_Xplained_ultra_isi "SAM V71 Xplained Ultra - ISI"
 * This page lists all the IO definitions connected to ISI module.
 * ISI
 * - \ref PIN_ISI_D0
 * - \ref PIN_ISI_D1
 * - \ref PIN_ISI_D2
 * - \ref PIN_ISI_D3
 * - \ref PIN_ISI_D4
 * - \ref PIN_ISI_D5
 * - \ref PIN_ISI_D6
 * - \ref PIN_ISI_D7
 * - \ref PIN_ISI_D8
 * - \ref PIN_ISI_D9
 * - \ref BOARD_ISI_VSYNC
 * - \ref BOARD_ISI_HSYNC
 * - \ref BOARD_ISI_PCK
 * - \ref BOARD_ISI_PINS
 *
 */
#define PIN_ISI_D0  {PIO_PD22D_ISI_D0,  PIOD, ID_PIOD, PIO_PERIPH_D, PIO_PULLUP}
#define PIN_ISI_D1  {PIO_PD21D_ISI_D1,  PIOD, ID_PIOD, PIO_PERIPH_D, PIO_PULLUP}
#define PIN_ISI_D2  {PIO_PB3D_ISI_D2,   PIOB, ID_PIOB, PIO_PERIPH_D, PIO_PULLUP}
#define PIN_ISI_D3  {PIO_PA9B_ISI_D3,   PIOA, ID_PIOA, PIO_PERIPH_B, PIO_PULLUP}
#define PIN_ISI_D4  {PIO_PA5B_ISI_D4,   PIOA, ID_PIOA, PIO_PERIPH_B, PIO_PULLUP}
#define PIN_ISI_D5  {PIO_PD11D_ISI_D5,  PIOD, ID_PIOD, PIO_PERIPH_D, PIO_PULLUP}
#define PIN_ISI_D6  {PIO_PD12D_ISI_D6,  PIOD, ID_PIOD, PIO_PERIPH_D, PIO_PULLUP}
#define PIN_ISI_D7  {PIO_PA27D_ISI_D7,  PIOA, ID_PIOA, PIO_PERIPH_D, PIO_PULLUP}
#define PIN_ISI_D8  {PIO_PD27D_ISI_D8,  PIOD, ID_PIOD, PIO_PERIPH_D, PIO_PULLUP}
#define PIN_ISI_D9  {PIO_PD28D_ISI_D9,  PIOD, ID_PIOD, PIO_PERIPH_D, PIO_PULLUP}

#define BOARD_ISI_VSYNC {PIO_PD25D_ISI_VSYNC, PIOD, ID_PIOD, PIO_PERIPH_D, PIO_DEFAULT}
#define BOARD_ISI_HSYNC {PIO_PD24D_ISI_HSYNC, PIOD, ID_PIOD, PIO_PERIPH_D, PIO_DEFAULT}
#define BOARD_ISI_PCK   {PIO_PA24D_ISI_PCK, PIOA, ID_PIOA, PIO_PERIPH_D, PIO_DEFAULT}

#define BOARD_ISI_PCK0  { PIO_PA6B_PCK0,  PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT }
#define BOARD_ISI_RST   { 1 << 13, PIOB, ID_PIOB, PIO_OUTPUT_1, PIO_DEFAULT }
#define BOARD_ISI_PWD   { 1 << 19,  PIOC, ID_PIOC, PIO_OUTPUT_1, PIO_DEFAULT }

#define BOARD_ISI_PINS \
		PIN_ISI_D0, PIN_ISI_D1, PIN_ISI_D2,PIN_ISI_D3,PIN_ISI_D4, PIN_ISI_D5,\
		PIN_ISI_D6,PIN_ISI_D7,PIN_ISI_D8, PIN_ISI_D9,BOARD_ISI_VSYNC ,\
		BOARD_ISI_HSYNC ,BOARD_ISI_PCK, BOARD_ISI_RST, BOARD_ISI_PWD,BOARD_ISI_PCK0
 
/*----------------------------------------------------------------------------*/
/**
 * \page samv7_Xplained_ultra_usb "SAM V71 Xplained Ultra - USB device"
 *
 * \section Definitions
 * - \ref BOARD_USB_BMATTRIBUTES
 *
 * \section vBus
 * - \ref PIN_USB_VBUS
 *
 */

/** 
 * USB attributes configuration descriptor (bus or self powered, 
 * remote wakeup)
 */
#define BOARD_USB_BMATTRIBUTES USBConfigurationDescriptor_SELFPOWERED_NORWAKEUP

/** USB VBus monitoring pin definition. */
#define PIN_USB_VBUS {PIO_PC16, PIOC, ID_PIOC, PIO_INPUT, PIO_DEFAULT}


/*----------------------------------------------------------------------------*/
/**
 * \page samv7_Xplained_ultra_extcomp "SAM V71 Xplained Ultra - External components"
 * This page lists the definitions related to external on-board components
 * located in the board.h file for the SAM V71 Xplained Ultra board.
 *
 * LCD
 */
/** Indicates board has an ILI9325 external component to manage LCD. */
#define BOARD_LCD_ILI9488
//#define BOARD_LCD_SPI_EXT1
#define BOARD_LCD_SPI_EXT2

/** SPI pin definition for LCD */
#if defined (BOARD_LCD_SPI_EXT1)
/** SPI MISO pin definition. */
#define LCD_SPI_MISO {PIO_PD20B_SPI0_MISO, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** SPI MOSI pin definition. */
#define LCD_SPI_MOSI {PIO_PD21B_SPI0_MOSI, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** SPI SPCK pin definition. */
#define LCD_SPI_SPCK {PIO_PD22B_SPI0_SPCK, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** SPI chip select pin definition. */
#define LCD_SPI_NPCS {PIO_PD27B_SPI0_NPCS3, PIOD, ID_PIOD, PIO_PERIPH_B,PIO_DEFAULT}

/** SPI chip select pin definition. */
#define LCD_SPI_NPCS    {PIO_PD25B_SPI0_NPCS1, PIOD, ID_PIOD, PIO_PERIPH_B,PIO_DEFAULT}

/** LCD pins definition. */
#define BOARD_SPI_LCD_PINS  {LCD_SPI_MISO, LCD_SPI_MOSI, LCD_SPI_SPCK, LCD_SPI_NPCS}

/** Back-light pin definition. */

#define BOARD_SPI_LCD_BACKLIGHT_PIN  \
		{PIO_PA0A_PWMC0_PWMH0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}

/** PWMC PWM0 pin definition: Output Low. */
#define LCD_SPI_PIN_RESET   {PIO_PD28, PIOD, ID_PIOD, PIO_OUTPUT_1, PIO_DEFAULT}

/** PWM channel for LED0 */
#define CHANNEL_PWM_LCD 0

#endif 
/*ENDIF BOARD_LCD_SPI_EXT1 */

#if defined (BOARD_LCD_SPI_EXT2)
 /** SPI MISO pin definition. */
#define LCD_SPI_MISO {PIO_PD20B_SPI0_MISO, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** SPI MOSI pin definition. */
#define LCD_SPI_MOSI {PIO_PD21B_SPI0_MOSI, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** SPI SPCK pin definition. */
#define LCD_SPI_SPCK {PIO_PD22B_SPI0_SPCK, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** SPI chip select pin definition. */
#define LCD_SPI_NPCS {PIO_PD27B_SPI0_NPCS3, PIOD, ID_PIOD, PIO_PERIPH_B,PIO_DEFAULT}

/** LCD pins definition. */
#define BOARD_SPI_LCD_PINS  {LCD_SPI_MISO, LCD_SPI_MOSI, LCD_SPI_SPCK, LCD_SPI_NPCS}

/** Back-light pin definition. */

#define BOARD_SPI_LCD_PIN_BACKLIGHT  \
		{PIO_PC19B_PWMC0_PWMH2, PIOC, ID_PIOC, PIO_OUTPUT_1, PIO_DEFAULT}

/** PWMC PWM0 pin definition: Output Low. */
#define LCD_SPI_PIN_RESET   {PIO_PA24, PIOA, ID_PIOA, PIO_OUTPUT_1, PIO_DEFAULT}

/** LCD command/data select pin */
#define BOARD_SPI_LCD_PIN_CDS   {PIO_PA6, PIOA, ID_PIOA, PIO_OUTPUT_1, PIO_DEFAULT}

/** PWM channel for LED0 */
#define CHANNEL_PWM_LCD 2

#endif 
/*ENDIF BOARD_LCD_SPI_EXT2 */

/** SMC pin definition for LCD */
/** LCD data pin */
#define PIN_EBI_LCD_DATAL           {0xFF, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_PULLUP}
#define PIN_EBI_LCD_DATAH_0         {0x3F, PIOE, ID_PIOE, PIO_PERIPH_A, PIO_PULLUP}
#define PIN_EBI_LCD_DATAH_1         {PIO_PA15A_D14|PIO_PA16A_D15, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_PULLUP}
/** LCD WE pin */
#define PIN_EBI_LCD_NWE             {PIO_PC8A_NWE,  PIOC, ID_PIOC, PIO_PERIPH_A, PIO_PULLUP}
/** LCD RD pin */
#define PIN_EBI_LCD_NRD             {PIO_PC11A_NRD, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_PULLUP}
/* LCD CS pin (NCS3) */
#define PIN_EBI_LCD_CS              {PIO_PD19A_NCS3, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_PULLUP}
/** LCD command/data select pin */
#define BOARD_EBI_LCD_PIN_CDS       {PIO_PC30, PIOC, ID_PIOC, PIO_OUTPUT_1, PIO_DEFAULT}
/** Back-light pin definition. */
#define BOARD_EBI_LCD_PIN_BACKLIGHT {PIO_PC9B_TIOB7, PIOC, ID_PIOC, PIO_PERIPH_B, PIO_DEFAULT}
/** LCD reset pin */
#define LCD_EBI_PIN_RESET           {PIO_PC13, PIOC, ID_PIOC, PIO_OUTPUT_1, PIO_DEFAULT}

/** LCD pins definition. */
#define BOARD_EBI_LCD_PINS          \
		{PIN_EBI_LCD_DATAL, PIN_EBI_LCD_DATAH_0, PIN_EBI_LCD_DATAH_1, \
		PIN_EBI_LCD_NWE,PIN_EBI_LCD_NRD,PIN_EBI_LCD_CS}


/** Display width in pixels. */
#define BOARD_LCD_WIDTH             320
/** Display height in pixels. */
#define BOARD_LCD_HEIGHT            480


/*----------------------------------------------------------------------------*/
/**
 * \page samv7_Xplained_ultra_mem "SAM V71 Xplained Ultra - Memories"
 * This page lists definitions related to internal & external on-board memories.
 * \section SDRAM
 * - \ref PIN_SDRAM_D0_7 
 * - \ref PIN_SDRAM_D8_13 
 * - \ref PIN_SDRAM_D14_15 
 * - \ref PIN_SDRAM_A0_9 
 * - \ref PIN_SDRAM_SDA10 
 * - \ref PIN_SDRAM_CAS 
 * - \ref PIN_SDRAM_RAS 
 * - \ref PIN_SDRAM_SDCKE 
 * - \ref PIN_SDRAM_SDCK  
 * - \ref PIN_SDRAM_SDSC 
 * - \ref PIN_SDRAM_NBS0 
 * - \ref PIN_SDRAM_NBS1 
 * - \ref PIN_SDRAM_SDWE 
 * - \ref PIN_SDRAM_BA0 
 *
 * \section SDMMC
 * - \ref BOARD_MCI_PIN_CD
 * - \ref BOARD_MCI_PIN_CK
 * - \ref BOARD_MCI_PINS_SLOTA
 * - \ref BOARD_SD_PINS
 *
 * \section QSPI
 * - \ref PINS_QSPI_IO
 * - \ref PINS_QSPI_IO3
 * - \ref PINS_QSPI
 */
 
/** List of all SDRAM pin definitions. */
#define BOARD_SDRAM_SIZE  (2*1024*1024)
#define PIN_SDRAM_D0_7    {0x000000FF, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT} 
#define PIN_SDRAM_D8_13   {0x0000003F, PIOE, ID_PIOE, PIO_PERIPH_A, PIO_DEFAULT} 
#define PIN_SDRAM_D14_15  {0x00018000, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT} 
#define PIN_SDRAM_A0_9    {0x3FF00000, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT} 
#define PIN_SDRAM_SDA10   {0x00002000, PIOD, ID_PIOD, PIO_PERIPH_C, PIO_DEFAULT} 

#define PIN_SDRAM_CAS     {0x00020000, PIOD, ID_PIOD, PIO_PERIPH_C, PIO_DEFAULT} 
#define PIN_SDRAM_RAS     {0x00010000, PIOD, ID_PIOD, PIO_PERIPH_C, PIO_DEFAULT} 
#define PIN_SDRAM_SDCKE   {0x00004000, PIOD, ID_PIOD, PIO_PERIPH_C, PIO_DEFAULT} 
#define PIN_SDRAM_SDCK    {0x00800000, PIOD, ID_PIOD, PIO_PERIPH_C, PIO_DEFAULT} 
#define PIN_SDRAM_SDSC    {0x00008000, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT} 
#define PIN_SDRAM_NBS0    {0x00040000, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT} 
#define PIN_SDRAM_NBS1    {0x00008000, PIOD, ID_PIOD, PIO_PERIPH_C, PIO_DEFAULT} 
#define PIN_SDRAM_SDWE    {0x20000000, PIOD, ID_PIOD, PIO_PERIPH_C, PIO_DEFAULT} 
#define PIN_SDRAM_BA0     {0x00100000, PIOA, ID_PIOA, PIO_PERIPH_C, PIO_DEFAULT} 

#define BOARD_SDRAM_PINS PIN_SDRAM_D0_7, PIN_SDRAM_D8_13 , PIN_SDRAM_D14_15,\
		PIN_SDRAM_A0_9, PIN_SDRAM_SDA10, PIN_SDRAM_BA0, \
		PIN_SDRAM_CAS, PIN_SDRAM_RAS, PIN_SDRAM_SDCKE,PIN_SDRAM_SDCK,\
		PIN_SDRAM_SDSC,PIN_SDRAM_NBS0 ,PIN_SDRAM_NBS1,PIN_SDRAM_SDWE


/** List of all MCI pin definitions. */

/** MCI0 Card detect pin definition. (PE5) */
#define BOARD_MCI_PIN_CD  {PIO_PD18, PIOD, ID_PIOD, PIO_INPUT, PIO_PULLUP}
/** MCI0 Clock . */
#define BOARD_MCI_PIN_CK  {PIO_PA25D_MCCK, PIOA, ID_PIOA, PIO_PERIPH_D, PIO_DEFAULT}

/** MCI0 Solt A IO pins definition. (PC4-PC13) */
#define BOARD_MCI_PINS_SLOTA \
		{(PIO_PA30C_MCDA0 | PIO_PA31C_MCDA1 | PIO_PA26C_MCDA2 | PIO_PA27C_MCDA3 | PIO_PA28C_MCCDA),\
		PIOA, ID_PIOA, PIO_PERIPH_C, PIO_DEFAULT}

/** MCI pins that shall be configured to access the SD card. */
#define BOARD_SD_PINS     {BOARD_MCI_PINS_SLOTA, BOARD_MCI_PIN_CK}
/** MCI Card Detect pin. */
#define BOARD_SD_PIN_CD   BOARD_MCI_PIN_CD
 /** Total number of MCI interface */
#define BOARD_NUM_MCI     1

/** List of all SQPI pin definitions. */
#define PINS_QSPI_IO   \
		{(PIO_PA11A_QCS | PIO_PA13A_QIO0 | PIO_PA12A_QIO1 | PIO_PA17A_QIO2 | PIO_PA14A_QSCK),\
		PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
#define PINS_QSPI_IO3   {PIO_PD31A_QIO3, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
#define PINS_QSPI      {PINS_QSPI_IO, PINS_QSPI_IO3}

/*----------------------------------------------------------------------------*/
/**
 * \page samv7_Xplained_ultra_chipdef "SAM V71 Xplained Ultra - Individual chip definition"
 * This page lists the definitions related to different chip's definition
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

/** Rtc */
#define BOARD_RTC_ID   ID_RTC

/** TWI ID for QTouch application to use */
#define BOARD_ID_TWI_AT42    ID_TWI0
/** TWI Base for QTouch application to use */
#define BOARD_BASE_TWI_AT42  TWI0
/** TWI pins for QTouch application to use */
#define BOARD_PINS_TWI_AT42  PINS_TWI0

/** USART RX pin for application */
#define BOARD_PIN_USART_RXD  PIN_USART1_RXD
/** USART TX pin for application */
#define BOARD_PIN_USART_TXD  PIN_USART1_TXD
/** USART CTS pin for application */
#define BOARD_PIN_USART_CTS  PIN_USART1_CTS
/** USART RTS pin for application */
#define BOARD_PIN_USART_RTS  PIN_USART1_RTS
/** USART ENABLE pin for application */
#define BOARD_PIN_USART_EN  PIN_USART1_EN
/** USART Base for application */
#define BOARD_USART_BASE  USART1
/** USART ID for application */
#define BOARD_ID_USART   ID_USART1



/*----------------------------------------------------------------------------*/
 /*
 * USB pins
 */
#define PINS_VBUS_EN   {PIO_PC16, PIOC, ID_PIOC, PIO_OUTPUT_1, PIO_DEFAULT}
#endif /* #ifndef _BOARD_H_ */

