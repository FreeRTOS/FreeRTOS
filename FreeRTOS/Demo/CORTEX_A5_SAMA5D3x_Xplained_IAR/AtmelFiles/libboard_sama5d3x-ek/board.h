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
 * \page sama5d3x_ek_board_desc sama5d3-xplained - Board Description
 *
 * \section Purpose
 *
 * This file is dedicated to describe the sama5d3-xplained board.
 *
 * \section Contents
 *
 *  - sama5d3-xplained 
 *  - For sama5d3-xplained information, see \subpage sama5d3x_ek_board_info.
 *  - For operating frequency information, see \subpage sama5d3x_ek_opfreq.
 *  - For using portable PIO definitions, see \subpage sama5d3x_ek_piodef.
 *  - For on-board memories, see \subpage sama5d3x_ek_mem.
 *  - Several USB definitions are included here, see \subpage sama5d3x_ek_usb.
 *  - For External components, see \subpage sama5d3x_ek_extcomp.
 *  - For Individual chip definition, see \subpage sama5d3x_ek_chipdef.
 *
 * To get more software details and the full list of parameters related to the
 * sama5d3-xplained board configuration, please have a look at the source file:
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
 *  Definition of sama5d3-xplained 
 *  characteristics, sama5d3x-dependant PIOs and external components interfacing.
 */

#ifndef _BOARD_
#define _BOARD_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

/**
 * Libc porting layers
 */
#if defined   ( __CC_ARM   ) /* Keil uvision 4 */
#    include "include/rand.h"
#elif defined ( __ICCARM__ ) /* IAR Ewarm 5.41+ */
#    include "include/rand.h"
#elif defined (  __GNUC__  ) /* GCC CS3 2009q3-68/2010q1-188 */
#    include "include/rand.h"
#    include "include/syscalls.h" /** RedHat Newlib minimal stub */
#endif

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------*/
/**
 * \page sama5d3x_ek_board_info "sama5d3-xplained - Board informations"
 * This page lists several definition related to the board description.
 *
 * \section Definitions
 * - \ref BOARD_NAME
 */

/** Name of the board */
#define BOARD_NAME "sama5d3-xplained"
/** Board definition */
#define sama5d3xek
/** Family definition (already defined) */
#if !defined sama5d3x
#define sama5d3x
#endif
/** Core definition */
#define cortexa5

#define BOARD_XPLAINED
//#define BOARD_EK
//#define BOARD_VB

// #define BOARD_REV_A_EK
// #define BOARD_REV_B_EK
// #define BOARD_REV_C_EK
// #define BOARD_REV_D_EK

// Low cost board
// #define BOARD_LCB

/*----------------------------------------------------------------------------*/
/**
 *  \page sama5d3x_ek_opfreq "sama5d3-xplained - Operating frequencies"
 *  This page lists several definition related to the board operating frequency
 *  (when using the initialization done by board_lowlevel.c).
 *
 *  \section Definitions
 *  - \ref BOARD_MAINOSC
 *  - \ref BOARD_MCK
 */

/** Frequency of the board main oscillator */
#define BOARD_MAINOSC           12000000

/** Master clock frequency (when using board_lowlevel.c) */
#define BOARD_MCK                ((unsigned long)((BOARD_MAINOSC / 3 / 2) * 66 ))

/*----------------------------------------------------------------------------*/
/**
 * \page sama5d3x_ek_piodef "sama5d3-xplained - PIO definitions"
 * This pages lists all the pio definitions contained in board.h. The constants
 * are named using the following convention: PIN_* for a constant which defines
 * a single Pin instance (but may include several PIOs sharing the same
 * controller), and PINS_* for a list of Pin instances.
 *
 * DBGU
 * - \ref PINS_DBGU
 *
 * USART0
 * - \ref PIN_USART0_TXD
 * - \ref PIN_USART0_RXD
 * - \ref PIN_USART0_RTS
 * - \ref PIN_USART0_CTS
 * - \ref PIN_USART0_SCK
 * 
 * TWI0
 * - \ref PIN_TWI_TWD0
 * - \ref PIN_TWI_TWCK0
 * - \ref PINS_TWI0
 *
 * SPI0
 * - \ref PIN_SPI0_MISO
 * - \ref PIN_SPI0_MOSI
 * - \ref PIN_SPI0_SPCK
 * - \ref PIN_SPI0_NPCS0
 * - \ref PINS_SPI0
 *
 * SSC
 * - \ref PIN_SSC_TD
 * - \ref PIN_SSC_TK
 * - \ref PIN_SSC_TF
 * - \ref PIN_SSC_RD
 * - \ref PIN_SSC_RK
 * - \ref PIN_SSC_RF
 * - \ref PINS_SSC_CODEC
 *
 * EMAC0
 * - \ref PIN_EMAC0_TXCK
 * - \ref PIN_EMAC0_TX0
 * - \ref PIN_EMAC0_TX1
 * - \ref PIN_EMAC0_TX2
 * - \ref PIN_EMAC0_TX3
 * - \ref PIN_EMAC0_TXEN
 * - \ref PIN_EMAC0_RXER
 * - \ref PIN_EMAC0_RXDV
 * - \ref PIN_EMAC0_RX0
 * - \ref PIN_EMAC0_RX1
 * - \ref PIN_EMAC0_RX2
 * - \ref PIN_EMAC0_RX3
 * - \ref PIN_EMAC0_MDC
 * - \ref PIN_EMAC0_MDIO
 * - \ref PIN_EMAC0_INTR
 * - \ref PINS_EMAC0_MII
 * - \ref PINS_EMAC0_RMII
 * LCD
 * - \ref PINS_LCD
 *
 * ADC
 * - \ref PIN_ADTRG
 *
 * ISI
 * - \ref PIN_ISI_MCK
 * - \ref PIN_ISI_VSYNC
 * - \ref PIN_ISI_HSYNC
 * - \ref PIN_ISI_PCK
 * - \ref PIN_ISI_PINS_DATA
 * - \ref PINS_ISI 
 */

/** List of all DBGU pin definitions. */

/** DBGU Monitor IO pin (detect any DBGU operation). */
#define PIN_DBGU_MON {PIO_PB30A_DRXD, PIOB, ID_PIOB, PIO_INPUT, PIO_IT_RISE_EDGE}
/** DBGU pin definition. */
#define PINS_DBGU   {PIO_PB30A_DRXD | PIO_PB31A_DTXD, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}

/** List of all USART pin definitions. */

/** USART0 TXD pin definition. */
#define PIN_USART0_TXD  {PIO_PD18A_TXD0, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** USART0 RXD pin definition. */
#define PIN_USART0_RXD  {PIO_PD17A_RXD0, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** USART0 RTS pin definition. */
#define PIN_USART0_RTS  {PIO_PD16A_RTS0, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** USART0 CTS pin definition. */
#define PIN_USART0_CTS  {PIO_PD15A_CTS0, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** USART0 SCK pin definition. */
#define PIN_USART0_SCK  {PIO_PD14A_SCK0, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}

/** USART1 TXD pin definition. */
#define PIN_USART1_TXD  {PIO_PB29A_TXD1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/** USART1 RXD pin definition. */
#define PIN_USART1_RXD  {PIO_PB28A_RXD1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/** USART1 RTS pin definition. */
#define PIN_USART1_RTS  {PIO_PB27A_RTS1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/** USART1 CTS pin definition. */
#define PIN_USART1_CTS  {PIO_PB26A_CTS1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}
/** USART1 SCK pin definition. */
#define PIN_USART1_SCK  {PIO_PB25A_SCK1, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}

/** USART2 TXD pin definition. */
#define PIN_USART2_TXD  {PIO_PE26B_TXD2, PIOE, ID_PIOE, PIO_PERIPH_B, PIO_DEFAULT}
/** USART2 RXD pin definition. */
#define PIN_USART2_RXD  {PIO_PE25B_RXD2, PIOE, ID_PIOE, PIO_PERIPH_B, PIO_DEFAULT}
/** USART2 RTS pin definition. */
#define PIN_USART2_RTS  {PIO_PE24B_RTS2, PIOE, ID_PIOE, PIO_PERIPH_B, PIO_DEFAULT}
/** USART2 CTS pin definition. */
#define PIN_USART2_CTS  {PIO_PE23B_CTS2, PIOE, ID_PIOE, PIO_PERIPH_B, PIO_DEFAULT}
/** USART2 SCK pin definition. */
#define PIN_USART2_SCK  {PIO_PE20B_SCK2, PIOE, ID_PIOE, PIO_PERIPH_B, PIO_DEFAULT}

/** PIN used for reset the smartcard */
#define PIN_ISO7816_RSTMC       {1 << 2, PIOA, ID_PIOA, PIO_OUTPUT_0, PIO_DEFAULT}
/** Pins used for connect the smartcard */
#define PINS_ISO7816            PIN_USART1_TXD, PIN_USART1_SCK, PIN_ISO7816_RSTMC

/** List of all TWI pin definitions. */

/** TWI0 data pin */
#define PIN_TWI_TWD0   {PIO_PA30A_TWD0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** TWI0 clock pin */
#define PIN_TWI_TWCK0  {PIO_PA31A_TWCK0, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** TWI0 pins */
#define PINS_TWI0      PIN_TWI_TWD0, PIN_TWI_TWCK0

/** TWI1 data pin */
#define PIN_TWI_TWD1   {PIO_PC26B_TWD1, PIOC, ID_PIOC, PIO_PERIPH_B, PIO_DEFAULT}
/** TWI1 clock pin */
#define PIN_TWI_TWCK1  {PIO_PC27B_TWCK1, PIOC, ID_PIOC, PIO_PERIPH_B, PIO_DEFAULT}
/** TWI1 pins */
#define PINS_TWI1      PIN_TWI_TWD1, PIN_TWI_TWCK1


/** List of all CAN pin deinitions. */
/** CAN0 pin TX */
#define PIN_CAN0_TX     {PIO_PD15C_CANTX0, PIOD, ID_PIOD, PIO_PERIPH_C, PIO_DEFAULT}
/** CAN0 pin RX */
#define PIN_CAN0_RX     {PIO_PD14C_CANRX0, PIOD, ID_PIOD, PIO_PERIPH_C, PIO_DEFAULT}
/** CAN0 pins */
#define PINS_CAN0       PIN_CAN0_TX, PIN_CAN0_RX
/** CAN1 pin TX */
#define PIN_CAN1_TX     {PIO_PB15B_CANTX1, PIOB, ID_PIOB, PIO_PERIPH_B, PIO_DEFAULT}
/** CAN1 pin RX */
#define PIN_CAN1_RX     {PIO_PB14B_CANRX1, PIOB, ID_PIOB, PIO_PERIPH_B, PIO_DEFAULT}
/** CAN0 pins */
#define PINS_CAN1       PIN_CAN1_TX, PIN_CAN1_RX


/** List of all SPI pin definitions. */

/** SPI0 MISO pin definition. */
#define PIN_SPI0_MISO     {PIO_PD10A_SPI0_MISO, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** SPI0 MOSI pin definition. */
#define PIN_SPI0_MOSI     {PIO_PD11A_SPI0_MOSI, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** SPI0 SPCK pin definition. */
#define PIN_SPI0_SPCK     {PIO_PD12A_SPI0_SPCK, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** SPI0 chip select pin definition. */
#define PIN_SPI0_NPCS0    {PIO_PD13A_SPI0_NPCS0, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** List of SPI0 pin definitions (MISO, MOSI & SPCK). */
#define PINS_SPI0         PIN_SPI0_MISO, PIN_SPI0_MOSI, PIN_SPI0_SPCK

/** SPI1 MISO pin definition. */
#define PIN_SPI1_MISO     {PIO_PC22A_SPI1_MISO, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT}
/** SPI1 MOSI pin definition. */
#define PIN_SPI1_MOSI     {PIO_PC23A_SPI1_MOSI, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT}
/** SPI1 SPCK pin definition. */
#define PIN_SPI1_SPCK     {PIO_PC24A_SPI1_SPCK, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT}
/** SPI1 chip select pin definition. */
#define PIN_SPI1_NPCS0    {PIO_PC25A_SPI1_NPCS0, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT}
/** List of SPI1 pin definitions (MISO, MOSI & SPCK). */
#define PINS_SPI1         PIN_SPI1_MISO, PIN_SPI1_MOSI, PIN_SPI1_SPCK


/** List of all SSC pin definitions. */

/** SSC pin Transmitter Data (TD) */
#define PIN_SSC_TD      {0x1 << 18, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT}
/** SSC pin Transmitter Clock (TK) */
#define PIN_SSC_TK      {0x1 << 16, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT}
/** SSC pin Transmitter FrameSync (TF) */
#define PIN_SSC_TF      {0x1 << 17, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT}
/** SSC pin RD */
#define PIN_SSC_RD      {0x1 << 21, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT}
/** SSC pin RK */
#define PIN_SSC_RK      {0x1 << 19, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT}
/** SSC pin RF */
#define PIN_SSC_RF      {0x1 << 20, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT}
/** SSC pins definition for codec. */

#define PINS_SSC_CODEC  PIN_SSC_TD, PIN_SSC_TK, PIN_SSC_TF, PIN_SSC_RD, PIN_SSC_RK, PIN_SSC_RF
#define PINS_SSC_HDMI   PIN_SSC_TD,  PIN_SSC_TK, PIN_SSC_TF

/** LCD pin list. */
#define PINS_LCD_PIOA   {0x3F00FFFF, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
#define PINS_LCD_PIOC   {0x0000FC00, PIOC, ID_PIOC, PIO_PERIPH_C, PIO_DEFAULT}
#define PINS_LCD_PIOE   {0x18000000, PIOE, ID_PIOE, PIO_PERIPH_C, PIO_DEFAULT}

#define PINS_LCD        PINS_LCD_PIOA, PINS_LCD_PIOC ,PINS_LCD_PIOE
//#define PINS_LCD        PINS_LCD_PIOA
/** ADC ADTRG pin (PD19). */
#define PIN_ADTRG       {PIO_PD19A_ADTRG, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_PULLUP}

/*----------------------------------------------------------------------------*/
/**
 * \page sama5d3x_ek_usb "sama5d3-xplained - USB device"
 *
 * \section Definitions
 * - \ref BOARD_USB_BMATTRIBUTES
 * - \ref CHIP_USB_UDP
 * - \ref CHIP_USB_PULLUP_INTERNAL
 * - \ref CHIP_USB_NUMENDPOINTS
 * - \ref CHIP_USB_ENDPOINTS_MAXPACKETSIZE
 * - \ref CHIP_USB_ENDPOINTS_BANKS
 */

/** USB VBus pin */
#define PIN_USB_VBUS      {PIO_PE9, PIOE, ID_PIOE, PIO_INPUT, PIO_PULLUP}
/** USB OverCurrent detection*/
#define PIN_USB_OVCUR     {PIO_PE5, PIOE, ID_PIOE, PIO_INPUT, PIO_PULLUP}

/** USB attributes configuration descriptor (bus or self powered, remote wakeup) */
#define BOARD_USB_BMATTRIBUTES   USBConfigurationDescriptor_SELFPOWERED_NORWAKEUP

/*----------------------------------------------------------------------------*/
/**
 * \page sama5d3x_ek_mem "sama5d3-xplained - Memories"
 * This page lists definitions related to internal & external on-board memories.
 *
 * \section Sdram
 *
 * - \ref EBI_SDRAM_PINS
 *
 * \section Nandflash
 * - \ref PINS_NANDFLASH
 * - \ref BOARD_NF_IO_PINS
 * - \ref BOARD_NF_CE_PIN
 * - \ref BOARD_NF_RB_PIN
 */

/** Nandflash IO pin definition.*/
#define BOARD_NF_IO_PINS        {0, 0, 0, 0, 0}
#define BOARD_NF_CE_PIN         {0, 0, 0, 0, 0}
/** Nandflash controller peripheral pins definition. */
#define PINS_NANDFLASH          BOARD_NF_IO_PINS

/** Address for transferring command bytes to the nandflash, CLE A22*/
#define BOARD_NF_COMMAND_ADDR   0x60400000
/** Address for transferring address bytes to the nandflash, ALE A21*/
#define BOARD_NF_ADDRESS_ADDR   0x60200000 
/** Address for transferring data bytes to the nandflash.*/ 
#define BOARD_NF_DATA_ADDR      0x60000000

/** Address for transferring command bytes to the norflash. */
#define BOARD_NORFLASH_ADDR     0x10000000
/** Default NOR bus size after power up reset */
#define BOARD_NORFLASH_DFT_BUS_SIZE 16

/** Ddram type */
#define DDRAM_MT47H64M16HR    0
#define DDRAM_MT47H128M16RT   1
#define BOARD_DDRAM_TYPE      DDRAM_MT47H128M16RT

/** PHY address */
#define BOARD_EMAC_PHY_ADDR         1
/** PHY Component */
#define BOARD_EMAC_PHY_COMP_KSZ8051RNL 1
/** Board EMAC power control - ALWAYS ON */
#define BOARD_EMAC_POWER_ALWAYS_ON
/** Board EMAC work mode - RMII/MII ( 1 / 0 ) */
#define BOARD_EMAC_MODE_RMII        1

/** The PIN list of PIO for EMAC */
#define BOARD_EMAC_PINS          {0x3FF, PIOC, ID_PIOC, PIO_PERIPH_A, PIO_DEFAULT},\
                                 {(1<<12),PIOB, ID_PIOB, PIO_INPUT, PIO_PULLUP}

/** The runtime pin configure list for EMAC */
#define BOARD_EMAC_RUN_PINS BOARD_EMAC_PINS

/** PHY address */
#define BOARD_GMAC_PHY_ADDR         7
#define BOARD_GMAC_PHY_COMP_KSZ9021RNL 1
#define BOARD_GMAC_POWER_ALWAYS_ON
#define BOARD_GMAC_MODE_RGMII        1

/** The PIN list of PIO for GMAC 0x7FFFF 0x73BFF */
#define BOARD_GMAC_PINS          {0x73BFF, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT},\
                                 {(1<<25),PIOB, ID_PIOB, PIO_INPUT,    PIO_PULLUP}

#define BOARD_GMAC_MODE_PINS     {0xF0, PIOB, ID_PIOB, PIO_OUTPUT_1, PIO_DEFAULT}

/** The runtime pin configure list for EMAC */
#define BOARD_GMAC_RUN_PINS BOARD_GMAC_PINS

/*----------------------------------------------------------------------------*/
/**
 * \page sama5d3x_ek_extcomp "sama5d3-xplained - External components"
 * This page lists the definitions related to external on-board components
 * located in the board.h file for the sama5d3-xplained.
 *
 * \section board_sdmmc SD/MMC
 * - \ref BOARD_MCI0_PINS
 * - \ref BOARD_MCI0_PIN_CD
 * - \ref BOARD_MCI1_PINS
 * - \ref BOARD_MCI1_PIN_CD
 * - \ref BOARD_NUM_MCI
 *
 * \section board_emac EMAC
 * - \ref BOARD_EMAC_RST_PINS
 * - \ref BOARD_EMAC_PHY_ADDR
 * - \ref BOARD_EMAC_RUN_PINS
 * 
 * \section board_lcd LCD Properties
 * - \ref BOARD_LCD_WIDTH
 * - \ref BOARD_LCD_HEIGHT
 * - \ref BOARD_LCD_IFWIDTH
 * - \ref BOARD_LCD_FRAMESIZE
 * - \ref BOARD_LCD_TIMING_VFP
 * - \ref BOARD_LCD_TIMING_VBP
 * - \ref BOARD_LCD_TIMING_VPW
 * - \ref BOARD_LCD_TIMING_HFP
 * - \ref BOARD_LCD_TIMING_HBP
 * - \ref BOARD_LCD_TIMING_HPW
 * - \ref BOARD_LCD_FRAMERATE
 * - \ref BOARD_LCD_PIXELCLOCK
 *
 * \section board_ts Touchscreen ADC Properties
 * - \ref BOARD_TOUCHSCREEN_ADCCLK
 * - \ref BOARD_TOUCHSCREEN_STARTUP
 * - \ref BOARD_TOUCHSCREEN_SHTIM
 * - \ref BOARD_TOUCHSCREEN_DEBOUNCE
 */


/** MCI0 Card detect pin definition. (PE0) */
#define BOARD_MCI0_PIN_CD       {PIO_PE0, PIOE, ID_PIOE, PIO_INPUT, PIO_PULLUP}
/** MCI0 has no WriteProtect pin */
/** MCI1 Card detect pin definition. (PE1) */
#define BOARD_MCI1_PIN_CD       {PIO_PE1, PIOE, ID_PIOE, PIO_INPUT, PIO_PULLUP}
/** MCI1 Write Protect pin Always to GND */

/** MCI0 power control. */
#define BOARD_MCI0_PIN_POWER    {PIO_PE2, PIOE, ID_PIOE, PIO_OUTPUT_0, PIO_PULLUP}

/** Total number of MCI interface */
#define BOARD_NUM_MCI           2
/** MCI0 IO pins definition. (PD0-PD9) */
#define BOARD_MCI0_PINS        {0x3FF, PIOD, ID_PIOD, PIO_PERIPH_A, PIO_DEFAULT}
/** MCI1 IO pins definition. (PA2-PA4, PA11-PA13) */
#define BOARD_MCI1_PINS        {0x1F80000, PIOB, ID_PIOB, PIO_PERIPH_A, PIO_DEFAULT}


/** Display width in pixels. */
#define BOARD_LCD_WIDTH             800
/** Display height in pixels. */
#define BOARD_LCD_HEIGHT            480

/** Display interface width in bits. */
#define BOARD_LCD_IFWIDTH           24
/** Frame size in words (height * width * bpp / 32) */
#define BOARD_LCD_FRAMESIZE         (BOARD_LCD_WIDTH * BOARD_LCD_HEIGHT * BOARD_LCD_IFWIDTH / 32)

/** Vertical front porch in number of lines. */
#define BOARD_LCD_TIMING_VFP        22
/** Vertical back porch in number of lines. */
#define BOARD_LCD_TIMING_VBP        21
/** Vertical pulse width in number of lines. */
#define BOARD_LCD_TIMING_VPW        2
/** Horizontal front porch in LCDDOTCLK cycles. */
#define BOARD_LCD_TIMING_HFP        64
/** Horizontal back porch in LCDDOTCLK cycles. */
#define BOARD_LCD_TIMING_HBP        64
/** Horizontal pulse width in LCDDOTCLK cycles. */
#define BOARD_LCD_TIMING_HPW        128

/** Frame rate in Hz. */
#define BOARD_LCD_FRAMERATE         40

/** Pixel clock rate in Hz (HS period * VS period * BOARD_LCD_FRAMERATE). */
#define BOARD_LCD_PIXELCLOCK        ((BOARD_LCD_TIMING_HPW+BOARD_LCD_TIMING_HBP+BOARD_LCD_WIDTH+BOARD_LCD_TIMING_HFP)\
                                    *(BOARD_LCD_TIMING_VPW+BOARD_LCD_TIMING_VBP+BOARD_LCD_HEIGHT+BOARD_LCD_TIMING_VFP)\
                                    *BOARD_LCD_FRAMERATE)


#define BOARD_ISI_VSYNC     {PIO_PA30C_ISI_VSYNC, PIOA, ID_PIOA, PIO_PERIPH_C, PIO_DEFAULT}
#define BOARD_ISI_HSYNC     {PIO_PA31C_ISI_HSYNC, PIOA, ID_PIOA, PIO_PERIPH_C, PIO_DEFAULT}
#define BOARD_ISI_PCK       {PIO_PC30C_ISI_PCK, PIOC, ID_PIOC, PIO_PERIPH_C, PIO_DEFAULT}
#define BOARD_ISI_PINS_DATA {0x00FF0000, PIOA, ID_PIOA, PIO_PERIPH_C, PIO_DEFAULT}

#define PIN_ISI_RST       {1 << 24, PIOE, ID_PIOE, PIO_OUTPUT_1, PIO_DEFAULT}
#define PIN_ISI_RSTN      {1 << 29, PIOE, ID_PIOE, PIO_OUTPUT_1, PIO_DEFAULT}

#define PINS_ISI          BOARD_ISI_VSYNC, BOARD_ISI_HSYNC, BOARD_ISI_PCK , BOARD_ISI_PINS_DATA

/** Touchscreen ADC clock frequency to use. */
#define BOARD_TOUCHSCREEN_ADCCLK    300000 /* 8MHz max */
/** Touchscreen ADC startup time in µseconds. */
#define BOARD_TOUCHSCREEN_STARTUP   40
/** Touchscreen ADC track and hold time in nanoseconds. */
#define BOARD_TOUCHSCREEN_SHTIM     2000    /* min 1µs at 8MHz */
/** Touchscreen pen debounce time in nanoseconds. */
#define BOARD_TOUCHSCREEN_DEBOUNCE  10000000

/** HDMI reset pins. */
#define PIN_HDMI_RESET_L  {PIO_PC31, PIOC, ID_PIOC, PIO_OUTPUT_0, PIO_DEFAULT}
#define PIN_HDMI_RESET_H  {PIO_PC31, PIOC, ID_PIOC, PIO_OUTPUT_1, PIO_DEFAULT}

/*----------------------------------------------------------------------------*/
/**
 * \page sama5d3x_ek_chipdef "sama5d3-xplained - Individual chip definition"
 * This page lists the definitions related to different chip's definition
 * located in the board.h file for the sama5d3-xplained.
 *
 * LEDs
 * - \ref PIN_LED_0
 * - \ref PIN_LED_1
 * - \ref PIN_LED_2
 * - \ref PINS_LEDS
 *
 * Push buttons
 * - \ref PIN_PUSHBUTTON_1
  * - \ref PINS_PUSHBUTTONS
 
 *
 * PCK0 
 * - \ref PIN_PCK0
 *
 * PCK1 
 * - \ref  PIN_PCK1
 */

#ifdef BOARD_VB
#define LED_BLUE      0
#define LED_GREEN     1
#define LED_RED       2
#define LED_YELLOW    3

/** LED #0 pin definition (BLUE). */
#define PIN_LED_0   {(1<<23), PIOA, ID_PIOA, PIO_OUTPUT_1, PIO_DEFAULT}
/** LED #1 pin definition (GREEN). */
#define PIN_LED_1   {(1<<21), PIOA, ID_PIOA, PIO_OUTPUT_1, PIO_DEFAULT}
/** LED #2 pin definition (RED). */
#define PIN_LED_2   {(1<<22), PIOA, ID_PIOA, PIO_OUTPUT_1, PIO_DEFAULT}
/** LED #3 pin definition (YELLOW). */
#define PIN_LED_3   {(1<<5), PIOD, ID_PIOD, PIO_OUTPUT_1, PIO_DEFAULT}

/** List of all LEDs definitions. */
#define PINS_LEDS   PIN_LED_0, PIN_LED_1, PIN_LED_2, PIN_LED_3
#endif

#if defined(BOARD_XPLAINED)
#define LED_BLUE      0
#define LED_RED       1

/** LED #0 pin definition (LED_BLUE). */
#define PIN_LED_0   {(PIO_PE23), PIOE, ID_PIOE, PIO_OUTPUT_1, PIO_DEFAULT}
/** LED #1 pin definition (LED_RED). */
#define PIN_LED_1   {(PIO_PE24), PIOE, ID_PIOE, PIO_OUTPUT_0, PIO_DEFAULT}

/** List of all LEDs definitions. */
#define PINS_LEDS   PIN_LED_0, PIN_LED_1
#endif
 
/** Push button #0 definition. Attributes = pull-up + debounce + interrupt on rising edge. */
#define PIN_PUSHBUTTON_1  {PIO_PE29, PIOE, ID_PIOE, PIO_INPUT, PIO_PULLUP | PIO_DEBOUNCE | PIO_IT_FALL_EDGE}

/** List of all push button definitions. */
#define PINS_PUSHBUTTONS    PIN_PUSHBUTTON_1

/** Push button #1 index. */
#define PUSHBUTTON_BP1   0
/** Push button #2 index. */
#define PUSHBUTTON_BP2   1
/** Simulate Joystick Left */
#define JOYSTICK_LEFT    1
/** Simulate Joystick Right */
#define JOYSTICK_RIGHT   0

#define NO_PUSHBUTTON

/** PCK0 */
#define PIN_PCK0        {PIO_PD30B_PCK0, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** PCK1 */
#define PIN_PCK1        {PIO_PD31B_PCK1, PIOD, ID_PIOD, PIO_PERIPH_B, PIO_DEFAULT}
/** PCK2 */
#define PIN_PCK2        {PIO_PC15B_PCK2, PIOC, ID_PIOC, PIO_PERIPH_B, PIO_DEFAULT}

/** PWM0 */
#define PIN_PWM0_H     {PIO_PA20B_PWMH0, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
#define PIN_PWM0_L     {PIO_PA21B_PWML0, PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
#define PIN_PWM0_FI    {PIO_PC28B_PWMFI0, PIOC, ID_PIOC, PIO_PERIPH_B, PIO_DEFAULT}


#define PIN_PWM1_H     {PIO_PA22B_PWMH1,  PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
#define PIN_PWM1_L     {PIO_PA23B_PWML1,  PIOA, ID_PIOA, PIO_PERIPH_B, PIO_DEFAULT}
#define PIN_PWM1_FI    {PIO_PC31B_PWMFI1, PIOC, ID_PIOC, PIO_PERIPH_B, PIO_DEFAULT}

/*----------------------------------------------------------------------------
 *        Headers for board
 *----------------------------------------------------------------------------*/
 
#include "include/board_lowlevel.h"
#include "include/board_memories.h"
#include "include/bmp.h"
#include "include/mii.h"
#include "include/gmii.h"
#include "include/emacd.h"
#include "include/macb.h"
#include "include/gmacd.h"
#include "include/gmacb.h"
#include "include/clock.h"
#include "include/dbgu_console.h"
#include "include/dbg_util.h"
#include "include/iso7816_4.h"
#include "include/dmad.h"
#include "include/dma_hardware_interface.h"
#include "include/hamming.h"

#include "include/led.h"
#include "include/math.h"
#include "include/mcid.h"
#include "include/timetick.h"
#include "include/wav.h"
#include "include/wm8904.h"
#include "include/qt1070.h"

#include "include/lcdd.h"
#include "include/lcd_draw.h"
#include "include/lcd_font10x14.h"
#include "include/lcd_font.h"
#include "include/lcd_color.h"
#include "include/tsd.h"
#include "include/tsd_com.h"
#include "include/cand.h"
#include "include/ov.h"
#include "include/omnivision.h"
#include "include/ovyuv.h"
#endif /* #ifndef _BOARD_ */

