/**
 * \page sama5d2_ptc_engi_board_desc sama5d2-PTC-ENGI - Board Description
 *
 * \section Purpose
 *
 * This file is dedicated to describe the sama5d2-PTC-ENGI board.
 *
 * \section Contents
 *
 *  - sama5d2-PTC-ENGI
 *  - For sama5d2-PTC-ENGI information, see \subpage sama5d2_ptc_engi_board_info.
 *  - For operating frequency information, see \subpage sama5d2_ptc_engi_opfreq.
 *  - For using portable PIO definitions, see \subpage sama5d2_ptc_engi_piodef.
 *  - For on-board memories, see \subpage sama5d2_ptc_engi_mem.
 *  - Several USB definitions are included here, see \subpage sama5d2_ptc_engi_usb.
 *  - For External components, see \subpage sama5d2_ptc_engi_extcomp.
 *  - For Individual chip definition, see \subpage sama5d2_ptc_engi_chipdef.
 *
 * To get more software details and the full list of parameters related to the
 * sama5d2-PTC-ENGI board configuration, please have a look at the source file:
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
 *  Definition of sama5d2-PTC-ENGI
 *  characteristics, sama5d4-dependant PIOs and external components interfacing.
 */

#ifndef _BOARD_D2_H
#define _BOARD_D2_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include "board_lowlevel.h"
#include "board_memories.h"

/*----------------------------------------------------------------------------
 *        HW BOARD Definitions
 *----------------------------------------------------------------------------*/

/**
 * \page sama5d2_ptc_engi_board_info "sama5d2-PTC-ENGI - Board informations"
 * This page lists several definition related to the board description.
 *
 * \section Definitions
 * - \ref BOARD_NAME
 */

/** Name of the board */
#define BOARD_NAME "sama5d2-ptc-engi"

/*----------------------------------------------------------------------------*/
/**
 *  \page sama5d2_ptc_engi_opfreq "sama5d2-PTC-ENGI - Operating frequencies"
 *  This page lists several definition related to the board operating frequency
 *  (when using the initialization done by board_lowlevel.c).
 */

/** Frequency of the board slow clock oscillator */
#define BOARD_SLOW_CLOCK_EXT_OSC 32768

/** Frequency of the board main clock oscillator */
#define BOARD_MAIN_CLOCK_EXT_OSC 12000000

/** /def Definition of DDRAM's type */
#define BOARD_DDRAM_TYPE         MT41K128M16

/** \def Board DDR memory size in bytes */
#define BOARD_DDR_MEMORY_SIZE    512*1024*1024

/** \def Board PIT tick resolution */
#define BOARD_TIMER_RESOLUTION    1000

/* =================== PIN CONSOLE definition ================== */

/** CONSOLE pin definition, Use only UART */
#define PINS_CONSOLE            PINS_UART0_IOS1
#define CONSOLE_PER_ADD         UART0
#define CONSOLE_ID              ID_UART0
#define CONSOLE_BAUDRATE        57600
#define CONSOLE_DRIVER          DRV_UART

/* =================== PIN LED definition ====================== */

/* RGB LED index */
#define LED_RED   0
#define LED_GREEN 1
#define LED_BLUE  2

/** LED #0 pin definition (Red). */
#define PIN_LED_0 { PIO_GROUP_A, PIO_PA30, PIO_OUTPUT_1, PIO_OPENDRAIN }

/** LED #1 pin definition (Green). */
#define PIN_LED_1 { PIO_GROUP_A, PIO_PA31, PIO_OUTPUT_1, PIO_OPENDRAIN }

/** LED #2 pin definition (Blue). */
#define PIN_LED_2 { PIO_GROUP_B, PIO_PB2, PIO_OUTPUT_1, PIO_OPENDRAIN }

/** List of all LEDs definitions. */
#define PINS_LEDS { PIN_LED_0, PIN_LED_1, PIN_LED_2 }

/* =================== PIN PUSH BUTTON definition ============== */

#define PIO_CFG_PB  (PIO_PULLUP | PIO_DEBOUNCE)

#define PIN_PUSHBUTTON_1 { PIO_GROUP_B, PIO_PB9, PIO_INPUT, PIO_CFG_PB }

/** List of all push button definitions. */
#define PINS_PUSHBUTTONS { PIN_PUSHBUTTON_1 }

/** Push button index. */
#define PUSHBUTTON_BP1 0

/* ================== ACT8945A PMIC definition ====================== */

#define ACT8945A_PINS PINS_FLEXCOM4_TWI_IOS3
#define ACT8945A_ADDR TWI0
#define ACT8945A_FREQ 400000
#define ACT8945A_PIN_CHGLEV \
	{ PIO_GROUP_A, PIO_PA22, PIO_OUTPUT_0, PIO_PULLUP }
#define ACT8945A_PIN_IRQ \
	{ PIO_GROUP_B, PIO_PB13, PIO_INPUT, PIO_PULLUP | PIO_IT_FALL_EDGE }
#define ACT8945A_PIN_LBO \
	{ PIO_GROUP_C, PIO_PC8, PIO_INPUT, PIO_PULLUP }

/* ================== PIN USB definition ======================= */

/** USB VBus pin */
#define PIN_USB_VBUS      {\
	{ PIO_GROUP_A, PIO_PA27, PIO_INPUT, PIO_DEBOUNCE | PIO_IT_BOTH_EDGE },\
}

/** USB OverCurrent detection*/
#define PIN_USB_OVCUR     {\
	{ PIO_GROUP_A, PIO_PA29, PIO_INPUT, PIO_DEFAULT },\
}

/** USB Power Enable B, Active high  */
#define PIN_USB_POWER_ENB {\
	{ PIO_GROUP_A, PIO_PBA28, PIO_OUTPUT_0, PIO_DEFAULT },\
}

/* =================== AT25 device definition =================== */

#define AT25_PINS     PINS_SPI0_NPCS0_IOS1
#define AT25_ADDR     SPI0
#define AT25_CS       0
#define AT25_ATTRS    (SPI_MR_MODFDIS | SPI_MR_WDRBT | SPI_MR_MSTR)
#define AT25_FREQ     40000 /* (value in KHz) */
#define AT25_LOW_FREQ 20000 /* (value in KHz) */
#define AT25_DLYBS    0
#define AT25_DLYCT    0
#define AT25_SPI_MODE (SPI_CSR_NCPHA | SPI_CSR_BITS_8_BIT)

/* =================== AT24 device definition =================== */
#define AT24_PINS       PINS_TWI1_IOS1;
#define AT24_ADDR       ((Twi*)TWIHS1)
#define AT24_FREQ       400000
#define AT24_DESC       {"AT24MAC402", 0xFF, 16}

/* =================== GMAC/PHY definition =================== */

#define GMAC0_ADDR        GMAC0
#define GMAC0_PINS        PINS_GMAC_RMII_IOS3
#define GMAC0_PHY_ADDR    0
#define GMAC0_PHY_IRQ_PIN PIN_GTSUCOM_IOS1
#define GMAC0_PHY_RETRIES PHY_DEFAULT_RETRIES

/* =================== NANDFLASH device definition =================== */

#define BOARD_NANDFLASH_PINS      PINS_NFC_IOS2
#define BOARD_NANDFLASH_ADDR      EBI_CS3_ADDR
#define BOARD_NANDFLASH_CS        3
#define BOARD_NANDFLASH_BUS_WIDTH 8

#endif /* #ifndef _BOARD_D2_H */
