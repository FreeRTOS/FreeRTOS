/**
 * \page sama5d2_xult_board_desc sama5d2-XULT - Board Description
 *
 * \section Purpose
 *
 * This file is dedicated to describe the sama5d2-XULT board.
 *
 * \section Contents
 *
 *  - sama5d2-XULT
 *  - For sama5d2-XULT information, see \subpage sama5d2_xult_board_info.
 *  - For operating frequency information, see \subpage sama5d2_xult_opfreq.
 *  - For using portable PIO definitions, see \subpage sama5d2_xult_piodef.
 *  - For on-board memories, see \subpage sama5d2_xult_mem.
 *  - Several USB definitions are included here, see \subpage sama5d2_xult_usb.
 *  - For External components, see \subpage sama5d2_xult_extcomp.
 *  - For Individual chip definition, see \subpage sama5d2_xult_chipdef.
 *
 * To get more software details and the full list of parameters related to the
 * sama5d2-XULT board configuration, please have a look at the source file:
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
 *  Definition of sama5d2-XULT
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
 * \page sama5d2_xult_board_info "sama5d2-XULT - Board informations"
 * This page lists several definition related to the board description.
 *
 * \section Definitions
 * - \ref BOARD_NAME
 */

/** Name of the board */
#define BOARD_NAME "sama5d2-xult-proto"

/** Family definition */
#if !defined sama5d2
  #define sama5d2
#endif

/** Board definition */
#define sama5d2xult

/** Core definition */
#define cortexa5

#define BOARD_REV_A_XULT

/*----------------------------------------------------------------------------*/
/**
 *  \page sama5d2_xult_opfreq "sama5d2-XULT - Operating frequencies"
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
#define PINS_CONSOLE            PINS_UART1_IOS1
#define CONSOLE_PER_ADD         UART1
#define CONSOLE_ID              ID_UART1
#define CONSOLE_BAUDRATE        57600
#define CONSOLE_DRIVER          DRV_UART

/* =================== PIN LED definition ====================== */

/* RGB LED index */
#define LED_RED   0    /* led red shared with SDMMC0 (eMMC) card detect used only by RomBoot */
#define LED_GREEN 1
#define LED_BLUE  2

/** LED #0 pin definition (Red). */
#define PIN_LED_0 { PIO_GROUP_A, PIO_PA13, PIO_OUTPUT_0, PIO_OPENDRAIN }

/** LED #1 pin definition (Green). */
#define PIN_LED_1 { PIO_GROUP_B, PIO_PB5, PIO_OUTPUT_1, PIO_OPENDRAIN }

/** LED #2 pin definition (Blue). */
#define PIN_LED_2 { PIO_GROUP_B, PIO_PB0, PIO_OUTPUT_1, PIO_OPENDRAIN }

/** List of all LEDs definitions. */
#define PINS_LEDS { PIN_LED_0, PIN_LED_1, PIN_LED_2 }

/* =================== LWM LED definition ====================== */

/** LED #1 PWM Channel */
#define PWM_LED_CH_0 2

/** LED #2 PWM Channel */
#define PWM_LED_CH_1 1

/** LED #1 pin definition (Green). */
#define PIN_PWM_LED_0 { PIO_GROUP_B, PIO_PB5C_PWMH2, PIO_PERIPH_C, PIO_PULLUP }

/** LED #2 pin definition (Blue). */
#define PIN_PWM_LED_1 { PIO_GROUP_B, PIO_PB0D_PWMH1, PIO_PERIPH_D, PIO_PULLUP }

/** List of all PWM LED channels */
#define PWM_LEDS_CH { PWM_LED_CH_0, PWM_LED_CH_1 }

/** List of all LEDs definitions in PWM mode (red LED is not on a PWM pin) */
#define PINS_PWM_LEDS { PIN_PWM_LED_0, PIN_PWM_LED_1 }

/* =================== PIN PUSH BUTTON definition ============== */

#define PIO_CFG_PB  (PIO_PULLUP | PIO_DEBOUNCE)

#define PIN_PUSHBUTTON_1 { PIO_GROUP_B, PIO_PB6, PIO_INPUT, PIO_CFG_PB }

/** List of all push button definitions. */
#define PINS_PUSHBUTTONS { PIN_PUSHBUTTON_1 }

/** Push button index. */
#define PUSHBUTTON_BP1 0

/* ================== ACT8945A PMIC definition ====================== */

#define ACT8945A_PINS PINS_FLEXCOM4_TWI_IOS3
#define ACT8945A_ADDR TWI4
#define ACT8945A_FREQ 400000
#define ACT8945A_PIN_CHGLEV \
	{ PIO_GROUP_A, PIO_PA12, PIO_OUTPUT_0, PIO_PULLUP }
#define ACT8945A_PIN_IRQ \
	{ PIO_GROUP_B, PIO_PB13, PIO_INPUT, PIO_PULLUP | PIO_IT_FALL_EDGE }
#define ACT8945A_PIN_LBO \
	{ PIO_GROUP_A, PIO_PB13, PIO_INPUT, PIO_PULLUP }

/* ================== PIN USB definition ======================= */

/** USB VBus pin */
#define PIN_USB_VBUS      {\
	{ PIO_GROUP_A, PIO_PA31, PIO_INPUT, PIO_DEBOUNCE | PIO_IT_BOTH_EDGE },\
}
/** USB OverCurrent detection*/
#define PIN_USB_OVCUR     {\
	{ PIO_GROUP_A, PIO_PA29, PIO_INPUT, PIO_DEFAULT },\
}
/** USB Power Enable A, Active high */
#define PIN_USB_POWER_ENA {\
	{ PIO_GROUP_B, PIO_PB9, PIO_OUTPUT_0, PIO_DEFAULT },\
}
/** USB Power Enable B, Active high  */
#define PIN_USB_POWER_ENB {\
	{ PIO_GROUP_B, PIO_PB10, PIO_OUTPUT_0, PIO_DEFAULT },\
}

/* ================= PIN LCD IRQ definition ===================== */

#define PIO_CFG_LCD_IRQ  (PIO_PULLUP | PIO_IT_FALL_EDGE)

#define PIN_QT1070_IRQ {\
	{ PIO_GROUP_B, PIO_PB8, PIO_INPUT, PIO_CFG_LCD_IRQ },\
}
#define PIN_MXT336S_IRQ {\
	{ PIO_GROUP_B, PIO_PB7, PIO_INPUT, PIO_CFG_LCD_IRQ },\
}
#define PIN_MXT768E_IRQ	{\
	{ PIO_GROUP_B, PIO_PB7, PIO_INPUT, PIO_CFG_LCD_IRQ },\
}

/* =================== PIN ISC definition ======================= */

#define ISC_TWI_ADDR ((Twi*)TWIHS0)
#define ISC_TWI_PINS PINS_TWI0_IOS4
#define ISC_PINS     PINS_ISC_IOS3
#define ISC_PIN_RST  { PIO_GROUP_B, PIO_PB11, PIO_OUTPUT_1, PIO_DEFAULT }
#define ISC_PIN_PWD  { PIO_GROUP_B, PIO_PB12, PIO_OUTPUT_1, PIO_DEFAULT }

/* =================== PIN ClassD definition ==================== */

#define CLASSD_PINS PINS_CLASSD_IOS1

/* =================== PIN SDMMC definition ===================== */

#define SDMMC0_PINS  { PINS_SDMMC0_8B_IOS1, PIN_SDMMC0_CK_IOS1,\
                       PIN_SDMMC0_VDDSEL_IOS1, PIN_SDMMC0_RSTN_IOS1 }

#define SDMMC1_PINS  { PINS_SDMMC1_4B_IOS1, PIN_SDMMC1_CK_IOS1,\
                       PIN_SDMMC1_CD_IOS1 }

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
#define AT24_PINS       PINS_TWI1_IOS2;
#define AT24_ADDR       ((Twi*)TWIHS1)
#define AT24_FREQ       400000
#define AT24_DESC       {"AT24MAC402", 0xFF, 16}

/* =================== QSPI serial flashdevice definition ======= */

#define QSPIFLASH_PINS     PINS_QSPI0_IOS3
#define QSPIFLASH_ADDR     QSPI0
#define QSPIFLASH_BAUDRATE 50000000 /* 50 MHz */

/* =================== CAN device definition ==================== */
/* Both ports are wired to the J9 connector:
 * CANTX0 = PC10 = J9:8
 * CANRX0 = PC11 = J9:7
 * CANTX1 = PC26 = J9:6
 * CANRX1 = PC27 = J9:5 */

#define CAN0_PINS          PINS_CAN0_IOS1
#define CAN1_PINS          PINS_CAN1_IOS0

/* =================== GMAC/PHY definition =================== */

#define GMAC0_ADDR        GMAC0
#define GMAC0_PINS        PINS_GMAC_RMII_IOS3
#define GMAC0_PHY_ADDR    0
#define GMAC0_PHY_IRQ_PIN PIN_GTSUCOM_IOS1
#define GMAC0_PHY_RETRIES PHY_DEFAULT_RETRIES

/* =================== ILI9488 device definition =================== */
/* Connected on board A5D2, XPRO EXT2 connector */

/* ILI9488 ID code */
#define ILI9488_DEVICE_CODE    0x2810

#define ILI9488_PINS    PINS_SPI1_NPCS1_IOS3
#define ILI9488_ADDR    SPI1
#define ILI9488_CS      1
#define ILI9488_ATTRS   (SPI_MR_MODFDIS | SPI_MR_MSTR) // | SPI_MR_WDRBT
#define ILI9488_FREQ    40000 /* (value in KHz) */
#define ILI9488_DLYBS   100
#define ILI9488_DLYCT   100
//#define ILI9488_SPI_MODE (SPI_CSR_NCPHA | SPI_CSR_BITS_9_BIT)
#define ILI9488_SPI_MODE (SPI_CSR_CPOL | SPI_CSR_BITS_9_BIT)

#define MXTX_RESET_PIN  {\
		{PIO_GROUP_D, PIO_PD28, PIO_OUTPUT_1, PIO_DEFAULT}	\
	}
#define MXTX_BACKLIGHT_PIN  {\
		{PIO_GROUP_B, PIO_PB5C_PWMH2, PIO_PERIPH_C, PIO_DEFAULT} \
	}

/* =================== LCD Touch board definition =================== */

/** PIO pins for LCD */
#define BOARD_LCD_PINS              PINS_LCD_IOS2

/** Display width in pixels. */
#define BOARD_LCD_WIDTH             480
/** Display height in pixels. */
#define BOARD_LCD_HEIGHT            272
/** Frame rate in Hz. */
#define BOARD_LCD_FRAMERATE         40

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

/* =================== QT1070 device definition =================== */
#define QT1070_PINS       PINS_TWI1_IOS2;
#define QT1070_ADDR       ((Twi*)TWIHS1)
#define QT1070_FREQ       400000
#define QT1070_DESC       {"QT1070", 0x00, 00}

#endif /* #ifndef _BOARD_D2_H */
