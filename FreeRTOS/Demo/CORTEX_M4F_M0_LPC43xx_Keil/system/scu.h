/***********************************************************************
 * $Id: scu.h 8389 2011-10-19 13:53:14Z nxp28536 $
 *
 * Project: LPC43xx Common
 *
 * Description:
 *     Header file for PINMUX configuration
 *
 ***********************************************************************
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * products. This software is supplied "AS IS" without any warranties.
 * NXP Semiconductors assumes no responsibility or liability for the
 * use of the software, conveys no license or title under any patent,
 * copyright, or mask work right to the product. NXP Semiconductors
 * reserves the right to make changes in the software without
 * notification. NXP Semiconductors also make no representation or
 * warranty that such application will be suitable for the specified
 * use without further testing or modification.
 **********************************************************************/
#ifndef __SCU_H 
#define __SCU_H

#define PORT_OFFSET 0x80
#define PIN_OFFSET  0x04

/* Pin modes */
#define MD_PUP  (0x0<<3)
#define MD_BUK  (0x1<<3)
#define MD_PLN  (0x2<<3)
#define MD_PDN  (0x3<<3)
#define MD_EHS  (0x1<<5)
#define MD_EZI  (0x1<<6)
#define MD_ZI   (0x1<<7)
#define MD_EHD0 (0x1<<8)
#define MD_EHD1 (0x1<<8)
#define MD_PLN_FAST (MD_PLN | MD_EHS | MD_EZI | MD_ZI)

/* Pin modes
*  ========= 
*  The EPUN and EPD bits in the SFS registers allow the selection of weak on-chip
*  pull-up or pull-down resistors with a typical value of 50 kOhm for each pin or the
*  selection of the repeater mode.
*  The possible on-chip resistor configurations are pull-up enabled, pull-down enabled, or no
*  pull-up/pull-down. The default value is pull-up enabled.
*
*  The repeater mode enables the pull-up resistor if the pin is at a logic HIGH and enables
*  the pull-down resistor if the pin is at a logic LOW. This causes the pin to retain its last
*  known state if it is configured as an input and is not driven externally. Repeater mode may
*  typically be used to prevent a pin from floating (and potentially using significant power if it
*  floats to an indeterminate state) if it is temporarily not driven.
*  
*  To be able to receive a digital signal, the input buffer must be enabled through bit EZI in
*  the pin configuration registers. By default, the input buffer is disabled.
*  For pads that support both a digital and an analog function, the input buffer must be
*  disabled before enabling the analog function
*  
*  All digital pins support a programmable glitch filter (bit ZIF), which can be switched on or
*  off. By default, the glitch filter is on. The glitch filter should be disabled for
*  clocking signals with frequencies higher than 30 MHz.
*  
*  Normal-drive and high-speed pins support a programmable slew rate (bit EHS) to select
*  between lower noise and low speed or higher noise and high speed . The typical
*  frequencies supported are 50 MHz/80 MHz for normal-drive pins and 75 MHz/180 MHz for
*  high-speed pins.
*/

/* these definitions allow to set or clear single configuration bits */
#define PDN_SET			(1 << 3)
#define PDN_CLR		  	(0)
#define PUP_SET		  	(0)
#define PUP_CLR		  	(1 << 4)

/* these definitions allow to configure the port in one specific mode */
/* within scu_pinmux() function */
#define PDN_ENABLE		(0x3 << 3)	/* pull down */
#define PUP_ENABLE		(0x0 << 3)	/* pull up */
#define REPEATER_ENABLE	(0x1 << 3)  /* repeater */
#define PLAIN_ENABLE	(0x2 << 3)	/* no pull up, no pull down (plain) */

#define SLEWRATE_SLOW	(0)
#define SLEWRATE_FAST	(1 << 5)

/* enable / disable the input buffer */
#define INBUF_ENABLE	  (1 << 6)
#define INBUF_DISABLE	  (0)

/* enable / disable the filter */
#define FILTER_ENABLE	  (0)
#define FILTER_DISABLE	  (1 << 7)

/* define the drive strenght */
#define DRIVE_8MA         (0x1 << 8)	// Drive strength of 8mA
#define DRIVE_14MA        (0x1 << 9)	// Drive strength of 14mA
#define DRIVE_20MA        (0x3 << 8)	// Drive strength of 20mA



// Configuration examples for external memory bus pins
#define EMC_OUT	   (PUP_CLR | SLEWRATE_FAST | FILTER_DISABLE) 
#define EMC_IO	   (PUP_CLR | SLEWRATE_FAST | INBUF_ENABLE | FILTER_DISABLE)

// Configuration examples 
#define CLK_OUT	   (PUP_CLR | SLEWRATE_FAST | FILTER_DISABLE) 
#define CLK_IN	   (PUP_CLR | SLEWRATE_FAST | INBUF_ENABLE | FILTER_DISABLE)

/* Pin functions */
#define FUNC0 0x0
#define FUNC1 0x1
#define FUNC2 0x2
#define FUNC3 0x3
#define FUNC4 0x4
#define FUNC5 0x5
#define FUNC6 0x6
#define FUNC7 0x7

extern void scu_pinmux(unsigned port, unsigned pin, unsigned mode, unsigned func);

#define LPC_SCU_PIN(po, pi)   (*(volatile int         *) (LPC_SCU_BASE + ((po) * 0x80) + ((pi) * 0x4))    )
#define LPC_SCU_CLK(c)        (*(volatile int         *) (LPC_SCU_BASE + 0xC00 + ((c) * 0x4))    )


#endif /* end __SCU_H */
/*****************************************************************************
**                            End Of File
******************************************************************************/
