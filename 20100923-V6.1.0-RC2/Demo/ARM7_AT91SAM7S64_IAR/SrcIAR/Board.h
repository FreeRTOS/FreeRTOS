/*----------------------------------------------------------------------------
*         ATMEL Microcontroller Software Support  -  ROUSSET  -
*----------------------------------------------------------------------------
* The software is delivered "AS IS" without warranty or condition of any
* kind, either express, implied or statutory. This includes without
* limitation any warranty or condition with respect to merchantability or
* fitness for any particular purpose, or against the infringements of
* intellectual property rights of others.
*----------------------------------------------------------------------------
* File Name           : Board.h
* Object              : AT91SAM7S Evaluation Board Features Definition File.
*
* Creation            : JPP   16/Jun/2004
*----------------------------------------------------------------------------
*/
#ifndef Board_h
#define Board_h

#include "AT91SAM7S64.h"
#define __inline static inline
#include "lib_AT91SAM7S64.h"

#define true	-1
#define false	0

/*-------------------------------*/
/* SAM7Board Memories Definition */
/*-------------------------------*/
// The AT91SAM7S64 embeds a 16-Kbyte SRAM bank, and 64 K-Byte Flash

#define  INT_SARM           0x00200000
#define  INT_SARM_REMAP	    0x00000000

#define  INT_FLASH          0x00000000
#define  INT_FLASH_REMAP    0x01000000

#define  FLASH_PAGE_NB		512
#define  FLASH_PAGE_SIZE	128

/*-----------------*/
/* Leds Definition */
/*-----------------*/
/*                                 PIO   Flash    PA    PB   PIN */
#define LED1            (1<<0)	/* PA0 / PGMEN0 & PWM0 TIOA0  48 */
#define LED2            (1<<1)	/* PA1 / PGMEN1 & PWM1 TIOB0  47 */
#define LED3            (1<<2)	/* PA2          & PWM2 SCK0   44 */
#define LED4            (1<<3)	/* PA3          & TWD  NPCS3  43 */
#define NB_LED			4

#define LED_MASK        (LED1|LED2|LED3|LED4)

/*-------------------------*/
/* Push Buttons Definition */
/*-------------------------*/
/*                                 PIO    Flash    PA    PB   PIN */
#define SW1_MASK        (1<<19)	/* PA19 / PGMD7  & RK   FIQ     13 */
#define SW2_MASK        (1<<20)	/* PA20 / PGMD8  & RF   IRQ0    16 */
#define SW3_MASK        (1<<15)	/* PA15 / PGM3   & TF   TIOA1   20 */
#define SW4_MASK        (1<<14)	/* PA14 / PGMD2  & SPCK PWM3    21 */
#define SW_MASK         (SW1_MASK|SW2_MASK|SW3_MASK|SW4_MASK)


#define SW1 	(1<<19)	// PA19
#define SW2 	(1<<20)	// PA20
#define SW3 	(1<<15)	// PA15
#define SW4 	(1<<14)	// PA14

/*------------------*/
/* USART Definition */
/*------------------*/
/* SUB-D 9 points J3 DBGU*/
#define DBGU_RXD		AT91C_PA9_DRXD	  /* JP11 must be close */
#define DBGU_TXD		AT91C_PA10_DTXD	  /* JP12 must be close */
#define AT91C_DBGU_BAUD	   115200   // Baud rate

#define US_RXD_PIN		AT91C_PA5_RXD0    /* JP9 must be close */
#define US_TXD_PIN		AT91C_PA6_TXD0    /* JP7 must be close */
#define US_RTS_PIN		AT91C_PA7_RTS0    /* JP8 must be close */
#define US_CTS_PIN		AT91C_PA8_CTS0    /* JP6 must be close */

/*--------------*/
/* Master Clock */
/*--------------*/

#define EXT_OC          18432000   // Exetrnal ocilator MAINCK
#define MCK             47923200   // MCK (PLLRC div by 2)
#define MCKKHz          (MCK/1000) //

#endif /* Board_h */
