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
* Object              : AT91SAM7X Evaluation Board Features Definition File.
*
* Creation            : JG   20/Jun/2005
*----------------------------------------------------------------------------
*/
#ifndef Board_h
#define Board_h

#include <AT91SAM7X256.h>
#define __inline inline
#include <lib_AT91SAM7X256.h>

#define true	-1
#define false	0

/*-------------------------------*/
/* SAM7Board Memories Definition */
/*-------------------------------*/
// The AT91SAM7X128 embeds a 32-Kbyte SRAM bank, and 128K-Byte Flash

#define  FLASH_PAGE_NB		256
#define  FLASH_PAGE_SIZE	128

/*-----------------*/
/* Leds Definition */
/*-----------------*/
#define LED1            (1<<19)	// PB19
#define LED2            (1<<20)	// PB20
#define LED3            (1<<21)	// PB21
#define LED4            (1<<22)	// PB22
#define NB_LED			4

#define LED_MASK        (LED1|LED2|LED3|LED4)

/*-------------------------*/
/* Push Buttons Definition */
/*-------------------------*/

#define SW1_MASK        (1<<21)	// PA21
#define SW2_MASK        (1<<22)	// PA22
#define SW3_MASK        (1<<23)	// PA23
#define SW4_MASK        (1<<24)	// PA24
#define SW_MASK         (SW1_MASK|SW2_MASK|SW3_MASK|SW4_MASK)


#define SW1 	(1<<21)	// PA21
#define SW2 	(1<<22)	// PA22
#define SW3 	(1<<23)	// PA23
#define SW4 	(1<<24)	// PA24

/*--------------*/
/* Master Clock */
/*--------------*/

#define EXT_OC          18432000   // Exetrnal ocilator MAINCK
#define MCK             47923200   // MCK (PLLRC div by 2)
#define MCKKHz          (MCK/1000) //

#endif /* Board_h */
