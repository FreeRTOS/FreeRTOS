/*
 * File:		m5225x_evb.h
 * Purpose:		Evaluation board definitions and memory map information
 *
 * Notes:
 * 
 * License:     All software covered by license agreement in -
 *              docs/Freescale_Software_License.pdf
 */

#ifndef _M5225xEVB_H
#define _M5225xEVB_H

#define COLDFIRE_MAC_ADDRESS	{0x00, 0x04, 0x9f, 0x00, 0xab, 0x2b}

/********************************************************************/

//#include "mcf5xxx.h"

/********************************************************************/
#define LED0_TOGGLE     MCF_GPIO_PORTTC = (uint8)(MCF_GPIO_PORTTC ^ MCF_GPIO_PORTTC_PORTTC0)

/*
 * Debug prints ON (#undef) or OFF (#define)
 */
#undef DEBUG

/* 
 * System Bus Clock Info 
 */
 
 								
#define	SYSTEM_CLOCK			80	/* system bus frequency in MHz */
//#define PERIOD			    12.5	/* system bus period in ns */
#define TERMINAL_BAUD			19200
#define UART_BAUD				TERMINAL_BAUD	/*  19200*/

#define TERMINAL_PORT			0
#define REF_CLK_MHZ         	48
#define SYS_CLK_MHZ         	SYSTEM_CLOCK
#define REF_CLK_KHZ         	(REF_CLK_MHZ * 1000)
#define SYS_CLK_KHZ         	(SYS_CLK_MHZ * 1000)

/* 
 * Memory map definitions from linker command files 
 */

extern uint8 __IPSBAR[];
extern uint8 __SRAM[];
extern uint8 __FLASH[];      
extern uint8 __SRAM_SIZE[];
extern uint8 __FLASH_SIZE[];
extern uint8 __DATA_ROM[];
extern uint8 __DATA_RAM[];
extern uint8 __DATA_END[];
extern uint8 __BSS_START[];
extern uint8 __BSS_END[];
extern uint32 VECTOR_TABLE[];
extern uint32 __VECTOR_RAM[];


/* 
 * Memory Map Info 
 */
#define IPSBAR_ADDRESS		(uint32)__IPSBAR

#define SRAM_ADDRESS		(uint32)__SRAM
#define SRAM_SIZE			(uint32)__SRAM_SIZE

#define FLASH_ADDRESS       (uint32)__FLASH
#define FLASH_SIZE          (uint32)__FLASH_SIZE

/*
 *	Interrupt Controller Definitions
 */
#define TIMER_NETWORK_LEVEL		3
#define USB_NETWORK_LEVEL		1

/*
 *	Timer period info
 */
 
 /* 1 sec / max timeout */
#define TIMER_NETWORK_PERIOD	1000000000/0x10000	

/*
 * Board specific function prototypes
 */

void leds_init();
void board_led_display(uint8 number);

/********************************************************************/

#endif /* _M5225xEVB_H */
