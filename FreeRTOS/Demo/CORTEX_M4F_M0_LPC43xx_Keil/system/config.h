/*****************************************************************************
 *   config.h:  Header file for NXP LPC43xx Family Microprocessors
 *
 *   Copyright(C) 2011, NXP Semiconductor
 *   All rights reserved.
 *
 *   History
 *   2011.6.22  ver 1.00    Preliminary version, first Release
 *
******************************************************************************/
#ifndef __CONFIG_H 
#define __CONFIG_H

#include <stdint.h>

/*----------------------------------------------------------------------------
  Define clocks
 *----------------------------------------------------------------------------*/
#define RTC_CLK		(   32768UL)	/* RTC oscillator frequency           */
#define IRC_OSC		(12000000UL)	/* Internal RC oscillator frequency   */
#define IRC_TRIM_VAL 0x34A			/* IRC trim value for 12MHz output    */
#define XTAL_FREQ	(12000000UL)	/* Frequency of external xtal */
#define EXT_FREQ	(12000000UL)	/* Frequency of external clock on EXT_TCK, ENET_RX_CLK or ENET_TX_CLK */

/*----------------------------------------------------------------------------
  Retarget selection
 *----------------------------------------------------------------------------*/

typedef enum {
	RETARGET_USART0	= 0,
	RETARGET_UART1	= 1,
	RETARGET_USART2	= 2,
	RETARGET_USART3	= 3
} RETARGET_Type;

#define RETARGET_UART_BUFSIZE		0x40
extern volatile uint32_t UART0Count;
extern volatile uint8_t UART0Buffer[RETARGET_UART_BUFSIZE];
extern volatile uint32_t UART1Count;
extern volatile uint8_t UART1Buffer[RETARGET_UART_BUFSIZE];
extern volatile uint32_t UART2Count;
extern volatile uint8_t UART2Buffer[RETARGET_UART_BUFSIZE];
extern volatile uint32_t UART3Count;
extern volatile uint8_t UART3Buffer[RETARGET_UART_BUFSIZE];
extern void RetargetInit(RETARGET_Type retarget, uint32_t baudrate);

/*----------------------------------------------------------------------------
  Board selection
 *----------------------------------------------------------------------------*/
//NXP LPC4300 validation board
//#define NXP_VALIDATION_BOARD

//Hitex LPC4350 evaluation board
//#define USE_HITEX_LPC4350_EVAL

#endif /* end __CONFIG_H */
/*****************************************************************************
**                            End Of File
******************************************************************************/
