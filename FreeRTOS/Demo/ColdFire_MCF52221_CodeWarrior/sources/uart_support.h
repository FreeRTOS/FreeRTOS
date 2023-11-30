/*
 * File:        uart_support.h
 * Purpose:     Implements UART basic support, Derivative Specific Interrupt handler and need function needed 
 *              for MSL Support (printf\cout to terminal), defined in <UART.h>
 *
 * Notes:       
 *              
 */

#ifndef __UART_SUPPORT_H__
#define __UART_SUPPORT_H__

#ifdef __cplusplus
extern "C" {
#endif


#include "support_common.h"

#if ENABLE_UART_SUPPORT==1 

/* 
 * Include the Freescale UART specific header file for printf/cout/scanf support 
 */
#include <ansi_parms.h>
#ifdef __cplusplus
extern "C" {
#endif
#include <UART.h>
#ifdef __cplusplus
}
#endif

#define UART_STANDARD	0
#define UART_DIVIDER	1
#define UART_5407		2
#define UART_PSC		3
#define UART_54451		4

#define UART_SUPPORT_TYPE    UART_STANDARD

void uart_init(int channel, unsigned long systemClockKHz, unsigned long baudRate);

/********************************************************************/
/*
 * Wait for a character to be received on the specified UART
 *
 * Return Values:
 *  the received character
 */
char uart_getchar (int channel);

/********************************************************************/
/*
 * Wait for space in the UART Tx FIFO and then send a character
 */ 
void uart_putchar (int channel, char ch);


#endif  /* ENABLE_UART_SUPPORT */

#ifdef __cplusplus
}
#endif

#endif /* __UART_SUPPORT_H__ */
