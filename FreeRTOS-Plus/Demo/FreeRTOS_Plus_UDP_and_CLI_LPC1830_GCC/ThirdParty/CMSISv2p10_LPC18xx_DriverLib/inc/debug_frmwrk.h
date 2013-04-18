/**********************************************************************
* $Id$		debug_frmwrk.h			2011-06-02
*//**
* @file		debug_frmwrk.h
* @brief	Contains some utilities that used for debugging through UART
* @version	1.0
* @date		02. June. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
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

/* Peripheral group ----------------------------------------------------------- */
/** @defgroup DEBUG_FRMWRK DEBUG FRAMEWORK
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef DEBUG_FRMWRK_H_
#define DEBUG_FRMWRK_H_

/* Includes ------------------------------------------------------------------- */
#include "lpc18xx_uart.h"

#define VCOM_DEBUG_MESSEGES
//#define UART_DEBUG_MESSEGES

#define USED_UART_DEBUG_PORT	1

#if (USED_UART_DEBUG_PORT==0)
#define DEBUG_UART_PORT	LPC_UART0
#elif (USED_UART_DEBUG_PORT==1)
#define DEBUG_UART_PORT	LPC_UART1
#endif

#define _DBG(x)	 	_db_msg((LPC_USARTn_Type*)DEBUG_UART_PORT, x)
#define _DBG_(x)	_db_msg_((LPC_USARTn_Type*)DEBUG_UART_PORT, x)
#define _DBC(x)	 	_db_char((LPC_USARTn_Type*)DEBUG_UART_PORT, x)
#define _DBD(x)	 	_db_dec((LPC_USARTn_Type*)DEBUG_UART_PORT, x)
#define _DBD16(x)	 _db_dec_16((LPC_USARTn_Type*)DEBUG_UART_PORT, x)
#define _DBD32(x)	 _db_dec_32((LPC_USARTn_Type*)DEBUG_UART_PORT, x)
#define _DBH(x)	 	_db_hex((LPC_USARTn_Type*)DEBUG_UART_PORT, x)
#define _DBH16(x)	 _db_hex_16((LPC_USARTn_Type*)DEBUG_UART_PORT, x)
#define _DBH32(x)	 _db_hex_32((LPC_USARTn_Type*)DEBUG_UART_PORT, x)
#define _DG			_db_get_char((LPC_USARTn_Type*)DEBUG_UART_PORT)
void  lpc_printf (const  char *format, ...);

extern void (*_db_msg)(LPC_USARTn_Type *UARTx, const void *s);
extern void (*_db_msg_)(LPC_USARTn_Type *UARTx, const void *s);
extern void (*_db_char)(LPC_USARTn_Type *UARTx, uint8_t ch);
extern void (*_db_dec)(LPC_USARTn_Type *UARTx, uint8_t decn);
extern void (*_db_dec_16)(LPC_USARTn_Type *UARTx, uint16_t decn);
extern void (*_db_dec_32)(LPC_USARTn_Type *UARTx, uint32_t decn);
extern void (*_db_hex)(LPC_USARTn_Type *UARTx, uint8_t hexn);
extern void (*_db_hex_16)(LPC_USARTn_Type *UARTx, uint16_t hexn);
extern void (*_db_hex_32)(LPC_USARTn_Type *UARTx, uint32_t hexn);
extern uint8_t (*_db_get_char)(LPC_USARTn_Type *UARTx);

void UARTPutChar (LPC_USARTn_Type *UARTx, uint8_t ch);
void UARTPuts(LPC_USARTn_Type *UARTx, const void *str);
void UARTPuts_(LPC_USARTn_Type *UARTx, const void *str);
void UARTPutDec(LPC_USARTn_Type *UARTx, uint8_t decnum);
void UARTPutDec16(LPC_USARTn_Type *UARTx, uint16_t decnum);
void UARTPutDec32(LPC_USARTn_Type *UARTx, uint32_t decnum);
void UARTPutHex (LPC_USARTn_Type *UARTx, uint8_t hexnum);
void UARTPutHex16 (LPC_USARTn_Type *UARTx, uint16_t hexnum);
void UARTPutHex32 (LPC_USARTn_Type *UARTx, uint32_t hexnum);
uint8_t UARTGetChar (LPC_USARTn_Type *UARTx);
void debug_frmwrk_init(void);

#endif /* DEBUG_FRMWRK_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
