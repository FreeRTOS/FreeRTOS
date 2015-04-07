/**********************************************************************
* $Id$		debug_frmwrk.c		2011-06-02
*//**
* @file		debug_frmwrk.c
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
/** @addtogroup DEBUG_FRMWRK
 * @{
 */

#ifndef _DEBUG_FRMWRK_
#define _DEBUG_FRMWRK_

/* Includes ------------------------------------------------------------------- */
#include "debug_frmwrk.h"
#include "lpc18xx_scu.h"
#include <stdarg.h>
#include <stdio.h>

#ifdef CDC_DEBUG_MESSEGES
#include "usbhw.h"
#include "cdcuser.h"
#include "CDCdemo.h"
#include "lpc18xx_utils.h"
#include <string.h>
#endif

/* Debug framework */

void (*_db_msg)(LPC_USARTn_Type *UARTx, const void *s);
void (*_db_msg_)(LPC_USARTn_Type *UARTx, const void *s);
void (*_db_char)(LPC_USARTn_Type *UARTx, uint8_t ch);
void (*_db_dec)(LPC_USARTn_Type *UARTx, uint8_t decn);
void (*_db_dec_16)(LPC_USARTn_Type *UARTx, uint16_t decn);
void (*_db_dec_32)(LPC_USARTn_Type *UARTx, uint32_t decn);
void (*_db_hex)(LPC_USARTn_Type *UARTx, uint8_t hexn);
void (*_db_hex_16)(LPC_USARTn_Type *UARTx, uint16_t hexn);
void (*_db_hex_32)(LPC_USARTn_Type *UARTx, uint32_t hexn);
uint8_t (*_db_get_char)(LPC_USARTn_Type *UARTx);



/*********************************************************************//**
 * @brief		Puts a character to UART port
 * @param[in]	UARTx	Pointer to UART peripheral
 * @param[in]	ch		Character to put
 * @return		None
 **********************************************************************/
void UARTPutChar (LPC_USARTn_Type *UARTx, uint8_t ch)
{
	UART_Send(UARTx, &ch, 1, BLOCKING);
}


/*********************************************************************//**
 * @brief		Get a character to UART port
 * @param[in]	UARTx	Pointer to UART peripheral
 * @return		character value that returned
 **********************************************************************/
uint8_t UARTGetChar (LPC_USARTn_Type *UARTx)
{
	uint8_t tmp = 0;
	UART_Receive(UARTx, &tmp, 1, BLOCKING);
	return(tmp);
}


/*********************************************************************//**
 * @brief		Puts a string to UART port
 * @param[in]	UARTx 	Pointer to UART peripheral
 * @param[in]	str 	string to put
 * @return		None
 **********************************************************************/
void UARTPuts(LPC_USARTn_Type *UARTx, const void *str)
{
#ifdef CDC_DEBUG_MESSEGES
	int num_of_bytes=0;
	num_of_bytes = strlen(str);
	timer_delay_us(num_of_bytes);
		
	USB_WriteEP (CDC_DEP_IN, (unsigned char *)str, num_of_bytes);
#else
	uint8_t *s = (uint8_t *) str;

	while (*s)
	{
		UARTPutChar(UARTx, *s++);
	}
#endif	
}


/*********************************************************************//**
 * @brief		Puts a string to UART port and print new line
 * @param[in]	UARTx	Pointer to UART peripheral
 * @param[in]	str		String to put
 * @return		None
 **********************************************************************/
void UARTPuts_(LPC_USARTn_Type *UARTx, const void *str)
{
	UARTPuts (UARTx, str);
	UARTPuts (UARTx, "\n\r");
}


/*********************************************************************//**
 * @brief		Puts a decimal number to UART port
 * @param[in]	UARTx	Pointer to UART peripheral
 * @param[in]	decnum	Decimal number (8-bit long)
 * @return		None
 **********************************************************************/
void UARTPutDec(LPC_USARTn_Type *UARTx, uint8_t decnum)
{
	uint8_t c1=decnum%10;
	uint8_t c2=(decnum/10)%10;
	uint8_t c3=(decnum/100)%10;
	UARTPutChar(UARTx, '0'+c3);
	UARTPutChar(UARTx, '0'+c2);
	UARTPutChar(UARTx, '0'+c1);
}

/*********************************************************************//**
 * @brief		Puts a decimal number to UART port
 * @param[in]	UARTx	Pointer to UART peripheral
 * @param[in]	decnum	Decimal number (8-bit long)
 * @return		None
 **********************************************************************/
void UARTPutDec16(LPC_USARTn_Type *UARTx, uint16_t decnum)
{
	uint8_t c1=decnum%10;
	uint8_t c2=(decnum/10)%10;
	uint8_t c3=(decnum/100)%10;
	uint8_t c4=(decnum/1000)%10;
	uint8_t c5=(decnum/10000)%10;
	UARTPutChar(UARTx, '0'+c5);
	UARTPutChar(UARTx, '0'+c4);
	UARTPutChar(UARTx, '0'+c3);
	UARTPutChar(UARTx, '0'+c2);
	UARTPutChar(UARTx, '0'+c1);
}

/*********************************************************************//**
 * @brief		Puts a decimal number to UART port
 * @param[in]	UARTx	Pointer to UART peripheral
 * @param[in]	decnum	Decimal number (8-bit long)
 * @return		None
 **********************************************************************/
void UARTPutDec32(LPC_USARTn_Type *UARTx, uint32_t decnum)
{
	uint8_t c1=decnum%10;
	uint8_t c2=(decnum/10)%10;
	uint8_t c3=(decnum/100)%10;
	uint8_t c4=(decnum/1000)%10;
	uint8_t c5=(decnum/10000)%10;
	uint8_t c6=(decnum/100000)%10;
	uint8_t c7=(decnum/1000000)%10;
	uint8_t c8=(decnum/10000000)%10;
	uint8_t c9=(decnum/100000000)%10;
	uint8_t c10=(decnum/1000000000)%10;
	UARTPutChar(UARTx, '0'+c10);
	UARTPutChar(UARTx, '0'+c9);
	UARTPutChar(UARTx, '0'+c8);
	UARTPutChar(UARTx, '0'+c7);
	UARTPutChar(UARTx, '0'+c6);
	UARTPutChar(UARTx, '0'+c5);
	UARTPutChar(UARTx, '0'+c4);
	UARTPutChar(UARTx, '0'+c3);
	UARTPutChar(UARTx, '0'+c2);
	UARTPutChar(UARTx, '0'+c1);
}

/*********************************************************************//**
 * @brief		Puts a hex number to UART port
 * @param[in]	UARTx	Pointer to UART peripheral
 * @param[in]	hexnum	Hex number (8-bit long)
 * @return		None
 **********************************************************************/
void UARTPutHex (LPC_USARTn_Type *UARTx, uint8_t hexnum)
{
	uint8_t nibble, i;

	UARTPuts(UARTx, "0x");
	i = 1;
	do {
		nibble = (hexnum >> (4*i)) & 0x0F;
		UARTPutChar(UARTx, (nibble > 9) ? ('A' + nibble - 10) : ('0' + nibble));
	} while (i--);
}


/*********************************************************************//**
 * @brief		Puts a hex number to UART port
 * @param[in]	UARTx	Pointer to UART peripheral
 * @param[in]	hexnum	Hex number (16-bit long)
 * @return		None
 **********************************************************************/
void UARTPutHex16 (LPC_USARTn_Type *UARTx, uint16_t hexnum)
{
	uint8_t nibble, i;

	UARTPuts(UARTx, "0x");
	i = 3;
	do {
		nibble = (hexnum >> (4*i)) & 0x0F;
		UARTPutChar(UARTx, (nibble > 9) ? ('A' + nibble - 10) : ('0' + nibble));
	} while (i--);
}

/*********************************************************************//**
 * @brief		Puts a hex number to UART port
 * @param[in]	UARTx	Pointer to UART peripheral
 * @param[in]	hexnum	Hex number (32-bit long)
 * @return		None
 **********************************************************************/
void UARTPutHex32 (LPC_USARTn_Type *UARTx, uint32_t hexnum)
{
	uint8_t nibble, i;

	UARTPuts(UARTx, "0x");
	i = 7;
	do {
		nibble = (hexnum >> (4*i)) & 0x0F;
		UARTPutChar(UARTx, (nibble > 9) ? ('A' + nibble - 10) : ('0' + nibble));
	} while (i--);
}

/*********************************************************************//**
 * @brief		print function that supports format as same as printf()
 * 				function of <stdio.h> library
 * @param[in]	format formated string to be print
 * @return		None
 **********************************************************************/
void  lpc_printf (const  char *format, ...)
{
    char  buffer[512 + 1];
    va_list vArgs;
    va_start(vArgs, format);
    vsprintf((char *)buffer, (char const *)format, vArgs);
    va_end(vArgs);

    _DBG(buffer);
}

/*********************************************************************//**
 * @brief		Initialize Debug frame work through initializing UART port
 * @param[in]	None
 * @return		None
 **********************************************************************/
void debug_frmwrk_init(void)
{
#ifdef UART_DEBUG_MESSEGES

	UART_CFG_Type UARTConfigStruct;

#if (USED_UART_DEBUG_PORT==0)
	/*
	 * Initialize UART0 pin connect	NGX board
	 */
	scu_pinmux(0xF ,10 , MD_PDN|MD_EZI, FUNC1); 			// P6.4 UART0_TXD
	scu_pinmux(0xF ,11 , MD_PDN|MD_EZI, FUNC1); 			// P6.5 UART0_RXD
#elif (USED_UART_DEBUG_PORT==1)
	/*
	 * Initialize UART1 pin connect
	 */
	scu_pinmux(0x1 ,13 , MD_PDN, FUNC1); 				// PC.13 : UART1_TXD
	scu_pinmux(0x1 ,14 , MD_PLN|MD_EZI|MD_ZI, FUNC1); 	// PC.14 : UART1_RXD
#endif

	/* Initialize UART Configuration parameter structure to default state:
	 * Baudrate = 9600bps
	 * 8 data bit
	 * 1 Stop bit
	 * None parity
	 */
	UART_ConfigStructInit(&UARTConfigStruct);

	// Initialize DEBUG_UART_PORT peripheral with given to corresponding parameter
	UART_Init((LPC_USARTn_Type*)DEBUG_UART_PORT, &UARTConfigStruct);

	// Enable UART Transmit
	UART_TxCmd((LPC_USARTn_Type*)DEBUG_UART_PORT, ENABLE);
#endif
#ifdef CDC_DEBUG_MESSEGES
	CDC_init();		//wait for usb enumeration

#endif

	_db_msg	= UARTPuts;
	_db_msg_ = UARTPuts_;
	_db_char = UARTPutChar;
	_db_hex = UARTPutHex;
	_db_hex_16 = UARTPutHex16;
	_db_hex_32 = UARTPutHex32;
	_db_dec = UARTPutDec;
	_db_dec_16 = UARTPutDec16;
	_db_dec_32 = UARTPutDec32;
	_db_get_char = UARTGetChar;
}

#endif /* _DEBUG_FRMWRK_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
