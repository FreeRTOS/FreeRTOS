/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Implements UART console.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

#include <stdio.h>
#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** Console baud rate always using 115200. */


#define CONSOLE_BAUDRATE    115200
#define CONSOLE_EDBG 

#if defined CONSOLE_EDBG
#define CONSOLE_ON_USART
#else
#define CONSOLE_ON_UART
#endif

#if defined CONSOLE_ON_UART
#ifdef SSC_AUDIO
/** Usart Hw interface used by the console (UART4). */
#warning Please use UART4 pins for debug consol as UART0 pins are used in SSC \
		audio for SAM V71 Xplained Ultra board
#define CONSOLE_UART       UART4

/** Pins description corresponding to Rxd,Txd, (UART pins) */
#define CONSOLE_PINS        {PINS_UART4}

#define CONSOLE_ID          ID_UART4
#else
/** Usart Hw interface used by the console (UART0). */
#define CONSOLE_UART       UART0

/** Pins description corresponding to Rxd,Txd, (UART pins) */
#define CONSOLE_PINS        {PINS_UART0}

#define CONSOLE_ID          ID_UART0

#endif
#endif

#if defined CONSOLE_ON_USART

/** USART1 pin RX */
#define PIN_USART1_RXD_DBG \
		{PIO_PA21A_RXD1, PIOA, ID_PIOA, PIO_PERIPH_A, PIO_DEFAULT}
/** USART1 pin TX */
#define PIN_USART1_TXD_DBG \
		{PIO_PB4D_TXD1, PIOB, ID_PIOB, PIO_PERIPH_D, PIO_DEFAULT}
#define PINS_USART1        PIN_USART1_TXD_DBG, PIN_USART1_RXD_DBG

/** Usart Hw interface used by the console (Usart0). */
#define CONSOLE_Usart      USART1

/** Pins description corresponding to Rxd,Txd, (Usart pins) */
#define CONSOLE_PINS      {PINS_USART1}

#define CONSOLE_ID        ID_USART1
#endif


/*----------------------------------------------------------------------------
 *        Variables
 *----------------------------------------------------------------------------*/

/** Is Console Initialized. */
static uint8_t _ucIsConsoleInitialized = 0;

/**
 * \brief Configures an USART peripheral with the specified parameters.
 *
 * \param baudrate  Baudrate at which the USART should operate (in Hz).
 * \param masterClock  Frequency of the system master clock (in Hz).
 */
extern void DBG_Configure( uint32_t baudrate, uint32_t masterClock)
{

	const Pin pPins[] = CONSOLE_PINS;
#if defined CONSOLE_ON_UART
	Uart *pUart = CONSOLE_UART;
	/* Configure PIO */
	PIO_Configure( pPins, PIO_LISTSIZE( pPins ) );
	
	// Reset & disable receiver and transmitter, disable interrupts
	pUart->UART_CR = UART_CR_RSTRX | UART_CR_RSTTX | UART_CR_RSTSTA;
	pUart->UART_IDR = 0xFFFFFFFF;
	PMC_EnablePeripheral(CONSOLE_ID);
	pUart->UART_BRGR = (masterClock / baudrate) / 16;
	// Configure mode register
	pUart->UART_MR 
			= (UART_MR_CHMODE_NORMAL | UART_MR_PAR_NO
					| UART_MR_BRSRCCK_PERIPH_CLK);
	// Enable receiver and transmitter
	pUart->UART_CR = UART_CR_RXEN | UART_CR_TXEN;
#endif

#if defined CONSOLE_ON_USART
	Usart *pUsart = CONSOLE_Usart;
	// Disable the MATRIX registers write protection
	MATRIX->MATRIX_WPMR  = MATRIX_WPMR_WPKEY_PASSWD;
	MATRIX->CCFG_SYSIO |= CCFG_SYSIO_SYSIO4;
  
	PIO_Configure( pPins, PIO_LISTSIZE( pPins ) );
	
	// Reset & disable receiver and transmitter, disable interrupts
	pUsart->US_CR = US_CR_RSTRX | US_CR_RSTTX | US_CR_RSTSTA;
	pUsart->US_IDR = 0xFFFFFFFF;
	PMC_EnablePeripheral(CONSOLE_ID);
	pUsart->US_BRGR = (masterClock / baudrate) / 16;
   
	// Configure mode register
	pUsart->US_MR 
			= (US_MR_USART_MODE_NORMAL | US_MR_PAR_NO| US_MR_USCLKS_MCK 
					| US_MR_CHRL_8_BIT);

	// Enable receiver and transmitter
	pUsart->US_CR = US_CR_RXEN | US_CR_TXEN;
#endif
	_ucIsConsoleInitialized = 1;

	/* Disable buffering for printf(). */
#if ( defined (__GNUC__) && !defined (__SAMBA__) )
	setvbuf(stdout, (char *)NULL, _IONBF, 0);
#endif
}

/**
 * \brief Outputs a character on the UART line.
 *
 * \note This function is synchronous (i.e. uses polling).
 * \param c  Character to send.
 */
extern void DBG_PutChar( uint8_t c )
{
#if defined CONSOLE_ON_UART
	Uart *pUart=CONSOLE_UART;
	if ( !_ucIsConsoleInitialized )
	{
		DBG_Configure(CONSOLE_BAUDRATE, BOARD_MCK);
	}
	// Wait for the transmitter to be ready
	while ((pUart->UART_SR & UART_SR_TXEMPTY) == 0);

	// Send character
	pUart->UART_THR = c;
	// Wait for the transfer to complete
	while ((pUart->UART_SR & UART_SR_TXEMPTY) == 0);
#endif

#if defined CONSOLE_ON_USART
	Usart *pUsart=CONSOLE_Usart;
	if ( !_ucIsConsoleInitialized )
	{
		DBG_Configure(CONSOLE_BAUDRATE, BOARD_MCK);
	}
	// Wait for the transmitter to be ready
	while ((pUsart->US_CSR & US_CSR_TXEMPTY) == 0);

	// Send character
	pUsart->US_THR = c;

	// Wait for the transfer to complete
	while ((pUsart->US_CSR & US_CSR_TXEMPTY) == 0);
#endif
}

/**
 * \brief Input a character from the UART line.
 *
 * \note This function is synchronous
 * \return character received.
 */
extern uint32_t DBG_GetChar( void )
{
#if defined CONSOLE_ON_UART
	Uart *pUart= CONSOLE_UART;

	if ( !_ucIsConsoleInitialized )
	{
		DBG_Configure(CONSOLE_BAUDRATE, BOARD_MCK);
	}

	while ((pUart->UART_SR & UART_SR_RXRDY) == 0);
	return pUart->UART_RHR;
#endif

#if defined CONSOLE_ON_USART
	Usart *pUsart= CONSOLE_Usart;

	if ( !_ucIsConsoleInitialized )
	{
		DBG_Configure(CONSOLE_BAUDRATE, BOARD_MCK);
	}

	while ((pUsart->US_CSR & US_CSR_RXRDY) == 0);
	return pUsart->US_RHR;
#endif
}

/**
 * \brief Check if there is Input from UART line.
 *
 * \return true if there is Input.
 */
extern uint32_t DBG_IsRxReady( void )
{
#if defined CONSOLE_ON_UART
	Uart *pUart=CONSOLE_UART;

	if ( !_ucIsConsoleInitialized )
	{
		DBG_Configure( CONSOLE_BAUDRATE, BOARD_MCK );
	}
	return (pUart->UART_SR & UART_SR_RXRDY);
#endif

#if defined CONSOLE_ON_USART
	Usart *pUsart=CONSOLE_Usart;

	if ( !_ucIsConsoleInitialized )
	{
		DBG_Configure( CONSOLE_BAUDRATE, BOARD_MCK );
	}

	return (pUsart->US_CSR & US_CSR_RXRDY);
#endif
}

/**
 *  Displays the content of the given frame on the UART0.
 *
 *  \param pucFrame Pointer to the frame to dump.
 *  \param dwSize   Buffer size in bytes.
 */
extern void DBG_DumpFrame( uint8_t* pucFrame, uint32_t dwSize )
{
	uint32_t dw;

	for ( dw=0; dw < dwSize; dw++ )
	{
		printf( "%02X ", pucFrame[dw] );
	}

	printf( "\n\r" );
}

/**
 *  Displays the content of the given buffer on the UART0.
 *
 *  \param pucBuffer  Pointer to the buffer to dump.
 *  \param dwSize     Buffer size in bytes.
 *  \param dwAddress  Start address to display
 */
extern void DBG_DumpMemory( uint8_t* pucBuffer, uint32_t dwSize, 
				uint32_t dwAddress )
{
	uint32_t i;
	uint32_t j;
	uint32_t dwLastLineStart;
	uint8_t* pucTmp;

	for (i=0; i < (dwSize / 16); i++ )
	{
		printf( "0x%08X: ", (unsigned int)(dwAddress + (i*16)));
		pucTmp = (uint8_t*)&pucBuffer[i*16];

		for (j=0; j < 4; j++)
		{
			printf( "%02X%02X%02X%02X ",
					pucTmp[0], pucTmp[1], pucTmp[2], pucTmp[3]);
			pucTmp += 4;
		}

		pucTmp=(uint8_t*)&pucBuffer[i*16];

		for (j=0; j < 16; j++)
		{
			DBG_PutChar( *pucTmp++);
		}

		printf( "\n\r" );
	}

	if ( (dwSize%16) != 0 )
	{
		dwLastLineStart=dwSize - (dwSize%16);

		printf( "0x%08X: ", (unsigned int)(dwAddress + dwLastLineStart));
		for (j=dwLastLineStart; j < dwLastLineStart+16; j++)
		{
			if ( (j!=dwLastLineStart) && (j%4 == 0) )
			{
				printf( " " );
			}

			if ( j < dwSize )
			{
				printf( "%02X", pucBuffer[j] );
			}
			else
			{
				printf("  ");
			}
		}

		printf( " " );
		for (j=dwLastLineStart; j < dwSize; j++)
		{
			DBG_PutChar( pucBuffer[j] );
		}

		printf( "\n\r" );
	}
}

/**
 * Reads an integer
 *
 * \param pdwValue  Pointer to a integer variable to contain the input value.
 *
 * \return success(1) or failure(0)
 */
extern uint32_t DBG_GetInteger( int32_t* pdwValue )
{
	uint8_t ucKey;
	uint8_t ucNum = 0;
	int32_t dwValue = 0;
	int32_t sign = 1;

	while (1)
	{
		ucKey=DBG_GetChar();
		DBG_PutChar( ucKey );

		if (((ucKey == '-') || (ucKey == '+')) && (ucNum == 0))
		{
			if (ucKey == '-')
			{
				sign = -1;
			}
			else
			{
				sign = 1;
			}
			ucNum++;
		}
		else
		{
			if (ucKey >= '0' && ucKey <= '9')
			{
				dwValue = (dwValue * 10) + (ucKey - '0');
				ucNum++;
			}
			else
			{
				if (ucKey == 0x0D || ucKey == ' ')
				{
					if ( ucNum == 0 )
					{
						printf("\n\rWrite a number and press ENTER or SPACE!\n\r");
						return 0;
					}
					else
					{
						printf( "\n\r" );
						*pdwValue = dwValue * sign;

						return 1;
					}
				}
				else
				{
					printf("\n\r'%c' not a number or sign(+/-)!\n\r", ucKey);
					return 0;
				}
			}
		}
	}
}

/**
 * Reads an integer and check the value
 *
 * \param pdwValue  Pointer to a integer variable to contain the input value.
 * \param dwMin     Minimum value
 * \param dwMax     Maximum value
 *
 * \return success(1) or failure(0)
 */
extern uint32_t DBG_GetIntegerMinMax(int32_t* pdwValue, int32_t dwMin,
				int32_t dwMax)
{
	int32_t dwValue = 0;

	if ( DBG_GetInteger( &dwValue ) == 0 )
	{
		return 0;
	}

	if ( dwValue < dwMin || dwValue > dwMax )
	{
		printf( "\n\rThe number have to be between %d and %d\n\r",
				(int)dwMin, (int)dwMax );

		return 0;
	}

	printf( "\n\r" );

	*pdwValue = dwValue;

	return 1;
}

/**
 *  Reads an hexadecimal number
 *
 *  \param pdwValue  Pointer to the uint32_t variable to contain the input value.
 */
extern uint32_t DBG_GetHexa32( uint32_t* pdwValue )
{
	uint8_t ucKey;
	uint32_t dw = 0;
	uint32_t dwValue = 0;

	for ( dw=0; dw < 8; dw++ )
	{
		ucKey = DBG_GetChar();
		DBG_PutChar( ucKey );

		if ( ucKey >= '0' &&  ucKey <= '9' )
		{
			dwValue = (dwValue * 16) + (ucKey - '0');
		}
		else
		{
			if ( ucKey >= 'A' &&  ucKey <= 'F' )
			{
				dwValue = (dwValue * 16) + (ucKey - 'A' + 10);
			}
			else
			{
				if ( ucKey >= 'a' &&  ucKey <= 'f' )
				{
					dwValue = (dwValue * 16) + (ucKey - 'a' + 10);
				}
				else
				{
					printf( "\n\rIt is not a hexadecimal character!\n\r" );

					return 0;
				}
			}
		}
	}

	printf("\n\r" );
	*pdwValue = dwValue;

	return 1;
}

#if defined __ICCARM__ /* IAR Ewarm 5.41+ */
/**
 * \brief Outputs a character on the UART.
 *
 * \param c  Character to output.
 *
 * \return The character that was output.
 */
extern WEAK signed int putchar( signed int c )
{
	DBG_PutChar( c );

	return c;
}

#endif  // defined __ICCARM__
extern WEAK int puts(const char *ptr )
{

	for (; *ptr != 0; ptr++ )
	{
		DBG_PutChar( *ptr );
	}

	return 0;

}

extern WEAK char * gets(char *ptr)
{
	uint8_t ch = 0;
	while (ch != '\r' )
	{
		ch = DBG_GetChar();
		DBG_PutChar( ch );
		*(ptr++) = ch;
	}
	*ptr = '\0';
	return 0;

}


