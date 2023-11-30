/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
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
 * Implementation of USART (Universal Synchronous Asynchronous Receiver 
 * Transmitter) controller.
 *
 */
/*------------------------------------------------------------------------------
 *         Headers
 *-----------------------------------------------------------------------------*/
#include "chip.h"

#include <assert.h>
#include <string.h>

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/


/*------------------------------------------------------------------------------
 *         Exported functions
 *-----------------------------------------------------------------------------*/

/**
 * \brief Configures an USART baudrate.
 *
 *
 *  \param pUsart  Pointer to the USART peripheral to configure.
 *  \param baudrate  Baudrate at which the USART should operate (in Hz).
 *  \param masterClock  Frequency of the system master clock (in Hz).
 */
void USART_SetBaudrate(Usart *pUsart,
					uint8_t OverSamp,
					uint32_t baudrate,
					uint32_t masterClock)
{
	unsigned int CD, FP, BaudError, ActualBaudRate;
	/* Configure baudrate*/  
	BaudError = 10;
	OverSamp = 0;

		/*Asynchronous*/
		if ((pUsart->US_MR & US_MR_SYNC) == 0)
		{
			/* 7816 mode */
			if( ((pUsart->US_MR & US_MR_USART_MODE_IS07816_T_0) 
					== US_MR_USART_MODE_IS07816_T_0 )
				|| ((pUsart->US_MR & US_MR_USART_MODE_IS07816_T_1) 
					== US_MR_USART_MODE_IS07816_T_1 ))
			{
				/* Define the baud rate divisor register */
				/* CD  = MCK / SCK */
				/* SCK = FIDI x BAUD = 372 x 9600 */
				/* BOARD_MCK */
				/* CD = MCK/(FIDI x BAUD) = 150000000 / (372x9600) = 42 */
				CD = masterClock / (pUsart->US_FIDI * baudrate);
				FP = 0;
			}
			else{
			while (BaudError > 5) {
				CD = (masterClock / (baudrate * 8 *( 2 - OverSamp)));
				FP = ((masterClock / (baudrate * ( 2 - OverSamp)) ) - CD * 8);
				ActualBaudRate = (masterClock/(CD * 8 + FP)) / ( 2 - OverSamp);
				BaudError = (100 - ((baudrate * 100 / ActualBaudRate)));

				if (BaudError > 5) 
				{
					OverSamp++;
					if(OverSamp >= 2) 
					{
						TRACE_ERROR("Canont set this baudrate \n\r");
								break;
					}
				}
			}
			}
		}
		/*Synchronous SPI  */
		if((pUsart->US_MR & US_MR_USART_MODE_SPI_MASTER) 
				== US_MR_USART_MODE_SPI_MASTER
			|| ((pUsart->US_MR & US_MR_SYNC) == US_MR_SYNC) )
		{
			if( (pUsart->US_MR & US_MR_USCLKS_Msk) == US_MR_USCLKS_MCK)
			{
				CD = masterClock / baudrate;
				FP = ((masterClock / baudrate) - CD);
			}
		}
		
	pUsart->US_BRGR = ( US_BRGR_CD(CD) | US_BRGR_FP(FP));
	
	/* Configure OverSamp*/
	pUsart->US_MR |= (OverSamp << 19);
}

/**
 * \brief Configures an USART peripheral with the specified parameters.
 *
 *
 *  \param pUsart  Pointer to the USART peripheral to configure.
 *  \param mode  Desired value for the USART mode register (see the datasheet).
 *  \param baudrate  Baudrate at which the USART should operate (in Hz).
 *  \param masterClock  Frequency of the system master clock (in Hz).
 */
void USART_Configure(Usart *pUsart,
		uint32_t mode,
		uint32_t baudrate,
		uint32_t masterClock)
{

	/* Reset and disable receiver & transmitter*/
	pUsart->US_CR = US_CR_RSTRX | US_CR_RSTTX
		| US_CR_RXDIS | US_CR_TXDIS | US_CR_RSTSTA;
	pUsart->US_IDR = 0xFFFFFFFF;

	pUsart->US_MR = mode; 
	/* Configure baudrate*/  
	USART_SetBaudrate(pUsart, 0, baudrate, masterClock);

	/* Enable receiver and transmitter */
	pUsart->US_CR = US_CR_RXEN | US_CR_TXEN;

	/* Disable buffering for printf(). */
#if ( defined (__GNUC__) && !defined (__SAMBA__) )
	setvbuf(stdout, (char *)NULL, _IONBF, 0);
#endif
 
}
/**
 * \brief Enables or disables the transmitter of an USART peripheral.
 *
 *
 * \param pUsart  Pointer to an USART peripheral
 * \param enabled  If true, the transmitter is enabled; otherwise it is
 * disabled.
 */
void USART_SetTransmitterEnabled(Usart *pUsart, uint8_t enabled)
{
	if (enabled) {
		pUsart->US_CR = US_CR_TXEN;
	} else {
		pUsart->US_CR = US_CR_TXDIS;
	}
}

/**
 * \brief Disables the Receiver of an USART peripheral.
 *
 * \param pUsart  Pointer to an USART peripheral
 */
void USART_DisableRx(Usart *pUsart)
{

  pUsart->US_CR = US_CR_RXDIS;
}

/**
 * \brief Disables the transmitter of an USART peripheral.
 *
 * \param pUsart  Pointer to an USART peripheral
 */
void USART_DisableTx(Usart *pUsart)
{
	 pUsart->US_CR =  US_CR_TXDIS;
}

/**
 * \brief Enables the Receiver of an USART peripheral.
 *
 * \param pUsart  Pointer to an USART peripheral
 */
void USART_EnableRx(Usart *pUsart)
{

  pUsart->US_CR = US_CR_RXEN;
}

/**
 * \brief Enables the transmitter of an USART peripheral
 *
 * \param pUsart  Pointer to an USART peripheral
 */
void USART_EnableTx(Usart *pUsart)
{
	 pUsart->US_CR =  US_CR_TXEN;
}
/**
 * \brief Resets or disables the Receiver of an USART peripheral.
 *
 *
 * \param pUsart  Pointer to an USART peripheral
 */
void USART_ResetRx(Usart *pUsart)
{

  pUsart->US_CR = US_CR_RSTRX | US_CR_RXDIS;
}

/**
 * \brief resets and disables the transmitter of an USART peripheral.
 *
 *
 * \param pUsart  Pointer to an USART peripheral
 */
void USART_ResetTx(Usart *pUsart)
{
	 pUsart->US_CR =  US_CR_RSTTX | US_CR_TXDIS;
}
/**
 * \brief Enables or disables the receiver of an USART peripheral
 *
 *
 * \param pUsart  Pointer to an USART peripheral
 * \param enabled  If true, the receiver is enabled; otherwise it is disabled.
 */
void USART_SetReceiverEnabled(Usart *pUsart, uint8_t enabled)
{
	if (enabled) {
		pUsart->US_CR = US_CR_RXEN;
	} else {
		pUsart->US_CR = US_CR_RXDIS;
	}
}

/**
 * \brief Enables or disables the Request To Send (RTS) of an USART peripheral
 *
 *
 * \param pUsart  Pointer to an USART peripheral
 * \param enabled  If true, the RTS is enabled (0); otherwise it is disabled.
 */
void USART_SetRTSEnabled( Usart *pUsart, uint8_t enabled)
{
	if (enabled) {
		pUsart->US_CR = US_CR_RTSEN;
	} else {
		pUsart->US_CR = US_CR_RTSDIS;
	}
}

/**
 * \brief Sends one packet of data through the specified USART peripheral. This
 * function operates synchronously, so it only returns when the data has been
 * actually sent.
 *
 *
 * \param pUsart  Pointer to an USART peripheral.
 * \param data  Data to send including 9nth bit and sync field if necessary (in
 *        the same format as the US_THR register in the datasheet).
 * \param timeOut  Time out value (0 = no timeout).
 */
void USART_Write( Usart *pUsart, uint16_t data, volatile uint32_t timeOut)
{
	if (timeOut == 0) {
		while ((pUsart->US_CSR & US_CSR_TXEMPTY) == 0);
	} else {
		while ((pUsart->US_CSR & US_CSR_TXEMPTY) == 0) {
			if (timeOut == 0) {
				TRACE_ERROR("USART_Write: Timed out.\n\r");
				return;
			}
			timeOut--;
		}
	}
	pUsart->US_THR = data;
}

/**
 * \brief  Reads and return a packet of data on the specified USART peripheral. 
 * This function operates asynchronously, so it waits until some data has been
 * received.
 *
 * \param pUsart  Pointer to an USART peripheral.
 * \param timeOut  Time out value (0 -> no timeout).
 */
uint16_t USART_Read( Usart *pUsart, volatile uint32_t timeOut)
{
	if (timeOut == 0) {
		while ((pUsart->US_CSR & US_CSR_RXRDY) == 0);
	} else {
		while ((pUsart->US_CSR & US_CSR_RXRDY) == 0) {
			if (timeOut == 0) {
				TRACE_ERROR( "USART_Read: Timed out.\n\r" ) ;
				return 0;
			}
			timeOut--;
		}
	}
	return pUsart->US_RHR;
}

/**
 * \brief  Returns 1 if some data has been received and can be read from an 
 * USART; otherwise returns 0.
 *
 * \param pUsart  Pointer to an USART instance.
 */
uint8_t USART_IsDataAvailable(Usart *pUsart)
{
	if ((pUsart->US_CSR & US_CSR_RXRDY) != 0) {
		return 1;
	} else {
		return 0;
	}
}

/**
 * \brief  Sends one packet of data through the specified USART peripheral. This
 * function operates synchronously, so it only returns when the data has been
 * actually sent.
 *
 * \param pUsart  Pointer to an USART peripheral.
 * \param c  Character to send
 */
void USART_PutChar( Usart *pUsart, uint8_t c)
{
	/* Wait for the transmitter to be ready*/
	while ((pUsart->US_CSR & US_CSR_TXEMPTY) == 0);

	/* Send character*/
	pUsart->US_THR = c;

	/* Wait for the transfer to complete*/
	while ((pUsart->US_CSR & US_CSR_TXEMPTY) == 0);
}

/**
 * \brief   Return 1 if a character can be read in USART
 * \param pUsart  Pointer to an USART peripheral.
 */
uint32_t USART_IsRxReady(Usart *pUsart)
{
	return (pUsart->US_CSR & US_CSR_RXRDY);
}

/**
 * \brief   Get present status
 * \param pUsart  Pointer to an USART peripheral.
 */
uint32_t USART_GetStatus(Usart *pUsart)
{
	return pUsart->US_CSR;
}

/**
 * \brief   Enable interrupt
 * \param pUsart  Pointer to an USART peripheral.
 * \param mode  Interrupt mode.
 */
void USART_EnableIt(Usart *pUsart,uint32_t mode)
{
	pUsart->US_IER = mode;
}

/**
 * \brief   Disable interrupt
 * \param pUsart  Pointer to an USART peripheral.
 * \param mode  Interrupt mode.
 */
void USART_DisableIt(Usart *pUsart,uint32_t mode)
{
	pUsart->US_IDR = mode;
}

/**
 * \brief   Return interrupt mask
 * \param pUsart  Pointer to an USART peripheral.
 */
uint32_t USART_GetItMask(Usart *pUsart)
{
	return pUsart->US_IMR;
}

/**
 * \brief  Reads and returns a character from the USART.
 *
 * \note This function is synchronous (i.e. uses polling).
 * \param pUsart  Pointer to an USART peripheral.
 * \return Character received.
 */
uint8_t USART_GetChar(Usart *pUsart)
{
	while ((pUsart->US_CSR & US_CSR_RXRDY) == 0);
	return pUsart->US_RHR;
}

/**
 * \brief  Enable Rx Timeout for USART.
 *
 * \param pUsart  Pointer to an USART peripheral.
 * \param Timeout  Timeout value
 * \return None
 */
void USART_EnableRecvTimeOut(Usart *pUsart, uint32_t Timeout)
{
	if( Timeout <= MAX_RX_TIMEOUT ) {
		pUsart->US_RTOR = Timeout;
	} else if( Timeout == 0) {
		TRACE_DEBUG("Timeout is disabled\n\r");
	} else {
		TRACE_INFO_WP("\n\r");
		TRACE_FATAL("Timeout value is out of range\n\r");
	}
}

/**
 * \brief  Enable Tx Timeout for USART.
 *
 * \param pUsart  Pointer to an USART peripheral.
 * \param TimeGaurd  TimeGaurd value
 * \return None
 */
void USART_EnableTxTimeGaurd(Usart *pUsart, uint32_t TimeGaurd)
{
	if( ( (pUsart->US_MR & US_MR_USART_MODE_LON ) && TimeGaurd <= 16777215) || 
			((pUsart->US_MR & US_MR_USART_MODE_LON ) && TimeGaurd <= 255) ) {
	  pUsart->US_TTGR = TimeGaurd;
	} else {
	  TRACE_ERROR(" TimeGaurd Value is too big for mode");
	}
}
/**
 * \brief  Acknowledge Rx timeout and sets to Idle or periodic repetitive state.
 *
 * \param pUsart  Pointer to an USART peripheral.
 * \param Periodic  If timeout is periodic or should wait for new char
 * \return None
 */
void USART_AcknowledgeRxTimeOut(Usart *pUsart, uint8_t Periodic)
{
	if(Periodic) {
		pUsart->US_CR = US_CR_RETTO;     // Restart timeout timer
	} else {
		// Puts USARt in Idle mode and waits for a char after timeout
		pUsart->US_CR = US_CR_STTTO; 
	}
}
