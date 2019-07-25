/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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
 * \section Purpose
 *
 * ISO 7816 driver
 *
 * \section Usage
 *
 * Explanation on the usage of the code made available through the header file.
 */

/*------------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

/*------------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/
/** Case for APDU commands*/
#define CASE1  1
#define CASE2  2
#define CASE3  3

/** Flip flop for send and receive char */
#define USART_SEND 0
#define USART_RECEIVE  1

#define USART7816BAUDRATE 9600
/*-----------------------------------------------------------------------------
 *          Internal variables
 *---------------------------------------------------------------------------*/
/** Variable for state of send and receive from USART */
static uint8_t StateUsartGlobal = USART_RECEIVE;
/** Pin reset master card */
static Pin st_pinIso7816RstMC;
static Usart *UsartIso;
static uint32_t UsartIsoId;

/*----------------------------------------------------------------------------
 *          Internal functions
 *----------------------------------------------------------------------------*/

/**
 * Get a character from ISO7816
 * \param pCharToReceive Pointer for store the received char
 * \return 0: if timeout else status of US_CSR
 */
static uint32_t ISO7816_GetChar( uint8_t *pCharToReceive )
{
	uint32_t status;
	uint32_t timeout=0;

	if( StateUsartGlobal == USART_SEND ) {
		while((UsartIso->US_CSR & US_CSR_TXEMPTY) == 0) {}
		UsartIso->US_CR = US_CR_RSTSTA | US_CR_RSTIT | US_CR_RSTNACK;
		StateUsartGlobal = USART_RECEIVE;
	}

	/* Wait USART ready for reception */
	while( ((UsartIso->US_CSR & US_CSR_RXRDY) == 0) ) {
		if(timeout++ > 12000 * (BOARD_MCK/1000000)) {
			TRACE_DEBUG("TimeOut\n\r");
			return( 0 );
		}
	}

	TRACE_DEBUG("T: %u\n\r", timeout);


	/* At least one complete character has been received and US_RHR has not 
	yet been read. */

	/* Get a char */
	*pCharToReceive = ((UsartIso->US_RHR) & 0xFF);

	status = (UsartIso->US_CSR&(US_CSR_OVRE | US_CSR_FRAME |
							US_CSR_PARE | US_CSR_TIMEOUT | US_CSR_NACK |
							(1<<10)));

	if (status != 0 ) {
		/* TRACE_DEBUG("R:0x%X\n\r", status); */
		TRACE_DEBUG("R:0x%X\n\r", UsartIso->US_CSR);
		TRACE_DEBUG("Nb:0x%X\n\r", UsartIso->US_NER );
		UsartIso->US_CR = US_CR_RSTSTA;
	}

	/* Return status */
	return( status );
}

/**
 * Send a char to ISO7816
 * \param CharToSend char to be send
 * \return status of US_CSR
 */
static uint32_t ISO7816_SendChar( uint8_t CharToSend )
{
	uint32_t status;

	if( StateUsartGlobal == USART_RECEIVE ) {
		UsartIso->US_CR = US_CR_RSTSTA | US_CR_RSTIT | US_CR_RSTNACK;
		StateUsartGlobal = USART_SEND;
	}

	/* Wait USART ready for transmit */
	while((UsartIso->US_CSR & US_CSR_TXRDY) == 0)  {}
	/* There is no character in the US_THR */

	/* Transmit a char */
	UsartIso->US_THR = CharToSend;

	status = (UsartIso->US_CSR & (US_CSR_OVRE | US_CSR_FRAME |
						US_CSR_PARE | US_CSR_TIMEOUT | US_CSR_NACK |
						(1<<10)));

	if (status != 0 ) {
		TRACE_DEBUG("E:0x%X\n\r", UsartIso->US_CSR);
		TRACE_DEBUG("Nb:0x%X\n\r", UsartIso->US_NER );
		UsartIso->US_CR = US_CR_RSTSTA;
	}

	/* Return status */
	return( status );
}


/**
 *  Iso 7816 ICC power on
 */
static void ISO7816_IccPowerOn( void )
{
	/* Set RESET Master Card */
	PIO_Set(&st_pinIso7816RstMC);
}

/*----------------------------------------------------------------------------
 *          Exported functions
 *----------------------------------------------------------------------------*/

/**
 *  Iso 7816 ICC power off
 */
void ISO7816_IccPowerOff( void )
{
	/* Clear RESET Master Card */
	PIO_Clear(&st_pinIso7816RstMC);
}

/**
 * Transfer Block TPDU T=0
 * \param pAPDU    APDU buffer
 * \param pMessage Message buffer
 * \param wLength  Block length
 * \return         Message index
 */
uint16_t ISO7816_XfrBlockTPDU_T0(const uint8_t *pAPDU,
									   uint8_t *pMessage,
									   uint16_t wLength )
{
	uint16_t NeNc;
	uint16_t indexApdu = 4;
	uint16_t indexMessage = 0;
	uint8_t SW1 = 0;
	uint8_t procByte = 0;
	uint8_t cmdCase;
	uint8_t ins;

	TRACE_DEBUG("pAPDU[0]=0x%X\n\r",pAPDU[0]);
	TRACE_DEBUG("pAPDU[1]=0x%X\n\r",pAPDU[1]);
	TRACE_DEBUG("pAPDU[2]=0x%X\n\r",pAPDU[2]);
	TRACE_DEBUG("pAPDU[3]=0x%X\n\r",pAPDU[3]);
	TRACE_DEBUG("pAPDU[4]=0x%X\n\r",pAPDU[4]);
	TRACE_DEBUG("wlength=%d\n\r",wLength);

	ISO7816_SendChar( pAPDU[0] ); /* CLA */
	ISO7816_SendChar( pAPDU[1] ); /* INS */
	ISO7816_SendChar( pAPDU[2] ); /* P1 */
	ISO7816_SendChar( pAPDU[3] ); /* P2 */
	ISO7816_SendChar( pAPDU[4] ); /* P3 */

	/* Handle the four structures of command APDU */
	indexApdu = 4;

	if( wLength == 4 ) {
		cmdCase = CASE1;
		NeNc = 0;
	} else if( wLength == 5) {
		cmdCase = CASE2;
		NeNc = pAPDU[4]; /* C5 */
		if (NeNc == 0) {
			NeNc = 256;
		}
	} else if( wLength == 6) {
		NeNc = pAPDU[4]; /* C5 */
		cmdCase = CASE3;
	} else if( wLength == 7) {
		NeNc = pAPDU[4]; /* C5 */
		if( NeNc == 0 ) {
			cmdCase = CASE2;
			NeNc = (pAPDU[5]<<8)+pAPDU[6];
		} else {
			cmdCase = CASE3;
		}
	} else {
		NeNc = pAPDU[4]; /* C5 */
		if( NeNc == 0 ) {
			cmdCase = CASE3;
			NeNc = (pAPDU[5]<<8)+pAPDU[6];
		} else {
			cmdCase = CASE3;
		}
	}

	TRACE_DEBUG("CASE=0x%X NeNc=0x%X\n\r", cmdCase, NeNc);

	/* Handle Procedure Bytes */
	do {
		ISO7816_GetChar(&procByte);
		ins = procByte ^ 0xff;
		/* Handle NULL */
		if ( procByte == ISO_NULL_VAL ) {
			TRACE_DEBUG("INS\n\r");
			continue;
		}
		/* Handle SW1 */
		else if ( ((procByte & 0xF0) ==0x60) || ((procByte & 0xF0) ==0x90) ) {
			TRACE_DEBUG("SW1\n\r");
			SW1 = 1;
		}
		/* Handle INS */
		else if ( pAPDU[1] == procByte) {
			TRACE_DEBUG("HdlINS\n\r");
			if (cmdCase == CASE2) {
				/* receive data from card */
				do {
					ISO7816_GetChar(&pMessage[indexMessage++]);
				} while( 0 != --NeNc );
			} else {
				 /* Send data */
				do {
					ISO7816_SendChar(pAPDU[indexApdu++]);
				} while( 0 != --NeNc );
			}
		}
		/* Handle INS ^ 0xff */
		else if ( pAPDU[1] == ins) {
			TRACE_DEBUG("HdlINS+\n\r");
			if (cmdCase == CASE2) {
				/* receive data from card */
				ISO7816_GetChar(&pMessage[indexMessage++]);
			} else {
				ISO7816_SendChar(pAPDU[indexApdu++]);
			}
			NeNc--;
		} else {
			/* ?? */
			TRACE_DEBUG("procByte=0x%X\n\r", procByte);
			break;
		}
	} while (NeNc != 0);

	/* Status Bytes */
	if (SW1 == 0) {
		ISO7816_GetChar(&pMessage[indexMessage++]); /* SW1 */
	} else {
		pMessage[indexMessage++] = procByte;
	}
	ISO7816_GetChar(&pMessage[indexMessage++]); /* SW2 */

	return( indexMessage );

}

/**
 *  Escape ISO7816
 */
void ISO7816_Escape( void )
{
	TRACE_DEBUG("For user, if needed\n\r");
}

/**
 *  Restart clock ISO7816
 */
void ISO7816_RestartClock( void )
{
	TRACE_DEBUG("ISO7816_RestartClock\n\r");
	UsartIso->US_BRGR = 13;
}

/**
 *  Stop clock ISO7816
 */
void ISO7816_StopClock( void )
{
	TRACE_DEBUG("ISO7816_StopClock\n\r");
	UsartIso->US_BRGR = 0;
}

/**
 *  T0 APDU
 */
void ISO7816_toAPDU( void )
{
	TRACE_DEBUG("ISO7816_toAPDU\n\r");
	TRACE_DEBUG("Not supported at this time\n\r");
}

/**
 * Answer To Reset (ATR)
 * \param pAtr    ATR buffer
 * \param pLength Pointer for store the ATR length
 */
void ISO7816_Datablock_ATR( uint8_t* pAtr, uint8_t* pLength )
{
	uint32_t i;
	uint32_t j;
	uint32_t y;

	*pLength = 0;

	/* Read ATR TS */
	ISO7816_GetChar(&pAtr[0]);
	/* Read ATR T0 */
	ISO7816_GetChar(&pAtr[1]);
	y = pAtr[1] & 0xF0;
	i = 2;

	/* Read ATR Ti */
	while (y) {
		if (y & 0x10) {  /* TA[i] */
			ISO7816_GetChar(&pAtr[i++]);
		}
		if (y & 0x20) {  /* TB[i] */
			ISO7816_GetChar(&pAtr[i++]);
		}
		if (y & 0x40) {  /* TC[i] */
			ISO7816_GetChar(&pAtr[i++]);
		}
		if (y & 0x80) {  /* TD[i] */
			ISO7816_GetChar(&pAtr[i]);
			y =  pAtr[i++] & 0xF0;
		} else {
			y = 0;
		}
	}

	/* Historical Bytes */
	y = pAtr[1] & 0x0F;
	for( j=0; j < y; j++ ) {
		ISO7816_GetChar(&pAtr[i++]);
	}

	*pLength = i;

}

/**
 * Set data rate and clock frequency
 * \param dwClockFrequency ICC clock frequency in KHz.
 * \param dwDataRate       ICC data rate in bpd
 */
void ISO7816_SetDataRateandClockFrequency( uint32_t dwClockFrequency, 
		uint32_t dwDataRate )
{
	uint8_t ClockFrequency;

	/* Define the baud rate divisor register */
	/* CD  = MCK / SCK */
	/* SCK = FIDI x BAUD = 372 x 9600 */
	/* BOARD_MCK */
	/* CD = MCK/(FIDI x BAUD) = 48000000 / (372x9600) = 13 */
	UsartIso->US_BRGR = BOARD_MCK / (dwClockFrequency*1000);

	ClockFrequency = BOARD_MCK / UsartIso->US_BRGR;

	UsartIso->US_FIDI = (ClockFrequency)/dwDataRate;

}

/**
 * Pin status for ISO7816 RESET
 * \return 1 if the Pin RstMC is high; otherwise 0.
 */
uint8_t ISO7816_StatusReset( void )
{
	return PIO_Get(&st_pinIso7816RstMC);
}

/**
 *  cold reset
 */
void ISO7816_cold_reset( void )
{
	volatile uint32_t i;

	/* tb: wait 400 cycles*/
	for( i=0; i<(120*(BOARD_MCK/1000000)); i++ ) {
	}

	UsartIso->US_RHR;
	UsartIso->US_CR = US_CR_RSTSTA | US_CR_RSTIT | US_CR_RSTNACK;

	ISO7816_IccPowerOn();
}

/**
 *  Warm reset
 */
void ISO7816_warm_reset( void )
{
	volatile uint32_t i;

	ISO7816_IccPowerOff();

	/* tb: wait 400 cycles */
	for( i=0; i<(120*(BOARD_MCK/1000000)); i++ ) {
	}

	UsartIso->US_RHR;
	UsartIso->US_CR = US_CR_RSTSTA | US_CR_RSTIT | US_CR_RSTNACK;

	ISO7816_IccPowerOn();
}

/**
 * Decode ATR trace
 * \param pAtr pointer on ATR buffer
 */
void ISO7816_Decode_ATR( uint8_t* pAtr )
{
	uint32_t i;
	uint32_t j;
	uint32_t y;
	uint8_t offset;

	printf("\n\r");
	printf("ATR: Answer To Reset:\n\r");
	printf("TS = 0x%X Initial character ",pAtr[0]);
	if( pAtr[0] == 0x3B ) {

		printf("Direct Convention\n\r");
	} else {
		if( pAtr[0] == 0x3F ) {
			printf("Inverse Convention\n\r");
		} else {
			printf("BAD Convention\n\r");
		}
	}

	printf("T0 = 0x%X Format character\n\r",pAtr[1]);
	printf("    Number of historical bytes: K = %d\n\r", pAtr[1]&0x0F);
	printf("    Presence further interface byte:\n\r");
	if( pAtr[1]&0x10 ) {
		printf("TA ");
	}
	if( pAtr[1]&0x20 ) {
		printf("TB ");
	}
	if( pAtr[1]&0x40 ) {
		printf("TC ");
	}
	if( pAtr[1]&0x80 ) {
		printf("TD ");
	}
	if( pAtr[1] != 0 ) {
		printf(" present\n\r");
	}

	i = 2;
	y = pAtr[1] & 0xF0;

	/* Read ATR Ti */
	offset = 1;
	while (y) {

		if (y & 0x10) {  /* TA[i] */
			printf("TA[%d] = 0x%X ", offset, pAtr[i]);
			if( offset == 1 ) {
				printf("FI = %d ", (pAtr[i]>>4));
				printf("DI = %d", (pAtr[i]&0x0F));
			}
			printf("\n\r");
			i++;
		}
		if (y & 0x20) {  /* TB[i] */
			printf("TB[%d] = 0x%X\n\r", offset, pAtr[i]);
			i++;
		}
		if (y & 0x40) {  /* TC[i] */
			printf("TC[%d] = 0x%X ", offset, pAtr[i]);
			if( offset == 1 ) {
				printf("Extra Guard Time: N = %d", pAtr[i]);
			}
			printf("\n\r");
			i++;
		}
		if (y & 0x80) {  /* TD[i] */
			printf("TD[%d] = 0x%X\n\r", offset, pAtr[i]);
			y =  pAtr[i++] & 0xF0;
		} else {
			y = 0;
		}
		offset++;
	}

	/* Historical Bytes */
	printf("Historical bytes:\n\r");
	y = pAtr[1] & 0x0F;
	for( j=0; j < y; j++ ) {
		printf(" 0x%X", pAtr[i]);
		if( (pAtr[i] > 0x21) && (pAtr[i] < 0x7D) ) {  /* ASCII */
			printf("(%c) ", pAtr[i]);
		}
		i++;
	}
	printf("\n\r\n\r");

}

/** Initializes a ISO driver
 * \param pUsart   Pointer to the USART peripheral to configure.
 * \param usartId USART ID for iso7816
 *  \param pPinIso7816RstMC Pin ISO 7816 Rst MC
 */
void ISO7816_Init( Usart *pUsart, uint32_t usartId , const Pin pPinIso7816RstMC )
{
	TRACE_DEBUG("ISO_Init\n\r");
	UsartIso = pUsart;
	UsartIsoId = usartId;
		uint32_t baudrate = USART7816BAUDRATE;
		
	/* Pin ISO7816 initialize */
	st_pinIso7816RstMC  = pPinIso7816RstMC;
	
		PMC_EnablePeripheral(UsartIsoId);

		UsartIso->US_FIDI = 372;  /* by default */

		/* Configure USART */
	USART_Configure( UsartIso,
					 US_MR_USART_MODE_IS07816_T_0
					 | US_MR_USCLKS_MCK
					 | US_MR_NBSTOP_1_BIT
					 | US_MR_PAR_EVEN
					 | US_MR_CHRL_8_BIT
					 | US_MR_CLKO
					 | (3<<24), /* MAX_ITERATION */
					 baudrate,
					 BOARD_MCK);

	/* Write the Time-guard Register */
	UsartIso->US_TTGR = 5;
}

