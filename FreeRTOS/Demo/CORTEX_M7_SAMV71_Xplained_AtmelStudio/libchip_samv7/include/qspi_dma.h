/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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
 * Implementation of SPI driver, transfer data through DMA.
 *
 */

#ifndef QSPI_DMA_H
#define QSPI_DMA_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
//_RB_#include "../../../../utils/utility.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** An unspecified error has occurred.*/
#define QSPID_ERROR          1

/** SPI driver is currently in use.*/
#define QSPID_ERROR_LOCK     2

#define QSPID_CH_NOT_ENABLED 0xFF
/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** SPI transfer complete callback. */
typedef void (*QspidCallback)( uint8_t, void* ) ;

/** Constant structure associated with SPI port. This structure prevents
	client applications to have access in the same time. */
typedef struct _Qspid
{
	Qspid_t Qspid;
	/** Pointer to DMA driver */
	sXdmad* pXdmad;
	/** Polling  */
	uint8_t Polling ;
	/** Tx ch num  */
	uint8_t TxChNum ;
	/** Rx ch num  */
	uint8_t RxChNum ;
	/** QSPI Xfr state. */
	volatile uint8_t progress ;
} QspiDma_t ;

#ifdef __cplusplus
 extern "C" {
#endif
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

uint32_t QSPID_Configure( QspiDma_t *pQspidma, QspiMode_t Mode,
		uint32_t dwConfiguration,  sXdmad* pXdmad);

uint32_t QSPID_EnableQspiRxChannel(QspiDma_t *pQspidma);
  
uint32_t QSPID_EnableQspiTxChannel(QspiDma_t *pQspidma);

uint32_t QSPID_DisableQspiRxChannel(QspiDma_t *pQspidma);

uint32_t QSPID_DisableQspiTxChannel(QspiDma_t *pQspidma);

uint32_t QSPID_DisableSpiChannel(QspiDma_t *pQspidma);

uint32_t QSPID_EnableSpiChannel(QspiDma_t *pQspidma);

uint32_t QSPID_ReadWriteQSPI( QspiDma_t *pQspidma, Access_t const ReadWrite);

uint32_t QSPID_ReadWriteSPI(QspiDma_t *pQspidma, Access_t const ReadWrite);

uint32_t QSPID_IsBusy( volatile uint8_t *QspiSemaphore) ;

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _SPI_DMA_ */
