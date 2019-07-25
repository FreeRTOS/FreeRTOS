/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2009, Atmel Corporation
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

#ifndef _QSPI_DMA_
#define _QSPI_DMA_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** An unspecified error has occured.*/
#define QSPID_ERROR          1

/** SPI driver is currently in use.*/
#define QSPID_ERROR_LOCK     2

/*----------------------------------------------------------------------------
 *        Macros
 *----------------------------------------------------------------------------*/

/** Calculates the value of the SCBR field of the Chip Select Register given MCK and SPCK.*/
#define QSPID_CSR_SCBR(mck, spck)    QSPI_CSR_SCBR((mck) / (spck))

/** Calculates the value of the DLYBS field of the Chip Select Register given delay in ns and MCK.*/
#define QSPID_CSR_DLYBS(mck, delay)  QSPI_CSR_DLYBS((((delay) * ((mck) / 1000000)) / 1000) + 1)

/** Calculates the value of the DLYBCT field of the Chip Select Register given delay in ns and MCK.*/
#define QSPID_CSR_DLYBCT(mck, delay) QSPI_CSR_DLYBCT((((delay) / 32 * ((mck) / 1000000)) / 1000) + 1)

#ifdef __cplusplus
 extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** SPI transfer complete callback. */
typedef void (*QspidCallback)( uint8_t, void* ) ;

/** \brief Qspi Transfer Request prepared by the application upper layer.
 *
 * This structure is sent to the SPI_SendCommand function to start the transfer.
 * At the end of the transfer, the callback is invoked by the interrupt handler.
 */
typedef struct _QspidCmd
{
    /** Pointer to the Tx data. */
    uint8_t *pTxBuff;
    /** Tx size in bytes. */
    uint8_t TxSize;
    /** Pointer to the Rx data. */
    uint8_t *pRxBuff;
    /** Rx size in bytes. */
    uint16_t RxSize;
    /** Callback function invoked at the end of transfer. */
    QspidCallback callback;
    /** Callback arguments. */
    void *pArgument;
} QspidCmd ;

/** Constant structure associated with SPI port. This structure prevents
    client applications to have access in the same time. */
typedef struct _Qspid
{
    /** Pointer to SPI Hardware registers */
    Qspi* pQspiHw ;
    /** Current QspiCommand being processed */
    QspidCmd *pCurrentCommand ;
    /** Pointer to DMA driver */
    sXdmad* pXdmad;
    /** SPI Id as defined in the product datasheet */
    uint8_t spiId ;
    /** Mutual exclusion semaphore. */
    volatile int8_t semaphore ;
} Qspid ;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern uint32_t QSPID_Configure( Qspid* pQspid,
                                Qspi* pQspiHw,
                                uint8_t spiId,
                                uint8_t QspiMode,
                                sXdmad* pXdmad ) ;

extern void QSPID_ConfigureCS( Qspid* pQspid, uint32_t dwCS, uint32_t dwCsr ) ;

extern uint32_t QSPID_SendCommand( Qspid* pQspid, QspidCmd* pCommand ) ;

extern void QSPID_Handler( Qspid* pQspid ) ;

extern void QSPID_DmaHandler( Qspid *pQspid );

extern uint32_t QSPID_IsBusy( const Qspid* pQspid ) ;

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _SPI_DMA_ */
