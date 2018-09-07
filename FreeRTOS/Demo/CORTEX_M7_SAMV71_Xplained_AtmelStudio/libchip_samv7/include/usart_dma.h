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
 * Implementation of USART driver, transfer data through DMA.
 *
 */

#ifndef _USART_DMA_H_
#define _USART_DMA_H_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** An unspecified error has occurred.*/
#define USARTD_ERROR          1

/** USART driver is currently in use.*/
#define USARTD_ERROR_LOCK     2


#ifdef __cplusplus
 extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** USART transfer complete callback. */
typedef void (*UsartdCallback)( uint8_t, void* ) ;

/** \brief usart Transfer Request prepared by the application upper layer.
 *
 * This structure is sent to the USART_Send or USART_Rcv to start the transfer.
 * At the end of the transfer, the callback is invoked by the interrupt handler.
 */
typedef struct
{
    /** Pointer to the Buffer. */
    uint8_t *pBuff;
    /** Buff size in bytes. */
    uint32_t BuffSize;
    /** Dma channel num. */
    uint8_t ChNum;
    /** Callback function invoked at the end of transfer. */
    UsartdCallback callback;
    /** Callback arguments. */
    void *pArgument;
    /** flag to indicate the current transfer progress */
    volatile uint8_t dmaProgress;   
    /* DMA LLI structure */
    LinkedListDescriporView1    *pLLIview;
     /* DMA transfer type */
    eXdmadProgState dmaProgrammingMode;
    /* DMA LLI size or num of micro block*/
    uint16_t dmaBlockSize;
    /* Flag using ring buffer or FiFo*/
    uint8_t dmaRingBuffer;
} UsartChannel ;

/** Constant structure associated with USART port. This structure prevents
    client applications to have access in the same time. */
typedef struct 
{
    /** USART Id as defined in the product datasheet */
    uint8_t usartId ;
    /** Pointer to USART Hardware registers */
    Usart* pUsartHw ;    
    /** Current Usart Rx channel */
    UsartChannel *pRxChannel ;
    /** Current Usart Tx channel */
    UsartChannel *pTxChannel ;
    /** Pointer to DMA driver */
    sXdmad* pXdmad;
} UsartDma;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

uint32_t USARTD_Configure( UsartDma *pUsartd ,
                                 uint8_t USARTId,
                                 uint32_t UsartMode,
                                 uint32_t BaudRate,
                                 uint32_t UsartClk);

uint32_t USARTD_EnableTxChannels( UsartDma *pUsartd, UsartChannel *pTxCh);

uint32_t USARTD_EnableRxChannels( UsartDma *pUsartd, UsartChannel *pRxCh);

uint32_t USARTD_DisableTxChannels( UsartDma *pUsartd, UsartChannel *pTxCh);

uint32_t USARTD_DisableRxChannels( UsartDma *pUsartd, UsartChannel *pTxCh);

uint32_t USARTD_SendData( UsartDma* pUsartd ) ;

uint32_t USARTD_RcvData( UsartDma *pUsartd);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _USART_DMA_ */
