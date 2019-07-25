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
 * Implementation of UART driver, transfer data through DMA.
 *
 */

#ifndef _UART_DMA_
#define _UART_DMA_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** An unspecified error has occurred.*/
#define UARTD_ERROR          1

/** UART driver is currently in use.*/
#define UARTD_ERROR_LOCK     2


#ifdef __cplusplus
 extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** UART transfer complete callback. */
typedef void (*UartdCallback)( uint8_t, void* ) ;

/** \brief usart Transfer Request prepared by the application upper layer.
 *
 * This structure is sent to the UART_Send or UART_Rcv to start the transfer.
 * At the end of the transfer, the callback is invoked by the interrupt handler.
 */
typedef struct
{
    /** Pointer to the Buffer. */
    uint8_t *pBuff;
    /** Buff size in bytes. */
    uint32_t BuffSize;
    /** Dma channel num. */
    uint32_t ChNum;
    /** Callback function invoked at the end of transfer. */
    UartdCallback callback;
    /** Callback arguments. */
    void *pArgument;
   /** flag to indicate the current transfer. */
    volatile uint8_t sempaphore;
    /* DMA LLI structure */
    LinkedListDescriporView1    *pLLIview;
    /* DMA transfer type */
    eXdmadProgState dmaProgrammingMode;
    /* DMA LLI size */
    uint16_t dmaBlockSize;
    /* Flag using ring buffer or FiFo*/
    uint8_t dmaRingBuffer;
} UartChannel ;

/** Constant structure associated with UART port. This structure prevents
    client applications to have access in the same time. */
typedef struct 
{
    /** USART Id as defined in the product datasheet */
    uint8_t uartId ;
    /** Pointer to DMA driver */
    sXdmad* pXdmad;    
    /** Pointer to UART Hardware registers */
    Uart* pUartHw ;
    /** Current Uart Rx channel */
    UartChannel *pRxChannel ;
    /** Current Uart Tx channel */
    UartChannel *pTxChannel ;
} UartDma;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

uint32_t UARTD_Configure( UartDma *pUartd ,
                                 uint8_t uartId,
                                 uint32_t uartMode,
                                 uint32_t baud,
                                 uint32_t clk );

uint32_t UARTD_EnableTxChannels( UartDma *pUartd, UartChannel *pTxCh);

uint32_t UARTD_EnableRxChannels( UartDma *pUartd, UartChannel *pRxCh);

uint32_t UARTD_DisableTxChannels( UartDma *pUartd, UartChannel *pTxCh);

uint32_t UARTD_DisableRxChannels( UartDma *pUartd, UartChannel *pRxCh);

uint32_t UARTD_SendData( UartDma* pUartd ) ;

uint32_t UARTD_RcvData( UartDma *pUartd);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _UART_DMA_ */
