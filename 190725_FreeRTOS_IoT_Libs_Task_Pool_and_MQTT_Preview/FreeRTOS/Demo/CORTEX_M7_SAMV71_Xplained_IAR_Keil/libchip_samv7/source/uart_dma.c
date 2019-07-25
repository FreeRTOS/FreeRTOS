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
 * \addtogroup uart_dma_module UART xDMA driver
 * \ingroup lib_uartflash
 * \section Usage
 *
 * <ul>
 * <li> UARTD_Configure() initializes and configures the UART peripheral and xDMA for data transfer.</li>
 * <li> Configures the parameters for the device corresponding to the cs value by UARTD_ConfigureCS(). </li>
 * <li> Starts a UART master transfer. This is a non blocking function UARTD_SendCommand(). It will
 * return as soon as the transfer is started..</li>
 * </ul>
 *
 */

/**
 * \file
 *
 * Implementation for the UART Flash with xDMA driver.
 *
 */


/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/


/** xDMA Link List size for uart transation*/
#define DMA_UART_LLI     2

/*----------------------------------------------------------------------------
 *        Macros
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------
 *        Local Variables
 *----------------------------------------------------------------------------*/


/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/


/**
 * \brief UART xDMA Rx callback
 * Invoked on UART DMA reception done.
 * \param channel DMA channel.
 * \param pArg Pointer to callback argument - Pointer to UARTDma instance.   
 */ 
static void UARTD_Rx_Cb(uint32_t channel, UartDma* pArg)
{

    UartChannel *pUartdCh = pArg->pRxChannel;
    if (channel != pUartdCh->ChNum)
        return;

    //    NVIC_ClearPendingIRQ(XDMAC_IRQn);

    /* Release the DMA channels */
    XDMAD_FreeChannel(pArg->pXdmad, pUartdCh->ChNum);

    /* Invoke the callback associated with the current command */
    if (pUartdCh && pUartdCh->callback) {
        pUartdCh->callback(0, pUartdCh->pArgument);
    }   
    pUartdCh->sempaphore = 1;
}

/**
 * \brief USART xDMA Rx callback
 * Invoked on USART DMA reception done.
 * \param channel DMA channel.
 * \param pArg Pointer to callback argument - Pointer to USARTDma instance.   
 */ 
static void UARTD_Tx_Cb(uint32_t channel, UartDma* pArg)
{
    UartChannel *pUartdCh = pArg->pTxChannel;
    if (channel != pUartdCh->ChNum)
        return;

    //    NVIC_ClearPendingIRQ(XDMAC_IRQn);

    /* Release the DMA channels */
    XDMAD_FreeChannel(pArg->pXdmad, pUartdCh->ChNum);

    /* Invoke the callback associated with the current command */
    if (pUartdCh && pUartdCh->callback) {
        pUartdCh->callback(0, pUartdCh->pArgument);
    }
    pUartdCh->sempaphore = 1;
}


/**
 * \brief Configure the UART Rx DMA Destination with Linker List mode.
 *
 * \param UartChannel Pointer to UART dma channel
 * \returns 0 if the dma multibuffer configuration successfully; otherwise returns
 * USARTD_ERROR_XXX.
 */
static uint8_t _configureRxLinkList(Uart *pUartHw, void *pXdmad, UartChannel *pUartRx)
{
    sXdmadCfg xdmadRxCfg;
    uint32_t xdmaCndc;
    uint32_t uartId;
    if ((unsigned int)pUartHw == (unsigned int)UART0 ) uartId = ID_UART0;
    if ((unsigned int)pUartHw == (unsigned int)UART1 ) uartId = ID_UART1;
    if ((unsigned int)pUartHw == (unsigned int)UART2 ) uartId = ID_UART2;
    if ((unsigned int)pUartHw == (unsigned int)UART3 ) uartId = ID_UART3;
    if ((unsigned int)pUartHw == (unsigned int)UART4 ) uartId = ID_UART4;

    /* Setup RX Link List */
    xdmadRxCfg.mbr_ubc = XDMA_UBC_NVIEW_NDV0 |
        XDMA_UBC_NDE_FETCH_DIS|
        XDMA_UBC_NDEN_UPDATED |
        pUartRx->BuffSize;
    xdmadRxCfg.mbr_da = (uint32_t)pUartRx->pBuff;

    xdmadRxCfg.mbr_sa = (uint32_t)&pUartHw->UART_RHR;
    xdmadRxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
        XDMAC_CC_MBSIZE_SINGLE |
        XDMAC_CC_DSYNC_PER2MEM |
        XDMAC_CC_CSIZE_CHK_1 |
        XDMAC_CC_DWIDTH_BYTE |
        XDMAC_CC_SIF_AHB_IF1 |
        XDMAC_CC_DIF_AHB_IF0 |
        XDMAC_CC_SAM_FIXED_AM |
        XDMAC_CC_DAM_INCREMENTED_AM |
        XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber(  uartId, XDMAD_TRANSFER_RX ));

    xdmadRxCfg.mbr_bc = 0;
    xdmadRxCfg.mbr_sus = 0;
    xdmadRxCfg.mbr_dus =0;
    xdmaCndc = 0;
    if (XDMAD_ConfigureTransfer( pXdmad, pUartRx->ChNum, &xdmadRxCfg, xdmaCndc, 0))
        return USARTD_ERROR;

    return 0;
}


/**
 * \brief Configure the UART tx DMA source with Linker List mode.
 *
 * \param UartChannel Pointer to UART dma channel
 * \returns 0 if the dma multibuffer configuration successfully; otherwise returns
 * USARTD_ERROR_XXX.
 */
static uint8_t _configureTxLinkList(Uart *pUartHw, void *pXdmad, UartChannel *pUartTx)
{
    sXdmadCfg xdmadTxCfg;
    uint32_t xdmaCndc;
    uint32_t uartId;
    if ((unsigned int)pUartHw == (unsigned int)UART0 ) uartId = ID_UART0;
    if ((unsigned int)pUartHw == (unsigned int)UART1 ) uartId = ID_UART1;
    if ((unsigned int)pUartHw == (unsigned int)UART2 ) uartId = ID_UART2;
    if ((unsigned int)pUartHw == (unsigned int)UART3 ) uartId = ID_UART3;
    if ((unsigned int)pUartHw == (unsigned int)UART4 ) uartId = ID_UART4;

    /* Setup TX Link List */ 
    xdmadTxCfg.mbr_ubc =   XDMA_UBC_NVIEW_NDV0 |
        XDMA_UBC_NDE_FETCH_DIS|
        XDMA_UBC_NSEN_UPDATED |  pUartTx->BuffSize;

    xdmadTxCfg.mbr_sa = (uint32_t)pUartTx->pBuff;
    xdmadTxCfg.mbr_da = (uint32_t)&pUartHw->UART_THR;
    xdmadTxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
        XDMAC_CC_MBSIZE_SINGLE |
        XDMAC_CC_DSYNC_MEM2PER |
        XDMAC_CC_CSIZE_CHK_1 |
        XDMAC_CC_DWIDTH_BYTE|
        XDMAC_CC_SIF_AHB_IF0 |
        XDMAC_CC_DIF_AHB_IF1 |
        XDMAC_CC_SAM_INCREMENTED_AM |
        XDMAC_CC_DAM_FIXED_AM |
        XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber(  uartId, XDMAD_TRANSFER_TX ));

    xdmadTxCfg.mbr_bc = 0;
    xdmadTxCfg.mbr_sus = 0;
    xdmadTxCfg.mbr_dus =0;
    xdmaCndc = 0;

    if (XDMAD_ConfigureTransfer( pXdmad, pUartTx->ChNum, &xdmadTxCfg, xdmaCndc, 0))
        return USARTD_ERROR;
    return 0;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Initializes the UartDma structure and the corresponding UART & DMA hardware.
 * select value.
 * The driver will uses DMA channel 0 for RX and DMA channel 1 for TX.
 * The DMA channels are freed automatically when no UART command processing.
 *
 * \param pUartd  Pointer to a UartDma instance.
 * \param pUartHw Associated UART peripheral.
 * \param uartId  UART peripheral identifier.
 * \param pXdmad  Pointer to a Dmad instance. 
 */
uint32_t UARTD_Configure( UartDma *pUartd ,
        Uart *pUartHw ,
        uint8_t uartId,
        uint32_t UartMode,
        sXdmad *pXdmad )
{
    /* Initialize the UART structure */
    pUartd->pUartHw = pUartHw;
    pUartd->uartId  = uartId;
    pUartd->pTxChannel = 0;
    pUartd->pRxChannel = 0;
    pUartd->pXdmad = pXdmad;

    /* Enable the UART Peripheral ,Execute a software reset of the UART, Configure UART in Master Mode*/
    UART_Configure ( pUartHw, UartMode, 115200, BOARD_MCK);

    /* Driver initialize */
    XDMAD_Initialize(  pUartd->pXdmad, 0 );
    /* Configure and enable interrupt on RC compare */ 
    NVIC_ClearPendingIRQ(XDMAC_IRQn);
    NVIC_SetPriority( XDMAC_IRQn ,1);
    return 0;
}


/**
 * \brief Enables USART Rx DMA channel
 * select value.
 * The driver will uses DMA channel 0 for RX and DMA channel 1 for TX.
 * The DMA channels are freed automatically when no USART command processing.
 *
 * \param pUSARTd  Pointer to a UartDma instance.
 * \param pUartHw Associated USART peripheral.
 * \param uartId  USART peripheral identifier.
 * \param UartClk USART clock.
 * \param pDmad  Pointer to a Dmad instance. 
 */

uint32_t UARTD_EnableRxChannels( UartDma *pUartd, UartChannel *pRxCh)
{
    Uart *pUartHw = pUartd->pUartHw;
    uint32_t Channel;

    // Initialize the callback
    pUartd->pRxChannel = pRxCh;

    /* Enables the USART to receive data. */
    UART_SetReceiverEnabled ( pUartHw , 1);

    XDMAD_FreeChannel( pUartd->pXdmad, pRxCh->ChNum);

    /* Allocate a DMA channel for UART0/1 RX. */
    Channel =  XDMAD_AllocateChannel( pUartd->pXdmad, pUartd->uartId, XDMAD_TRANSFER_MEMORY);
    if ( Channel == XDMAD_ALLOC_FAILED ) 
    {
        return USARTD_ERROR;
    }

    pRxCh->ChNum = Channel ;

    /* Setup callbacks for UART0/1 RX */
    XDMAD_SetCallback(pUartd->pXdmad, pRxCh->ChNum, (XdmadTransferCallback)UARTD_Rx_Cb, pUartd);
    if (XDMAD_PrepareChannel( pUartd->pXdmad, pRxCh->ChNum ))
        return USARTD_ERROR;

    /* Enable interrupt  */ 
    NVIC_EnableIRQ(XDMAC_IRQn);

    if (_configureRxLinkList(pUartHw, pUartd->pXdmad, pRxCh))
        return USARTD_ERROR_LOCK;

    return 0;
}



uint32_t UARTD_EnableTxChannels( UartDma *pUartd, UartChannel *pTxCh)
{
    Uart *pUartHw = pUartd->pUartHw;
    uint32_t Channel;

    // Initialize the callback
    pUartd->pTxChannel = pTxCh;

    /* Enables the USART to transfer data. */
    UART_SetTransmitterEnabled ( pUartHw , 1);

    XDMAD_FreeChannel( pUartd->pXdmad, pTxCh->ChNum);

    /* Allocate a DMA channel for USART0/1 TX. */
    Channel =  XDMAD_AllocateChannel( pUartd->pXdmad, XDMAD_TRANSFER_MEMORY, pUartd->uartId);
    if ( pTxCh->ChNum == XDMAD_ALLOC_FAILED ) 
    {
        return USARTD_ERROR;
    }

    pTxCh->ChNum = Channel ;

    /* Setup callbacks for USART0/1 TX */
    XDMAD_SetCallback(pUartd->pXdmad, pTxCh->ChNum, (XdmadTransferCallback)UARTD_Tx_Cb, pUartd);
    if ( XDMAD_PrepareChannel( pUartd->pXdmad, pTxCh->ChNum ))
        return USARTD_ERROR;

    /* Enable interrupt  */ 
    NVIC_EnableIRQ(XDMAC_IRQn);

    if (_configureTxLinkList(pUartHw, pUartd->pXdmad, pTxCh))
        return USARTD_ERROR_LOCK;

    return 0;
}

/**
 * \brief Starts a USART master transfer. This is a non blocking function. It will
 *  return as soon as the transfer is started.
 *
 * \param pUSARTd  Pointer to a USARTDma instance.
 * \param pCommand Pointer to the USART command to execute.
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * USARTD_ERROR_LOCK is the driver is in use, or USARTD_ERROR if the command is not
 * valid.
 */
uint32_t UARTD_SendData( UartDma *pUartd)
{

    /* Start DMA 0(RX) && 1(TX) */
    while(!pUartd->pTxChannel->sempaphore);
    if (XDMAD_StartTransfer( pUartd->pXdmad, pUartd->pTxChannel->ChNum )) 
        return USARTD_ERROR_LOCK;
    pUartd->pTxChannel->sempaphore=0;
    return 0;
}

/**
 * \brief Starts a USART master transfer. This is a non blocking function. It will
 *  return as soon as the transfer is started.
 *
 * \param pUSARTd  Pointer to a USARTDma instance.
 * \param pCommand Pointer to the USART command to execute.
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * USARTD_ERROR_LOCK is the driver is in use, or USARTD_ERROR if the command is not
 * valid.
 */
uint32_t UARTD_RcvData( UartDma *pUartd)
{    

    while(!pUartd->pRxChannel->sempaphore);
    /* Start DMA 0(RX) && 1(TX) */
    if (XDMAD_StartTransfer( pUartd->pXdmad, pUartd->pRxChannel->ChNum )) 
        return USARTD_ERROR_LOCK;
    pUartd->pRxChannel->sempaphore=0;
    return 0;
}

