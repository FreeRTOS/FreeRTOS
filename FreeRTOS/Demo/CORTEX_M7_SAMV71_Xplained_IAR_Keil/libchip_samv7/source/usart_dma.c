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
 * \addtogroup usart_dma_module USART xDMA driver
 * \section Usage
 *
 * <ul>
 * <li> USARTD_Configure() initializes and configures the USART peripheral and xDMA for data transfer.</li>
 * <li> Configures the parameters for the device corresponding to the cs value by USARTD_ConfigureCS(). </li>
 * </ul>
 *
 */

/**
 * \file
 *
 * Implementation for the USART with xDMA driver.
 *
 */


/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/


/** xDMA Link List size for usart transmition*/
#define DMA_USART_LLI     2

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
 * \brief USART xDMA Rx callback
 * Invoked on USART DMA reception done.
 * \param channel DMA channel.
 * \param pArg Pointer to callback argument - Pointer to USARTDma instance.   
 */ 
static void USARTD_Rx_Cb(uint32_t channel, UsartDma* pArg)
{

    UsartChannel *pUsartdCh = pArg->pRxChannel;
    if (channel != pUsartdCh->ChNum)
        return;

    //    NVIC_ClearPendingIRQ(XDMAC_IRQn);

    /* Release the DMA channels */
    XDMAD_FreeChannel(pArg->pXdmad, pUsartdCh->ChNum);

    /* Invoke the callback associated with the current command */
    if (pUsartdCh && pUsartdCh->callback) {
        pUsartdCh->callback(0, pUsartdCh->pArgument);
    }    
    pUsartdCh->Done = 1;
    memory_barrier();
}

/**
 * \brief USART xDMA Rx callback
 * Invoked on USART DMA reception done.
 * \param channel DMA channel.
 * \param pArg Pointer to callback argument - Pointer to USARTDma instance.   
 */ 
static void USARTD_Tx_Cb(uint32_t channel, UsartDma* pArg)
{
    UsartChannel *pUsartdCh = pArg->pTxChannel;
    if (channel != pUsartdCh->ChNum)
        return;

    //    NVIC_ClearPendingIRQ(XDMAC_IRQn);

    /* Release the DMA channels */
    XDMAD_FreeChannel(pArg->pXdmad, pUsartdCh->ChNum);

    /* Invoke the callback associated with the current command */
    if (pUsartdCh && pUsartdCh->callback) {
        pUsartdCh->callback(0, pUsartdCh->pArgument);
    }
    pUsartdCh->Done = 1;
    memory_barrier();
}

/**
 * \brief Configure the USART Rx DMA Destination with Linker List mode.
 *
 * \param UsartChannel Pointer to USART dma channel
 * \returns 0 if the dma multibuffer configuration successfully; otherwise returns
 * USARTD_ERROR_XXX.
 */
static uint8_t _configureRxLinkList(Usart *pUsartHw, void *pXdmad, UsartChannel *pUsartRx)
{
    sXdmadCfg xdmadRxCfg;
    uint32_t xdmaCndc;
    uint32_t usartId;
    if ((unsigned int)pUsartHw == (unsigned int)USART0 ) usartId = ID_USART0;
    if ((unsigned int)pUsartHw == (unsigned int)USART1 ) usartId = ID_USART1;
    if ((unsigned int)pUsartHw == (unsigned int)USART2 ) usartId = ID_USART2;

    /* Setup RX Link List */
    xdmadRxCfg.mbr_ubc = XDMA_UBC_NVIEW_NDV0 |
        XDMA_UBC_NDE_FETCH_DIS|
        XDMA_UBC_NDEN_UPDATED |
        pUsartRx->BuffSize;
    xdmadRxCfg.mbr_da = (uint32_t)pUsartRx->pBuff;

    xdmadRxCfg.mbr_sa = (uint32_t)&pUsartHw->US_RHR;
    xdmadRxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
        XDMAC_CC_MBSIZE_SINGLE |
        XDMAC_CC_DSYNC_PER2MEM |
        XDMAC_CC_CSIZE_CHK_1 |
        XDMAC_CC_DWIDTH_BYTE |
        XDMAC_CC_SIF_AHB_IF1 |
        XDMAC_CC_DIF_AHB_IF0 |
        XDMAC_CC_SAM_FIXED_AM |
        XDMAC_CC_DAM_INCREMENTED_AM |
        XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber(  usartId, XDMAD_TRANSFER_RX ));

    xdmadRxCfg.mbr_bc = 0;
    xdmadRxCfg.mbr_sus = 0;
    xdmadRxCfg.mbr_dus =0;
    xdmaCndc = 0;
    if (XDMAD_ConfigureTransfer( pXdmad, pUsartRx->ChNum, &xdmadRxCfg, xdmaCndc, 0))
        return USARTD_ERROR;

    return 0;
}


/**
 * \brief Configure the USART tx DMA source with Linker List mode.
 *
 * \param UsartChannel Pointer to USART dma channel
 * \returns 0 if the dma multibuffer configuration successfully; otherwise returns
 * USARTD_ERROR_XXX.
 */
static uint8_t _configureTxLinkList(Usart *pUsartHw, void *pXdmad, UsartChannel *pUsartTx)
{
    sXdmadCfg xdmadTxCfg;
    uint32_t xdmaCndc;
    uint32_t usartId;
    if ((unsigned int)pUsartHw == (unsigned int)USART0 ) usartId = ID_USART0;
    if ((unsigned int)pUsartHw == (unsigned int)USART1 ) usartId = ID_USART1;
    if ((unsigned int)pUsartHw == (unsigned int)USART2 ) usartId = ID_USART2;
    /* Setup TX Link List */ 
    xdmadTxCfg.mbr_ubc =   XDMA_UBC_NVIEW_NDV0 |
        XDMA_UBC_NDE_FETCH_DIS|
        XDMA_UBC_NSEN_UPDATED |  pUsartTx->BuffSize;

    xdmadTxCfg.mbr_sa = (uint32_t)pUsartTx->pBuff;
    xdmadTxCfg.mbr_da = (uint32_t)&pUsartHw->US_THR;
    xdmadTxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
        XDMAC_CC_MBSIZE_SINGLE |
        XDMAC_CC_DSYNC_MEM2PER |
        XDMAC_CC_CSIZE_CHK_1 |
        XDMAC_CC_DWIDTH_BYTE|
        XDMAC_CC_SIF_AHB_IF0 |
        XDMAC_CC_DIF_AHB_IF1 |
        XDMAC_CC_SAM_INCREMENTED_AM |
        XDMAC_CC_DAM_FIXED_AM |
        XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber(  usartId, XDMAD_TRANSFER_TX ));

    xdmadTxCfg.mbr_bc = 0;
    xdmadTxCfg.mbr_sus = 0;
    xdmadTxCfg.mbr_dus =0;
    xdmaCndc = 0;

    if (XDMAD_ConfigureTransfer( pXdmad, pUsartTx->ChNum, &xdmadTxCfg, xdmaCndc, 0))
        return USARTD_ERROR;
    return 0;
}


/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Initializes the USARTDma structure and the corresponding USART & DMA hardware.
 * select value.
 * The driver will uses DMA channel 0 for RX and DMA channel 1 for TX.
 * The DMA channels are freed automatically when no USART command processing.
 *
 * \param pUSARTd  Pointer to a UsartDma instance.
 * \param pUsartHw Associated USART peripheral.
 * \param usartId  USART peripheral identifier.
 * \param UsartClk USART clock.
 * \param pXdmad  Pointer to a Dmad instance. 
 */
uint32_t USARTD_Configure( UsartDma *pUsartd ,
        Usart *pUsartHw ,
        uint8_t usartId,
        uint32_t UsartMode,
        uint32_t UsartClk,
        sXdmad *pXdmad )
{
    /* Initialize the USART structure */
    pUsartd->pUsartHw = pUsartHw;
    pUsartd->usartId  = usartId;
    pUsartd->pRxChannel = 0;
    pUsartd->pTxChannel = 0;
    pUsartd->pXdmad = pXdmad;

    /* Enable the USART Peripheral ,Execute a software reset of the USART, Configure USART in Master Mode*/
    USART_Configure ( pUsartHw, UsartMode, UsartClk, BOARD_MCK);

    /* Driver initialize */
    XDMAD_Initialize(  pUsartd->pXdmad, 0 );
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
 * \param pUSARTd  Pointer to a UsartDma instance.
 * \param pUsartHw Associated USART peripheral.
 * \param usartId  USART peripheral identifier.
 * \param UsartClk USART clock.
 * \param pDmad  Pointer to a Dmad instance. 
 */

uint32_t USARTD_EnableRxChannels( UsartDma *pUsartd, UsartChannel *pRxCh)
{
    Usart *pUsartHw = pUsartd->pUsartHw;

    // Initialize the callback
    pUsartd->pRxChannel = pRxCh;

    /* Enables the USART to receive data. */
    USART_SetReceiverEnabled ( pUsartHw , 1);

    XDMAD_FreeChannel( pUsartd->pXdmad, pRxCh->ChNum);

    /* Allocate a DMA channel for USART0/1 RX. */
    pRxCh->ChNum =  XDMAD_AllocateChannel( pUsartd->pXdmad, pUsartd->usartId, XDMAD_TRANSFER_MEMORY);
    if ( pRxCh->ChNum == XDMAD_ALLOC_FAILED ) 
    {
        return USARTD_ERROR;
    }

    /* Setup callbacks for USART0/1 RX */
    XDMAD_SetCallback(pUsartd->pXdmad, pRxCh->ChNum, (XdmadTransferCallback)USARTD_Rx_Cb, pUsartd);
    if (XDMAD_PrepareChannel( pUsartd->pXdmad, pRxCh->ChNum ))
        return USARTD_ERROR;

    /* Enable interrupt  */ 
    NVIC_EnableIRQ(XDMAC_IRQn);

    if (_configureRxLinkList(pUsartHw, pUsartd->pXdmad, pRxCh))
        return USARTD_ERROR_LOCK;

    return 0;
}



uint32_t USARTD_EnableTxChannels( UsartDma *pUsartd, UsartChannel *pTxCh)
{
    Usart *pUsartHw = pUsartd->pUsartHw;

    // Initialize the callback
    pUsartd->pTxChannel = pTxCh;

    /* Enables the USART to transfer data. */
    USART_SetTransmitterEnabled ( pUsartHw , 1);    

    XDMAD_FreeChannel( pUsartd->pXdmad, pTxCh->ChNum);

    /* Allocate a DMA channel for USART0/1 TX. */
    pTxCh->ChNum =  XDMAD_AllocateChannel( pUsartd->pXdmad, XDMAD_TRANSFER_MEMORY, pUsartd->usartId);
    if ( pTxCh->ChNum == XDMAD_ALLOC_FAILED ) 
    {
        return USARTD_ERROR;
    }

    /* Setup callbacks for USART0/1 TX */
    XDMAD_SetCallback(pUsartd->pXdmad, pTxCh->ChNum, (XdmadTransferCallback)USARTD_Tx_Cb, pUsartd);
    if ( XDMAD_PrepareChannel( pUsartd->pXdmad, pTxCh->ChNum ))
        return USARTD_ERROR;

    /* Enable interrupt  */ 
    NVIC_EnableIRQ(XDMAC_IRQn);

    if (_configureTxLinkList(pUsartHw, pUsartd->pXdmad, pTxCh))
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
uint32_t USARTD_SendData( UsartDma *pUsartd)
{

    /* Start DMA 0(RX) && 1(TX) */
    while(!pUsartd->pTxChannel->Done);
    if (XDMAD_StartTransfer( pUsartd->pXdmad, pUsartd->pTxChannel->ChNum )) 
        return USARTD_ERROR_LOCK;
    pUsartd->pTxChannel->Done=0;
    memory_barrier();
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
uint32_t USARTD_RcvData( UsartDma *pUsartd)
{    

    while(!pUsartd->pRxChannel->Done);
    /* Start DMA 0(RX) && 1(TX) */
    if (XDMAD_StartTransfer( pUsartd->pXdmad, pUsartd->pRxChannel->ChNum )) 
        return USARTD_ERROR_LOCK;
    pUsartd->pRxChannel->Done=0;
    memory_barrier();
    return 0;
}

