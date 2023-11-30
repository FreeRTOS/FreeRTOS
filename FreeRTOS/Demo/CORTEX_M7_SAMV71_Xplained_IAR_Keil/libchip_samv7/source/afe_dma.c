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

/** \addtogroup afecc_module Working with afecC
 *  \ingroup peripherals_module
 * The afecC driver provides the interface to configure and use the afecC peripheral.\n
 *
 * The afecC(Digital-to-Analog Converter Controller) converts digital code to analog output.
 * The data to be converted are sent in a common register for all channels. It offers up to 2
 * analog outputs.The output voltage ranges from (1/6)ADVREF to (5/6)ADVREF.
 *
 * To Enable a afecC conversion,the user has to follow these few steps:
 * <ul>
 * <li> Select an appropriate reference voltage on ADVREF   </li>
 * <li> Configure the afecC according to its requirements and special needs,which could be
 broken down into several parts:
 * -#   Enable afecC in free running mode by clearing TRGEN in afecC_MR;
 * -#   Configure Refresh Period through setting REFRESH fields
 *      in afecC_MR; The refresh mechanism is used to protect the output analog value from
 *      decreasing.
 * -#   Enable channels and write digital code to afecC_CDR,in free running mode, the conversion
 *      is started right after at least one channel is enabled and data is written .
 </li>
 * </ul>
 *
 * For more accurate information, please look at the afecC section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref afecC.c\n
 * \ref afecC.h\n
 */
/*@{*/
/*@}*/
/**
 * \file
 *
 * Implementation of Digital-to-Analog Converter Controller (afecC).
 *
 */
/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>
#include <assert.h>

/*  DMA driver instance */
static uint32_t afeDmaRxChannel;

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * \brief AFE xDMA Rx callback
 * Invoked on AFE DMA reception done.
 * \param channel DMA channel.
 * \param pArg Pointer to callback argument - Pointer to AfeDma instance.
 */ 
static void Afe_Rx_Cb(uint32_t channel, AfeDma* pArg)
{
    AfeCmd *pAfedCmd = pArg->pCurrentCommand;
    if (channel != afeDmaRxChannel)
        return;

    /* Configure and enable interrupt on RC compare */
    NVIC_ClearPendingIRQ(XDMAC_IRQn);
    NVIC_DisableIRQ(XDMAC_IRQn);

    /* Release the DMA channels */
    XDMAD_FreeChannel(pArg->pXdmad, afeDmaRxChannel);

    /* Release the dataflash semaphore */
    pArg->semaphore++;

    /* Invoke the callback associated with the current command */
    if (pAfedCmd && pAfedCmd->callback) {
        pAfedCmd->callback(0, pAfedCmd->pArgument);
    }
}

/**
 * \brief Configure the DMA Channels: 0 RX.
 * Channels are disabled after configure.
 * \returns 0 if the dma channel configuration successfully; otherwise returns
 * AFE_ERROR_XXX.
 */
static uint8_t _AfeConfigureDmaChannels( AfeDma* pAfed )
{

    /* Driver initialize */
    XDMAD_Initialize( pAfed->pXdmad, 0 );

    XDMAD_FreeChannel( pAfed->pXdmad, afeDmaRxChannel);

    /* Allocate a DMA channel for AFE0/1 RX. */
    afeDmaRxChannel = XDMAD_AllocateChannel( pAfed->pXdmad, pAfed->afeId, XDMAD_TRANSFER_MEMORY);
    {
        if ( afeDmaRxChannel == XDMAD_ALLOC_FAILED ) 
        {
            return AFE_ERROR;
        }
    }

    /* Setup callbacks for AFE0/1 RX */
    XDMAD_SetCallback(pAfed->pXdmad, afeDmaRxChannel, (XdmadTransferCallback)Afe_Rx_Cb, pAfed);
    if (XDMAD_PrepareChannel( pAfed->pXdmad, afeDmaRxChannel ))
        return AFE_ERROR;
    return AFE_OK;
}


/**
 * \brief Configure the DMA source and destination with Linker List mode.
 *
 * \param pBuffer Pointer to afec buffer
 * \param size length of buffer
 */

static uint8_t _Afe_configureLinkList(Afec *pAfeHw, void *pXdmad, AfeCmd *pCommand)
{
    uint32_t xdmaCndc;
    sXdmadCfg xdmadRxCfg;
    uint32_t afeId;
    if ((unsigned int)pAfeHw == (unsigned int)AFEC0 ) afeId = ID_AFEC0;
    if ((unsigned int)pAfeHw == (unsigned int)AFEC1 ) afeId = ID_AFEC1;
    /* Setup RX Link List */
    xdmadRxCfg.mbr_ubc = XDMA_UBC_NVIEW_NDV0 |
        XDMA_UBC_NDE_FETCH_EN|
        XDMA_UBC_NDEN_UPDATED |
        pCommand->RxSize;;
    xdmadRxCfg.mbr_da = (uint32_t)pCommand->pRxBuff;
    xdmadRxCfg.mbr_sa = (uint32_t)&(pAfeHw->AFEC_LCDR);
    xdmadRxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
        XDMAC_CC_MBSIZE_SINGLE |
        XDMAC_CC_DSYNC_PER2MEM |
        XDMAC_CC_CSIZE_CHK_1 |
        XDMAC_CC_DWIDTH_WORD|
        XDMAC_CC_SIF_AHB_IF1 |
        XDMAC_CC_DIF_AHB_IF0 |
        XDMAC_CC_SAM_FIXED_AM |
        XDMAC_CC_DAM_INCREMENTED_AM |
        XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber(  afeId, XDMAD_TRANSFER_RX ));

    xdmadRxCfg.mbr_bc = 0;
    xdmadRxCfg.mbr_sus = 0;
    xdmadRxCfg.mbr_dus =0;

    xdmaCndc = 0;
    if (XDMAD_ConfigureTransfer( pXdmad, afeDmaRxChannel, &xdmadRxCfg, xdmaCndc, 0))
        return AFE_ERROR;

    return AFE_OK;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/


/**
 * \brief Initializes the AfeDma structure and the corresponding AFE & DMA hardware.
 * select value.
 * The driver will uses DMA channel 0 for RX .
 * The DMA channels are freed automatically when no DMA command processing.
 *
 * \param pAfed  Pointer to a AfeDma instance.
 * \param pAfeHw Associated Afe peripheral.
 * \param AfeId  Afe peripheral identifier.
 * \param pDmad  Pointer to a Dmad instance. 
 */
uint32_t Afe_ConfigureDma( AfeDma *pAfed ,
        Afec *pAfeHw ,
        uint8_t AfeId,
        sXdmad *pXdmad )
{
    /* Initialize the Afe structure */
    pAfed->pAfeHw = pAfeHw;
    pAfed->afeId  = AfeId;
    pAfed->semaphore = 1;
    pAfed->pCurrentCommand = 0;
    pAfed->pXdmad = pXdmad;
    return 0;
}

/**
 * \brief Starts a AFE transfer. This is a non blocking function. It will
 *  return as soon as the transfer is started.
 *
 * \param pAfed  Pointer to a AfeDma instance.
 * \param pCommand Pointer to the Afe command to execute.
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * AFE_ERROR_LOCK is the driver is in use, or AFE_ERROR if the command is not
 * valid.
 */
uint32_t Afe_SendData( AfeDma *pAfed, AfeCmd *pCommand)
{
    Afec *pAfeHw = pAfed->pAfeHw;

    /* Try to get the dataflash semaphore */
    if (pAfed->semaphore == 0) {

        return AFE_ERROR_LOCK;
    }
    pAfed->semaphore--;

    // Initialize the callback
    pAfed->pCurrentCommand = pCommand;

    /* Initialize DMA controller using channel 0 for RX. */
    if (_AfeConfigureDmaChannels(pAfed) )
        return AFE_ERROR_LOCK;

    /* Configure and enable interrupt on RC compare */
    NVIC_ClearPendingIRQ(XDMAC_IRQn);
    NVIC_SetPriority( XDMAC_IRQn ,1);
    NVIC_EnableIRQ(XDMAC_IRQn);

    if (_Afe_configureLinkList(pAfeHw, pAfed->pXdmad, pCommand))
        return AFE_ERROR_LOCK;

    AFEC_StartConversion(pAfeHw);
    /* Start DMA 0(RX) */
    if (XDMAD_StartTransfer( pAfed->pXdmad, afeDmaRxChannel )) 
        return AFE_ERROR_LOCK;

    return AFE_OK;;
}
