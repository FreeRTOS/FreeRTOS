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

/** \addtogroup dmad_module 
 *
 * \section DmaConfig Dma Configuration Usage
 *
 * To configure a DMA channel, the user has to follow these few steps :
 * <ul>
 * <li> Initialize a DMA driver instance by DMAD_Initialize().</li>
 * <li> choose an available (disabled) channel using DMAD_AllocateChannel().</li>
 * <li> After the DMAC selected channel has been programmed, DMAD_PrepareChannel() is to enable 
 * clock and dma peripheral of the DMA, and set Configuration register to set up the transfer type 
 * (memory or non-memory peripheral for source and destination) and flow control device.</li>
 * <li> Configure DMA multi-buffer transfers using DMAD_PrepareMultiTransfer() to set up the chain of Linked List Items,
 * single-buffer transfers using DMAD_PrepareSingleTransfer().</li>
 * <li> Invoke DMAD_StartTransfer() to start DMA transfer, or DMAD_StopTransfer() to force stop DMA transfer.</li>
 * <li> If picture-in-picture mode is enabled, DMAD_ConfigurePIP() helps to configure PIP mode.</li>
 * <li> Once the buffer of data is transferred, DMAD_IsTransferDone() checks if DMA transfer is finished.</li>
 * <li> DMAD_Handler() handles DMA interrupt, and invoking DMAD_SetCallback() if provided.</li>
 * </ul>
 *
 * Related files:\n
 * \ref dmad.h\n
 * \ref dmad.c.\n
 */

/** \file */

/** \addtogroup dmad_functions
  @{*/
 
/*----------------------------------------------------------------------------
 *        Includes
 *----------------------------------------------------------------------------*/

#include "board.h"
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Try to allocate a DMA channel for on given controller.
 * \param pDmad  Pointer to DMA driver instance.
 * \param bDmac  DMA controller ID (0 ~ 1).
 * \param bSrcID Source peripheral ID, 0xFF for memory.
 * \param bDstID Destination peripheral ID, 0xFF for memory.
 * \return Channel number if allocation sucessful, return 
 * DMAD_ALLOC_FAILED if allocation failed.
 */
static uint32_t DMAD_AllocateDmacChannel( sDmad *pDmad,
                                          uint8_t bDmac,
                                          uint8_t bSrcID, 
                                          uint8_t bDstID)
{
    uint32_t i;

    /* Can't support peripheral to peripheral */
    if ((( bSrcID != DMAD_TRANSFER_MEMORY ) && ( bDstID != DMAD_TRANSFER_MEMORY ))) 
    {
        return DMAD_ALLOC_FAILED;
    }
    /* dma transfer from peripheral to memory */
    if ( bDstID == DMAD_TRANSFER_MEMORY)
    {
        if( (!DMAIF_IsValidatedPeripherOnDma(bDmac, bSrcID)) )
        {
            return DMAD_ALLOC_FAILED;
        }
    }
    /* dma transfer from memory to peripheral */
    if ( bSrcID == DMAD_TRANSFER_MEMORY )
    {
        if( (!DMAIF_IsValidatedPeripherOnDma(bDmac, bDstID)) )
        {
            return DMAD_ALLOC_FAILED;
        }
    }
    for (i = 0; i < pDmad->numChannels; i ++)
    {
        if ( pDmad->dmaChannels[bDmac][i].state == DMAD_FREE ) 
        {
            /* Allocate the channel */
            pDmad->dmaChannels[bDmac][i].state = DMAD_IN_USE;
            /* Get general informations */
            pDmad->dmaChannels[bDmac][i].bSrcPeriphID = bSrcID;
            pDmad->dmaChannels[bDmac][i].bDstPeriphID = bDstID;
            pDmad->dmaChannels[bDmac][i].bSrcTxIfID =
                DMAIF_Get_ChannelNumber(bDmac, bSrcID, 0);
            pDmad->dmaChannels[bDmac][i].bSrcRxIfID =
                DMAIF_Get_ChannelNumber(bDmac, bSrcID, 1);
            pDmad->dmaChannels[bDmac][i].bDstTxIfID =
                DMAIF_Get_ChannelNumber(bDmac, bDstID, 0);
            pDmad->dmaChannels[bDmac][i].bDstTxIfID =
                DMAIF_Get_ChannelNumber(bDmac, bDstID, 1);

            return ((bDmac << 8)) | ((i) & 0xFF);
        }
    }
    return DMAD_ALLOC_FAILED;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Initialize DMA driver instance.
 * \param pDmad Pointer to DMA driver instance.
 * \param bPollingMode Polling DMA transfer:
 *                     1. Via DMAD_IsTransferDone(); or
 *                     2. Via DMAD_Handler().
 */
void DMAD_Initialize( sDmad *pDmad,
                      uint8_t bPollingMode )
{
    uint32_t i, j;
    
    assert( pDmad != NULL ) ;
    
    pDmad->pDmacs[0] = DMAC0;
    pDmad->pDmacs[1] = DMAC1;
    pDmad->pollingMode = bPollingMode;
    pDmad->numControllers = 2;
    pDmad->numChannels    = 8;
    
    for (i = 0; i < pDmad->numControllers; i ++)
    {
        for (j = 0; j < pDmad->numChannels; j ++)
        {
            pDmad->dmaChannels[i][j].fCallback = 0;
            pDmad->dmaChannels[i][j].pArg      = 0;

            pDmad->dmaChannels[i][j].bIrqOwner    = 0;
            pDmad->dmaChannels[i][j].bSrcPeriphID = 0;
            pDmad->dmaChannels[i][j].bDstPeriphID = 0;
            pDmad->dmaChannels[i][j].bSrcTxIfID   = 0;
            pDmad->dmaChannels[i][j].bSrcRxIfID   = 0;
            pDmad->dmaChannels[i][j].bDstTxIfID   = 0;
            pDmad->dmaChannels[i][j].bDstRxIfID   = 0;
            
            pDmad->dmaChannels[i][j].state = DMAD_FREE;
        }
    }
}

/**
 * \brief DMA interrupt handler
 * \param pDmad Pointer to DMA driver instance.
 */
void DMAD_Handler( sDmad *pDmad )
{
    Dmac *pDmac;
    sDmadChannel *pCh;
    uint32_t _iController, iChannel;
    uint32_t dmaSr, chSr;
    uint32_t dmaRc = DMAD_OK;

    assert( pDmad != NULL ) ;
    
    for (_iController = 0; _iController < pDmad->numControllers; _iController ++)
    {
        pDmac = pDmad->pDmacs[_iController];

        /* Check raw status but not masked one for polling mode support */
        dmaSr = DMAC_GetStatus( pDmac );
        if ((dmaSr & 0x00FFFFFF) == 0) continue;

        chSr  = DMAC_GetChannelStatus( pDmac );
        //printf("iDma(%x,%x)\n\r", dmaSr, chSr);

        for (iChannel = 0; iChannel < pDmad->numChannels; iChannel ++)
        {
            uint8_t bExec = 1;

            pCh = &pDmad->dmaChannels[_iController][iChannel];
            /* Error */
            if (dmaSr & (DMAC_EBCIDR_ERR0 << iChannel))
            {
                DMAC_DisableChannel( pDmac, iChannel );
                if (pCh->state > DMAD_IN_USE)   pCh->state = DMAD_STALL;
                dmaRc = DMAD_ERROR;
            }
            /* Chained buffer complete */
            else if (dmaSr & (DMAC_EBCIDR_CBTC0 << iChannel))
            {
                DMAC_DisableChannel( pDmac, iChannel );
                if (pCh->state > DMAD_IN_USE)   pCh->state = DMAD_IN_USE;
                dmaRc = DMAD_OK;
                
            }
            /* Buffer complete */
            else if (dmaSr & (DMAC_EBCIDR_BTC0 << iChannel))
            {
                dmaRc = DMAD_PARTIAL_DONE;
                /* Re-enable */
                if ((chSr & (DMAC_CHSR_ENA0 << iChannel)) == 0)
                {
                    DMAC_EnableChannel( pDmac, iChannel );
                }
            }
            else
            {
                bExec = 0;
            }
            /* Execute callback */
            if (bExec && pCh->fCallback)
            {
                pCh->fCallback(dmaRc, pCh->pArg);
            }
        }
    }
}

/**
 * \brief Allocate a DMA channel for upper layer.
 * \param pDmad  Pointer to DMA driver instance.
 * \param bSrcID Source peripheral ID, 0xFF for memory.
 * \param bDstID Destination peripheral ID, 0xFF for memory.
 * \return Channel number if allocation sucessful, return 
 * DMAD_ALLOC_FAILED if allocation failed.
 */
uint32_t DMAD_AllocateChannel( sDmad *pDmad,
                               uint8_t bSrcID, 
                               uint8_t bDstID)
{
    uint32_t _iController;
    uint32_t _dwChannel = DMAD_ALLOC_FAILED;

    for ( _iController = 0; _iController < pDmad->numControllers; _iController ++)
    {
        _dwChannel = DMAD_AllocateDmacChannel( pDmad, _iController,
                                              bSrcID, bDstID );
        if (_dwChannel != DMAD_ALLOC_FAILED)
            break;
    }
    return _dwChannel;
}

/**
 * \brief Free the specified DMA channel.
 * \param pDmad     Pointer to DMA driver instance.
 * \param _dwChannel ControllerNumber << 8 | ChannelNumber.
 */
eDmadRC DMAD_FreeChannel( sDmad *pDmad, uint32_t _dwChannel )
{
    uint8_t _iController = (_dwChannel >> 8);
    uint8_t iChannel    = (_dwChannel) & 0xFF;
    
    assert( pDmad != NULL ) ;
    switch ( pDmad->dmaChannels[_iController][iChannel].state )
    {

    case DMAD_IN_XFR:
        return DMAD_BUSY;

    case DMAD_IN_USE:
        pDmad->dmaChannels[_iController][iChannel].state = DMAD_FREE;
        break;
    }   
	return DMAD_OK;
}

/**
 * \brief Set the callback function for DMA channel transfer.
 * \param pDmad     Pointer to DMA driver instance.
 * \param _dwChannel ControllerNumber << 8 | ChannelNumber.
 * \param fCallback Pointer to callback function.
 * \param pArg Pointer to optional argument for callback.
 */
eDmadRC DMAD_SetCallback( sDmad *pDmad, uint32_t _dwChannel,
                          DmadTransferCallback fCallback, void* pArg )
{
    uint8_t _iController = (_dwChannel >> 8);
    uint8_t iChannel    = (_dwChannel) & 0xFF;
    
    assert( pDmad != NULL ) ;
    if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_FREE )
        return DMAD_ERROR;
    else if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_IN_XFR )
        return DMAD_BUSY;
    
    pDmad->dmaChannels[_iController][iChannel].fCallback = fCallback;
    pDmad->dmaChannels[_iController][iChannel].pArg = pArg;
    
    return DMAD_OK;
}

/**
 * \brief Configure Picture-in-Picture mode for DMA transfer.
 * \param pDmad     Pointer to DMA driver instance.
 * \param _dwChannel ControllerNumber << 8 | ChannelNumber.
 * \param srcPIP    Source PIP setting.
 * \param dstPIP    Destination PIP setting.
 */
eDmadRC DMAD_ConfigurePIP( sDmad *pDmad, 
                           uint32_t _dwChannel,
                           uint32_t dwSrcPIP, 
                           uint32_t dwDstPIP )
{
    uint8_t _iController = (_dwChannel >> 8);
    uint8_t iChannel    = (_dwChannel) & 0xFF;
    
    assert( pDmad != NULL ) ;
    Dmac *pDmac = pDmad->pDmacs[_iController];
    if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_FREE )
        return DMAD_ERROR;
    else if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_IN_XFR )
        return DMAD_BUSY;

    DMAC_SetPipMode(pDmac, iChannel, dwSrcPIP, dwDstPIP);
    return DMAD_OK;
}

/**
 * \brief Enable clock of the DMA peripheral, Enable the dma peripheral, 
 * configure configuration register for DMA transfer.
 * \param pDmad     Pointer to DMA driver instance.
 * \param _dwChannel ControllerNumber << 8 | ChannelNumber.
 * \param dwCfg     Configuration value.
 */
eDmadRC DMAD_PrepareChannel( sDmad *pDmad, 
                             uint32_t _dwChannel,
                             uint32_t dwCfg )
{
    uint8_t _iController = (_dwChannel >> 8);
    uint8_t iChannel    = (_dwChannel) & 0xFF;
    uint32_t _dwdmaId;

    assert( pDmad != NULL ) ;
    Dmac *pDmac = pDmad->pDmacs[_iController];

    if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_FREE )
        return DMAD_ERROR;
    else if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_IN_XFR )
        return DMAD_BUSY;
    DMAC_SetCFG( pDmac, iChannel, dwCfg );

    _dwdmaId = (_iController == 0) ? ID_DMAC0 : ID_DMAC1;
    /* Enable clock of the DMA peripheral */
    if (!PMC_IsPeriphEnabled( _dwdmaId ))
    {
        PMC_EnablePeripheral( _dwdmaId );
    }
    /* Enables the DMAC peripheral. */
    DMAC_Enable( pDmac );
    /* Disables DMAC interrupt for the given channel. */
    DMAC_DisableIt (pDmac, 
                    (DMAC_EBCIDR_BTC0 << iChannel)
                   |(DMAC_EBCIDR_CBTC0 << iChannel)
                   |(DMAC_EBCIDR_ERR0 << iChannel) );
    /* Disable the given dma channel. */
    DMAC_DisableChannel( pDmac, iChannel );
    /* Clear dummy status */
    DMAC_GetChannelStatus( pDmac );
    DMAC_GetStatus (pDmac);
    return DMAD_OK;
}

/**
 * \brief Check if DMA transfer is finished.
 *        In polling mode DMAD_Handler() is polled.
 * \param pDmad     Pointer to DMA driver instance.
 * \param _dwChannel ControllerNumber << 8 | ChannelNumber.
 */
eDmadRC DMAD_IsTransferDone( sDmad *pDmad, uint32_t _dwChannel )
{
    uint8_t _iController = (_dwChannel >> 8);
    uint8_t iChannel    = (_dwChannel) & 0xFF;

    assert( pDmad != NULL ) ;
    if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_FREE )
        return DMAD_ERROR;
    else if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_IN_XFR )
    {
        if ( pDmad->pollingMode ) DMAD_Handler( pDmad );
        return DMAD_BUSY;
    }
    return DMAD_OK;
}

/**
 * \brief Clear the automatic mode that services the next-to-last 
    buffer transfer.
 * \param pDmad     Pointer to DMA driver instance.
 * \param _dwChannel ControllerNumber << 8 | ChannelNumber.
 */
void DMAD_ClearAuto( sDmad *pDmad, uint32_t _dwChannel )
{
    uint8_t _iController = (_dwChannel >> 8);
    uint8_t iChannel    = (_dwChannel) & 0xFF;
    Dmac *pDmac;
    assert( pDmad != NULL ) ;
    
    pDmac = pDmad->pDmacs[_iController];
    DMAC_DisableAutoMode( pDmac, iChannel );   
}

/**
 * \brief Start DMA transfer.
 * \param pDmad     Pointer to DMA driver instance.
 * \param _dwChannel ControllerNumber << 8 | ChannelNumber.
 */
eDmadRC DMAD_StartTransfer( sDmad *pDmad, uint32_t _dwChannel )
{
    uint8_t _iController = (_dwChannel >> 8);
    uint8_t iChannel    = (_dwChannel) & 0xFF;
    
    assert( pDmad != NULL ) ;
    Dmac *pDmac = pDmad->pDmacs[_iController];

    if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_FREE )
        return DMAD_ERROR;
    else if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_IN_XFR )
        return DMAD_BUSY;
    /* Change state to transferring */
    pDmad->dmaChannels[_iController][iChannel].state = DMAD_IN_XFR;

    if ( pDmad->pollingMode == 0 )
    {
        /* Monitor status in interrupt handler */
        DMAC_EnableIt(pDmac, (DMAC_EBCIDR_BTC0 << iChannel)
                            |(DMAC_EBCIDR_CBTC0 << iChannel)
                            |(DMAC_EBCIDR_ERR0 << iChannel) );
    }
    DMAC_EnableChannel(pDmac, iChannel);
    return DMAD_OK;
}

/**
 * \brief Start DMA transfers on the same controller.
 * \param pDmad      Pointer to DMA driver instance.
 * \param bDmac      DMA Controller number. 
 * \param bmChannels Channels bitmap.
 */
eDmadRC DMAD_StartTransfers( sDmad *pDmad, uint8_t bDmac, uint32_t bmChannels )
{
    uint32_t iChannel;
    uint32_t bmChs = 0, bmIts = 0;

    assert( pDmad != NULL ) ;
    Dmac *pDmac = pDmad->pDmacs[bDmac];

    for (iChannel = 0; iChannel < pDmad->numChannels; iChannel ++)
    {
        uint32_t bmChBit = 1 << iChannel;

        /* Skipped channels */
        if ( pDmad->dmaChannels[bDmac][iChannel].state == DMAD_FREE )
            continue;
        else if ( pDmad->dmaChannels[bDmac][iChannel].state == DMAD_IN_XFR )
            continue;
        /* Log to start bit map */
        if (bmChannels & bmChBit)
        {
            bmChs |= bmChBit;
            bmIts |= (  (DMAC_EBCIDR_BTC0 << iChannel)
                       |(DMAC_EBCIDR_CBTC0 << iChannel)
                       |(DMAC_EBCIDR_ERR0 << iChannel) );
            /* Change state */
            pDmad->dmaChannels[bDmac][iChannel].state = DMAD_IN_XFR;
        }
    }

    DMAC_EnableChannels(pDmac, bmChs);
    if ( pDmad->pollingMode == 0 )
    {
        /* Monitor status in interrupt handler */
        DMAC_EnableIt( pDmac, bmIts );
    }
    
    return DMAD_OK;
}

/**
 * \brief Stop DMA transfer.
 * \param pDmad     Pointer to DMA driver instance.
 * \param _dwChannel ControllerNumber << 8 | ChannelNumber.
 */
eDmadRC DMAD_StopTransfer( sDmad *pDmad, uint32_t _dwChannel )
{
    uint8_t _iController = (_dwChannel >> 8);
    uint8_t iChannel    = (_dwChannel) & 0xFF;
    
    assert( pDmad != NULL ) ;
    Dmac *pDmac = pDmad->pDmacs[_iController];
    sDmadChannel *pCh = &pDmad->dmaChannels[_iController][iChannel];

    uint32_t to = 0x1000;

    if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_FREE )
        return DMAD_ERROR;

    if ( pDmad->dmaChannels[_iController][iChannel].state != DMAD_IN_XFR )
        return DMAD_OK;

    /* Suspend */
    DMAC_SuspendChannel(pDmac, iChannel);

    /* Poll empty */
    for (;to; to --)
    {
        if (DMAC_GetChannelStatus(pDmac) & (DMAC_CHSR_EMPT0 << iChannel))
        {
            break;
        }
    }

    /* Disable channel */
    DMAC_DisableChannel(pDmac, iChannel);
    /* Disable interrupts */
    DMAC_DisableIt(pDmac, (DMAC_EBCIDR_BTC0 << iChannel)
                         |(DMAC_EBCIDR_CBTC0 << iChannel)
                         |(DMAC_EBCIDR_ERR0 << iChannel) );
    /* Clear pending status */
    DMAC_GetChannelStatus(pDmac);
    DMAC_GetStatus(pDmac);
    /* Resume */
    DMAC_RestoreChannel(pDmac, iChannel);
    /* Change state */
    pDmad->dmaChannels[_iController][iChannel].state = DMAD_IN_USE;
    /* Invoke callback */
    if (pCh->fCallback) pCh->fCallback(DMAD_CANCELED, pCh->pArg);
    return DMAD_OK;
}

/**
 * \brief Configure DMA for a single transfer.
 * \param pDmad     Pointer to DMA driver instance.
 * \param _dwChannel ControllerNumber << 8 | ChannelNumber.
 */
eDmadRC DMAD_PrepareSingleTransfer( sDmad *pDmad, 
                                    uint32_t _dwChannel,
                                    sDmaTransferDescriptor *pXfrDesc )
{
    uint8_t _iController = (_dwChannel >> 8);
    uint8_t iChannel    = (_dwChannel) & 0xFF;
    Dmac *pDmac = pDmad->pDmacs[_iController];

    if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_FREE )
        return DMAD_ERROR;
    if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_IN_XFR )
        return DMAD_BUSY;
    
    DMAC_SetSourceAddr(pDmac, iChannel, pXfrDesc->dwSrcAddr);
    DMAC_SetDestinationAddr(pDmac, iChannel, pXfrDesc->dwDstAddr);
    DMAC_SetDescriptorAddr(pDmac, iChannel, 0, 0);
    DMAC_SetControlA(pDmac, iChannel, pXfrDesc->dwCtrlA);
    DMAC_SetControlB(pDmac, iChannel, pXfrDesc->dwCtrlB);

    return DMAD_OK;
}

/**
 * \brief Configure DMA multi-buffer transfers using linked lists
 * \param pDmad     Pointer to DMA driver instance.
 * \param _dwChannel ControllerNumber << 8 | ChannelNumber.
 * \param pXfrDesc  Pointer to DMA Linked List.
 */
eDmadRC DMAD_PrepareMultiTransfer( sDmad *pDmad, 
                                   uint32_t _dwChannel,
                                   sDmaTransferDescriptor *pXfrDesc )
{
    uint8_t _iController = (_dwChannel >> 8);
    uint8_t iChannel    = (_dwChannel) & 0xFF;
    
    assert( pDmad != NULL ) ;
    Dmac *pDmac = pDmad->pDmacs[_iController];

    if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_FREE )
        return DMAD_ERROR;
    if ( pDmad->dmaChannels[_iController][iChannel].state == DMAD_IN_XFR )
        return DMAD_BUSY;
    
    DMAC_SetDescriptorAddr( pDmac, iChannel, (uint32_t)pXfrDesc, 0 );
    DMAC_SetControlB( pDmac, iChannel, 0);

    return DMAD_OK;
}

/**@}*/

