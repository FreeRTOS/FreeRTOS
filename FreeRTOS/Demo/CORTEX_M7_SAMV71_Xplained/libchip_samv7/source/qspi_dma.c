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
 * \addtogroup spi_dma_module SPI xDMA driver
 * \ingroup lib_spiflash
 * \section Usage
 *
 * <ul>
 * <li> QSPID_Configure() initializes and configures the SPI peripheral and xDMA for data transfer.</li>
 * <li> Configures the parameters for the device corresponding to the cs value by QSPID_ConfigureCS(). </li>
 * <li> Starts a SPI master transfer. This is a non blocking function QSPID_SendCommand(). It will
 * return as soon as the transfer is started..</li>
 * </ul>
 *
 */

/**
 * \file
 *
 * Implementation for the SPI Flash with xDMA driver.
 *
 */


/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** xDMA support */
#define USE_QSPI_DMA

#define TX_MICROBLOCK_LEN       256
#define RX_MICROBLOCK_LEN       256

/*----------------------------------------------------------------------------
 *        Macros
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------
 *        Local Variables
 *----------------------------------------------------------------------------*/


/*  DMA driver instance */
static uint32_t qspiDmaTxChannel;
static uint32_t qspiDmaRxChannel;

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * \brief SPI xDMA Rx callback
 * Invoked on SPi DMA reception done.
 * \param channel DMA channel.
 * \param pArg Pointer to callback argument - Pointer to Qspid instance.   
 */ 
static void QSPID_Rx_Cb(uint32_t channel, Qspid* pArg)
{
    QspidCmd *pQspidCmd = pArg->pCurrentCommand;
    Qspi *pQspiHw = pArg->pQspiHw;
    if (channel != qspiDmaRxChannel)
        return;

    /* Disable the SPI TX & RX */
    QSPI_Disable ( pQspiHw );

    /* Configure and enable interrupt on RC compare */    
    NVIC_ClearPendingIRQ(XDMAC_IRQn);
    NVIC_DisableIRQ(XDMAC_IRQn);

    /* Disable the SPI Peripheral */
    PMC_DisablePeripheral ( pArg->spiId );

    /* Release CS */
    QSPI_ReleaseCS(pQspiHw);

    /* Release the DMA channels */
    XDMAD_FreeChannel(pArg->pXdmad, qspiDmaRxChannel);
    XDMAD_FreeChannel(pArg->pXdmad, qspiDmaTxChannel);

    /* Release the dataflash semaphore */
    pArg->semaphore++;

    printf("\n\r%s\n\r",pArg->pCurrentCommand->pRxBuff);

    /* Invoke the callback associated with the current command */
    if (pQspidCmd && pQspidCmd->callback) {
        //printf("p %d", pArg->semaphore);
        pQspidCmd->callback(0, pQspidCmd->pArgument);
    }
}

/**
 * \brief Configure the DMA Channels: 0 RX, 1 TX.
 * Channels are disabled after configure.
 * \returns 0 if the dma channel configuration successfully; otherwise returns
 * QSPID_ERROR_XXX.
 */
static uint8_t _qspid_configureDmaChannels( Qspid* pQspid )
{

    /* Driver initialize */
    XDMAD_Initialize(  pQspid->pXdmad, 0 );

    XDMAD_FreeChannel( pQspid->pXdmad, qspiDmaTxChannel);
    XDMAD_FreeChannel( pQspid->pXdmad, qspiDmaRxChannel);

    /* Allocate a DMA channel for SPI0/1 TX. */
    qspiDmaTxChannel = XDMAD_AllocateChannel( pQspid->pXdmad, XDMAD_TRANSFER_MEMORY, pQspid->spiId);
    {
        if ( qspiDmaTxChannel == XDMAD_ALLOC_FAILED ) 
        {
            return QSPID_ERROR;
        }
    }
    /* Allocate a DMA channel for SPI0/1 RX. */
    qspiDmaRxChannel = XDMAD_AllocateChannel( pQspid->pXdmad, pQspid->spiId, XDMAD_TRANSFER_MEMORY);
    {
        if ( qspiDmaRxChannel == XDMAD_ALLOC_FAILED ) 
        {
            return QSPID_ERROR;
        }
    }

    /* Setup callbacks for SPI0/1 RX */
    XDMAD_SetCallback(pQspid->pXdmad, qspiDmaRxChannel, (XdmadTransferCallback)QSPID_Rx_Cb, pQspid);
    if (XDMAD_PrepareChannel( pQspid->pXdmad, qspiDmaRxChannel ))
        return QSPID_ERROR;

    /* Setup callbacks for SPI0/1 TX (ignored) */
    XDMAD_SetCallback(pQspid->pXdmad, qspiDmaTxChannel, NULL, NULL);
    if ( XDMAD_PrepareChannel( pQspid->pXdmad, qspiDmaTxChannel ))
        return QSPID_ERROR;


    return 0;
}

/**
 * \brief Configure the DMA source and destination with Linker List mode.
 *
 * \param pCommand Pointer to command
 * \returns 0 if the dma multibuffer configuration successfully; otherwise returns
 * QSPID_ERROR_XXX.
 */
static uint8_t _spid_configureLinkList(Qspi *pQspiHw, void *pXdmad, QspidCmd *pCommand)
{
    sXdmadCfg xdmadRxCfg,xdmadTxCfg;
    uint32_t xdmaCndc;
    uint32_t qspiId;
    if ((unsigned int)pQspiHw == (unsigned int)QSPI ) qspiId = ID_QSPI;



    /* Setup TX  */ 

    xdmadTxCfg.mbr_ubc = TX_MICROBLOCK_LEN;
    xdmadTxCfg.mbr_sa = (uint32_t)pCommand->pTxBuff;
    xdmadTxCfg.mbr_da = (uint32_t)QSPIMEM_ADDR;
    xdmadTxCfg.mbr_cfg = XDMAC_CC_TYPE_MEM_TRAN |
        XDMAC_CC_MBSIZE_SINGLE |
        XDMAC_CC_MEMSET_NORMAL_MODE |
        XDMAC_CC_CSIZE_CHK_1 |
        XDMAC_CC_DWIDTH_BYTE|
        XDMAC_CC_SIF_AHB_IF0 |
        XDMAC_CC_DIF_AHB_IF0 |
        XDMAC_CC_SAM_INCREMENTED_AM |
        XDMAC_CC_DAM_INCREMENTED_AM |
        XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber(  qspiId, XDMAD_TRANSFER_TX ));

    xdmadTxCfg.mbr_bc = 0;
    xdmadTxCfg.mbr_ds =  0;
    xdmadTxCfg.mbr_sus = 0;
    xdmadTxCfg.mbr_dus = 0; 


    /* Setup RX Link List */

    xdmadRxCfg.mbr_ubc = RX_MICROBLOCK_LEN;
    xdmadRxCfg.mbr_sa = (uint32_t)QSPIMEM_ADDR;
    xdmadRxCfg.mbr_da = (uint32_t)pCommand->pRxBuff;
    xdmadRxCfg.mbr_cfg = XDMAC_CC_TYPE_MEM_TRAN |
        XDMAC_CC_MBSIZE_SINGLE |
        XDMAC_CC_MEMSET_NORMAL_MODE |
        XDMAC_CC_CSIZE_CHK_1 |
        XDMAC_CC_DWIDTH_BYTE|
        XDMAC_CC_SIF_AHB_IF0 |
        XDMAC_CC_DIF_AHB_IF0 |
        XDMAC_CC_SAM_INCREMENTED_AM |
        XDMAC_CC_DAM_INCREMENTED_AM |
        XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber(  qspiId, XDMAD_TRANSFER_RX ));

    xdmadRxCfg.mbr_bc = 0;
    xdmadRxCfg.mbr_ds =  0;
    xdmadRxCfg.mbr_sus = 0;
    xdmadRxCfg.mbr_dus = 0; 


    if (XDMAD_ConfigureTransfer( pXdmad, qspiDmaRxChannel, &xdmadRxCfg, 0, 0))
        return QSPID_ERROR;

    if (XDMAD_ConfigureTransfer( pXdmad, qspiDmaTxChannel, &xdmadTxCfg, 0, 0))
        return QSPID_ERROR;


    return 0;
}


/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Initializes the Qspid structure and the corresponding SPI & DMA hardware.
 * select value.
 * The driver will uses DMA channel 0 for RX and DMA channel 1 for TX.
 * The DMA channels are freed automatically when no SPI command processing.
 *
 * \param pQspid  Pointer to a Qspid instance.
 * \param pQspiHw Associated SPI peripheral.
 * \param spiId  SPI peripheral identifier.
 * \param pDmad  Pointer to a Dmad instance. 
 */
uint32_t QSPID_Configure( Qspid *pQspid ,
        Qspi *pQspiHw , 
        uint8_t spiId,
        uint8_t QspiMode,
        sXdmad *pXdmad )
{
    /* Initialize the SPI structure */
    pQspid->pQspiHw = pQspiHw;
    pQspid->spiId  = spiId;
    pQspid->semaphore = 1;
    pQspid->pCurrentCommand = 0;
    pQspid->pXdmad = pXdmad;

    /* Enable the SPI Peripheral ,Execute a software reset of the SPI, Configure SPI in Master Mode*/
    QSPI_Configure ( pQspiHw, pQspid->spiId, QspiMode );

    return 0;
}



/**
 * \brief Starts a SPI master transfer. This is a non blocking function. It will
 *  return as soon as the transfer is started.
 *
 * \param pQspid  Pointer to a Qspid instance.
 * \param pCommand Pointer to the SPI command to execute.
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * QQSPID_ERROR_LOCK is the driver is in use, or QQSPID_ERROR if the command is not
 * valid.
 */
uint32_t QSPID_SendCommand( Qspid *pQspid, QspidCmd *pCommand)
{
    Qspi *pQspiHw = pQspid->pQspiHw;

    /* Try to get the dataflash semaphore */
    if (pQspid->semaphore == 0) {

        return QQSPID_ERROR_LOCK;
    }
    pQspid->semaphore--;

    /* Enable the SPI Peripheral */
    PMC_EnablePeripheral (pQspid->spiId );

    /* SPI chip select */
    SPI_ChipSelect (pQspiHw, 1 << pCommand->spiCs);

    // Initialize the callback
    pQspid->pCurrentCommand = pCommand;

    /* Initialize DMA controller using channel 0 for RX, 1 for TX. */
    if (_spid_configureDmaChannels(pQspid) )
        return QQSPID_ERROR_LOCK;

    /* Configure and enable interrupt on RC compare */    
    NVIC_ClearPendingIRQ(XDMAC_IRQn);
    NVIC_SetPriority( XDMAC_IRQn ,1);
    NVIC_EnableIRQ(XDMAC_IRQn);


    if (_spid_configureLinkList(pQspiHw, pQspid->pXdmad, pCommand))
        return QSPID_ERROR_LOCK;

    /* Enables the SPI to transfer and receive data. */
    SPI_Enable (pQspiHw );

    /* Start DMA 0(RX) && 1(TX) */
    if (XDMAD_StartTransfer( pQspid->pXdmad, qspiDmaRxChannel )) 
        return QSPID_ERROR_LOCK;
    if (XDMAD_StartTransfer( pQspid->pXdmad, qspiDmaTxChannel )) 
        return QSPID_ERROR_LOCK;

    return 0;
}

/**
 * \brief Check if the SPI driver is busy.
 *
 * \param pQspid  Pointer to a Qspid instance.
 * \returns 1 if the SPI driver is currently busy executing a command; otherwise
 */
uint32_t QSPID_IsBusy(const Qspid *pQspid)
{
    if (pQspid->semaphore == 0) {
        return 1;
    }
    else {
        return 0;
    }
}
