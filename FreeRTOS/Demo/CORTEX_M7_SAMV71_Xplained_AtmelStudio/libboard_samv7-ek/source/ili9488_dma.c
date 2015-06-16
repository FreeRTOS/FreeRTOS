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
 * Implementation of ILI9488 SPI DMA driver.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "board.h"

#include <string.h>
#include <stdio.h>

#ifdef BOARD_LCD_ILI9488

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/
/** Pins to configure for the application. */
static const Pin ILI9488_CDS[] = { BOARD_LCD_PIN_CDS};

static sIli9488Dma         ili9488Dma;
static sIli9488DmaCtl      ili9488DmaCtl;
 /* Maximum 5 bytes data buffer */
static uint32_t paramBuf[5];
static sXdmad xDmaLcd;

void XDMAC_Handler(void)
{
    XDMAD_Handler(&xDmaLcd);
}

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

#if defined(BOARD_LCD_SMC)

/**
 * \brief Configure SMC timing for static memory (LCD)
 */
static void _ILI9488_ConfigureSmc( void )
{
    /* Enable peripheral clock */
    PMC_EnablePeripheral( ID_SMC ) ;

    /* Configure SMC, NCS3 is assigned to LCD */

    SMC->SMC_CS_NUMBER[SMC_EBI_LCD_CS].SMC_SETUP = SMC_SETUP_NWE_SETUP(2)
                                     | SMC_SETUP_NCS_WR_SETUP(0)
                                     | SMC_SETUP_NRD_SETUP(0)
                                     | SMC_SETUP_NCS_RD_SETUP(0);

    SMC->SMC_CS_NUMBER[SMC_EBI_LCD_CS].SMC_PULSE = SMC_PULSE_NWE_PULSE(6)
                                     | SMC_PULSE_NCS_WR_PULSE(0xA)
                                     | SMC_PULSE_NRD_PULSE(0xA)
                                     | SMC_PULSE_NCS_RD_PULSE(0xA);

    SMC->SMC_CS_NUMBER[SMC_EBI_LCD_CS].SMC_CYCLE = SMC_CYCLE_NWE_CYCLE(0xA)
                                     | SMC_CYCLE_NRD_CYCLE(0xA);

    SMC->SMC_CS_NUMBER[SMC_EBI_LCD_CS].SMC_MODE  = SMC_MODE_READ_MODE
                                     | SMC_MODE_WRITE_MODE
                                     | SMC_MODE_DBW_16_BIT
                                     | SMC_MODE_EXNW_MODE_DISABLED
                                     | SMC_MODE_TDF_CYCLES(0xF);
}
#endif


/**
 * \brief ILI9488_SPI xDMA Rx callback
 */ 
static void _ILI9488_Rx_CB(void)
{
    if(!ili9488DmaCtl.Cds)
       ili9488DmaCtl.rxDone = 1;
}

/**
 * \brief ILI9488_SPI xDMA Tx callback
 */ 
static void _ILI9488_Tx_CB(void)
{
    volatile uint32_t i;
    if(ili9488DmaCtl.Cds)
    {
        for(i = 0; i<0xF; i++);
        PIO_Set(ILI9488_CDS);
        ili9488DmaCtl.Cds = 0;
    }
    ili9488DmaCtl.txDone = 1;
}

/**
 * \brief Initializes the ILI9488Dma structure and the corresponding DMA hardware.
 * select value.
 */
static void _ILI9488DmaInitialize(void)
{
    ili9488DmaCtl.Cds = 1;
    ili9488DmaCtl.rxDone = 0;
    ili9488DmaCtl.txDone = 1;

    ili9488Dma.xdmaD = &xDmaLcd;
    ili9488Dma.xdmaD->pXdmacs = XDMAC;
    ili9488Dma.ili9488DmaTxChannel = 0;
    ili9488Dma.ili9488DmaRxChannel = 0;
    ili9488Dma.xdmaInt = 0;
    ili9488Dma.pSpiHw = ILI9488_SPI;
    ili9488Dma.spiId = ILI9488_SPI_ID;
}

/**
 * \brief This function initialize the appropriate DMA channel for Rx/Tx channel of SPI or SMC
 * \returns             0 if the transfer has been started successfully; otherwise returns
 * ILI9488_ERROR_XX is the driver is in use, or ILI9488_ERROR_XX if the command is not
 * valid.
 */
static uint8_t _ILI9488DmaConfigChannels(void)
{
    uint32_t srcType,dstType;

    /* Driver initialize */
    XDMAD_Initialize(  ili9488Dma.xdmaD, 0 );

    XDMAD_FreeChannel( ili9488Dma.xdmaD, ili9488Dma.ili9488DmaTxChannel);
    XDMAD_FreeChannel( ili9488Dma.xdmaD, ili9488Dma.ili9488DmaRxChannel);

#if !defined(BOARD_LCD_SMC)
    srcType = XDMAD_TRANSFER_MEMORY;
    dstType = ili9488Dma.spiId;
#else
    srcType = XDMAD_TRANSFER_MEMORY;
    dstType = XDMAD_TRANSFER_MEMORY;
#endif

    /* Allocate a DMA channel for  ILI9488_SPI TX. */
    ili9488Dma.ili9488DmaTxChannel = XDMAD_AllocateChannel( ili9488Dma.xdmaD, srcType, dstType);
    {
        if ( ili9488Dma.ili9488DmaTxChannel == XDMAD_ALLOC_FAILED )
        {
            return ILI9488_ERROR_DMA_ALLOCATE_CHANNEL;
        }
    }

    /* Allocate a DMA channel for ILI9488_SPI  RX. */
    ili9488Dma.ili9488DmaRxChannel = XDMAD_AllocateChannel( ili9488Dma.xdmaD, dstType, srcType);
    {
        if ( ili9488Dma.ili9488DmaRxChannel == XDMAD_ALLOC_FAILED )
        {
            return ILI9488_ERROR_DMA_ALLOCATE_CHANNEL; 
        }
    }

    /* Setup callbacks for ILI9488_SPI RX */
    XDMAD_SetCallback(ili9488Dma.xdmaD, ili9488Dma.ili9488DmaRxChannel, (XdmadTransferCallback)_ILI9488_Rx_CB, &ili9488Dma);
    if (XDMAD_PrepareChannel( ili9488Dma.xdmaD, ili9488Dma.ili9488DmaRxChannel ))
        return ILI9488_ERROR_DMA_ALLOCATE_CHANNEL;

    /* Setup callbacks for ILI9488_SPI  TX (ignored) */
    XDMAD_SetCallback(ili9488Dma.xdmaD, ili9488Dma.ili9488DmaTxChannel, (XdmadTransferCallback)_ILI9488_Tx_CB, &ili9488Dma);
    if ( XDMAD_PrepareChannel( ili9488Dma.xdmaD, ili9488Dma.ili9488DmaTxChannel ))
        return  ILI9488_ERROR_DMA_ALLOCATE_CHANNEL;

    /* Check if DMA IRQ is enable; if not Enable it */
    if(!(NVIC_GetActive(XDMAC_IRQn)))
    {
      /* Enable interrupt  */ 
      NVIC_EnableIRQ(XDMAC_IRQn);
    }
    return 0;
}

/**
 * \brief Configure the SPI/SMC tx/rx DMA.
 * \returns 0 if the xDMA configuration successfully; otherwise returns
 * ILI9488_ERROR_XXX.
 */
static uint8_t _ILI9488DmaConfigureRxTx(void)
{
    uint32_t txAddress,rxAddress;
    sXdmad *pXdmad;
    pXdmad = ili9488Dma.xdmaD;

#if !defined(BOARD_LCD_SMC)
    txAddress = (uint32_t)&ILI9488_SPI->SPI_TDR;
    rxAddress = (uint32_t)&ILI9488_SPI->SPI_RDR;
    ili9488Dma.xdmadExtTxCfg.mbr_cfg = 
          XDMAC_CC_TYPE_PER_TRAN 
        | XDMAC_CC_DSYNC_MEM2PER 
        | XDMAC_CC_DWIDTH_BYTE 
        | XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber(ili9488Dma.spiId, XDMAD_TRANSFER_TX ));

    ili9488Dma.xdmadExtRxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN | XDMAC_CC_DSYNC_PER2MEM | 
            XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber(ili9488Dma.spiId, XDMAD_TRANSFER_RX ));
#else
    txAddress = rxAddress =(uint32_t)ILI9488_BASE_ADDRESS;
    ili9488Dma.xdmadExtTxCfg.mbr_cfg = XDMAC_CC_DWIDTH_HALFWORD;
    ili9488Dma.xdmadExtRxCfg.mbr_cfg = 0;
#endif

    /* Setup DMA TX channel */
    ili9488Dma.xdmadTxCfg.mbr_sa = 0;
    ili9488Dma.xdmadTxCfg.mbr_da = txAddress;
    ili9488Dma.xdmadTxCfg.mbr_ubc =  XDMA_UBC_NVIEW_NDV0 |  XDMA_UBC_NDE_FETCH_DIS| XDMA_UBC_NSEN_UPDATED ;

    ili9488Dma.xdmadTxCfg.mbr_cfg = 
          XDMAC_CC_TYPE_MEM_TRAN 
        | XDMAC_CC_MBSIZE_SINGLE 
        | XDMAC_CC_CSIZE_CHK_1 
        | XDMAC_CC_SIF_AHB_IF0 
        | XDMAC_CC_DIF_AHB_IF1 
        | XDMAC_CC_SAM_INCREMENTED_AM 
        | XDMAC_CC_DAM_FIXED_AM;

    ili9488Dma.xdmadTxCfg.mbr_cfg |= ili9488Dma.xdmadExtTxCfg.mbr_cfg;

    ili9488Dma.xdmadTxCfg.mbr_bc = 0;
    ili9488Dma.xdmadTxCfg.mbr_sus = 0;
    ili9488Dma.xdmadTxCfg.mbr_dus = 0;

    /* Setup RX DMA channel */
    ili9488Dma.xdmadRxCfg.mbr_ubc = XDMA_UBC_NVIEW_NDV0 | XDMA_UBC_NDE_FETCH_DIS | XDMA_UBC_NDEN_UPDATED ;
    ili9488Dma.xdmadRxCfg.mbr_da = 0;
    ili9488Dma.xdmadRxCfg.mbr_sa = rxAddress;

    ili9488Dma.xdmadRxCfg.mbr_cfg = 
          XDMAC_CC_TYPE_MEM_TRAN 
        | XDMAC_CC_MBSIZE_SINGLE 
        | XDMAC_CC_CSIZE_CHK_1 
        | XDMAC_CC_DWIDTH_WORD
        | XDMAC_CC_SIF_AHB_IF1 
        | XDMAC_CC_DIF_AHB_IF0 
        | XDMAC_CC_SAM_FIXED_AM 
        | XDMAC_CC_DAM_INCREMENTED_AM;

    ili9488Dma.xdmadRxCfg.mbr_cfg |= ili9488Dma.xdmadExtRxCfg.mbr_cfg;
    ili9488Dma.xdmadRxCfg.mbr_bc = 0;
    ili9488Dma.xdmadRxCfg.mbr_sus = 0;
    ili9488Dma.xdmadRxCfg.mbr_dus =0;

    /* Put all interrupts on for non LLI list setup of DMA */
    ili9488Dma.xdmaInt =  (XDMAC_CIE_BIE 
                          | XDMAC_CIE_RBIE
                          | XDMAC_CIE_WBIE
                          | XDMAC_CIE_ROIE);

    if (XDMAD_ConfigureTransfer( pXdmad, ili9488Dma.ili9488DmaRxChannel, &ili9488Dma.xdmadRxCfg, 0, 0, ili9488Dma.xdmaInt))
        return ILI9488_ERROR_DMA_CONFIGURE;

    if (XDMAD_ConfigureTransfer( pXdmad, ili9488Dma.ili9488DmaTxChannel, &ili9488Dma.xdmadTxCfg, 0, 0, ili9488Dma.xdmaInt))
        return ILI9488_ERROR_DMA_CONFIGURE;
    return 0;
}

/**
 * \brief Update Rx/Tx DMA configuration with new buffer address and buffer size.
 * \param pTxBuffer point to Tx buffer address
 * \param wTxSize  Tx buffer size in byte
 * \param pRxBuffer point to Rx buffer address
 * \param wRxSize Rx buffer size in byte
 * \returns 0 if the xDMA configuration successfully; otherwise returns
 * ILI9488_DMA_ERROR_XXX.
 */
static uint8_t _ILI9488DmaUpdateBuffer(uint16_t *pTxBuffer,uint32_t wTxSize, uint32_t *pRxBuffer,uint32_t wRxSize)
{
    sXdmad *pXdmad;
    pXdmad = ili9488Dma.xdmaD;

    ili9488Dma.xdmadTxCfg.mbr_sa = (uint32_t)pTxBuffer;
    ili9488Dma.xdmadTxCfg.mbr_ubc = wTxSize;

    ili9488Dma.xdmadRxCfg.mbr_da = (uint32_t)pRxBuffer;
    ili9488Dma.xdmadRxCfg.mbr_ubc = wRxSize;

    if (XDMAD_ConfigureTransfer( pXdmad, ili9488Dma.ili9488DmaRxChannel, &ili9488Dma.xdmadRxCfg, 0, 0, ili9488Dma.xdmaInt))
        return ILI9488_ERROR_DMA_CONFIGURE;
    if (XDMAD_ConfigureTransfer( pXdmad, ili9488Dma.ili9488DmaTxChannel, &ili9488Dma.xdmadTxCfg, 0, 0, ili9488Dma.xdmaInt))
        return ILI9488_ERROR_DMA_CONFIGURE;
    return 0;
}


/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Initialize ILI9488 driver with DMA support.
 * \returns 0 if the xDMA configuration successfully; otherwise returns
 * ILI9488_DMA_ERROR_XXX.
 */
uint8_t ILI9488_InitializeWithDma(void)
{
#if defined(BOARD_LCD_SMC)
    _ILI9488_ConfigureSmc();
#endif
    _ILI9488DmaInitialize();
    if (_ILI9488DmaConfigChannels()) return ILI9488_ERROR_DMA_ALLOCATE_CHANNEL;
    if(_ILI9488DmaConfigureRxTx()) return ILI9488_ERROR_DMA_CONFIGURE;
    return 0;
}

/**
 * \brief Start ILI9488 DMA transfer .
 * \param pTxBuffer point to Tx buffer address
 * \param wTxSize  Tx buffer size in byte
 * \returns 0 if the xDMA configuration successfully; otherwise returns
 * ILI9488_DMA_ERROR_XXX.
 */
uint8_t ILI9488DmaTxTransfer( uint16_t *pTxBuffer,uint32_t wTxSize)
{
    _ILI9488DmaUpdateBuffer(pTxBuffer, wTxSize, 0, 0);
    SCB_CleanInvalidateDCache();
    if (XDMAD_StartTransfer( ili9488Dma.xdmaD, ili9488Dma.ili9488DmaTxChannel))
        return ILI9488_ERROR_DMA_TRANSFER;
    while(!ili9488DmaCtl.txDone);
    ili9488DmaCtl.txDone = 0;

    return 0;
}

/**
 * \brief Start ILI9488 DMA Rx transfer .
 * \param pRxBuffer point to Rx buffer address
 * \param wRxSize Rx buffer size in byte
 * \returns 0 if the xDMA transfer successfully; otherwise returns ILI9488_DMA_ERROR_XXX.
 */
uint8_t ILI9488DmaRxTransfer(uint32_t *pRxBuffer,uint32_t wRxSize)
{
    uint16_t dummyTxBuffer[5];

    _ILI9488DmaUpdateBuffer(dummyTxBuffer, wRxSize, pRxBuffer, wRxSize);

    SCB_CleanInvalidateDCache();
    if (XDMAD_StartTransfer( ili9488Dma.xdmaD, ili9488Dma.ili9488DmaRxChannel))
        return ILI9488_ERROR_DMA_TRANSFER;

#if !defined(BOARD_LCD_SMC)
    if (XDMAD_StartTransfer( ili9488Dma.xdmaD, ili9488Dma.ili9488DmaTxChannel))
        return ILI9488_ERROR_DMA_TRANSFER;
#endif
    return 0;
}

/**
 * \brief ILI9488 Send command with DMA.
 * \param command Command to be sent
 * \returns 0 if the xDMA transfer successfully; otherwise returns ILI9488_DMA_ERROR_XXX.
 */
uint8_t ILI9488_SendCmd( uint16_t command )
{
    PIO_Clear(ILI9488_CDS);
    ili9488DmaCtl.Cds = 1;
    return ILI9488DmaTxTransfer((uint16_t*)&command, 1 );
}

/**
 * \brief ILI9488 Write register for SPI/SMC mode.
 * \param command Command to be sent
 * \param pTxBuffer Point to tx buffer contains parameters
 * \param bufSize Size of buffer
 * \returns 0 if the xDMA transfer successfully; otherwise returns ILI9488_DMA_ERROR_XXX.
 */
void ILI9488_WriteReg(uint16_t command, uint16_t* pTxBuffer, uint32_t bufSize)
{
    ILI9488_SendCmd(command);
    if(bufSize == 0)  return;
    ILI9488DmaTxTransfer(pTxBuffer,bufSize);
}

/**
 * \brief ILI9488 Read registers for SPI/SMC mode.
 * \param command Command to be sent
 * \param size Size of parameters
 * \returns register value.
 */
uint32_t ILI9488ReadReg(uint16_t cmd,uint32_t size)
{
    uint32_t i;
    uint32_t value = 0;
    uint32_t *ptr;
    uint32_t shift_cnt = size-1;
   
    if (size > 4) return ILI9488_ERROR_DMA_SIZE;

    ILI9488_SendCmd(cmd);
    ILI9488DmaRxTransfer(paramBuf, size+1);

    while(!ili9488DmaCtl.rxDone);
    ili9488DmaCtl.rxDone = 0;

    ptr = &paramBuf[1];
    for(i = 1; i < size+1;i++)
    {
        value |= (*ptr&0xFF)<<(shift_cnt << 3);
        ptr++;
        shift_cnt--;
    }
    return value;
}


/**
 * \brief ILI9488 Read Ext registers for SPI/SMC mode.
 * \param command Command to be sent
 * \param size Size of buffer
 * \returns Ext register value.
 */
uint32_t ILI9488ReadExtReg(uint16_t cmd,uint32_t size)
{
    uint32_t value=0;
 
#if !defined(BOARD_LCD_SMC)
    uint32_t shift_cnt = size-1;
    uint16_t nSpiCnt = 0x81;
    uint16_t def_val = 0;

    if (size > 4) return ILI9488_ERROR_DMA_SIZE;
    while(size > 0)
    {
        ILI9488_WriteReg(ILI9488_CMD_SPI_READ_SETTINGS,&nSpiCnt,1);
        ILI9488_SendCmd(cmd);
        ILI9488DmaRxTransfer( paramBuf,2);
        while(!ili9488DmaCtl.rxDone);
        ili9488DmaCtl.rxDone = 0;
        ILI9488_WriteReg(ILI9488_CMD_SPI_READ_SETTINGS,&def_val,1);
        value |= (paramBuf[1]&0xFF)<<(shift_cnt << 3);
        nSpiCnt++;
        shift_cnt--;
        size--;
    }
#else
    value = ILI9488ReadReg(cmd,size);
#endif
    return value;
}
#endif  //BOARD_LCD_ILI9488
