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

/** \addtogroup dacc_module Working with DACC
 *  \ingroup peripherals_module
 * The DACC driver provides the interface to configure and use the DACC
 * peripheral.\n
 *
 * The DACC(Digital-to-Analog Converter Controller) converts digital code to 
 * analog output.
 * The data to be converted are sent in a common register for all channels. 
 * It offers up to 2 analog outputs.The output voltage ranges from (1/6)ADVREF 
 * to (5/6)ADVREF.
 *
 * To Enable a DACC conversion,the user has to follow these few steps:
 * <ul>
 * <li> Select an appropriate reference voltage on ADVREF   </li>
 * <li> Configure the DACC according to its requirements and special needs,
 * which could be broken down into several parts:
 * -#   Enable DACC in free running mode by clearing TRGEN in DACC_MR;
 * -#   Configure Refresh Period through setting REFRESH fields
 *      in DACC_MR; The refresh mechanism is used to protect the output analog 
 * value from
 *      decreasing.
 * -#   Enable channels and write digital code to DACC_CDR,in free running mode,
 * the conversion is started right after at least one channel is enabled and 
 * data is written .
 </li>
 * </ul>
 *
 * For more accurate information, please look at the DACC section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref dac_dma.c\n
 * \ref dac_dma.h\n
 */
/*@{*/
/*@}*/
/**
 * \file
 *
 * Implementation of Digital-to-Analog Converter Controller (DACC).
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>
#include <assert.h>

/*  DMA driver instance */
static uint32_t dacDmaTxChannel;
static LinkedListDescriporView1 dmaWriteLinkList[256];
/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Configure the DMA Channels: 0 RX.
 * Channels are disabled after configure.
 * \returns 0 if the dma channel configuration successfully; otherwise returns
 * DAC_ERROR_XXX.
 */
static uint8_t _DacConfigureDmaChannels( DacDma* pDacd )
{

	/* Driver initialize */
	XDMAD_Initialize( pDacd->pXdmad, 0 );

	XDMAD_FreeChannel( pDacd->pXdmad, dacDmaTxChannel);

	/* Allocate a DMA channel for DAC0/1 TX. */
	dacDmaTxChannel = 
		XDMAD_AllocateChannel( pDacd->pXdmad, XDMAD_TRANSFER_MEMORY, ID_DACC);
	if ( dacDmaTxChannel == XDMAD_ALLOC_FAILED ) {
		return DAC_ERROR;
	}

	if ( XDMAD_PrepareChannel( pDacd->pXdmad, dacDmaTxChannel )) 
		return DAC_ERROR;
	return DAC_OK;
}


/**
 * \brief Configure the DMA source and destination with Linker List mode.
 *
 * \param pBuffer Pointer to dac buffer
 * \param size length of buffer
 */

static uint8_t _Dac_configureLinkList(Dacc *pDacHw, void *pXdmad, DacCmd *pCommand)
{
	uint32_t xdmaCndc;
	sXdmadCfg xdmadCfg;
	uint32_t * pBuffer;
	/* Setup TX Link List */
	uint8_t i;
	pBuffer = (uint32_t *)pCommand->pTxBuff;
	for(i = 0; i < pCommand->TxSize; i++){
		dmaWriteLinkList[i].mbr_ubc = XDMA_UBC_NVIEW_NDV1 
									| XDMA_UBC_NDE_FETCH_EN
									| XDMA_UBC_NSEN_UPDATED
									| XDMAC_CUBC_UBLEN(4);
		dmaWriteLinkList[i].mbr_sa = (uint32_t)pBuffer;
		dmaWriteLinkList[i].mbr_da = 
			(uint32_t)&(pDacHw->DACC_CDR[pCommand->dacChannel]);
		if ( i == (pCommand->TxSize - 1 )) {
			if (pCommand->loopback) {
				dmaWriteLinkList[i].mbr_nda = (uint32_t)&dmaWriteLinkList[0];
			} else {
				dmaWriteLinkList[i].mbr_nda = 0;
			}
		} else {
			dmaWriteLinkList[i].mbr_nda = (uint32_t)&dmaWriteLinkList[i+1];
		}
		pBuffer++;
	}
	xdmadCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN 
					 | XDMAC_CC_MBSIZE_SINGLE 
					 | XDMAC_CC_DSYNC_MEM2PER 
					 | XDMAC_CC_CSIZE_CHK_1 
					 | XDMAC_CC_DWIDTH_WORD
					 | XDMAC_CC_SIF_AHB_IF0 
					 | XDMAC_CC_DIF_AHB_IF1 
					 | XDMAC_CC_SAM_INCREMENTED_AM 
					 | XDMAC_CC_DAM_FIXED_AM 
					 | XDMAC_CC_PERID(
						XDMAIF_Get_ChannelNumber(ID_DACC, XDMAD_TRANSFER_TX ));
	xdmaCndc = XDMAC_CNDC_NDVIEW_NDV1 
			 | XDMAC_CNDC_NDE_DSCR_FETCH_EN 
			 | XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED
			 | XDMAC_CNDC_NDDUP_DST_PARAMS_UPDATED ;
	XDMAD_ConfigureTransfer( pXdmad, dacDmaTxChannel, &xdmadCfg, xdmaCndc, 
			(uint32_t)&dmaWriteLinkList[0], XDMAC_CIE_LIE);
	return DAC_OK;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Initializes the DacDma structure and the corresponding DAC & DMA .
 * hardware select value.
 * The driver will uses DMA channel 0 for RX .
 * The DMA channels are freed automatically when no DMA command processing.
 *
 * \param pDacd  Pointer to a DacDma instance.
 * \param pDacHw Associated Dac peripheral.
 * \param DacId  Dac peripheral identifier.
 * \param pDmad  Pointer to a Dmad instance. 
 */
uint32_t Dac_ConfigureDma( DacDma *pDacd ,
		Dacc *pDacHw ,
		uint8_t DacId,
		sXdmad *pXdmad )
{
	/* Initialize the Dac structure */
	pDacd->pDacHw = pDacHw;
	pDacd->dacId  = DacId;
	pDacd->semaphore = 1;
	pDacd->pCurrentCommand = 0;
	pDacd->pXdmad = pXdmad;
	return 0;
}

/**
 * \brief Starts a DAC transfer. This is a non blocking function. It will
 *  return as soon as the transfer is started.
 *
 * \param pDacd  Pointer to a DacDma instance.
 * \param pCommand Pointer to the Dac command to execute.
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * DAC_ERROR_LOCK is the driver is in use, or DAC_ERROR if the command is not
 * valid.
 */
uint32_t Dac_SendData( DacDma *pDacd, DacCmd *pCommand)
{
	Dacc *pDacHw = pDacd->pDacHw;

	/* Try to get the dataflash semaphore */
	if (pDacd->semaphore == 0) {
		return DAC_ERROR_LOCK;
	}
	pDacd->semaphore--;

	// Initialize the callback
	pDacd->pCurrentCommand = pCommand;

	/* Initialize DMA controller using channel 0 for RX. */
	if (_DacConfigureDmaChannels(pDacd) )
		return DAC_ERROR_LOCK;

	if (_Dac_configureLinkList(pDacHw, pDacd->pXdmad, pCommand))
		return DAC_ERROR_LOCK;

	SCB_CleanDCache();

	/* Start DMA TX */
	if (XDMAD_StartTransfer( pDacd->pXdmad, dacDmaTxChannel )) 
		return DAC_ERROR_LOCK;
	return DAC_OK;;
}
