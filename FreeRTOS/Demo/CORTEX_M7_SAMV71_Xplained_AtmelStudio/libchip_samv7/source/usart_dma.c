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
 * <li> USARTD_Configure() initializes and configures the USART peripheral 
 * and xDMA for data transfer.</li>
 * <li> Configures the parameters for the device corresponding to the cs 
 * value by USARTD_ConfigureCS(). </li>
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
#include "string.h"
#include "stdlib.h"

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
	
	/* Release the DMA channels */
	XDMAD_FreeChannel(pArg->pXdmad, pUsartdCh->ChNum);
	pUsartdCh->dmaProgress = 1;
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
	/* Release the DMA channels */
	XDMAD_FreeChannel(pArg->pXdmad, pUsartdCh->ChNum);
  
	pUsartdCh->dmaProgress = 1;
	memory_barrier();
}

/**
 * \brief Configure the USART Rx DMA Destination with Linker List mode.
 *
 * \param UsartChannel Pointer to USART dma channel
 * \returns 0 if the dma multibuffer configuration successfully; otherwise 
 * returnsUSARTD_ERROR_XXX.
 */
static uint8_t _configureRxDma(UsartDma *pUsart, UsartChannel *pUsartRx)
{
	sXdmadCfg xdmadRxCfg;
	uint32_t xdmaCndc, xdmaInt;
	uint32_t i, LLI_Size;
	Usart *pUsartHwRx = pUsart->pUsartHw;
	sXdmad* pXdmadRx = pUsart->pXdmad;
	uint8_t *pBuff = 0;
	
	
	/* Setup RX Single block */
	if(pUsartRx->dmaProgrammingMode < XDMAD_LLI) {
	  xdmadRxCfg.mbr_ubc = pUsartRx->BuffSize;
	  xdmadRxCfg.mbr_da = (uint32_t)pUsartRx->pBuff;
	  
	  xdmadRxCfg.mbr_sa = (uint32_t)&pUsartHwRx->US_RHR;
	  xdmadRxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
						XDMAC_CC_MBSIZE_SIXTEEN |
						XDMAC_CC_DSYNC_PER2MEM |
						XDMAC_CC_CSIZE_CHK_1 |
						XDMAC_CC_DWIDTH_BYTE |
						XDMAC_CC_SIF_AHB_IF1 |
						XDMAC_CC_DIF_AHB_IF0 |
						XDMAC_CC_SAM_FIXED_AM |
						XDMAC_CC_DAM_INCREMENTED_AM |
						XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber
							( pUsart->usartId, XDMAD_TRANSFER_RX ));
	  
	  xdmadRxCfg.mbr_bc = 0;
	  if(pUsartRx->dmaProgrammingMode == XDMAD_MULTI)
	  {
		xdmadRxCfg.mbr_bc = pUsartRx->dmaBlockSize;
	  }
	  xdmadRxCfg.mbr_sus = 0;
	  xdmadRxCfg.mbr_dus =0;
	  xdmaCndc = 0;
	  xdmaInt =  (XDMAC_CIE_BIE   |
				 XDMAC_CIE_DIE   |
				 XDMAC_CIE_FIE   |
				 XDMAC_CIE_RBIE  |
				 XDMAC_CIE_WBIE  |
				 XDMAC_CIE_ROIE);
	} else if(pUsartRx->dmaProgrammingMode == XDMAD_LLI) {
		
	/* Setup RX Link List */
		LLI_Size = pUsartRx->dmaBlockSize;
		pBuff = pUsartRx->pBuff;
		if(pUsartRx->pLLIview != NULL)
		{
		  free(pUsartRx->pLLIview);
		  pUsartRx->pLLIview = NULL;
		}
		
		pUsartRx->pLLIview = malloc(sizeof(LinkedListDescriporView1)*LLI_Size);
		if( pUsartRx->pLLIview == NULL) {
		  TRACE_ERROR(" Can not allocate memory to Rx LLI");
		  return USARTD_ERROR;
		}
		xdmadRxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
							XDMAC_CC_MBSIZE_SIXTEEN |
							XDMAC_CC_DSYNC_PER2MEM |
							XDMAC_CC_MEMSET_NORMAL_MODE |
							XDMAC_CC_CSIZE_CHK_1 |
							XDMAC_CC_DWIDTH_BYTE |
							XDMAC_CC_SIF_AHB_IF1 |
							XDMAC_CC_DIF_AHB_IF0 |
							XDMAC_CC_SAM_FIXED_AM |
							XDMAC_CC_DAM_INCREMENTED_AM |
							XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber
								( pUsart->usartId, XDMAD_TRANSFER_RX ));
		xdmadRxCfg.mbr_bc = 0;
		for (i = 0; i < LLI_Size; i++) {
			 pUsartRx->pLLIview[i].mbr_ubc = XDMA_UBC_NVIEW_NDV1 |
											XDMA_UBC_NSEN_UNCHANGED | 
											XDMA_UBC_NDEN_UPDATED |
											((i== LLI_Size- 1)? ( 
											(pUsartRx->dmaRingBuffer)? 
											XDMA_UBC_NDE_FETCH_EN : 0): 
											XDMA_UBC_NDE_FETCH_EN) | 
											pUsartRx->BuffSize;
				pUsartRx->pLLIview[i].mbr_sa = (uint32_t)&pUsartHwRx->US_RHR;
				pUsartRx->pLLIview[i].mbr_da = (uint32_t)pBuff;
				pUsartRx->pLLIview[i].mbr_nda = (i == ( LLI_Size - 1))? 
					( (pUsartRx->dmaRingBuffer)? (uint32_t)pUsartRx->pLLIview : 0 )
					:(uint32_t)&pUsartRx->pLLIview[ i + 1 ];
				pBuff += pUsartRx->BuffSize;
			} 
		xdmaCndc = XDMAC_CNDC_NDVIEW_NDV1 | 
				XDMAC_CNDC_NDE_DSCR_FETCH_EN |
				XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED|
				XDMAC_CNDC_NDDUP_DST_PARAMS_UPDATED ;
		xdmaInt = ((pUsartRx->dmaRingBuffer)? XDMAC_CIE_BIE : XDMAC_CIE_LIE);
	} else {
	  return 1;
	}
	memory_barrier();
	if (XDMAD_ConfigureTransfer( 
			pXdmadRx, pUsartRx->ChNum, &xdmadRxCfg, xdmaCndc, 
			(uint32_t)pUsartRx->pLLIview, xdmaInt))
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
static uint8_t _configureTxDma(UsartDma *pUsart, UsartChannel *pUsartTx)
{
	sXdmadCfg xdmadTxCfg;
	uint32_t xdmaCndc, xdmaInt, LLI_Size, i;
	uint8_t *pBuff = 0;
	Usart *pUsartHwTx = pUsart->pUsartHw;
	sXdmad* pXdmadTx = pUsart->pXdmad;
	
	/* Setup TX Link List */ 
	
	if(pUsartTx->dmaProgrammingMode < XDMAD_LLI) {
		/* Number of Data */
		xdmadTxCfg.mbr_ubc =   pUsartTx->BuffSize;
		/* Source and Destination address of DMA */
		xdmadTxCfg.mbr_sa = (uint32_t)pUsartTx->pBuff;
		xdmadTxCfg.mbr_da = (uint32_t)&pUsartHwTx->US_THR;
		/* DMA Channel configuration */
		xdmadTxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
						   XDMAC_CC_MBSIZE_SIXTEEN |
						   XDMAC_CC_DSYNC_MEM2PER |
						   XDMAC_CC_CSIZE_CHK_1 |
						   XDMAC_CC_DWIDTH_BYTE|
						   XDMAC_CC_SIF_AHB_IF0 |
						   XDMAC_CC_DIF_AHB_IF1 |
						   XDMAC_CC_SAM_INCREMENTED_AM |
						   XDMAC_CC_DAM_FIXED_AM |
						   XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber
							( pUsart->usartId, XDMAD_TRANSFER_TX ));
	  
	  xdmadTxCfg.mbr_bc = 0;
	  if(pUsartTx->dmaProgrammingMode == XDMAD_MULTI)
	  {
		xdmadTxCfg.mbr_bc = pUsartTx->dmaBlockSize;
	  }
	  xdmadTxCfg.mbr_sus = 0;
	  xdmadTxCfg.mbr_dus =0;
	  xdmadTxCfg.mbr_ds= 0;
	  xdmaCndc = 0;
	  /* Enable End of Block; Read Bus error;  Write Bus Error; 
	  Overflow Error interrupt */
	  xdmaInt =  (XDMAC_CIE_BIE    |
				   XDMAC_CIE_RBIE  |
				   XDMAC_CIE_WBIE  |
				   XDMAC_CIE_ROIE); 
	} else if(pUsartTx->dmaProgrammingMode == XDMAD_LLI) {
		LLI_Size = pUsartTx->dmaBlockSize;
		pBuff = pUsartTx->pBuff;
		/* If channel's LLI is already configured and application 
		want to reconfigured it, free before re-allocating memory */
		if(pUsartTx->pLLIview != NULL) {
		  free(pUsartTx->pLLIview);
		  pUsartTx->pLLIview = NULL;
		}
		pUsartTx->pLLIview = malloc(sizeof(LinkedListDescriporView1)*LLI_Size);
		
		if( pUsartTx->pLLIview == NULL) {
		  TRACE_ERROR(" Can not allocate memory to Tx LLI");
		  return USARTD_ERROR;
		}
		
		xdmadTxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
							   XDMAC_CC_MBSIZE_SIXTEEN |
							   XDMAC_CC_DSYNC_MEM2PER |
							   XDMAC_CC_MEMSET_NORMAL_MODE |
							   XDMAC_CC_CSIZE_CHK_1 |
							   XDMAC_CC_DWIDTH_BYTE |
							   XDMAC_CC_SIF_AHB_IF0 |
							   XDMAC_CC_DIF_AHB_IF1 |
							   XDMAC_CC_SAM_INCREMENTED_AM |
							   XDMAC_CC_DAM_FIXED_AM |
							   XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber
								( pUsart->usartId, XDMAD_TRANSFER_TX ));
		xdmadTxCfg.mbr_bc = 0;
		for (i = 0; i < LLI_Size; i++) {
			 pUsartTx->pLLIview[i].mbr_ubc = XDMA_UBC_NVIEW_NDV1 |
								   XDMA_UBC_NSEN_UPDATED | 
								   XDMA_UBC_NDEN_UNCHANGED |
								   ((i== LLI_Size- 1)? ( (pUsartTx->dmaRingBuffer)
								   ? XDMA_UBC_NDE_FETCH_EN : 0): 
								   XDMA_UBC_NDE_FETCH_EN) | pUsartTx->BuffSize;
				pUsartTx->pLLIview[i].mbr_sa = (uint32_t)pBuff;
				pUsartTx->pLLIview[i].mbr_da = (uint32_t)&pUsartHwTx->US_THR;
				pUsartTx->pLLIview[i].mbr_nda = (i == ( LLI_Size - 1))? 
					( (pUsartTx->dmaRingBuffer)? (uint32_t)pUsartTx->pLLIview : 0 )
					:(uint32_t)&pUsartTx->pLLIview[ i + 1 ];
				pBuff += pUsartTx->BuffSize;
		} 
		xdmaCndc = XDMAC_CNDC_NDVIEW_NDV1 | 
				XDMAC_CNDC_NDE_DSCR_FETCH_EN |
				XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED|
				XDMAC_CNDC_NDDUP_DST_PARAMS_UPDATED ;
		xdmaInt = ((pUsartTx->dmaRingBuffer)? XDMAC_CIE_BIE : XDMAC_CIE_LIE);
	} else {
	  TRACE_ERROR("DmaProgState is incorrect \n\r");
	  return 1;
	}
	memory_barrier();
	if (XDMAD_ConfigureTransfer( pXdmadTx, pUsartTx->ChNum, 
		&xdmadTxCfg, xdmaCndc, (uint32_t)pUsartTx->pLLIview, xdmaInt))
		  return USARTD_ERROR;
	return 0;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Initializes the USARTDma structure and the corresponding USART & DMA .
 * hardware select value.
 * The driver will uses DMA channel 0 for RX and DMA channel 1 for TX.
 * The DMA channels are freed automatically when no USART command processing.
 *
 * \param pUSARTD  Pointer to a UsartDma instance.
 * \param pUsartHw Associated USART peripheral.
 * \param usartId  USART peripheral identifier.
 * \param UsartClk USART clock.
 * \param pXdmad  Pointer to a Dmad instance. 
 */
uint32_t USARTD_Configure( UsartDma *pUsartd ,
						 uint8_t usartId,
						 uint32_t UsartMode,
						 uint32_t BaudRate,
						 uint32_t UsartClk)
{
	/* Enable the peripheral clock in the PMC*/
	PMC_EnablePeripheral( usartId );
	
	/* Initialize the USART structure */
	pUsartd->usartId  = usartId;
   
	if (usartId == ID_USART0)
	  pUsartd->pUsartHw = USART0;
	if (usartId == ID_USART1)
	  pUsartd->pUsartHw = USART1;
	if (usartId == ID_USART2)
	  pUsartd->pUsartHw = USART2;
	
	   
	pUsartd->pXdmad->pXdmacs = XDMAC;
	/* Enable the USART Peripheral ,Execute a software reset of the USART, 
		Configure USART in Master Mode*/
	USART_Configure ( pUsartd->pUsartHw, UsartMode, BaudRate, UsartClk);
	
	 /* Driver initialize */
	XDMAD_Initialize(  pUsartd->pXdmad, 0 );
	
	/* Check if DMA IRQ is enable; if not clear pending IRQs in init it */
	if(!(NVIC_GetActive(XDMAC_IRQn))) {
	  NVIC_ClearPendingIRQ(XDMAC_IRQn);
	}
	return 0;
}

/**
 * \brief This function initialize the appropriate DMA channel for Rx channel 
 * of USART
 * \param pUsartd       Pointer to a UsartDma instance.
 * \param pRxCh         Pointer to TxChannel configuration
 * \returns             0 if the transfer has been started successfully; 
 * otherwise returns USARTD_ERROR_LOCK is the driver is in use, or 
 * USARTD_ERROR if the command is not valid.
 */
uint32_t USARTD_EnableRxChannels( UsartDma *pUsartd, UsartChannel *pRxCh)
{
	uint32_t Channel;
	   
	assert(pRxCh);
	/* Init USART Rx Channel. */
	pUsartd->pRxChannel = pRxCh;
			
	/* Enables the USART to receive data. */
	USART_SetReceiverEnabled ( pUsartd->pUsartHw , ENABLE);
	
	
	/* Allocate a DMA channel for USART0/1 RX. */
	Channel =  XDMAD_AllocateChannel( pUsartd->pXdmad, pUsartd->usartId, 
		XDMAD_TRANSFER_MEMORY);
	if ( Channel == XDMAD_ALLOC_FAILED ) {
	  return USARTD_ERROR;
	}
	
	pRxCh->ChNum = Channel;
	
	 /* Setup callbacks for USART RX */
	if(pUsartd->pRxChannel->callback) {
	  XDMAD_SetCallback(pUsartd->pXdmad, pRxCh->ChNum, 
		(XdmadTransferCallback)pRxCh->callback, pRxCh->pArgument);
	} else {
	  XDMAD_SetCallback(pUsartd->pXdmad, pRxCh->ChNum, 
			(XdmadTransferCallback)USARTD_Rx_Cb, pUsartd);
	}
	
	
	if (XDMAD_PrepareChannel( pUsartd->pXdmad, pRxCh->ChNum ))
		return USARTD_ERROR;
	
	if (_configureRxDma(pUsartd , pUsartd->pRxChannel))
		return USARTD_ERROR_LOCK;
  
	/* Check if DMA IRQ is enable; if not Enable it */
	if(!(NVIC_GetActive(XDMAC_IRQn))) {
	  /* Enable interrupt  */ 
	  NVIC_EnableIRQ(XDMAC_IRQn);
	}
	return 0;
}

/**
 * \brief This function initialize the appropriate DMA channel for Tx channel 
 * of USART
 * \param pUsartd       Pointer to a USARTDma instance.
 * \param pTxCh         Pointer to TxChannel configuration
 * \returns             0 if the transfer has been started successfully; 
 * otherwise returns USARTD_ERROR_LOCK is the driver is in use, or 
 * USARTD_ERROR if the command is not valid.
 */
uint32_t USARTD_EnableTxChannels( UsartDma *pUsartd, UsartChannel *pTxCh)
{
	
	uint32_t Channel;
	   
	assert(pTxCh);
	
	/* Init USART Tx Channel. */
	pUsartd->pTxChannel = pTxCh;
		
	/* Enables the USART to transfer data. */
	USART_SetTransmitterEnabled ( pUsartd->pUsartHw , ENABLE);
	
	 /* Allocate a DMA channel for USART0/1 TX. */
	Channel =  XDMAD_AllocateChannel( pUsartd->pXdmad, XDMAD_TRANSFER_MEMORY, 
			pUsartd->usartId);
	if ( Channel == XDMAD_ALLOC_FAILED ) {
	  return USARTD_ERROR;
	}
	pTxCh->ChNum = Channel;
	/* Setup callbacks for USART0/1 TX */
	if(pUsartd->pTxChannel->callback) {
	  XDMAD_SetCallback(pUsartd->pXdmad, pTxCh->ChNum, 
			(XdmadTransferCallback)pTxCh->callback, pTxCh->pArgument);
	} else {
	  XDMAD_SetCallback(pUsartd->pXdmad, pTxCh->ChNum, (XdmadTransferCallback)USARTD_Tx_Cb, pUsartd);
	}
	
	if ( XDMAD_PrepareChannel( pUsartd->pXdmad, pTxCh->ChNum ))
		return USARTD_ERROR;
	
	if (_configureTxDma(pUsartd , pUsartd->pTxChannel))
		return USARTD_ERROR_LOCK;
	
	/* Check if DMA IRQ is enable; if not Enable it */
	if(!(NVIC_GetActive(XDMAC_IRQn))) {
	  /* Enable interrupt  */ 
	  NVIC_EnableIRQ(XDMAC_IRQn);
	}
	return 0;
}

/**
 * \brief This function disables the appropriate DMA channel for Rx channel of 
 * USART
 * \param pUsartd       Pointer to a UsartDma instance.
 * \param pRxCh         Pointer to TxChannel configuration
 * \returns             0 if the transfer has been started successfully; 
 * otherwise returns USARTD_ERROR_LOCK is the driver is in use, or 
 * USARTD_ERROR if the command is not valid.
 */
uint32_t USARTD_DisableRxChannels( UsartDma *pUsartd, UsartChannel *pRxCh)
{
	assert(pRxCh);
	
	/* Enables the USART to transfer data. */
	USART_SetReceiverEnabled ( pUsartd->pUsartHw , DISABLE);
	
	XDMAD_StopTransfer(pUsartd->pXdmad, pRxCh->ChNum);
	
	XDMAD_SetCallback(pUsartd->pXdmad, pRxCh->ChNum, NULL, NULL);
	 /* Free allocated DMA channel for USART TX. */
	if(XDMAD_FreeChannel( pUsartd->pXdmad, pRxCh->ChNum) != XDMAD_OK) {
		return USARTD_ERROR;
	}
	
	if (pRxCh->dmaProgrammingMode == XDMAD_LLI) {
		free(pRxCh->pLLIview);
		pRxCh->pLLIview = NULL;
	}
	pRxCh->dmaProgress = 1;
	memory_barrier();
	return 0;
}

/**
 * \brief This function disables the appropriate DMA channel for Tx channel of 
 * USART
 * \param pUsartd       Pointer to a USARTDma instance.
 * \param pTxCh         Pointer to TxChannel configuration
 * \returns             0 if the transfer has been started successfully; 
 * otherwise returns USARTD_ERROR_LOCK is the driver is in use, or 
 * USARTD_ERROR if the command is not valid.
 */

uint32_t USARTD_DisableTxChannels( UsartDma *pUsartd, UsartChannel *pTxCh)
{
	assert(pTxCh);
	
	/* Enables the USART to transfer data. */
	USART_SetTransmitterEnabled ( pUsartd->pUsartHw , DISABLE);
	
	XDMAD_StopTransfer(pUsartd->pXdmad, pTxCh->ChNum);
	
	XDMAD_SetCallback(pUsartd->pXdmad, pTxCh->ChNum, NULL, NULL);
	/* Free allocated DMA channel for USART TX. */
	if(XDMAD_FreeChannel( pUsartd->pXdmad, pTxCh->ChNum) != XDMAD_OK) {
		return USARTD_ERROR;
	}
	
	if (pTxCh->dmaProgrammingMode == XDMAD_LLI) {
		free(pTxCh->pLLIview);
		pTxCh->pLLIview = NULL;
	}
	pTxCh->dmaProgress = 1;
	memory_barrier();
	return 0;
}

/**
 * \brief Starts a USART master transfer. This is a non blocking function. It 
 * will return as soon as the transfer is started.
 *
 * \param pUSARTD  Pointer to a USARTDma instance.
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * USARTD_ERROR_LOCK is the driver is in use, or USARTD_ERROR if the command is 
 * not valid.
 */
uint32_t USARTD_SendData( UsartDma *pUsartd)
{
	/* Start DMA 0(RX) && 1(TX) */
	SCB_CleanInvalidateDCache();
	pUsartd->pTxChannel->dmaProgress=0;
	memory_barrier();
	if (XDMAD_StartTransfer( pUsartd->pXdmad, pUsartd->pTxChannel->ChNum ))
		return USARTD_ERROR_LOCK; 
	return 0;
}

/**
 * \brief Starts a USART master transfer. This is a non blocking function. It will
 *  return as soon as the transfer is started.
 *
 * \param pUSARTD  Pointer to a USARTDma instance.
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * USARTD_ERROR_LOCK is the driver is in use, or USARTD_ERROR if the command is not
 * valid.
 */
uint32_t USARTD_RcvData( UsartDma *pUsartd)
{
	/* Start DMA 0(RX) && 1(TX) */
	SCB_CleanInvalidateDCache();
	pUsartd->pRxChannel->dmaProgress=0;
	memory_barrier();
	if (XDMAD_StartTransfer( pUsartd->pXdmad, pUsartd->pRxChannel->ChNum )) 
		return USARTD_ERROR_LOCK;
	return 0;
}

