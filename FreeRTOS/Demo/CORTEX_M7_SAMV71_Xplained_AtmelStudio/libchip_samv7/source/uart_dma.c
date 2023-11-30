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
 * \addtogroup uart_dma_module UART xDMA driver
 * \ingroup lib_uart
 * \section Usage
 *
 * <ul>
 * <li> UARTD_Configure() initializes and configures the UART peripheral and 
 * xDMA for data transfer.</li>
 * <li> Configures the parameters for the device corresponding to the cs value 
 * by UARTD_ConfigureCS(). </li>
 * <li> Starts a UART master transfer. This is a non blocking function 
 * UARTD_SendData(). It will
 * return as soon as the transfer is started..</li>
 * </ul>
 *
 */

/**
 * \file
 *
 * Implementation for the UART with xDMA driver.
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

	/* Release the DMA channels */
	XDMAD_FreeChannel(pArg->pXdmad, pUartdCh->ChNum);
	pUartdCh->sempaphore = 1;
	memory_barrier();
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

	/* Release the DMA channels */
	XDMAD_FreeChannel(pArg->pXdmad, pUartdCh->ChNum);
	pUartdCh->sempaphore = 1;
	memory_barrier();
}

/**
 * \brief Configure the UART Rx DMA mode.
 *
 * \param pUartHw   Pointer to UART instance
 * \param pXdmad    Pointer to XDMA instance
 * \param pUsartRx  Pointer to Usart Rx channel
 * \returns 0 if the dma multibuffer configuration successfully; otherwise 
 * returns USARTD_ERROR_XXX.
 */
static uint8_t _configureUartRxDma(UartDma *pUartd ,  UartChannel *pUartRx)
{
	sXdmadCfg xdmadRxCfg;
	uint32_t xdmaCndc, xdmaInt;
	uint32_t i, LLI_Size;
	Uart *pUartHwRx = pUartd->pUartHw;
	sXdmad* pXdmadRx = pUartd->pXdmad;
	uint8_t *pBuff = 0;
	
	/* Setup RX Single block */
	if(pUartRx->dmaProgrammingMode < XDMAD_LLI) {
	  xdmadRxCfg.mbr_ubc = pUartRx->BuffSize;
	  xdmadRxCfg.mbr_da = (uint32_t)pUartRx->pBuff;

	  xdmadRxCfg.mbr_sa = (uint32_t)&pUartHwRx->UART_RHR;
	  xdmadRxCfg.mbr_cfg =  XDMAC_CC_TYPE_PER_TRAN |
							XDMAC_CC_MBSIZE_SIXTEEN |
							XDMAC_CC_DSYNC_PER2MEM |
							XDMAC_CC_CSIZE_CHK_1 |
							XDMAC_CC_DWIDTH_BYTE |
							XDMAC_CC_SIF_AHB_IF1 |
							XDMAC_CC_DIF_AHB_IF0 |
							XDMAC_CC_SAM_FIXED_AM |
							XDMAC_CC_DAM_INCREMENTED_AM |
							XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber
								( pUartd->uartId, XDMAD_TRANSFER_RX ));

	  xdmadRxCfg.mbr_bc = 0;
	  if(pUartRx->dmaProgrammingMode == XDMAD_MULTI) {
		xdmadRxCfg.mbr_bc = pUartRx->dmaBlockSize;
	  }
	  xdmadRxCfg.mbr_sus = 0;
	  xdmadRxCfg.mbr_dus =0;
	  xdmaCndc = 0;
	  
	  /* Put all interrupts on for non LLI list setup of DMA */
	  xdmaInt =  (XDMAC_CIE_BIE   |
				 XDMAC_CIE_DIE   |
				 XDMAC_CIE_FIE   |
				 XDMAC_CIE_RBIE  |
				 XDMAC_CIE_WBIE  |
				 XDMAC_CIE_ROIE);
			 
	} else if(pUartRx->dmaProgrammingMode == XDMAD_LLI) {
	/* Setup RX Link List */
		LLI_Size = pUartRx->dmaBlockSize;
		pBuff = pUartRx->pBuff;
		if(pUartRx->pLLIview != NULL)	{
		  free(pUartRx->pLLIview);
		  pUartRx->pLLIview = NULL;
		}
		
		pUartRx->pLLIview = malloc(sizeof(LinkedListDescriporView1)*LLI_Size);
		if( pUartRx->pLLIview == NULL) {
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
							XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber( 
								pUartd->uartId, XDMAD_TRANSFER_RX ));
		xdmadRxCfg.mbr_bc = 0;
		for (i = 0; i < LLI_Size; i++) {
			 pUartRx->pLLIview[i].mbr_ubc = XDMA_UBC_NVIEW_NDV1 |
								XDMA_UBC_NSEN_UNCHANGED | 
								XDMA_UBC_NDEN_UPDATED |
								((i== LLI_Size- 1)? ( (pUartRx->dmaRingBuffer)?
								XDMA_UBC_NDE_FETCH_EN : 0): 
								XDMA_UBC_NDE_FETCH_EN) | pUartRx->BuffSize;
				pUartRx->pLLIview[i].mbr_sa = (uint32_t)&pUartHwRx->UART_RHR;
				pUartRx->pLLIview[i].mbr_da = (uint32_t)pBuff;
				pUartRx->pLLIview[i].mbr_nda = (i == ( LLI_Size - 1))? 
					( (pUartRx->dmaRingBuffer)? (uint32_t)pUartRx->pLLIview : 0 ):
					(uint32_t)&pUartRx->pLLIview[ i + 1 ];
				pBuff += pUartRx->BuffSize;
			} 
		xdmaCndc = XDMAC_CNDC_NDVIEW_NDV1 | 
				   XDMAC_CNDC_NDE_DSCR_FETCH_EN |
				   XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED|
				   XDMAC_CNDC_NDDUP_DST_PARAMS_UPDATED ;
		
		xdmaInt = ((pUartRx->dmaRingBuffer)? XDMAC_CIE_BIE : XDMAC_CIE_LIE);
		
	} else {
	  return 1;
	}
	memory_barrier();
	if (XDMAD_ConfigureTransfer( pXdmadRx, pUartRx->ChNum, &xdmadRxCfg,
			xdmaCndc, (uint32_t)pUartRx->pLLIview, xdmaInt))
		 return USARTD_ERROR;
	return 0;
}

/**
 * \brief Configure the UART Tx DMA mode.
 *
 * \param pUartHw   Pointer to UART instance
 * \param pXdmad    Pointer to XDMA instance
 * \param pUsartTx  Pointer to Usart Tx channel
 * \returns 0 if the dma multibuffer configuration successfully; otherwise 
 * returns USARTD_ERROR_XXX.
 */
static uint8_t _configureUartTxDma(UartDma *pUartd, UartChannel *pUartTx)
{
	sXdmadCfg xdmadTxCfg;
	uint32_t xdmaCndc, xdmaInt, LLI_Size, i;
	uint8_t *pBuff = 0;
	Uart *pUartHwTx = pUartd->pUartHw;
	sXdmad* pXdmadTx = pUartd->pXdmad;
	

	/* Setup TX  */ 
	if(pUartTx->dmaProgrammingMode < XDMAD_LLI) {
	  xdmadTxCfg.mbr_ubc = pUartTx->BuffSize;

	  xdmadTxCfg.mbr_sa = (uint32_t)pUartTx->pBuff;
	  xdmadTxCfg.mbr_da = (uint32_t)&pUartHwTx->UART_THR;
	  xdmadTxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
						   XDMAC_CC_MBSIZE_SIXTEEN |
						   XDMAC_CC_DSYNC_MEM2PER |
						   XDMAC_CC_CSIZE_CHK_1 |
						   XDMAC_CC_DWIDTH_BYTE|
						   XDMAC_CC_SIF_AHB_IF0 |
						   XDMAC_CC_DIF_AHB_IF1 |
						   XDMAC_CC_SAM_INCREMENTED_AM |
						   XDMAC_CC_DAM_FIXED_AM |
						   XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber( 
								pUartd->uartId, XDMAD_TRANSFER_TX ));
	  
	  xdmadTxCfg.mbr_bc = 0;
	  if(pUartTx->dmaProgrammingMode == XDMAD_MULTI) {
		xdmadTxCfg.mbr_bc = pUartTx->dmaBlockSize;
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
			 
	} else if(pUartTx->dmaProgrammingMode == XDMAD_LLI) {
		LLI_Size = pUartTx->dmaBlockSize;
		pBuff = pUartTx->pBuff;
		if(pUartTx->pLLIview != NULL) {
		  free(pUartTx->pLLIview);
		  pUartTx->pLLIview = NULL;
		}
		
		pUartTx->pLLIview = malloc(sizeof(LinkedListDescriporView1)*LLI_Size);
		if( pUartTx->pLLIview == NULL) {
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
							XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber( 
								pUartd->uartId, XDMAD_TRANSFER_TX ));
		xdmadTxCfg.mbr_bc = 0;
		for (i = 0; i < LLI_Size; i++) {
			 pUartTx->pLLIview[i].mbr_ubc = XDMA_UBC_NVIEW_NDV1 |
								XDMA_UBC_NSEN_UPDATED | 
								XDMA_UBC_NDEN_UNCHANGED |
								((i== LLI_Size- 1)? ( (pUartTx->dmaRingBuffer)? 
								XDMA_UBC_NDE_FETCH_EN : 0): 
								XDMA_UBC_NDE_FETCH_EN) | pUartTx->BuffSize;
				pUartTx->pLLIview[i].mbr_da = (uint32_t)&pUartHwTx->UART_THR;
				pUartTx->pLLIview[i].mbr_sa = (uint32_t)pBuff;
				pUartTx->pLLIview[i].mbr_nda = (i == ( LLI_Size - 1))? 
					( (pUartTx->dmaRingBuffer)? (uint32_t)pUartTx->pLLIview : 0 ):
					(uint32_t)&pUartTx->pLLIview[ i + 1 ];
				pBuff += pUartTx->BuffSize;
			} 
		xdmaCndc = XDMAC_CNDC_NDVIEW_NDV1 | 
				XDMAC_CNDC_NDE_DSCR_FETCH_EN |
				XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED|
				XDMAC_CNDC_NDDUP_DST_PARAMS_UPDATED ;
		xdmaInt = ((pUartTx->dmaRingBuffer)? XDMAC_CIE_BIE : XDMAC_CIE_LIE);
			
	} else {
	  TRACE_ERROR("DmaProgState is incorrect \n\r");
	  return 1;
	}
	memory_barrier();
	if (XDMAD_ConfigureTransfer( pXdmadTx, pUartTx->ChNum, &xdmadTxCfg, xdmaCndc,
		(uint32_t)pUartTx->pLLIview, xdmaInt))
		 return USARTD_ERROR;
	return 0;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Initializes the UartDma structure and the corresponding UART & DMA .
 * hardware select value.
 * The driver will uses DMA channel 0 for RX and DMA channel 1 for TX.
 * The DMA channels are freed automatically when no UART command processing.
 *
 * \param pUartd    Pointer to a UartDma instance.
 * \param pUartHw   Associated UART peripheral.
 * \param uartId    UART peripheral identifier.
 * \param uartMode  UART peripheral identifier.*
 * \param baud      UART baud rate
 * \param clk       UART ref clock
 * \param pXdmad    Pointer to a Dmad instance. 
 */
uint32_t UARTD_Configure( UartDma *pUartd ,
		uint8_t uartId,
		uint32_t uartMode,
		uint32_t baud,
		uint32_t clk)
{
	/* Enable the peripheral clock in the PMC*/
	PMC_EnablePeripheral( uartId );
	
	/* Initialize the UART structure */
	pUartd->uartId  = uartId;
	
	if (uartId == ID_UART0)
	  pUartd->pUartHw = UART0;
	if (uartId == ID_UART1)
	  pUartd->pUartHw = UART1;
	if (uartId == ID_UART2)
	  pUartd->pUartHw = UART2;
	if (uartId == ID_UART3)
	  pUartd->pUartHw = UART3;
	if (uartId == ID_UART4)
	  pUartd->pUartHw = UART4;
	
	pUartd->pXdmad->pXdmacs = XDMAC;

	/* Enable the UART Peripheral ,Execute a software reset of the UART, 
		Configure UART in Master Mode*/
	UART_Configure ( pUartd->pUartHw, uartMode, baud, clk);
	
	/* Driver initialize */
	XDMAD_Initialize(  pUartd->pXdmad, 0 );
	
	/* Check if DMA IRQ is enable; if not clear pending IRQs in init it */
	if(!(NVIC_GetActive(XDMAC_IRQn))) {
	  NVIC_ClearPendingIRQ(XDMAC_IRQn);
	}
	return 0;
}

/**
 * \brief This function initialize the appropriate DMA channel for Rx channel of 
 * UART
 * \param pUartd     Pointer to a UartDma instance.
 * \param pRxCh      Pointer to TxChannel configuration
 * \returns          0 if the transfer has been started successfully; 
 * otherwise returns UARTD_ERROR_LOCK is the driver is in use, or UARTD_ERROR 
 * if the command is not valid.
 */
uint32_t UARTD_EnableRxChannels( UartDma *pUartd, UartChannel *pRxCh)
{
	Uart *pUartHw = pUartd->pUartHw;
	uint32_t Channel;
	   
	assert(pRxCh);
	/* Init USART Rx Channel. */
	pUartd->pRxChannel = pRxCh;
		
	/* Enables the USART to receive data. */
	UART_SetReceiverEnabled ( pUartHw , ENABLE);

	
	/* Allocate a DMA channel for UART RX. */
	Channel =  XDMAD_AllocateChannel( pUartd->pXdmad, pUartd->uartId, 
			XDMAD_TRANSFER_MEMORY);
	if ( Channel == XDMAD_ALLOC_FAILED ) {
		return UARTD_ERROR;
	}
	pRxCh->ChNum = Channel ;
	
	 /* Setup callbacks for UART RX */
	if(pRxCh->callback) {
	  XDMAD_SetCallback(pUartd->pXdmad, pRxCh->ChNum, 
			(XdmadTransferCallback)pRxCh->callback, pRxCh->pArgument);
	} else {
		XDMAD_SetCallback(pUartd->pXdmad, pRxCh->ChNum, 
				(XdmadTransferCallback)UARTD_Rx_Cb, pUartd);
	}
	
	if (XDMAD_PrepareChannel( pUartd->pXdmad, pRxCh->ChNum ))
		return UARTD_ERROR;
	if (_configureUartRxDma(pUartd, pRxCh))
		return UARTD_ERROR_LOCK;
	/* Check if DMA IRQ is enable; if not Enable it */
	if(!(NVIC_GetActive(XDMAC_IRQn))) {
		/* Enable interrupt  */ 
		NVIC_EnableIRQ(XDMAC_IRQn);
	}
	return 0;
}

/**
 * \brief This function initialize the appropriate DMA channel for Tx channel of 
 * UART
 * \param pUartd     Pointer to a UartDma instance.
 * \param pTxCh      Pointer to RxChannel configuration
 * \returns          0 if the transfer has been started successfully; 
 * otherwise returns UARTD_ERROR_LOCK is the driver is in use, or UARTD_ERROR 
 * if the command is not valid.
 */
uint32_t UARTD_EnableTxChannels( UartDma *pUartd, UartChannel *pTxCh)
{
	Uart *pUartHw = pUartd->pUartHw;
	uint32_t Channel;

	/* Init USART Tx Channel. */
	pUartd->pTxChannel = pTxCh;
	
	/* Enables the USART to transfer data. */
	UART_SetTransmitterEnabled ( pUartHw , ENABLE);
	
	/* Allocate a DMA channel for UART TX. */
	Channel =  XDMAD_AllocateChannel( pUartd->pXdmad, 
			XDMAD_TRANSFER_MEMORY, pUartd->uartId);
	if ( pTxCh->ChNum == XDMAD_ALLOC_FAILED ) {
		return USARTD_ERROR;
	}

	pTxCh->ChNum = Channel ;

	/* Setup callbacks for UART TX */
	if(pUartd->pTxChannel->callback) {
	  XDMAD_SetCallback(pUartd->pXdmad, pTxCh->ChNum, 
			(XdmadTransferCallback)pTxCh->callback, pTxCh->pArgument);
	} else {
		XDMAD_SetCallback(pUartd->pXdmad, pTxCh->ChNum, (XdmadTransferCallback)UARTD_Tx_Cb, pUartd);
	}
	
	if ( XDMAD_PrepareChannel( pUartd->pXdmad, pTxCh->ChNum ))
		return USARTD_ERROR;

	if (_configureUartTxDma(pUartd, pTxCh))
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
 * otherwise returns USARTD_ERROR_LOCK is the driver is in use, or USARTD_ERROR 
 * if the command is not valid.
 */

uint32_t UARTD_DisableRxChannels( UartDma *pUartd, UartChannel *pRxCh)
{
	assert(pRxCh);
	
	/* Enables the USART to transfer data. */
	UART_SetReceiverEnabled ( pUartd->pUartHw , DISABLE);
	
	XDMAD_StopTransfer(pUartd->pXdmad, pRxCh->ChNum);
	
	XDMAD_SetCallback(pUartd->pXdmad, pRxCh->ChNum, NULL, NULL);
	
	 /* Free allocated DMA channel for USART TX. */
	if(XDMAD_FreeChannel( pUartd->pXdmad, pRxCh->ChNum) != XDMAD_OK) {
	  return USARTD_ERROR;
	}
	
	if (pRxCh->dmaProgrammingMode == XDMAD_LLI) {
		free(pRxCh->pLLIview);
		pRxCh->pLLIview = NULL;
	}
	
	pRxCh->sempaphore = 1;
	memory_barrier();
	return 0;
}


/**
 * \brief This function disables the appropriate DMA channel for Tx channel of 
 * USART
 * \param pUsartd       Pointer to a USARTDma instance.
 * \param pTxCh         Pointer to TxChannel configuration
 * \returns             0 if the transfer has been started successfully;
 *  otherwise returns USARTD_ERROR_LOCK is the driver is in use, or USARTD_ERROR 
 * if the command is not valid.
 */

uint32_t UARTD_DisableTxChannels( UartDma *pUartd, UartChannel *pTxCh)
{
	assert(pTxCh);
	
	/* Enables the USART to transfer data. */
	UART_SetTransmitterEnabled ( pUartd->pUartHw , DISABLE);
	
	XDMAD_StopTransfer(pUartd->pXdmad, pTxCh->ChNum);
	
	XDMAD_SetCallback(pUartd->pXdmad, pTxCh->ChNum, NULL, NULL);
	
	 /* Free allocated DMA channel for USART TX. */
	if(XDMAD_FreeChannel( pUartd->pXdmad, pTxCh->ChNum) != XDMAD_OK) {
	  return USARTD_ERROR;
	}
		
	if (pTxCh->dmaProgrammingMode == XDMAD_LLI) {
		free(pTxCh->pLLIview);
		pTxCh->pLLIview = NULL;
	}
	
	pTxCh->sempaphore = 1;
	memory_barrier();
	return 0;
}

/**
 * \brief Starts a UART master transfer. This is a non blocking function. It 
 * will return as soon as the transfer is started.
 *
 * \param pUartd  Pointer to a UartDma instance.
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * UARTD_ERROR_LOCK is the driver is in use, or UARTD_ERROR if the command is 
 * not valid.
 */
uint32_t UARTD_SendData( UartDma *pUartd)
{
	/* Start DMA 0(RX) && 1(TX) */
	SCB_CleanInvalidateDCache();
	pUartd->pTxChannel->sempaphore=0;
	memory_barrier();
	if (XDMAD_StartTransfer( pUartd->pXdmad, pUartd->pTxChannel->ChNum )) 
		return USARTD_ERROR_LOCK;
	
	return 0;
}

/**
 * \brief Starts a UART master transfer. This is a non blocking function. It 
 *  will return as soon as the transfer is started.
 *
 * \param pUartd  Pointer to a UartDma instance.
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * UARTD_ERROR_LOCK is the driver is in use, or UARTD_ERROR if the command is 
 * not valid.
 */
uint32_t UARTD_RcvData( UartDma *pUartd)
{
	SCB_CleanInvalidateDCache();
	pUartd->pRxChannel->sempaphore=0;
	memory_barrier();
	/* Start DMA 0(RX) && 1(TX) */
	if (XDMAD_StartTransfer( pUartd->pXdmad, pUartd->pRxChannel->ChNum )) 
		return USARTD_ERROR_LOCK;
	
	return 0;
}
