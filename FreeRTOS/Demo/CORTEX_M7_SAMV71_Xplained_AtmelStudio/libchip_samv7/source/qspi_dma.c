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
 * \addtogroup qspi_dma_module QSPI xDMA driver
 * \ingroup peripherals_module
 *
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

/** xDMA Link List size for SPI transmission*/
#define DMA_QSPI_LLI     2

/*-----------------------------------------------------------------------------
 *        QSPI DMA Local functions
 *----------------------------------------------------------------------------*/

/**
 * \brief SPI xDMA Rx callback
 * Invoked on SPi DMA reception done.
 * \param channel DMA channel.
 * \param pArg Pointer to callback argument - Pointer to Spid instance.   
 */ 
static void QSPID_Spi_Cb(uint32_t channel, QspiDma_t* pArg)
{
	Qspi *pQspiHw = pArg->Qspid.pQspiHw;
	if (channel != pArg->RxChNum)
		return;
	/* Release the semaphore */
	ReleaseMutex(pArg->progress); 
	QSPI_EndTransfer(pQspiHw); 
	memory_sync();
}


/**
 * \brief QSPI xDMA Tx callback
 * Invoked on QSPi DMA Write done.
 * \param channel DMA channel.
 * \param pArg Pointer to callback argument - Pointer to Spid instance.
 */ 
static void QSPID_qspiTx_Cb(uint32_t channel, QspiDma_t* pArg)
{
	Qspi *pQspiHw = pArg->Qspid.pQspiHw;
	if (channel != pArg->TxChNum)
		return;
	/* Release the semaphore */
	ReleaseMutex(pArg->progress);
	QSPI_EndTransfer(pQspiHw);
	while(!QSPI_GetStatus(pArg->Qspid.pQspiHw, IsEofInst )); 
	memory_sync();
}


/**
 * \brief QSPI xDMA Rx callback
 * Invoked on SPi DMA reception done.
 * \param channel DMA channel.
 * \param pArg Pointer to callback argument - Pointer to Spid instance.   
 */ 
static void QSPID_qspiRx_Cb(uint32_t channel, QspiDma_t* pArg)
{
	Qspi *pQspiHw = pArg->Qspid.pQspiHw;
	if (channel != pArg->RxChNum)
		return;
	/* Release the semaphore */
	ReleaseMutex(pArg->progress); 
	QSPI_EndTransfer(pQspiHw);
	while(!QSPI_GetStatus(pArg->Qspid.pQspiHw, IsEofInst )); 
	memory_sync();
}

/**
 * \brief Configures the DMA for QSPI
 *
 * \param pQspidma  Pointer to QSPI DMA structure
 * \param Addr      Address to Read or write of QSPI flash memory
 * \param pBuffer   Pointer input/output buffer
 * \param ReadWrite Read or write memory flag
 * \returns 0 if the dma multibuffer configuration successfully; otherwise returns
 * QSPID_ERROR_XXX.
 */
static uint8_t QSPID_configureQpsiDma(QspiDma_t *pQspidma, uint32_t Addr, 
			QspiBuffer_t *pBuffer, Access_t const ReadWrite)
{
	sXdmadCfg xdmadCfg, xdmadRxCfg,xdmadTxCfg;
	uint8_t chanNum;
	uint8_t qspi_id =  pQspidma->Qspid.qspiId;
	Qspi *pQspiHw = pQspidma->Qspid.pQspiHw;
	uint32_t xdmaCndc, xdmaInt, BurstSize, ChannelWidth;
	
	
	/* Setup DMA  for QSPI */ 
	
	if(pQspidma->Qspid.qspiMode == QSPI_MR_SMM_SPI) {
	// SPI mode  
	/* SPI TX DMA config */
		xdmadTxCfg.mbr_sa   =   (uint32_t)pBuffer->pDataTx;
		xdmadTxCfg.mbr_da   =   (uint32_t)&pQspiHw->QSPI_TDR;
		xdmadTxCfg.mbr_ubc  =   (pBuffer->TxDataSize);
	
		xdmadTxCfg.mbr_cfg =  XDMAC_CC_TYPE_PER_TRAN |
							XDMAC_CC_MBSIZE_SINGLE |
							XDMAC_CC_DSYNC_MEM2PER |
							XDMAC_CC_CSIZE_CHK_1 |
							XDMAC_CC_DWIDTH_BYTE|
							XDMAC_CC_SIF_AHB_IF0 |
							XDMAC_CC_DIF_AHB_IF1 |
							XDMAC_CC_SAM_INCREMENTED_AM |
							XDMAC_CC_DAM_FIXED_AM |
							XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber
								( qspi_id, XDMAD_TRANSFER_TX ));
	
		xdmadTxCfg.mbr_bc = 0;
		xdmadTxCfg.mbr_sus = 0;
		xdmadTxCfg.mbr_dus =0;

		/* SPI RX DMA config */
	
		xdmadRxCfg.mbr_da  =  (uint32_t)pBuffer->pDataRx;
		xdmadRxCfg.mbr_sa  =  (uint32_t)&pQspiHw->QSPI_RDR;
		xdmadRxCfg.mbr_ubc =   (pBuffer->RxDataSize);
		xdmadRxCfg.mbr_cfg =    XDMAC_CC_TYPE_PER_TRAN |
							  XDMAC_CC_MBSIZE_SINGLE |
							  XDMAC_CC_DSYNC_PER2MEM |
							  XDMAC_CC_CSIZE_CHK_1 |
							  XDMAC_CC_DWIDTH_BYTE|
							  XDMAC_CC_SIF_AHB_IF1 |
							  XDMAC_CC_DIF_AHB_IF0 |
							  XDMAC_CC_SAM_FIXED_AM |
							  XDMAC_CC_DAM_INCREMENTED_AM |
							  XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber
								( qspi_id, XDMAD_TRANSFER_RX ));

		xdmadRxCfg.mbr_bc = 0;
		xdmadRxCfg.mbr_sus = 0;
		xdmadRxCfg.mbr_dus =0; 
		xdmaCndc = 0;
	/* Put all interrupts on for non LLI list setup of DMA */
		xdmaInt =  (XDMAC_CIE_BIE   |
				   XDMAC_CIE_RBIE  |
				   XDMAC_CIE_WBIE  |
				   XDMAC_CIE_ROIE);
	
		memory_barrier();
		if (XDMAD_ConfigureTransfer
		( pQspidma->pXdmad, pQspidma->RxChNum, &xdmadRxCfg, xdmaCndc, 0, xdmaInt))
		return QSPID_ERROR;

		if (XDMAD_ConfigureTransfer
			( pQspidma->pXdmad, pQspidma->TxChNum, &xdmadTxCfg, xdmaCndc, 0, xdmaInt))
			return QSPID_ERROR;
	return 0;
	 
	} else {
		if(ReadWrite == WriteAccess) {
			xdmadCfg.mbr_sa = (uint32_t)pBuffer->pDataTx;
			xdmadCfg.mbr_da = (uint32_t)( QSPIMEM_ADDR | Addr);
			xdmadCfg.mbr_ubc =  (pBuffer->TxDataSize);
			chanNum =  pQspidma->TxChNum;
			ChannelWidth = XDMAC_CC_DWIDTH_BYTE;
			BurstSize = XDMAC_CC_MBSIZE_SIXTEEN;
		} else if(ReadWrite == ReadAccess) {
			xdmadCfg.mbr_da = (uint32_t)pBuffer->pDataRx;
			xdmadCfg.mbr_sa = (uint32_t)( QSPIMEM_ADDR | Addr);
			xdmadCfg.mbr_ubc =  ((pBuffer->RxDataSize>>2) + 1);
			chanNum =  pQspidma->RxChNum;
			ChannelWidth = XDMAC_CC_DWIDTH_WORD;
			BurstSize = XDMAC_CC_MBSIZE_SIXTEEN;
		} else {
			TRACE_ERROR(" QSPI error \n\r");
			return 1;
		}

		xdmadCfg.mbr_cfg = XDMAC_CC_TYPE_MEM_TRAN |
					XDMAC_CC_MEMSET_NORMAL_MODE |
					BurstSize |
					ChannelWidth |
					XDMAC_CC_SIF_AHB_IF1 |
					XDMAC_CC_DIF_AHB_IF1 |
					XDMAC_CC_SAM_INCREMENTED_AM |
					XDMAC_CC_DAM_INCREMENTED_AM ;
	
		xdmadCfg.mbr_bc = 0;
		xdmadCfg.mbr_sus = 0;
		xdmadCfg.mbr_dus =0;

		xdmaCndc = 0;


	/* Put all interrupts on for non LLI list setup of DMA */
		xdmaInt =  (XDMAC_CIE_BIE   |
				   XDMAC_CIE_RBIE  |
				   XDMAC_CIE_WBIE  |
				   XDMAC_CIE_ROIE);
	  
		memory_barrier();
		if (XDMAD_ConfigureTransfer( pQspidma->pXdmad, chanNum, &xdmadCfg, xdmaCndc, 0, xdmaInt))
			return QSPID_ERROR;
		return 0;
	}
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Initializes the pQspidma structure and the corresponding QSPI & DMA .
 * hardware select value.
 *
 * \param pQspidma  Pointer to a QspiDma_t instance.
 * \param Mode      Associated SPI peripheral.
 * \param dwConf    QSPI peripheral configuration.
 * \param pXdmad    Pointer to a Xdmad instance. 
 */
uint32_t QSPID_Configure( QspiDma_t *pQspidma, QspiMode_t Mode, 
		uint32_t dwConf, sXdmad* pXdmad)
{
	/* Initialize the QSPI structure */
	
	QSPI_ConfigureInterface(&pQspidma->Qspid, Mode, dwConf);
	
	pQspidma->Qspid.qspiCommand.Instruction = 0;
	pQspidma->Qspid.qspiCommand.Option = 0;
	
	pQspidma->RxChNum = QSPID_CH_NOT_ENABLED;
	pQspidma->TxChNum = QSPID_CH_NOT_ENABLED;
	
	pQspidma->pXdmad = pXdmad;
	
	/* XDMA Driver initialize */
	XDMAD_Initialize(  pQspidma->pXdmad, 0 );
	
	/* Configure and enable interrupt  */
	NVIC_ClearPendingIRQ(XDMAC_IRQn);
	NVIC_SetPriority( XDMAC_IRQn ,1);
	NVIC_EnableIRQ(XDMAC_IRQn);
	
	
	return QSPI_SUCCESS;
}



/**
 * \brief Enables a QSPI Rx channel. This function will allocate a dma Rx 
 *  channel for QSPI
 *
 * \param pQspidma  Pointer to a Spid instance.

 * \returns 0 if the transfer has been started successfully; otherwise returns
 * QSPID_ERROR_LOCK is the driver is in use, or QSPID_ERROR if the command is not
 * valid.
 */
uint32_t QSPID_EnableQspiRxChannel(QspiDma_t *pQspidma)
{
	static uint16_t DmaChannel;

	/* Try to get the semaphore */
	if (pQspidma->RxChNum != QSPID_CH_NOT_ENABLED) {
		return QSPID_ERROR_LOCK;
	}
	
	/* Allocate a DMA channel */
	DmaChannel = XDMAD_AllocateChannel( 
			pQspidma->pXdmad, XDMAD_TRANSFER_MEMORY, XDMAD_TRANSFER_MEMORY);
	if ( DmaChannel == XDMAD_ALLOC_FAILED ){
		return QSPID_ERROR;
	}

	pQspidma->RxChNum = DmaChannel;
	/* Setup callbacks*/
	XDMAD_SetCallback(pQspidma->pXdmad, pQspidma->RxChNum, 
			(XdmadTransferCallback)QSPID_qspiRx_Cb, pQspidma);
	
	if (XDMAD_PrepareChannel( pQspidma->pXdmad, pQspidma->RxChNum ))
		return QSPID_ERROR;
	return 0;
}


/**
 * \brief Enables a QSPI Tx channel. This function will allocate a dma Tx 
 * channel for QSPI
 *
 * \param pQspidma  Pointer to a Spid instance.

 * \returns 0 if the transfer has been started successfully; otherwise returns
 * QSPID_ERROR_LOCK is the driver is in use, or QSPID_ERROR if the command is 
 * not valid.
 */
uint32_t QSPID_EnableQspiTxChannel(QspiDma_t *pQspidma)
{
	static uint16_t DmaChannel;

	/* Try to get the  semaphore */
	if (pQspidma->TxChNum != QSPID_CH_NOT_ENABLED) {
		return QSPID_ERROR_LOCK;
	}
	/* Allocate a DMA channel */
	DmaChannel = XDMAD_AllocateChannel( pQspidma->pXdmad, 
			XDMAD_TRANSFER_MEMORY, XDMAD_TRANSFER_MEMORY);
	if ( DmaChannel == XDMAD_ALLOC_FAILED ) {
			return QSPID_ERROR;
	}
	
	pQspidma->TxChNum = DmaChannel;
	/* Setup callbacks  */
	XDMAD_SetCallback(pQspidma->pXdmad, pQspidma->TxChNum, 
			(XdmadTransferCallback)QSPID_qspiTx_Cb, pQspidma);
	
	if (XDMAD_PrepareChannel( pQspidma->pXdmad, pQspidma->TxChNum ))
		return QSPID_ERROR;
	
	return 0;
}


/**
 * \brief Enables a QSPI SPI Rx channel. This function will allocate a dma 
 *  Rx channel for QSPI SPI mode
 *
 * \param pQspidma  Pointer to a Spid instance.

 * \returns 0 if the transfer has been started successfully; otherwise returns
 * QSPID_ERROR_LOCK is the driver is in use, or QSPID_ERROR if the command is 
 * not valid.
 */
uint32_t QSPID_EnableSpiChannel(QspiDma_t *pQspidma)
{
	static uint16_t DmaChannel;

	/* Try to get the semaphore */
	if (pQspidma->RxChNum != QSPID_CH_NOT_ENABLED) {
		return QSPID_ERROR_LOCK;
	}
	
	/* Try to get the  semaphore */
	if (pQspidma->TxChNum != QSPID_CH_NOT_ENABLED) {
		return QSPID_ERROR_LOCK;
	}
	   
	/* Allocate a DMA channel */
	DmaChannel = XDMAD_AllocateChannel
		( pQspidma->pXdmad, pQspidma->Qspid.qspiId, XDMAD_TRANSFER_MEMORY);
	if ( DmaChannel == XDMAD_ALLOC_FAILED ) {
		return QSPID_ERROR;
	}

	pQspidma->RxChNum = DmaChannel;
	
	/* Allocate a DMA channel */
	DmaChannel = XDMAD_AllocateChannel( pQspidma->pXdmad, 
			XDMAD_TRANSFER_MEMORY, pQspidma->Qspid.qspiId);
	if ( DmaChannel == XDMAD_ALLOC_FAILED ) {
		return QSPID_ERROR;
	}
	
	pQspidma->TxChNum = DmaChannel;
	
	/* Setup callbacks*/
	XDMAD_SetCallback(pQspidma->pXdmad, pQspidma->RxChNum, 
			(XdmadTransferCallback)QSPID_Spi_Cb, pQspidma);
	if (XDMAD_PrepareChannel( pQspidma->pXdmad, pQspidma->RxChNum ))
		return QSPID_ERROR;
	
	/* Setup callbacks for SPI0/1 TX (ignored) */
	XDMAD_SetCallback(pQspidma->pXdmad, pQspidma->TxChNum, NULL, NULL);
	if ( XDMAD_PrepareChannel( pQspidma->pXdmad, pQspidma->TxChNum ))
		return QSPID_ERROR;
	
	return 0;
}


/**
 * \brief Disables a QSPI Rx channel. This function will de-allocate previous 
 *  allocated dma Rx channel for QSPI
 *
 * \param pQspidma  Pointer to a Spid instance.

 * \returns 0 if the transfer has been started successfully; otherwise returns
 * QSPID_ERROR_LOCK is the driver is in use, or QSPID_ERROR if the command is 
 * not valid.
 */
uint32_t QSPID_DisableQspiRxChannel(QspiDma_t *pQspidma)
{    
  
	XDMAC_SoftwareFlushReq(pQspidma->pXdmad->pXdmacs, pQspidma->RxChNum);
	XDMAD_StopTransfer(pQspidma->pXdmad, pQspidma->RxChNum);
	
	XDMAD_SetCallback(pQspidma->pXdmad, pQspidma->RxChNum, NULL, NULL);    
	
	
	 /* Free allocated DMA channel for QSPI RX. */
	XDMAD_FreeChannel( pQspidma->pXdmad, pQspidma->RxChNum);
	
	pQspidma->RxChNum = QSPID_CH_NOT_ENABLED;
	
	return 0;
}



/**
 * \brief Disables a QSPI Tx channel. This function will de-allocate previous 
 * allocated dma Tx channel for QSPI
 *
 * \param pQspidma  Pointer to a Spid instance.

 * \returns 0 if the transfer has been started successfully; otherwise returns
 * QSPID_ERROR_LOCK is the driver is in use, or QSPID_ERROR if the command is 
 * not valid.
 */
uint32_t QSPID_DisableQspiTxChannel(QspiDma_t *pQspidma)
{    
  
	XDMAC_SoftwareFlushReq(pQspidma->pXdmad->pXdmacs, pQspidma->TxChNum);
	XDMAD_StopTransfer(pQspidma->pXdmad, pQspidma->TxChNum);
	
	XDMAD_SetCallback(pQspidma->pXdmad, pQspidma->TxChNum, NULL, NULL);
	
	 /* Free allocated DMA channel for QSPI TX. */
	XDMAD_FreeChannel( pQspidma->pXdmad, pQspidma->TxChNum);
	
	pQspidma->TxChNum = QSPID_CH_NOT_ENABLED;
	
	return 0;
}


/**
 * \brief Disables a QSPI SPI Rx and Tx channels. This function will 
 *  de-allocate privious allocated dma Rx, Txchannel for QSPI in SPI mode
 *
 * \param pQspidma  Pointer to a Spid instance.

 * \returns 0 if the transfer has been started successfully; otherwise returns
 * QSPID_ERROR_LOCK is the driver is in use, or QSPID_ERROR if the command is 
 * not valid.
 */
uint32_t QSPID_DisableSpiChannel(QspiDma_t *pQspidma)
{    
  
	XDMAC_SoftwareFlushReq(pQspidma->pXdmad->pXdmacs, pQspidma->RxChNum);
	//XDMAC_SoftwareFlushReq(pQspidma->pXdmad->pXdmacs, pQspidma->TxChNum);
	XDMAD_StopTransfer(pQspidma->pXdmad, pQspidma->RxChNum);
	XDMAD_StopTransfer(pQspidma->pXdmad, pQspidma->TxChNum);
	
	XDMAD_SetCallback(pQspidma->pXdmad, pQspidma->RxChNum, NULL, NULL);
	
	 /* Free allocated DMA channel for QSPI RX. */
	XDMAD_FreeChannel( pQspidma->pXdmad, pQspidma->RxChNum);
	 
	XDMAD_FreeChannel( pQspidma->pXdmad, pQspidma->TxChNum);
	
	pQspidma->RxChNum = QSPID_CH_NOT_ENABLED;
	pQspidma->TxChNum = QSPID_CH_NOT_ENABLED;
	
	return 0;
}


/**
 * \brief Starts a QSPI read or write operation. 
 *
 * \param pQspidma  Pointer to a Qspid instance.
 * \param ReadWrite Defines the memory access type
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * QSPID_ERROR_LOCK is the driver is in use, or QSPID_ERROR if the command is 
 * not valid.
 */
uint32_t QSPID_ReadWriteQSPI(QspiDma_t *pQspidma, Access_t const ReadWrite)
{ 
	QspiBuffer_t *pBuffer = &pQspidma->Qspid.qspiBuffer;
	uint8_t chanNum;
	uint32_t semTimer = 0x7FF;
	
	//assert(pBuffer->pDataTx);
	
	if (pQspidma->progress) {
		return QSPID_ERROR_LOCK;
	}
	LockMutex(pQspidma->progress, semTimer);
	if(ReadWrite == WriteAccess) {
	  chanNum =  pQspidma->TxChNum; 
	} else if(ReadWrite == ReadAccess) {
	  chanNum =  pQspidma->RxChNum;
	} else {
	  TRACE_ERROR("%s QSPI Access Error\n\r", __FUNCTION__);
	}
	
	if (QSPID_configureQpsiDma
			( pQspidma, pQspidma->Qspid.pQspiFrame->Addr, pBuffer, ReadWrite) )
		return QSPID_ERROR_LOCK;
	
	SCB_CleanInvalidateDCache();
	/* Start DMA 0(RX) && 1(TX) */
	if (XDMAD_StartTransfer( pQspidma->pXdmad,chanNum )) 
		return QSPID_ERROR_LOCK;
	return 0;
}

/**
 * \brief Starts a SPI master transfer. This is a non blocking function. It will
 *  return as soon as the transfer is started.
 *
 * \param pSpid  Pointer to a Spid instance.
 * \param pCommand Pointer to the SPI command to execute.
 * \returns 0 if the transfer has been started successfully; otherwise returns
 * SPID_ERROR_LOCK is the driver is in use, or SPID_ERROR if the command is not
 * valid.
 */
uint32_t QSPID_ReadWriteSPI(QspiDma_t *pQspidma, Access_t const ReadWrite)
{
	QspiBuffer_t *pBuffer = &pQspidma->Qspid.qspiBuffer;
	uint32_t semTimer = 0x7FF;
	
	assert(pBuffer->pDataRx);
	assert(pBuffer->pDataTx);
	
	/* Try to get the dataflash semaphore */
	if (pQspidma->progress) {

		return QSPID_ERROR_LOCK;
	}
	
	LockMutex(pQspidma->progress, semTimer);
	
	
	if (QSPID_configureQpsiDma
			( pQspidma, pQspidma->Qspid.pQspiFrame->Addr, pBuffer, ReadWrite) )
		return QSPID_ERROR_LOCK;
	
	SCB_CleanInvalidateDCache();
   
	/* Start DMA 0(RX) && 1(TX) */
	if (XDMAD_StartTransfer(  pQspidma->pXdmad, pQspidma->RxChNum )) 
		return QSPID_ERROR_LOCK;
	if (XDMAD_StartTransfer(  pQspidma->pXdmad, pQspidma->TxChNum  )) 
		return QSPID_ERROR_LOCK;
	return 0;
}

/**
 * \brief Check if the QSPI driver is busy.
 *
 * \param pSpid  Pointer to a Spid instance.
 * \returns 1 if the SPI driver is currently busy executing a command; otherwise
 */
uint32_t QSPID_IsBusy(volatile uint8_t *QspiSemaphore)
{    
	if( Is_LockFree(QspiSemaphore) ) {
	  return 1;
	} else {
	  return 0;
	}
}
