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


/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

#include <assert.h>

/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/
#define TWITIMEOUTMAX 400
static uint32_t dmaWriteChannel,dmaReadChannel;

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** TWI driver callback function.*/
typedef void (*TwiCallback)(Async *);

/** \brief TWI asynchronous transfer descriptor.*/
typedef struct _AsyncTwi {

	/** Asynchronous transfer status. */
	volatile uint8_t status;
	/** Callback function to invoke when transfer completes or fails.*/
	TwiCallback callback;
	/** Pointer to the data buffer.*/
	uint8_t *pData;
	/** Total number of bytes to transfer.*/
	uint32_t num;
	/** Number of already transferred bytes.*/
	uint32_t transferred;

} AsyncTwi;

/**
 * \brief Initializes a TWI DMA Read channel.
 */
static void TWID_DmaInitializeRead(TwihsDma *pTwiXdma)
{
	/* Allocate a XDMA channel, Read accesses into TWI_THR */
	dmaReadChannel = XDMAD_AllocateChannel( pTwiXdma->pTwiDma, pTwiXdma->Twi_id, 
			XDMAD_TRANSFER_MEMORY);
	if ( dmaReadChannel == XDMAD_ALLOC_FAILED ) {
		printf("-E- Can't allocate XDMA channel\n\r");
	}
	XDMAD_PrepareChannel(pTwiXdma->pTwiDma, dmaReadChannel );
}

/**
 * \brief Initializes a TWI DMA write channel.
 */
static void TWID_DmaInitializeWrite(TwihsDma *pTwiXdma)
{
	/* Allocate a XDMA channel, Write accesses into TWI_THR */
	dmaWriteChannel = XDMAD_AllocateChannel( pTwiXdma->pTwiDma, XDMAD_TRANSFER_MEMORY,
			pTwiXdma->Twi_id);
	if ( dmaWriteChannel == XDMAD_ALLOC_FAILED ) {
		printf("-E- Can't allocate XDMA channel\n\r");
	}
	XDMAD_PrepareChannel(pTwiXdma->pTwiDma, dmaWriteChannel );
}

/**
 * \brief Configure xDMA write linker list for TWI transfer.
 */
static uint8_t TWID_XdmaConfigureWrite(TwihsDma *pTwiXdma, uint8_t *buf, uint32_t len)
{
	uint32_t xdmaCndc, Thr, xdmaInt;
	sXdmadCfg xdmadTxCfg;

	Thr = (uint32_t)&(TWIHS0->TWIHS_THR);
	if(pTwiXdma->Twi_id==ID_TWIHS1) {
		Thr = (uint32_t)&(TWIHS1->TWIHS_THR);
	}
	if(pTwiXdma->Twi_id==ID_TWIHS2) {
		Thr = (uint32_t)&(TWIHS2->TWIHS_THR);
	}
	xdmadTxCfg.mbr_ubc =      XDMA_UBC_NVIEW_NDV0 |
							 XDMA_UBC_NDE_FETCH_DIS|
							 XDMA_UBC_NSEN_UPDATED |  len;
	  
	xdmadTxCfg.mbr_sa = (uint32_t)buf;
	xdmadTxCfg.mbr_da = Thr;
	xdmadTxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
						 XDMAC_CC_MBSIZE_SINGLE |
						 XDMAC_CC_DSYNC_MEM2PER |
						 XDMAC_CC_CSIZE_CHK_1 |
						 XDMAC_CC_DWIDTH_BYTE|
						 XDMAC_CC_SIF_AHB_IF0 |
						 XDMAC_CC_DIF_AHB_IF1 |
						 XDMAC_CC_SAM_INCREMENTED_AM |
						 XDMAC_CC_DAM_FIXED_AM |
						 XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber( 
							pTwiXdma->Twi_id, XDMAD_TRANSFER_TX ));
	
	xdmadTxCfg.mbr_bc = 0;
	xdmadTxCfg.mbr_sus = 0;
	xdmadTxCfg.mbr_dus =0;
	xdmaCndc = 0;
	
	xdmaInt =  (XDMAC_CIE_BIE |
			   XDMAC_CIE_RBIE  |
			   XDMAC_CIE_WBIE );
	if (XDMAD_ConfigureTransfer( pTwiXdma->pTwiDma, dmaWriteChannel, 
			&xdmadTxCfg, xdmaCndc, 0, xdmaInt) )
	  return USARTD_ERROR;

	return 0;
}


/**
 * \brief Configure xDMA read linker list for TWI transfer.
 */
static uint8_t TWID_XdmaConfigureRead(TwihsDma *pTwiXdma, uint8_t *buf, uint32_t len)
{
	uint32_t xdmaCndc, Rhr, xdmaInt;
	sXdmadCfg xdmadRxCfg;

	Rhr = (uint32_t)&(TWIHS0->TWIHS_RHR);
	if(pTwiXdma->Twi_id==ID_TWIHS1) {
		Rhr = (uint32_t)&(TWIHS1->TWIHS_RHR);
	}
	if(pTwiXdma->Twi_id==ID_TWIHS2) {
		Rhr = (uint32_t)&(TWIHS2->TWIHS_RHR);
	}
	xdmadRxCfg.mbr_ubc = XDMA_UBC_NVIEW_NDV0 |
						  XDMA_UBC_NDE_FETCH_DIS|
						  XDMA_UBC_NDEN_UPDATED |
						  len;
	
	xdmadRxCfg.mbr_da = (uint32_t)buf;
	xdmadRxCfg.mbr_sa = Rhr;
	
	xdmadRxCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN |
						   XDMAC_CC_MBSIZE_SINGLE |
						   XDMAC_CC_DSYNC_PER2MEM |
						   XDMAC_CC_CSIZE_CHK_1 |
						   XDMAC_CC_DWIDTH_BYTE |
						   XDMAC_CC_SIF_AHB_IF1 |
						   XDMAC_CC_DIF_AHB_IF0 |
						   XDMAC_CC_SAM_FIXED_AM |
						   XDMAC_CC_DAM_INCREMENTED_AM |
						   XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber( 
								pTwiXdma->Twi_id , XDMAD_TRANSFER_RX ));
	  
	xdmadRxCfg.mbr_bc = 0;
	xdmadRxCfg.mbr_sus = 0;
	xdmadRxCfg.mbr_dus =0;
	xdmaCndc = 0;
	xdmaInt =  (XDMAC_CIE_BIE |
			   XDMAC_CIE_RBIE  |
			   XDMAC_CIE_WBIE );
		
	if (XDMAD_ConfigureTransfer( pTwiXdma->pTwiDma, dmaReadChannel, 
			&xdmadRxCfg, xdmaCndc, 0, xdmaInt))
	  return 1;
	return 0;
}

/*----------------------------------------------------------------------------
 *        Global functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Returns 1 if the given transfer has ended; otherwise returns 0.
 * \param pAsync  Pointer to an Async instance.
 */
uint32_t ASYNC_IsFinished( Async* pAsync )
{
	return (pAsync->status != ASYNC_STATUS_PENDING) ;
}

/**
 * \brief Initializes a TWI driver instance, using the given TWI peripheral.
 * \note The peripheral must have been initialized properly before calling this
 * function.
 * \param pTwid  Pointer to the Twid instance to initialize.
 * \param pTwi  Pointer to the TWI peripheral to use.
 */
void TWID_Initialize(Twid *pTwid, Twihs *pTwi)
{
	TRACE_DEBUG( "TWID_Initialize()\n\r" ) ;
	assert( pTwid != NULL ) ;
	assert( pTwi != NULL ) ;

	/* Initialize driver. */
	pTwid->pTwi = pTwi;
	pTwid->pTransfer = 0;
}

/**
 * \brief Interrupt handler for a TWI peripheral. Manages asynchronous transfer
 * occurring on the bus. This function MUST be called by the interrupt service
 * routine of the TWI peripheral if asynchronous read/write are needed.
 * \param pTwid  Pointer to a Twid instance.
 */
void TWID_Handler( Twid *pTwid )
{
	uint8_t status;
	AsyncTwi *pTransfer ;
	Twihs *pTwi ;

	assert( pTwid != NULL ) ;

	pTransfer = (AsyncTwi*)pTwid->pTransfer ;
	assert( pTransfer != NULL ) ;
	pTwi = pTwid->pTwi ;
	assert( pTwi != NULL ) ;

	/* Retrieve interrupt status */
	status = TWI_GetMaskedStatus(pTwi);

	/* Byte received */
	if (TWI_STATUS_RXRDY(status)) {

		pTransfer->pData[pTransfer->transferred] = TWI_ReadByte(pTwi);
		pTransfer->transferred++;

		/* check for transfer finish */
		if (pTransfer->transferred == pTransfer->num) {

			TWI_DisableIt(pTwi, TWIHS_IDR_RXRDY);
			TWI_EnableIt(pTwi, TWIHS_IER_TXCOMP);
		}
		/* Last byte? */
		else if (pTransfer->transferred == (pTransfer->num - 1)) {

			TWI_Stop(pTwi);
		}
	}
	/* Byte sent*/
	else if (TWI_STATUS_TXRDY(status)) {

		/* Transfer finished ? */
		if (pTransfer->transferred == pTransfer->num) {

			TWI_DisableIt(pTwi, TWIHS_IDR_TXRDY);
			TWI_EnableIt(pTwi, TWIHS_IER_TXCOMP);
			TWI_SendSTOPCondition(pTwi);
		}
		/* Bytes remaining */
		else {

			TWI_WriteByte(pTwi, pTransfer->pData[pTransfer->transferred]);
			pTransfer->transferred++;
		}
	}
	/* Transfer complete*/
	else if (TWI_STATUS_TXCOMP(status)) {

		TWI_DisableIt(pTwi, TWIHS_IDR_TXCOMP);
		pTransfer->status = 0;
		if (pTransfer->callback) {
			pTransfer->callback((Async *) pTransfer);
		}
		pTwid->pTransfer = 0;
	}
}

/**
 * \brief Asynchronously reads data from a slave on the TWI bus. An optional
 * callback function is triggered when the transfer is complete.
 * \param pTwid  Pointer to a Twid instance.
 * \param address  TWI slave address.
 * \param iaddress  Optional slave internal address.
 * \param isize  Internal address size in bytes.
 * \param pData  Data buffer for storing received bytes.
 * \param num  Number of bytes to read.
 * \param pAsync  Asynchronous transfer descriptor.
 * \return 0 if the transfer has been started; otherwise returns a TWI error code.
 */
uint8_t TWID_Read(
		Twid *pTwid,
		uint8_t address,
		uint32_t iaddress,
		uint8_t isize,
		uint8_t *pData,
		uint32_t num,
		Async *pAsync)
{
	Twihs *pTwi;
	AsyncTwi *pTransfer;
	uint32_t startTime;
	assert( pTwid != NULL ) ;
	pTwi = pTwid->pTwi;
	pTransfer = (AsyncTwi *) pTwid->pTransfer;

	assert( (address & 0x80) == 0 ) ;
	assert( (iaddress & 0xFF000000) == 0 ) ;
	assert( isize < 4 ) ;

	/* Check that no transfer is already pending*/
	if (pTransfer) {

		TRACE_ERROR("TWID_Read: A transfer is already pending\n\r");
		return TWID_ERROR_BUSY;
	}

	/* Set STOP signal if only one byte is sent*/
	if (num == 1) {

		TWI_Stop(pTwi);
	}

	/* Asynchronous transfer*/
	if (pAsync) {

		/* Update the transfer descriptor */
		pTwid->pTransfer = pAsync;
		pTransfer = (AsyncTwi *) pAsync;
		pTransfer->status = ASYNC_STATUS_PENDING;
		pTransfer->pData = pData;
		pTransfer->num = num;
		pTransfer->transferred = 0;

		/* Enable read interrupt and start the transfer */
		TWI_EnableIt(pTwi, TWIHS_IER_RXRDY);
		TWI_StartRead(pTwi, address, iaddress, isize);
	}
	/* Synchronous transfer*/
	else {

		/* Start read*/
		TWI_StartRead(pTwi, address, iaddress, isize);

		/* Read all bytes, setting STOP before the last byte*/
		while (num > 0) {

			/* Last byte ?*/
			if (num == 1) {
				TWI_Stop(pTwi);
			}
			/* Wait for byte then read and store it*/
			startTime = GetTicks();
			while( !TWI_ByteReceived(pTwi)) {
				if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
					TRACE_ERROR("TWID Timeout BR\n\r");
					break;
				}
			}
			
			*pData++ = TWI_ReadByte(pTwi);
			num--;
		}

		/* Wait for transfer to be complete */
		startTime = GetTicks();
		while( !TWI_TransferComplete(pTwi) ) {
			if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
				TRACE_ERROR("TWID Timeout TC\n\r");
				break;
			}
		}
	}
	return 0;
}

/**
 * \brief Asynchronously sends data to a slave on the TWI bus. An optional 
 * callback function is invoked whenever the transfer is complete.
 * \param pTwid  Pointer to a Twid instance.
 * \param address  TWI slave address.
 * \param iaddress  Optional slave internal address.
 * \param isize  Number of internal address bytes.
 * \param pData  Data buffer for storing received bytes.
 * \param num  Data buffer to send.
 * \param pAsync  Asynchronous transfer descriptor.
 * \return 0 if the transfer has been started; otherwise returns a TWI error code.
 */
uint8_t TWID_Write(
		Twid *pTwid,
		uint8_t address,
		uint32_t iaddress,
		uint8_t isize,
		uint8_t *pData,
		uint32_t num,
		Async *pAsync)
{
	Twihs *pTwi = pTwid->pTwi;
	uint32_t startTime;
	AsyncTwi *pTransfer = (AsyncTwi *) pTwid->pTransfer;

	assert( pTwi != NULL ) ;
	assert( (address & 0x80) == 0 ) ;
	assert( (iaddress & 0xFF000000) == 0 ) ;
	assert( isize < 4 ) ;

	/* Check that no transfer is already pending */
	if (pTransfer) {
		TRACE_ERROR("TWI_Write: A transfer is already pending\n\r");
		return TWID_ERROR_BUSY;
	}

	/* Asynchronous transfer */
	if (pAsync) {
		/* Update the transfer descriptor */
		pTwid->pTransfer = pAsync;
		pTransfer = (AsyncTwi *) pAsync;
		pTransfer->status = ASYNC_STATUS_PENDING;
		pTransfer->pData = pData;
		pTransfer->num = num;
		pTransfer->transferred = 1;

		/* Enable write interrupt and start the transfer */
		TWI_StartWrite(pTwi, address, iaddress, isize, *pData);
		TWI_EnableIt(pTwi, TWIHS_IER_TXRDY);
		
	} else {
		/* Synchronous transfer*/
		// Start write
		TWI_StartWrite(pTwi, address, iaddress, isize, *pData++);
		num--;
		/* Send all bytes */
		while (num > 0) {
			/* Wait before sending the next byte */
			startTime = GetTicks();
			while( !TWI_ByteSent(pTwi) ) {
				if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
					TRACE_ERROR("TWID Timeout BS\n\r");
					break;
				}
			}
			TWI_WriteByte(pTwi, *pData++);
			num--;
		}
		/* Wait for actual end of transfer */
		startTime = GetTicks();
		/* Send a STOP condition */
		TWI_SendSTOPCondition(pTwi);
		while( !TWI_TransferComplete(pTwi) ) {
			if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
				TRACE_ERROR("TWID Timeout TC2\n\r");
				break;
			}
		}  
	}
	return 0;
}

/**
 * \brief Initializes a TWI driver instance, using the given TWI peripheral.
 * \note The peripheral must have been initialized properly before calling this
 * function.
 * \param pTwid  Pointer to the Twid instance to initialize.
 * \param pTwi  Pointer to the TWI peripheral to use.
 */
void TWID_DmaInitialize(TwihsDma *pTwidma, Twihs *pTwi, uint8_t bPolling)
{
	TRACE_DEBUG( "TWID_Initialize()\n\r" ) ;
	assert( pTwidma != NULL ) ;

	if ((unsigned int)pTwi == (unsigned int)TWIHS0 ) pTwidma->Twi_id = ID_TWIHS0;
	if ((unsigned int)pTwi == (unsigned int)TWIHS1 ) pTwidma->Twi_id = ID_TWIHS1;
	if ((unsigned int)pTwi == (unsigned int)TWIHS2 ) pTwidma->Twi_id = ID_TWIHS2;
	
	/* Initialize driver. */
	pTwidma->pTwid->pTwi = pTwi;
	pTwidma->pTwid->pTransfer = 0;
	
	if(!bPolling) {
	  /* Enable XDMA interrupt and give it priority over any other peripheral 
		interrupt */
	  NVIC_ClearPendingIRQ(XDMAC_IRQn);
	  NVIC_SetPriority(XDMAC_IRQn, 1);
	  NVIC_EnableIRQ( XDMAC_IRQn );
	}
	/* Initialize XDMA driver instance with polling mode */
	XDMAD_Initialize( pTwidma->pTwiDma, bPolling );
}

/**
 * \brief Asynchronously reads data from a slave on the TWI bus. An optional
 * callback function is triggered when the transfer is complete.
 * \param pTwid  Pointer to a Twid instance.
 * \param address  TWI slave address.
 * \param iaddress  Optional slave internal address.
 * \param isize  Internal address size in bytes.
 * \param pData  Data buffer for storing received bytes.
 * \param num  Number of bytes to read.
 * \param pAsync  Asynchronous transfer descriptor.
 * \param TWI_ID  TWI ID for TWI0, TWIHS1, TWIHS2.
 * \return 0 if the transfer has been started; otherwise returns a TWI error code.
 */
uint8_t TWID_DmaRead(
		TwihsDma *pTwiXdma,
		uint8_t address,
		uint32_t iaddress,
		uint8_t isize,
		uint8_t *pData,
		uint32_t num,
		Async *pAsync)
{
	Twihs *pTwi;
	AsyncTwi *pTransfer;
	uint32_t status, startTime;

	assert( pTwiXdma->pTwid != NULL ) ;
	pTwi = pTwiXdma->pTwid->pTwi;
	pTransfer = (AsyncTwi *) pTwiXdma->pTwid->pTransfer;

	assert( (address & 0x80) == 0 ) ;
	assert( (iaddress & 0xFF000000) == 0 ) ;
	assert( isize < 4 ) ;

	/* Check that no transfer is already pending*/
	if (pTransfer) {

		TRACE_ERROR("TWID_Read: A transfer is already pending\n\r");
		return TWID_ERROR_BUSY;
	}
	/* Asynchronous transfer*/
	if (pAsync) {
		/* Update the transfer descriptor */
		pTwiXdma->pTwid->pTransfer = pAsync;
		pTransfer = (AsyncTwi *) pAsync;
		pTransfer->status = ASYNC_STATUS_PENDING;
		pTransfer->pData = pData;
		pTransfer->num = num;
		pTransfer->transferred = 0;

		/* Enable read interrupt and start the transfer */
		TWI_EnableIt(pTwi, TWIHS_IER_RXRDY);
		TWI_StartRead(pTwi, address, iaddress, isize);
	} else {
	/* Synchronous transfer*/
		TWID_DmaInitializeRead(pTwiXdma);
		TWID_XdmaConfigureRead(pTwiXdma, pData, (num - 2));
		
		// cache maintenance before starting DMA Xfr 
		SCB_CleanInvalidateDCache();
		/* Start read*/
		XDMAD_StartTransfer( pTwiXdma->pTwiDma, dmaReadChannel );
		TWI_StartRead(pTwi, address, iaddress, isize);

		startTime = GetTicks();
		while( XDMAD_IsTransferDone(pTwiXdma->pTwiDma, dmaReadChannel) )	{
			if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
				TRACE_ERROR("TWID DMA not done\n\r");
				break;
			}
		}  

		status = TWI_GetStatus(pTwi);
		startTime = GetTicks();
		
		while( !(status & TWIHS_SR_RXRDY)) {
			status = TWI_GetStatus(pTwi);
			if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
				TRACE_ERROR("TWID DMA not done\n\r");
				break;
			}
		}
		TWI_Stop(pTwi);
		
		pData[num - 2] = TWI_ReadByte(pTwi);
		status = TWI_GetStatus(pTwi);
		startTime = GetTicks();
		
		while( !(status & TWIHS_SR_RXRDY)) {
			status = TWI_GetStatus(pTwi);
			if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
				TRACE_ERROR("TWID Timeout Read\n\r");
				break;
			}
		}
		pData[num-1] = TWI_ReadByte(pTwi);
		status = TWI_GetStatus(pTwi);
		startTime = GetTicks();
		while( !(status & TWIHS_SR_TXCOMP)) {
			status = TWI_GetStatus(pTwi);
			if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
				TRACE_ERROR("TWID Timeout Read\n\r");
				break;
			}
		}
		
		XDMAD_StopTransfer( pTwiXdma->pTwiDma, dmaReadChannel );
		XDMAD_FreeChannel(pTwiXdma->pTwiDma, dmaWriteChannel);
	}
	return 0;
}

/**
 * \brief Asynchronously sends data to a slave on the TWI bus. An optional 
 * callback function is invoked whenever the transfer is complete.
 * \param pTwid  Pointer to a Twid instance.
 * \param address  TWI slave address.
 * \param iaddress  Optional slave internal address.
 * \param isize  Number of internal address bytes.
 * \param pData  Data buffer for storing received bytes.
 * \param num  Data buffer to send.
 * \param pAsync  Asynchronous transfer descriptor.
 * \param TWI_ID  TWIHS ID for TWIHS0, TWIHS1, TWIHS2.
 * \return 0 if the transfer has been started; otherwise returns a TWI error code.
 */
uint8_t TWID_DmaWrite(
		TwihsDma *pTwiXdma,
		uint8_t address,
		uint32_t iaddress,
		uint8_t isize,
		uint8_t *pData,
		uint32_t num,
		Async *pAsync)
{
	Twihs *pTwi = pTwiXdma->pTwid->pTwi;
	AsyncTwi *pTransfer = (AsyncTwi *) pTwiXdma->pTwid->pTransfer;
	uint32_t status, startTime;
	//uint8_t singleTransfer = 0;
	assert( pTwi != NULL ) ;
	assert( (address & 0x80) == 0 ) ;
	assert( (iaddress & 0xFF000000) == 0 ) ;
	assert( isize < 4 ) ;

	//    if(num == 1) singleTransfer = 1;
	/* Check that no transfer is already pending */
	if (pTransfer) {

		TRACE_ERROR("TWI_Write: A transfer is already pending\n\r");
		return TWID_ERROR_BUSY;
	}

	/* Asynchronous transfer */
	if (pAsync) {

		/* Update the transfer descriptor */
		pTwiXdma->pTwid->pTransfer = pAsync;
		pTransfer = (AsyncTwi *) pAsync;
		pTransfer->status = ASYNC_STATUS_PENDING;
		pTransfer->pData = pData;
		pTransfer->num = num;
		pTransfer->transferred = 1;

		/* Enable write interrupt and start the transfer */
		TWI_StartWrite(pTwi, address, iaddress, isize, *pData);
		TWI_EnableIt(pTwi, TWIHS_IER_TXRDY);
	} else {
	/* Synchronous transfer*/
		TWID_DmaInitializeWrite(pTwiXdma);
		TWID_XdmaConfigureWrite(pTwiXdma, pData, (num - 1) );
		/* Set slave address and number of internal address bytes. */
		pTwi->TWIHS_MMR = 0;
		pTwi->TWIHS_MMR = (isize << 8) | (address << 16);

		/* Set internal address bytes. */
		pTwi->TWIHS_IADR = 0;
		pTwi->TWIHS_IADR = iaddress;
		
		// cache maintenance before starting DMA Xfr 
		SCB_CleanInvalidateDCache();
	   
		startTime = GetTicks();
		
		XDMAD_StartTransfer( pTwiXdma->pTwiDma, dmaWriteChannel );
		
		while( (XDMAD_IsTransferDone(pTwiXdma->pTwiDma, dmaWriteChannel)) ) {
			if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
				TRACE_ERROR("TWID DMA not done, Channel State is %d\n\r", 
						pTwiXdma->pTwiDma->XdmaChannels[dmaWriteChannel].state);
				break;
			}
		}
		status = TWI_GetStatus(pTwi);
		startTime = GetTicks();
		
		while( !(status & TWIHS_SR_TXRDY)) {
			status = TWI_GetStatus(pTwi);
			if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
				TRACE_ERROR("TWID Timeout TXRDY\n\r");
				break;
			}
		}
		/* Send a STOP condition */
		TWI_Stop(pTwi);

		TWI_WriteByte(pTwi, pData[num-1]);
		status = TWI_GetStatus(pTwi);
		startTime = GetTicks();
		
		while( !(status & TWIHS_SR_TXCOMP)) {
			status = TWI_GetStatus(pTwi);
			if ( (GetDelayInTicks(startTime, GetTicks() ) ) > TWITIMEOUTMAX) {
				TRACE_ERROR("TWID Timeout Write\n\r");
				break;
			}
		}
		XDMAD_StopTransfer(pTwiXdma->pTwiDma, dmaWriteChannel );
		XDMAD_FreeChannel(pTwiXdma->pTwiDma, dmaWriteChannel);
		
	} 
	return 0;
}
