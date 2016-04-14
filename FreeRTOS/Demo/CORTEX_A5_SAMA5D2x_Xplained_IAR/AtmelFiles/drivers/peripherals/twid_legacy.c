/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
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

/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "peripherals/twid_legacy.h"
#include "peripherals/xdmad.h"
#include "cortex-a/cp15.h"
#include "trace.h"

#include <assert.h>

/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/
#define TWITIMEOUTMAX 0xfffff

static struct _xdmad_cfg twi_dmaCfg;
static struct _xdmad_channel *dmaWriteChannel;
static struct _xdmad_channel *dmaReadChannel;
static struct _xdmad_desc_view1 dmaWriteLinkList[1];
static struct _xdmad_desc_view1 dmaReadLinkList[1];

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** TWI driver callback function.*/
typedef void (*TwiCallback) (struct _async *);

/** \brief TWI asynchronous transfer descriptor.*/
struct _async_twi {
	volatile uint32_t status;	/** Asynchronous transfer status. */
	TwiCallback callback;		/** Callback function to invoke when transfer completes or fails.*/
	uint8_t *pData;				/** Pointer to the data buffer.*/
	uint32_t num;				/** Total number of bytes to transfer.*/
	uint32_t transferred; 		/** Number of already transferred bytes.*/
};

//struct _async_twi async_twi ;

/*----------------------------------------------------------------------------
 *        Global functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Initializes a TWI DMA Read channel.
 */
static void twid_dma_initialize_read(uint8_t TWI_ID)
{
	/* Allocate a XDMA channel, Read accesses into TWI_THR */
	dmaReadChannel =  xdmad_allocate_channel(TWI_ID, XDMAD_PERIPH_MEMORY);
	if (!dmaReadChannel) {
		printf("-E- Can't allocate XDMA channel\n\r");
	}
	xdmad_prepare_channel(dmaReadChannel);
}

/**
 * \brief Initializes a TWI DMA write channel.
 */
static void twid_dma_initialize_write(uint8_t TWI_ID)
{

	/* Allocate a XDMA channel, Write accesses into TWI_THR */
	dmaWriteChannel = xdmad_allocate_channel(XDMAD_PERIPH_MEMORY, TWI_ID);
	if (!dmaWriteChannel) {
		printf("-E- Can't allocate XDMA channel\n\r");
	}
	xdmad_prepare_channel(dmaWriteChannel);

}

/**
 * \brief Initializes a TWI driver instance, using the given TWI peripheral.
 * \note The peripheral must have been initialized properly before calling this function.
 * \param pTwid  Pointer to the Twid instance to initialize.
 * \param pTwi  Pointer to the TWI peripheral to use.
 */
void twid_initialize(struct _twid* pTwid, Twi * pTwi)
{
	trace_debug("twid_initialize()\n\r");
	assert(pTwid != NULL);
	assert(pTwi != NULL);

	/* Initialize driver. */
	pTwid->pTwi = pTwi;
	pTwid->pTransfer = 0;
	/* Initialize XDMA driver instance with polling mode */

	// ************* need to be updated XDMAD_Initialize(&twi_dma, 1);
}

/**
 * \brief Configure xDMA write linker list for TWI transfer.
 */
static void _xdma_configure_write(uint8_t * buf, uint32_t len, uint8_t twi_id)
{
	uint32_t i;
	uint32_t xdmaCndc, Thr;
	Twi* twi = (Twi*)get_twi_addr_from_id(twi_id);

	Thr = (uint32_t) & (TWI0->TWI_THR);
	if (twi)
		Thr = (uint32_t) & (twi->TWI_THR);
	for (i = 0; i < 1; i++) {
		dmaWriteLinkList[i].ublock_size = XDMA_UBC_NVIEW_NDV1
		    | ((i == len - 1) ? 0 : XDMA_UBC_NDE_FETCH_EN)
		    | len;
		dmaWriteLinkList[i].src_addr = & buf[i];
		dmaWriteLinkList[i].dest_addr = (void*)Thr;
		if (i == len - 1)
			dmaWriteLinkList[i].next_desc = 0;
		else
			dmaWriteLinkList[i].next_desc =
			    & dmaWriteLinkList[i + 1];
	}
	twi_dmaCfg.cfg.uint32_value = XDMAC_CC_TYPE_PER_TRAN
	    | XDMAC_CC_MBSIZE_SINGLE
	    | XDMAC_CC_DSYNC_MEM2PER
	    | XDMAC_CC_CSIZE_CHK_1
	    | XDMAC_CC_DWIDTH_BYTE
	    | XDMAC_CC_SIF_AHB_IF0
	    | XDMAC_CC_DIF_AHB_IF1
	    | XDMAC_CC_SAM_INCREMENTED_AM
	    | XDMAC_CC_DAM_FIXED_AM
	    |
	    XDMAC_CC_PERID(get_peripheral_xdma_channel(twi_id, XDMAC0, true));
	xdmaCndc =
	    XDMAC_CNDC_NDVIEW_NDV1 | XDMAC_CNDC_NDE_DSCR_FETCH_EN |
	    XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED |
	    XDMAC_CNDC_NDDUP_DST_PARAMS_UNCHANGED;
	cp15_coherent_dcache_for_dma((uint32_t) & dmaWriteLinkList,
				     ((uint32_t) & dmaWriteLinkList +
				      sizeof (*dmaWriteLinkList) * len));
	xdmad_configure_transfer(dmaWriteChannel, &twi_dmaCfg,
				xdmaCndc, dmaWriteLinkList);
}

/**
 * \brief Configure xDMA read linker list for TWI transfer.
 */
static void _xdma_configure_read(uint8_t * buf, uint32_t len, uint8_t twi_id)
{
	uint32_t i;
	uint32_t xdmaCndc, Rhr;
	Twi* twi = get_twi_addr_from_id(twi_id);

	Rhr = (uint32_t) & (TWI0->TWI_RHR);
	if (twi) {
		Rhr = twi->TWI_RHR;
	}
	/* if (twi_id == ID_TWI1) { */
	/* 	Rhr = (uint32_t) & (TWI1->TWI_RHR); */
	/* } */
	/* if (twi_id == ID_TWI2) { */
	/* 	Rhr = (uint32_t) & (TWI2->TWI_RHR); */
	/* } */
	for (i = 0; i < 1; i++) {
		dmaReadLinkList[i].ublock_size = XDMA_UBC_NVIEW_NDV1
		    | ((i == len - 1) ? 0 : XDMA_UBC_NDE_FETCH_EN)
		    | len;
		dmaReadLinkList[i].src_addr = (void*)Rhr;
		dmaReadLinkList[i].dest_addr = & buf[i];
		if (i == len - 1)
			dmaReadLinkList[i].next_desc = 0;
		else
			dmaReadLinkList[i].next_desc =
			    & dmaReadLinkList[i + 1];
	}
	twi_dmaCfg.cfg.uint32_value = XDMAC_CC_TYPE_PER_TRAN
	    | XDMAC_CC_MBSIZE_SINGLE
	    | XDMAC_CC_DSYNC_PER2MEM
	    | XDMAC_CC_CSIZE_CHK_1
	    | XDMAC_CC_DWIDTH_BYTE
	    | XDMAC_CC_SIF_AHB_IF1
	    | XDMAC_CC_DIF_AHB_IF0
	    | XDMAC_CC_SAM_FIXED_AM
	    | XDMAC_CC_DAM_INCREMENTED_AM
	    |
	    XDMAC_CC_PERID(get_peripheral_xdma_channel(twi_id, XDMAC0, false));
	xdmaCndc =
	    XDMAC_CNDC_NDVIEW_NDV1 | XDMAC_CNDC_NDE_DSCR_FETCH_EN |
	    XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED |
	    XDMAC_CNDC_NDDUP_DST_PARAMS_UPDATED;
	cp15_coherent_dcache_for_dma((uint32_t) & dmaReadLinkList,
				     ((uint32_t) & dmaReadLinkList +
				      sizeof (*dmaReadLinkList) * len));
	xdmad_configure_transfer(dmaReadChannel, &twi_dmaCfg, xdmaCndc,
				dmaReadLinkList);
}

/**
 * \brief Interrupt handler for a TWI peripheral. Manages asynchronous transfer
 * occuring on the bus. This function MUST be called by the interrupt service
 * routine of the TWI peripheral if asynchronous read/write are needed.
  * \param pTwid  Pointer to a Twid instance.
 */
void twid_handler(struct _twid* pTwid)
{
	uint32_t status;
	struct _async_twi* pTransfer;
	Twi *pTwi;

	assert(pTwid != NULL);

	pTransfer = (struct _async_twi *) pTwid->pTransfer;
	assert(pTransfer != NULL);
	pTwi = pTwid->pTwi;
	assert(pTwi != NULL);

	/* Retrieve interrupt status */
	status = twi_get_masked_status(pTwi);

	/* Byte received */
	if (TWI_STATUS_RXRDY(status)) {

		pTransfer->pData[pTransfer->transferred] = twi_read_byte(pTwi);
		pTransfer->transferred++;

		/* check for transfer finish */
		if (pTransfer->transferred == pTransfer->num) {

			twi_enable_it(pTwi, TWI_IDR_RXRDY);
			twi_enable_it(pTwi, TWI_IER_TXCOMP);
		}
		/* Last byte? */
		else if (pTransfer->transferred == (pTransfer->num - 1)) {

			twi_stop(pTwi);
		}
	}
	/* Byte sent */
	else if (TWI_STATUS_TXRDY(status)) {

		/* Transfer finished ? */
		if (pTransfer->transferred == pTransfer->num) {

			twi_enable_it(pTwi, TWI_IDR_TXRDY);
			twi_enable_it(pTwi, TWI_IER_TXCOMP);
			twi_send_stop_condition(pTwi);
		}
		/* Bytes remaining */
		else {

			twi_write_byte(pTwi,
				      pTransfer->pData[pTransfer->transferred]);
			pTransfer->transferred++;
		}
	}
	/* Transfer complete */
	else if (TWI_STATUS_TXCOMP(status)) {

		twi_enable_it(pTwi, TWI_IDR_TXCOMP);
		pTransfer->status = 0;
		if (pTransfer->callback) {
			pTransfer->callback((struct _async *) (void *) pTransfer);
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
uint8_t twid_read(struct _twid* pTwid, uint8_t address,  uint32_t iaddress,
	  uint8_t isize, uint8_t * pData, uint32_t num, struct _async * pAsync)
{
	Twi *pTwi;
	struct _async_twi* pTransfer;
	uint32_t timeout = 0;
	uint32_t i = 0;
	uint32_t status;

	assert(pTwid != NULL);
	pTwi = pTwid->pTwi;
	pTransfer = (struct _async_twi*) pTwid->pTransfer;

	assert((address & 0x80) == 0);
	assert((iaddress & 0xFF000000) == 0);
	assert(isize < 4);

	/* Check that no transfer is already pending */
	if (pTransfer) {

		trace_error("twid_read: A transfer is already pending\n\r");
		return TWID_ERROR_BUSY;
	}

	/* Asynchronous transfer */
	if (pAsync) {

		/* Update the transfer descriptor */
		pTwid->pTransfer = pAsync;
		pTransfer = (struct _async_twi*) pAsync;
		pTransfer->status = ASYNC_STATUS_PENDING;
		pTransfer->pData = pData;
		pTransfer->num = num;
		pTransfer->transferred = 0;

		/* Enable read interrupt and start the transfer */
		twi_enable_it(pTwi, TWI_IER_RXRDY);
		twi_start_read(pTwi, address, iaddress, isize);
	}
	/* Synchronous transfer */
	else {

		/* Start read */
		twi_start_read(pTwi, address, iaddress, isize);
		if (num != 1) {
			status = twi_get_status(pTwi);

			if (status & TWI_SR_NACK)
				trace_error("TWID NACK error\n\r");
			timeout = 0;
			while (!(status & TWI_SR_RXRDY)
			       && (++timeout < TWITIMEOUTMAX)) {
				status = twi_get_status(pTwi);
				//trace_error("TWID status %x\n\r",twi_get_status(pTwi));
			}

			pData[0] = twi_read_byte(pTwi);
			for (i = 1; i < num - 1; i++) {
				status = twi_get_status(pTwi);
				if (status & TWI_SR_NACK)
					trace_error("TWID NACK error\n\r");
				timeout = 0;
				while (!(status & TWI_SR_RXRDY)
				       && (++timeout < TWITIMEOUTMAX)) {
					status = twi_get_status(pTwi);
					//trace_error("TWID status %x\n\r",twi_get_status(pTwi));
				}
				pData[i] = twi_read_byte(pTwi);
			}
		}
		twi_stop(pTwi);
		status = twi_get_status(pTwi);
		if (status & TWI_SR_NACK)
			trace_error("TWID NACK error\n\r");
		timeout = 0;
		while (!(status & TWI_SR_RXRDY) && (++timeout < TWITIMEOUTMAX)) {
			status = twi_get_status(pTwi);
			//trace_error("TWID status %x\n\r",twi_get_status(pTwi));
		}

		pData[i] = twi_read_byte(pTwi);
		timeout = 0;
		status = twi_get_status(pTwi);
		while (!(status & TWI_SR_TXCOMP) && (++timeout < TWITIMEOUTMAX)) {
			status = twi_get_status(pTwi);
			//trace_error("TWID status %x\n\r",twi_get_status(pTwi));
		}
	}

	return 0;
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
 * \param twi_id  TWI ID for TWI0, TWI1, TWI2.
 * \return 0 if the transfer has been started; otherwise returns a TWI error code.
 */
uint8_t twid_dma_read(struct _twid* pTwid, uint8_t address, uint32_t iaddress,
	     uint8_t isize, uint8_t * pData, uint32_t num, struct _async * pAsync, uint8_t twi_id)
{
	Twi *pTwi;
	struct _async_twi* pTransfer;
	uint32_t timeout = 0;
	uint32_t status;

	assert(pTwid != NULL);
	pTwi = pTwid->pTwi;
	pTransfer = (struct _async_twi*) pTwid->pTransfer;

	assert((address & 0x80) == 0);
	assert((iaddress & 0xFF000000) == 0);
	assert(isize < 4);

	/* Check that no transfer is already pending */
	if (pTransfer) {

		trace_error("twid_read: A transfer is already pending\n\r");
		return TWID_ERROR_BUSY;
	}

	/* Asynchronous transfer */
	if (pAsync) {

		/* Update the transfer descriptor */
		pTwid->pTransfer = pAsync;
		pTransfer = (struct _async_twi*) pAsync;
		pTransfer->status = ASYNC_STATUS_PENDING;
		pTransfer->pData = pData;
		pTransfer->num = num;
		pTransfer->transferred = 0;

		/* Enable read interrupt and start the transfer */
		twi_enable_it(pTwi, TWI_IER_RXRDY);
		twi_start_read(pTwi, address, iaddress, isize);
	}
	/* Synchronous transfer */
	else {

		twid_dma_initialize_read(twi_id);
		_xdma_configure_read(pData, num, twi_id);
		/* Start read */
		xdmad_start_transfer(dmaReadChannel);

		twi_start_read(pTwi, address, iaddress, isize);

		while ((!xdmad_is_transfer_done(dmaReadChannel))
		       && (++timeout < TWITIMEOUTMAX))
			xdmad_poll();

		xdmad_stop_transfer(dmaReadChannel);

		status = twi_get_status(pTwi);
		timeout = 0;
		while (!(status & TWI_SR_RXRDY)
		       && (++timeout < TWITIMEOUTMAX)) ;

		twi_stop(pTwi);

		twi_read_byte(pTwi);

		status = twi_get_status(pTwi);
		timeout = 0;
		while (!(status & TWI_SR_RXRDY)
		       && (++timeout < TWITIMEOUTMAX)) ;

		twi_read_byte(pTwi);

		status = twi_get_status(pTwi);
		timeout = 0;
		while (!(status & TWI_SR_TXCOMP)
		       && (++timeout < TWITIMEOUTMAX)) ;
		if (timeout == TWITIMEOUTMAX) {
			trace_error("TWID Timeout Read\n\r");
		}
		xdmad_free_channel(dmaReadChannel);
	}
	return 0;
}

/**
 * \brief Asynchronously sends data to a slave on the TWI bus. An optional callback
 * function is invoked whenever the transfer is complete.
 * \param pTwid  Pointer to a Twid instance.
 * \param address  TWI slave address.
 * \param iaddress  Optional slave internal address.
 * \param isize  Number of internal address bytes.
 * \param pData  Data buffer for storing received bytes.
 * \param num  Data buffer to send.
 * \param pAsync  Asynchronous transfer descriptor.
 * \param twi_id  TWI ID for TWI0, TWI1, TWI2.
 * \return 0 if the transfer has been started; otherwise returns a TWI error code.
 */
uint8_t twid_dma_write(struct _twid* pTwid, uint8_t address, uint32_t iaddress,
	      uint8_t isize, uint8_t * pData, uint32_t num, struct _async * pAsync, uint8_t twi_id)
{
	Twi *pTwi = pTwid->pTwi;
	struct _async_twi* pTransfer;
	uint32_t timeout = 0;
	uint32_t status;
	//uint8_t singleTransfer = 0;

	assert(pTwi != NULL);
	assert((address & 0x80) == 0);
	assert((iaddress & 0xFF000000) == 0);
	assert(isize < 4);

	pTransfer = (struct _async_twi *) pTwid->pTransfer;
//    if(num == 1) singleTransfer = 1;
	/* Check that no transfer is already pending */
	if (pTransfer) {
		trace_error("TWI_Write: A transfer is already pending\n\r");
		return TWID_ERROR_BUSY;
	}

	/* Asynchronous transfer */
	if (pAsync) {
		/* Update the transfer descriptor */
		pTwid->pTransfer = pAsync;
		pTransfer = (struct _async_twi*) pAsync;
		pTransfer->status = ASYNC_STATUS_PENDING;
		pTransfer->pData = pData;
		pTransfer->num = num;
		pTransfer->transferred = 1;
		/* Enable write interrupt and start the transfer */
		twi_start_write(pTwi, address, iaddress, isize, *pData);
		twi_enable_it(pTwi, TWI_IER_TXRDY);
	}
	/* Synchronous transfer */
	else {
		cp15_coherent_dcache_for_dma((uint32_t) pData, (uint32_t) pData);
		twid_dma_initialize_write(twi_id);
		_xdma_configure_write(pData, num, twi_id);
		/* Set slave address and number of internal address bytes. */
		pTwi->TWI_MMR = 0;
		pTwi->TWI_MMR = (isize << 8) | (address << 16);
		/* Set internal address bytes. */
		pTwi->TWI_IADR = 0;
		pTwi->TWI_IADR = iaddress;
		xdmad_start_transfer(dmaWriteChannel);
		while (!xdmad_is_transfer_done(dmaWriteChannel))
			xdmad_poll();
		xdmad_stop_transfer(dmaWriteChannel);
		status = twi_get_status(pTwi);
		timeout = 0;
		while (!(status & TWI_SR_TXRDY) && (timeout++ < TWITIMEOUTMAX)) {
			status = twi_get_status(pTwi);
		}
		if (timeout == TWITIMEOUTMAX) {
			trace_error("TWID Timeout TXRDY\n\r");
		}
		/* Send a STOP condition */
		twi_stop(pTwi);
		status = twi_get_status(pTwi);
		timeout = 0;
		while (!(status & TWI_SR_TXCOMP) && (++timeout < TWITIMEOUTMAX)) {
			status = twi_get_status(pTwi);
		}
		if (timeout == TWITIMEOUTMAX) {
			trace_error("TWID Timeout Write\n\r");
		}
		cp15_invalidate_dcache_for_dma((uint32_t) pData, (uint32_t) (pData));
		xdmad_free_channel(dmaWriteChannel);
	}
	return 0;
}

/**
 * \brief Asynchronously sends data to a slave on the TWI bus. An optional callback
 * function is invoked whenever the transfer is complete.
 * \param pTwid  Pointer to a Twid instance.
 * \param address  TWI slave address.
 * \param iaddress  Optional slave internal address.
 * \param isize  Number of internal address bytes.
 * \param pData  Data buffer for storing received bytes.
 * \param num  Data buffer to send.
 * \param pAsync  Asynchronous transfer descriptor.
 * \return 0 if the transfer has been started; otherwise returns a TWI error code.
 */
uint8_t twid_write(struct _twid* pTwid, uint8_t address, uint32_t iaddress,
	   uint8_t isize, uint8_t * pData, uint32_t num, struct _async * pAsync)
{
	Twi *pTwi = pTwid->pTwi;
	struct _async_twi* pTransfer;
	uint32_t timeout = 0;
	uint32_t status;
	uint8_t singleTransfer = 0;

	assert(pTwi != NULL);
	assert((address & 0x80) == 0);
	assert((iaddress & 0xFF000000) == 0);
	assert(isize < 4);

	pTransfer = (struct _async_twi *) pTwid->pTransfer;
	if (num == 1)
		singleTransfer = 1;
	/* Check that no transfer is already pending */
	if (pTransfer) {
		trace_error("TWI_Write: A transfer is already pending\n\r");
		return TWID_ERROR_BUSY;
	}
	/* Asynchronous transfer */
	if (pAsync) {
		/* Update the transfer descriptor */
		pTwid->pTransfer = pAsync;
		pTransfer = (struct _async_twi*) pAsync;
		pTransfer->status = ASYNC_STATUS_PENDING;
		pTransfer->pData = pData;
		pTransfer->num = num;
		pTransfer->transferred = 1;
		/* Enable write interrupt and start the transfer */
		twi_start_write(pTwi, address, iaddress, isize, *pData);
		twi_enable_it(pTwi, TWI_IER_TXRDY);
	}
	/* Synchronous transfer */
	else {
		// Start write
		twi_start_write(pTwi, address, iaddress, isize, *pData++);
		num--;
		if (singleTransfer) {
			/* Send a STOP condition */
			twi_send_stop_condition(pTwi);
		}
		status = twi_get_status(pTwi);
		if (status & TWI_SR_NACK)
			trace_error("TWID NACK error\n\r");
		while (!(status & TWI_SR_TXRDY) && (timeout++ < TWITIMEOUTMAX)) {
			status = twi_get_status(pTwi);
		}
		if (timeout == TWITIMEOUTMAX) {
			trace_error("TWID Timeout BS\n\r");
		}
		timeout = 0;
		/* Send all bytes */
		while (num > 0) {
			/* Wait before sending the next byte */
			timeout = 0;
			twi_write_byte(pTwi, *pData++);
			status = twi_get_status(pTwi);
			if (status & TWI_SR_NACK)
				trace_error("TWID NACK error\n\r");
			while (!(status & TWI_SR_TXRDY)
			       && (timeout++ < TWITIMEOUTMAX)) {
				status = twi_get_status(pTwi);
			}
			if (timeout == TWITIMEOUTMAX) {
				trace_error("TWID Timeout BS\n\r");
			}
			num--;
		}
		/* Wait for actual end of transfer */
		timeout = 0;
		if (!singleTransfer) {
			/* Send a STOP condition */
			twi_send_stop_condition(pTwi);
		}
		while (!twi_is_transfer_complete(pTwi)
		       && (++timeout < TWITIMEOUTMAX)) ;
		if (timeout == TWITIMEOUTMAX) {
			trace_error("TWID Timeout TC2\n\r");
		}
	}
	return 0;
}
