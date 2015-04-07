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
 
/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "board.h"

#include <assert.h>

/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/
#define TWITIMEOUTMAX 0xfffff


static sXdmad twi_dma;
static sXdmadCfg twi_dmaCfg;
static uint32_t dmaWriteChannel,dmaReadChannel;
static LinkedListDescriporView1 dmaWriteLinkList[1];
static LinkedListDescriporView1 dmaReadLinkList[1];

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** TWI driver callback function.*/
typedef void (*TwiCallback)(Async *);

/** \brief TWI asynchronous transfer descriptor.*/
typedef struct _AsyncTwi {

    /** Asynchronous transfer status. */
    volatile uint32_t status;
    // Callback function to invoke when transfer completes or fails.*/
    TwiCallback callback;
    /** Pointer to the data buffer.*/
    uint8_t *pData;
    /** Total number of bytes to transfer.*/
    uint32_t num;
    /** Number of already transferred bytes.*/
    uint32_t transferred;

} AsyncTwi;

/*----------------------------------------------------------------------------
 *        Global functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Initializes a TWI DMA Read channel.
 */
static void TWID_DmaInitializeRead(uint8_t TWI_ID)
{
    
    /* Allocate a XDMA channel, Read accesses into TWI_THR */
    dmaReadChannel = XDMAD_AllocateChannel( &twi_dma, TWI_ID, XDMAD_TRANSFER_MEMORY);
    if ( dmaReadChannel == XDMAD_ALLOC_FAILED )
    {
        printf("-E- Can't allocate XDMA channel\n\r");
    }
    XDMAD_PrepareChannel(&twi_dma, dmaReadChannel );
}

/**
 * \brief Initializes a TWI DMA write channel.
 */
static void TWID_DmaInitializeWrite(uint8_t TWI_ID)
{
    
    /* Allocate a XDMA channel, Write accesses into TWI_THR */
    dmaWriteChannel = XDMAD_AllocateChannel( &twi_dma, XDMAD_TRANSFER_MEMORY, TWI_ID);
    if ( dmaWriteChannel == XDMAD_ALLOC_FAILED )
    {
        printf("-E- Can't allocate XDMA channel\n\r");
    }
    XDMAD_PrepareChannel(&twi_dma, dmaWriteChannel );

   
}
/**
 * \brief Initializes a TWI driver instance, using the given TWI peripheral.
 * \note The peripheral must have been initialized properly before calling this function.
 * \param pTwid  Pointer to the Twid instance to initialize.
 * \param pTwi  Pointer to the TWI peripheral to use.
 */
void TWID_Initialize(Twid *pTwid, Twi *pTwi)
{
    TRACE_DEBUG( "TWID_Initialize()\n\r" ) ;
    assert( pTwid != NULL ) ;
    assert( pTwi != NULL ) ;

    /* Initialize driver. */
    pTwid->pTwi = pTwi;
    pTwid->pTransfer = 0;
    
    /* Initialize XDMA driver instance with polling mode */
    XDMAD_Initialize( &twi_dma, 1 );
}


/**
 * \brief Configure xDMA write linker list for TWI transfer.
 */
static void _xdma_configure_write(uint8_t *buf, uint32_t len, uint8_t TWI_ID)
{
    uint32_t i;
    uint32_t xdmaCndc, Thr;
    
    Thr = (uint32_t)&(TWI0->TWI_THR);
    if(TWI_ID==ID_TWI1)
    {
      Thr = (uint32_t)&(TWI1->TWI_THR);
    }
    if(TWI_ID==ID_TWI2)
    {
      Thr = (uint32_t)&(TWI2->TWI_THR);
    }
    for ( i = 0; i < 1; i++){
        dmaWriteLinkList[i].mbr_ubc = XDMA_UBC_NVIEW_NDV1 
                                    |(( i == len - 1) ? 0: XDMA_UBC_NDE_FETCH_EN)
                                    | len ;
        dmaWriteLinkList[i].mbr_sa = (uint32_t)&buf[i];
        dmaWriteLinkList[i].mbr_da = Thr;
        if ( i == len - 1) dmaWriteLinkList[i].mbr_nda = 0;
            else dmaWriteLinkList[i].mbr_nda = (uint32_t)&dmaWriteLinkList[ i + 1 ];
        }
        twi_dmaCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN 
                         | XDMAC_CC_MBSIZE_SINGLE 
                         | XDMAC_CC_DSYNC_MEM2PER 
                         | XDMAC_CC_CSIZE_CHK_1 
                         | XDMAC_CC_DWIDTH_BYTE
                         | XDMAC_CC_SIF_AHB_IF0 
                         | XDMAC_CC_DIF_AHB_IF1 
                         | XDMAC_CC_SAM_INCREMENTED_AM 
                         | XDMAC_CC_DAM_FIXED_AM 
                         | XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber( 0, TWI_ID, XDMAD_TRANSFER_TX ));
        xdmaCndc = XDMAC_CNDC_NDVIEW_NDV1 
                 | XDMAC_CNDC_NDE_DSCR_FETCH_EN 
                 | XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED
                 | XDMAC_CNDC_NDDUP_DST_PARAMS_UNCHANGED ;
        CP15_coherent_dcache_for_dma((uint32_t)&dmaWriteLinkList, ((uint32_t)&dmaWriteLinkList + sizeof(LinkedListDescriporView1) * len));
        XDMAD_ConfigureTransfer( &twi_dma, dmaWriteChannel, &twi_dmaCfg, xdmaCndc, (uint32_t)&dmaWriteLinkList[0]);
}


/**
 * \brief Configure xDMA read linker list for TWI transfer.
 */
static void _xdma_configure_read(uint8_t *buf, uint32_t len, uint8_t TWI_ID)
{
    uint32_t i;
    uint32_t xdmaCndc, Rhr;
    
    Rhr = (uint32_t)&(TWI0->TWI_RHR);
    if(TWI_ID==ID_TWI1)
    {
      Rhr = (uint32_t)&(TWI1->TWI_RHR);
    }
    if(TWI_ID==ID_TWI2)
    {
      Rhr = (uint32_t)&(TWI2->TWI_RHR);
    }
    for ( i = 0; i < 1; i++){
        dmaReadLinkList[i].mbr_ubc = XDMA_UBC_NVIEW_NDV1 
                               | (( i == len - 1) ? 0: XDMA_UBC_NDE_FETCH_EN)
                               | len ;
        dmaReadLinkList[i].mbr_sa  = Rhr;
        dmaReadLinkList[i].mbr_da = (uint32_t)&buf[i];
        if ( i == len - 1)
             dmaReadLinkList[i].mbr_nda = 0;
        else
             dmaReadLinkList[i].mbr_nda = (uint32_t)&dmaReadLinkList[ i + 1 ];
        }
        twi_dmaCfg.mbr_cfg = XDMAC_CC_TYPE_PER_TRAN 
                         | XDMAC_CC_MBSIZE_SINGLE 
                         | XDMAC_CC_DSYNC_PER2MEM 
                         | XDMAC_CC_CSIZE_CHK_1 
                         | XDMAC_CC_DWIDTH_BYTE
                         | XDMAC_CC_SIF_AHB_IF1 
                         | XDMAC_CC_DIF_AHB_IF0 
                         | XDMAC_CC_SAM_FIXED_AM 
                         | XDMAC_CC_DAM_INCREMENTED_AM 
                         | XDMAC_CC_PERID(XDMAIF_Get_ChannelNumber( 0, TWI_ID, XDMAD_TRANSFER_RX ));
        xdmaCndc = XDMAC_CNDC_NDVIEW_NDV1 
                 | XDMAC_CNDC_NDE_DSCR_FETCH_EN 
                 | XDMAC_CNDC_NDSUP_SRC_PARAMS_UPDATED
                 | XDMAC_CNDC_NDDUP_DST_PARAMS_UPDATED ;
        CP15_coherent_dcache_for_dma((uint32_t)&dmaReadLinkList, ((uint32_t)&dmaReadLinkList + sizeof(LinkedListDescriporView1) * len));
        XDMAD_ConfigureTransfer( &twi_dma, dmaReadChannel, &twi_dmaCfg, xdmaCndc, (uint32_t)&dmaReadLinkList[0]);
}


/**
 * \brief Interrupt handler for a TWI peripheral. Manages asynchronous transfer
 * occuring on the bus. This function MUST be called by the interrupt service
 * routine of the TWI peripheral if asynchronous read/write are needed.
  * \param pTwid  Pointer to a Twid instance.
 */
void TWID_Handler( Twid *pTwid )
{
    uint32_t status;
    AsyncTwi *pTransfer ;
    Twi *pTwi ;

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

            TWI_DisableIt(pTwi, TWI_IDR_RXRDY);
            TWI_EnableIt(pTwi, TWI_IER_TXCOMP);
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

            TWI_DisableIt(pTwi, TWI_IDR_TXRDY);
            TWI_EnableIt(pTwi, TWI_IER_TXCOMP);
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

        TWI_DisableIt(pTwi, TWI_IDR_TXCOMP);
        pTransfer->status = 0;
        if (pTransfer->callback) {
            pTransfer->callback((Async *)(void*) pTransfer);
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
    Twi *pTwi;
    AsyncTwi *pTransfer;
    uint32_t timeout = 0;
    uint32_t i = 0;
    uint32_t status;

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
        TWI_EnableIt(pTwi, TWI_IER_RXRDY);
        TWI_StartRead(pTwi, address, iaddress, isize);
    }
    /* Synchronous transfer*/
    else {

        /* Start read*/
        TWI_StartRead(pTwi, address, iaddress, isize);
        if (num != 1) 
        {
                status = TWI_GetStatus(pTwi);

                if(status & TWI_SR_NACK)
                    TRACE_ERROR("TWID NACK error\n\r");
                timeout = 0;
                while( ! (status & TWI_SR_RXRDY) && (++timeout<TWITIMEOUTMAX))
                {
                    status = TWI_GetStatus(pTwi);
                    //TRACE_ERROR("TWID status %x\n\r",TWI_GetStatus(pTwi));
                }

                pData[0] = TWI_ReadByte(pTwi);
                for( i = 1; i < num - 1; i++)
                {
                    status = TWI_GetStatus(pTwi);
                    if(status & TWI_SR_NACK)
                      TRACE_ERROR("TWID NACK error\n\r");
                    timeout = 0;
                    while( ! (status & TWI_SR_RXRDY) && (++timeout<TWITIMEOUTMAX))
                    {
                        status = TWI_GetStatus(pTwi);
                        //TRACE_ERROR("TWID status %x\n\r",TWI_GetStatus(pTwi));
                    }
                    pData[i] = TWI_ReadByte(pTwi);
                }
        }
        TWI_Stop(pTwi);
        status = TWI_GetStatus(pTwi);
        if(status & TWI_SR_NACK)
          TRACE_ERROR("TWID NACK error\n\r");
        timeout = 0;
        while( ! (status & TWI_SR_RXRDY)  && (++timeout<TWITIMEOUTMAX))
        {
            status = TWI_GetStatus(pTwi);
            //TRACE_ERROR("TWID status %x\n\r",TWI_GetStatus(pTwi));
        }

        pData[i] = TWI_ReadByte(pTwi);
        timeout = 0;
        status = TWI_GetStatus(pTwi);
        while( !(status & TWI_SR_TXCOMP) && (++timeout<TWITIMEOUTMAX))
        {
            status = TWI_GetStatus(pTwi);
            //TRACE_ERROR("TWID status %x\n\r",TWI_GetStatus(pTwi));
        }
#if 0
        /* Read all bytes, setting STOP before the last byte*/
        while (num > 0) {

            /* Last byte ?*/
            if (num == 1) {

                TWI_Stop(pTwi);
            }

            /* Wait for byte then read and store it*/
            timeout = 0;
            while( !TWI_ByteReceived(pTwi) && (++timeout<TWITIMEOUTMAX) );
            if (timeout == TWITIMEOUTMAX) {
                TRACE_ERROR("TWID Timeout BR\n\r");
            }
            *pData++ = TWI_ReadByte(pTwi);
            num--;
        }

        /* Wait for transfer to be complete */
        timeout = 0;
        while( !TWI_TransferComplete(pTwi) && (++timeout<TWITIMEOUTMAX) );
        if (timeout == TWITIMEOUTMAX) {
            TRACE_ERROR("TWID Timeout TC\n\r");
        }
#endif
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
 * \param TWI_ID  TWI ID for TWI0, TWI1, TWI2.
 * \return 0 if the transfer has been started; otherwise returns a TWI error code.
 */
uint8_t TWID_DmaRead(
    Twid *pTwid,
    uint8_t address,
    uint32_t iaddress,
    uint8_t isize,
    uint8_t *pData,
    uint32_t num,
    Async *pAsync,
    uint8_t TWI_ID)
{
    Twi *pTwi;
    AsyncTwi *pTransfer;
    uint32_t timeout = 0;
    uint32_t status;

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
        TWI_EnableIt(pTwi, TWI_IER_RXRDY);
        TWI_StartRead(pTwi, address, iaddress, isize);
    }
    /* Synchronous transfer*/
    else {

        TWID_DmaInitializeRead(TWI_ID);
        _xdma_configure_read(pData, num, TWI_ID);
        /* Start read*/
        XDMAD_StartTransfer( &twi_dma, dmaReadChannel );
        
        TWI_StartRead(pTwi, address, iaddress, isize);   
        
        while((XDMAD_IsTransferDone(&twi_dma, dmaReadChannel)) && (++timeout<TWITIMEOUTMAX));
        
        XDMAD_StopTransfer( &twi_dma, dmaReadChannel );
        
        status = TWI_GetStatus(pTwi);
        timeout=0;
        while( !(status & TWI_SR_RXRDY) && (++timeout<TWITIMEOUTMAX));
        
        TWI_Stop(pTwi);
        
        TWI_ReadByte(pTwi);
        
        status = TWI_GetStatus(pTwi);
        timeout=0;
        while( !(status & TWI_SR_RXRDY) && (++timeout<TWITIMEOUTMAX));
        
        TWI_ReadByte(pTwi);
        
        status = TWI_GetStatus(pTwi);
        timeout=0;
        while( !(status & TWI_SR_TXCOMP) && (++timeout<TWITIMEOUTMAX));
        if (timeout == TWITIMEOUTMAX) {
            TRACE_ERROR("TWID Timeout Read\n\r");
        }
        XDMAD_FreeChannel(&twi_dma, dmaReadChannel);

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
 * \param TWI_ID  TWI ID for TWI0, TWI1, TWI2.
 * \return 0 if the transfer has been started; otherwise returns a TWI error code.
 */
uint8_t TWID_DmaWrite(
    Twid *pTwid,
    uint8_t address,
    uint32_t iaddress,
    uint8_t isize,
    uint8_t *pData,
    uint32_t num,
    Async *pAsync,
    uint8_t TWI_ID)
{
    Twi *pTwi = pTwid->pTwi;
    AsyncTwi *pTransfer = (AsyncTwi *) pTwid->pTransfer;
    uint32_t timeout = 0;
    uint32_t status;
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
        pTwid->pTransfer = pAsync;
        pTransfer = (AsyncTwi *) pAsync;
        pTransfer->status = ASYNC_STATUS_PENDING;
        pTransfer->pData = pData;
        pTransfer->num = num;
        pTransfer->transferred = 1;

        /* Enable write interrupt and start the transfer */
        TWI_StartWrite(pTwi, address, iaddress, isize, *pData);
        TWI_EnableIt(pTwi, TWI_IER_TXRDY);
    }
    /* Synchronous transfer*/
    else {

        CP15_coherent_dcache_for_dma ( (uint32_t)pData, (uint32_t)pData );
        TWID_DmaInitializeWrite(TWI_ID);
        _xdma_configure_write(pData, num, TWI_ID);
        /* Set slave address and number of internal address bytes. */
        pTwi->TWI_MMR = 0;
        pTwi->TWI_MMR = (isize << 8) | (address << 16);

        /* Set internal address bytes. */
        pTwi->TWI_IADR = 0;
        pTwi->TWI_IADR = iaddress;
        XDMAD_StartTransfer( &twi_dma, dmaWriteChannel );
           
        while(XDMAD_IsTransferDone(&twi_dma, dmaWriteChannel));
        
        XDMAD_StopTransfer( &twi_dma, dmaWriteChannel );
        
        status = TWI_GetStatus(pTwi);
        timeout = 0;
        while( !(status & TWI_SR_TXRDY) && (timeout++ < TWITIMEOUTMAX) )
        {
            status = TWI_GetStatus(pTwi);
        }
        if (timeout == TWITIMEOUTMAX) {
            TRACE_ERROR("TWID Timeout TXRDY\n\r");
        }
        
        /* Send a STOP condition */
        TWI_Stop(pTwi);
        
        status = TWI_GetStatus(pTwi);
        timeout = 0;
        while( !(status & TWI_SR_TXCOMP) && (++timeout<TWITIMEOUTMAX))
        {
            status = TWI_GetStatus(pTwi);
        }
        if (timeout == TWITIMEOUTMAX) {
            TRACE_ERROR("TWID Timeout Write\n\r");
        }
       
        CP15_invalidate_dcache_for_dma ( (uint32_t)pData, (uint32_t)(pData) );
        XDMAD_FreeChannel(&twi_dma, dmaWriteChannel);
        
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
uint8_t TWID_Write(
    Twid *pTwid,
    uint8_t address,
    uint32_t iaddress,
    uint8_t isize,
    uint8_t *pData,
    uint32_t num,
    Async *pAsync)
{
    Twi *pTwi = pTwid->pTwi;
    AsyncTwi *pTransfer = (AsyncTwi *) pTwid->pTransfer;
    uint32_t timeout = 0;
    uint32_t status;
    uint8_t singleTransfer = 0;
    assert( pTwi != NULL ) ;
    assert( (address & 0x80) == 0 ) ;
    assert( (iaddress & 0xFF000000) == 0 ) ;
    assert( isize < 4 ) ;

    if(num == 1) singleTransfer = 1;
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
        TWI_EnableIt(pTwi, TWI_IER_TXRDY);
    }
    /* Synchronous transfer*/
    else {

        // Start write
        TWI_StartWrite(pTwi, address, iaddress, isize, *pData++);
        num--;
        if (singleTransfer) {
            /* Send a STOP condition */
            TWI_SendSTOPCondition(pTwi);
        }
        status = TWI_GetStatus(pTwi);

        if(status & TWI_SR_NACK)
            TRACE_ERROR("TWID NACK error\n\r");
        while( !(status & TWI_SR_TXRDY) && (timeout++ < TWITIMEOUTMAX) )
        {
            status = TWI_GetStatus(pTwi);
        }
        if (timeout == TWITIMEOUTMAX) {
            TRACE_ERROR("TWID Timeout BS\n\r");
        }
        timeout = 0;
        /* Send all bytes */
        while (num > 0) {

            /* Wait before sending the next byte */
            timeout = 0;
            TWI_WriteByte(pTwi, *pData++);
            status = TWI_GetStatus(pTwi);

            if(status & TWI_SR_NACK)
                TRACE_ERROR("TWID NACK error\n\r");
            while( !(status & TWI_SR_TXRDY) && (timeout++ < TWITIMEOUTMAX) )
            {
                status = TWI_GetStatus(pTwi);
            }
            if (timeout == TWITIMEOUTMAX) {
                TRACE_ERROR("TWID Timeout BS\n\r");
            }


            num--;
        }

        /* Wait for actual end of transfer */
        timeout = 0;
        if (!singleTransfer) {
           /* Send a STOP condition */
           TWI_SendSTOPCondition(pTwi);
        }
        while( !TWI_TransferComplete(pTwi) && (++timeout<TWITIMEOUTMAX) );
        if (timeout == TWITIMEOUTMAX) {
            TRACE_ERROR("TWID Timeout TC2\n\r");
        }

    }

    return 0;
}

