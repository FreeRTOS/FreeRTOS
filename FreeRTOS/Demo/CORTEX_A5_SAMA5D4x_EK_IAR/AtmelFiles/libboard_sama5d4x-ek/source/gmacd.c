/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
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

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include <board.h>
#include <string.h>

/** \addtogroup gmacd_defines
    @{*/


/*----------------------------------------------------------------------------
 *        Macro
 *----------------------------------------------------------------------------*/
/** Return count in buffer */
#define GCIRC_CNT(head,tail,size) (((head) - (tail)) % (size))

/** Return space available, 0..size-1. always leave one free char as a completely full buffer 
    has head == tail, which is the same as empty */
#define GCIRC_SPACE(head,tail,size) GCIRC_CNT((tail),((head)+1),(size))

/** Return count up to the end of the buffer. Carefully avoid accessing head and tail more than once,
    so they can change underneath us without returning inconsistent results */
#define GCIRC_CNT_TO_END(head,tail,size) \
     ({int end = (size) - (tail); \
     int n = ((head) + end) % (size); \
     n < end ? n : end;})

/** Return space available up to the end of the buffer */
#define GCIRC_SPACE_TO_END(head,tail,size) \
   ({int end = (size) - 1 - (head); \
     int n = (end + (tail)) % (size); \
     n <= end ? n : end+1;})

/** Increment head or tail */
#define GCIRC_INC(headortail,size) \
       headortail++;             \
        if(headortail >= size) {  \
            headortail = 0;       \
        }

/** Circular buffer is empty ? */
#define GCIRC_EMPTY(head, tail)     (head == tail)

/** Clear circular buffer */
#define GCIRC_CLEAR(head, tail)  (head = tail = 0)

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------
/// The buffer addresses written into the descriptors must be aligned so the
/// last few bits are zero.  These bits have special meaning for the GMAC
/// peripheral and cannot be used as part of the address.
#define GMAC_ADDRESS_MASK   ((unsigned int)0xFFFFFFFC)
#define GMAC_LENGTH_FRAME   ((unsigned int)0x3FFF)    /// Length of frame mask

// receive buffer descriptor bits
#define GMAC_RX_OWNERSHIP_BIT   (1 <<  0)
#define GMAC_RX_WRAP_BIT        (1 <<  1)
#define GMAC_RX_SOF_BIT         (1 << 14)
#define GMAC_RX_EOF_BIT         (1 << 15)

// Transmit buffer descriptor bits
#define GMAC_TX_LAST_BUFFER_BIT (1 << 15)
#define GMAC_TX_WRAP_BIT        (1 << 30)
#define GMAC_TX_USED_BIT        (1 << 31)
#define GMAC_TX_RLE_BIT         (1 << 29) /// Retry Limit Exceeded
#define GMAC_TX_UND_BIT         (1 << 28) /// Tx Buffer Underrun
#define GMAC_TX_ERR_BIT         (1 << 27) /// Exhausted in mid-frame
#define GMAC_TX_ERR_BITS  \
    (GMAC_TX_RLE_BIT | GMAC_TX_UND_BIT | GMAC_TX_ERR_BIT)

/*---------------------------------------------------------------------------
 *         Local functions
 *---------------------------------------------------------------------------*/

/**
 *  \brief Disable TX & reset registers and descriptor list
 *  \param pDrv Pointer to GMAC Driver instance.
 */
static void GMACD_ResetTx(sGmacd *pDrv )
{
    Gmac *pHw = pDrv->pHw;
    uint8_t *pTxBuffer = pDrv->pTxBuffer;
    sGmacTxDescriptor *pTd = pDrv->pTxD;
    uint32_t Index;
    uint32_t Address;

    /* Disable TX */
    GMAC_TransmitEnable(pHw, 0);
    /* Setup the TX descriptors. */
    GCIRC_CLEAR(pDrv->wTxHead, pDrv->wTxTail);
    for(Index = 0; Index < pDrv->wTxListSize; Index++) {
        Address = (uint32_t)(&(pTxBuffer[Index * GMAC_TX_UNITSIZE]));
        pTd[Index].addr = Address;
        pTd[Index].status.val = (uint32_t)GMAC_TX_USED_BIT;
    }
    pTd[pDrv->wTxListSize - 1].status.val = GMAC_TX_USED_BIT | GMAC_TX_WRAP_BIT;
    /* Transmit Buffer Queue Pointer Register */
    GMAC_SetTxQueue(pHw, (uint32_t)pTd);
}
    
/**
 *  \brief Disable RX & reset registers and descriptor list
 *  \param pDrv Pointer to GMAC Driver instance. 
 */
static void GMACD_ResetRx(sGmacd *pDrv )
{
    Gmac    *pHw = pDrv->pHw;
    uint8_t *pRxBuffer = pDrv->pRxBuffer;
    sGmacRxDescriptor *pRd = pDrv->pRxD;

    uint32_t Index;
    uint32_t Address;

    /* Disable RX */
    GMAC_ReceiveEnable(pHw, 0);

    /* Setup the RX descriptors. */
    pDrv->wRxI = 0;
    for(Index = 0; Index < pDrv->wRxListSize; Index++)
    {
        Address = (uint32_t)(&(pRxBuffer[Index * GMAC_RX_UNITSIZE]));
        /* Remove GMAC_RXD_bmOWNERSHIP and GMAC_RXD_bmWRAP */
        pRd[Index].addr.val = Address & GMAC_ADDRESS_MASK;
        pRd[Index].status.val = 0;
    }
    pRd[pDrv->wRxListSize - 1].addr.val |= GMAC_RX_WRAP_BIT;

    /* Receive Buffer Queue Pointer Register */
    GMAC_SetRxQueue(pHw, (uint32_t) pRd);
}

    
/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/
 
 
/**
 *  \brief GMAC Interrupt handler
 *  \param pGmacd Pointer to GMAC Driver instance.
 */
void GMACD_Handler(sGmacd *pGmacd )
{
    Gmac *pHw = pGmacd->pHw;
    sGmacTxDescriptor      *pTxTd;
    fGmacdTransferCallback *pTxCb = NULL;
    uint32_t isr;
    uint32_t rsr;
    uint32_t tsr;
   
    uint32_t rxStatusFlag;
    uint32_t txStatusFlag;
    isr = GMAC_GetItStatus(pHw);
    rsr = GMAC_GetRxStatus(pHw);
    tsr = GMAC_GetTxStatus(pHw);

    isr &= ~(GMAC_GetItMask(pHw)| 0xF8030300);

    /* RX packet */
    if ((isr & GMAC_ISR_RCOMP) || (rsr & GMAC_RSR_REC)) {
        asm("nop");
        rxStatusFlag = GMAC_RSR_REC;
        /* Frame received */
        /* Check OVR */
        if (rsr & GMAC_RSR_RXOVR) {
            rxStatusFlag |= GMAC_RSR_RXOVR;
        }
        /* Check BNA */
        if (rsr & GMAC_RSR_BNA) {
            rxStatusFlag |= GMAC_RSR_BNA;
        }
        /* Check HNO */
        if (rsr & GMAC_RSR_HNO) {
            rxStatusFlag |= GMAC_RSR_HNO;
        }        
        /* Clear status */
        GMAC_ClearRxStatus(pHw, rxStatusFlag);

        /* Invoke callbacks */
        if (pGmacd->fRxCb)
        {
            pGmacd->fRxCb(rxStatusFlag);
        }
    }

    /* TX packet */
    if ((isr & GMAC_ISR_TCOMP) || (tsr & GMAC_TSR_TXCOMP)) {
        asm("nop");
        txStatusFlag = GMAC_TSR_TXCOMP;

        /*  A frame transmitted Check RLE */
        if (tsr & GMAC_TSR_RLE) {
            /* Status RLE & Number of discarded buffers */
            txStatusFlag = GMAC_TSR_RLE
                         | GCIRC_CNT(pGmacd->wTxHead,
                                     pGmacd->wTxTail,
                                     pGmacd->wTxListSize);
            pTxCb = &pGmacd->fTxCbList[pGmacd->wTxTail];
            GMACD_ResetTx(pGmacd);
            TRACE_INFO("Tx RLE!!\n\r");
            GMAC_TransmitEnable(pHw, 1);
        }
        /* Check COL */
        if (tsr & GMAC_TSR_COL) {
            txStatusFlag |= GMAC_TSR_COL;
        }
        /* Check TFC */
        if (tsr & GMAC_TSR_TFC) {
            txStatusFlag |= GMAC_TSR_TFC;
        }
        /* Check UND */
        if (tsr & GMAC_TSR_UND) {
            txStatusFlag |= GMAC_TSR_UND;
        }
        /* Check HRESP */
        if (tsr & GMAC_TSR_HRESP) {
            txStatusFlag |= GMAC_TSR_HRESP;
        }
        /* Clear status */
        GMAC_ClearTxStatus(pHw, txStatusFlag);

        if (!GCIRC_EMPTY(pGmacd->wTxHead, pGmacd->wTxTail))
        {
            /* Check the buffers */
            do {
                pTxTd = &pGmacd->pTxD[pGmacd->wTxTail];
                pTxCb = &pGmacd->fTxCbList[pGmacd->wTxTail];
                /* Exit if buffer has not been sent yet */

                if ((pTxTd->status.val & (uint32_t)GMAC_TX_USED_BIT) == 0) {
                    break;
                }
                /* Notify upper layer that a packet has been sent */
                if (*pTxCb) {
                    (*pTxCb)(txStatusFlag);
                }
                GCIRC_INC( pGmacd->wTxTail, pGmacd->wTxListSize );
            } while (GCIRC_CNT(pGmacd->wTxHead, pGmacd->wTxTail, pGmacd->wTxListSize));
        }
        
        if (tsr & GMAC_TSR_RLE) {
            /* Notify upper layer RLE */
            if (*pTxCb) {
                (*pTxCb)(txStatusFlag);
            }
        }
        
        /* If a wakeup has been scheduled, notify upper layer that it can
           send other packets, send will be successfull. */
        if((GCIRC_SPACE(pGmacd->wTxHead,
                         pGmacd->wTxTail,
                         pGmacd->wTxListSize) >= pGmacd->bWakeupThreshold) && pGmacd->fWakupCb)
        {
            pGmacd->fWakupCb();
        }
    }

    /* PAUSE Frame */
    if (isr & GMAC_ISR_PFNZ) TRACE_INFO("Pause!\n\r");
    if (isr & GMAC_ISR_PTZ)  TRACE_INFO("Pause TO!\n\r");
}


/**
 * \brief Initialize the GMAC with the Gmac controller address
 *  \param pGmacd Pointer to GMAC Driver instance. 
 *  \param pHw    Pointer to HW address for registers.
 *  \param bID     HW ID for power management
 *  \param enableCAF    Enable/Disable CopyAllFrame.
 *  \param enableNBC    Enable/Disable NoBroadCast.
 */
 void GMACD_Init(sGmacd *pGmacd,
                Gmac *pHw,
                uint8_t bID, 
                uint8_t enableCAF, 
                uint8_t enableNBC )
{
    uint32_t dwNcfgr;
    
    /* Check parameters */
    assert(GRX_BUFFERS * GMAC_RX_UNITSIZE > GMAC_FRAME_LENTGH_MAX);

    TRACE_DEBUG("GMAC_Init\n\r");

    /* Initialize struct */
    pGmacd->pHw = pHw;
    pGmacd->bId = bID;

    /* Power ON */
    PMC_EnablePeripheral(bID);

    /* Disable TX & RX and more */
    GMAC_NetworkControl(pHw, 0);
    GMAC_DisableIt(pHw, ~0u);
    
    GMAC_ClearStatistics(pHw);
    /* Clear all status bits in the receive status register. */
    GMAC_ClearRxStatus(pHw, GMAC_RSR_RXOVR | GMAC_RSR_REC | GMAC_RSR_BNA |GMAC_RSR_HNO);

    /* Clear all status bits in the transmit status register */
    GMAC_ClearTxStatus(pHw, GMAC_TSR_UBR | GMAC_TSR_COL | GMAC_TSR_RLE
                            | GMAC_TSR_TXGO | GMAC_TSR_TFC | GMAC_TSR_TXCOMP
                            | GMAC_TSR_UND | GMAC_TSR_HRESP );

    /* Clear interrupts */
    GMAC_GetItStatus(pHw);

    /* Enable the copy of data into the buffers
       ignore broadcasts, and don't copy FCS. */
    dwNcfgr = GMAC_NCFGR_FD | GMAC_NCFGR_DBW_DBW32 | GMAC_NCFGR_CLK_MCK_64;
    if( enableCAF ) {
        dwNcfgr |= GMAC_NCFGR_CAF;
    }
    if( enableNBC ) {
        dwNcfgr |= GMAC_NCFGR_NBC;
    }
    
    GMAC_Configure(pHw, dwNcfgr);
}


/**
 * Initialize necessary allocated buffer lists for GMAC Driver to transfer data.
 * Must be invoked after GMACD_Init() but before RX/TX start.
 * \param pGmacd Pointer to GMAC Driver instance.
 * \param pRxBuffer Pointer to allocated buffer for RX. The address should
 *                  be 8-byte aligned and the size should be
 *                  GMAC_RX_UNITSIZE * wRxSize.
 * \param pRxD      Pointer to allocated RX descriptor list.
 * \param wRxSize   RX size, in number of registered units (RX descriptors).
 * \param pTxBuffer Pointer to allocated buffer for TX. The address should
 *                  be 8-byte aligned and the size should be
 *                  GMAC_TX_UNITSIZE * wTxSize.
 * \param pTxD      Pointer to allocated TX descriptor list.
 * \param pTxCb     Pointer to allocated TX callback list.
 * \param wTxSize   TX size, in number of registered units (TX descriptors).
 * \return GMACD_OK or GMACD_PARAM.
 * \note If input address is not 8-byte aligned the address is automatically
 *       adjusted and the list size is reduced by one.
 */
uint8_t GMACD_InitTransfer( sGmacd *pGmacd,
    uint8_t *pRxBuffer, sGmacRxDescriptor *pRxD,
    uint16_t wRxSize,
    uint8_t *pTxBuffer, sGmacTxDescriptor *pTxD, fGmacdTransferCallback *pTxCb,
    uint16_t wTxSize)
{
    Gmac *pHw = pGmacd->pHw;

    if (wRxSize <= 1 || wTxSize <= 1 || pTxCb == NULL) return GMACD_PARAM;

    /* Assign RX buffers */
    if (   ((uint32_t)pRxBuffer & 0x7)
        || ((uint32_t)pRxD      & 0x7) )
    {
        wRxSize --;
        TRACE_DEBUG("RX list address adjusted\n\r");
    }
    pGmacd->pRxBuffer = (uint8_t*)((uint32_t)pRxBuffer & 0xFFFFFFF8);
    pGmacd->pRxD = (sGmacRxDescriptor*)((uint32_t)pRxD & 0xFFFFFFF8);
    pGmacd->wRxListSize = wRxSize;

    /* Assign TX buffers */
    if (   ((uint32_t)pTxBuffer & 0x7)
        || ((uint32_t)pTxD      & 0x7) )
    {
        wTxSize --;
        TRACE_DEBUG("TX list address adjusted\n\r");
    }
    pGmacd->pTxBuffer = (uint8_t*)((uint32_t)pTxBuffer & 0xFFFFFFF8);
    pGmacd->pTxD = (sGmacTxDescriptor*)((uint32_t)pTxD & 0xFFFFFFF8);
    pGmacd->wTxListSize = wTxSize;
    pGmacd->fTxCbList = pTxCb;

    /* Reset TX & RX */
    GMACD_ResetRx(pGmacd);
    GMACD_ResetTx(pGmacd);

    /* Enable Rx and Tx, plus the stats register. */
    GMAC_TransmitEnable(pHw, 1);
    GMAC_ReceiveEnable(pHw, 1);
    GMAC_StatisticsWriteEnable(pHw, 1);

    /* Setup the interrupts for TX (and errors) */
    GMAC_EnableIt(pHw, GMAC_IER_MFS 
                      |GMAC_IER_RCOMP
                      |GMAC_IER_RXUBR
                      |GMAC_IER_TXUBR
                      |GMAC_IER_TUR
                      |GMAC_IER_RLEX
                      |GMAC_IER_TFC 
                      |GMAC_IER_TCOMP
                      |GMAC_IER_ROVR 
                      |GMAC_IER_HRESP
                      |GMAC_IER_PFNZ 
                      |GMAC_IER_PTZ 
                      |GMAC_IER_PFTR
                      |GMAC_IER_EXINT
                      |GMAC_IER_DRQFR
                      |GMAC_IER_SFR
                      |GMAC_IER_DRQFT
                      |GMAC_IER_SFT
                      |GMAC_IER_PDRQFR
                      |GMAC_IER_PDRSFR
                      |GMAC_IER_PDRQFT
                      |GMAC_IER_PDRSFT);
    //0x03FCFCFF
    return GMACD_OK;
}


/**
 * Reset TX & RX queue & statistics
 * \param pGmacd Pointer to GMAC Driver instance.
 */
void GMACD_Reset(sGmacd *pGmacd)
{
    Gmac *pHw = pGmacd->pHw;

    GMACD_ResetRx(pGmacd);
    GMACD_ResetTx(pGmacd);
    //memset((void*)&GmacStatistics, 0x00, sizeof(GmacStats));
    GMAC_NetworkControl(pHw, GMAC_NCR_TXEN | GMAC_NCR_RXEN
                             | GMAC_NCR_WESTAT | GMAC_NCR_CLRSTAT);
}

/**
 * \brief Send a packet with GMAC. If the packet size is larger than transfer buffer size 
 * error returned. If packet transfer status is monitored, specify callback for each packet.
 *  \param pGmacd Pointer to GMAC Driver instance. 
 *  \param buffer   The buffer to be send
 *  \param size     The size of buffer to be send
 *  \param fGMAC_TxCallback Threshold Wakeup callback
 *  \param fWakeUpCb   TX Wakeup
 *  \return         OK, Busy or invalid packet
 */
uint8_t GMACD_Send(sGmacd *pGmacd,
                  void *pBuffer,
                  uint32_t size,
                  fGmacdTransferCallback fTxCb )
{
    Gmac *pHw = pGmacd->pHw;
    sGmacTxDescriptor      *pTxTd;
    volatile fGmacdTransferCallback *pfTxCb;
    
    TRACE_DEBUG("GMAC_Send\n\r");
    /* Check parameter */
    if (size > GMAC_TX_UNITSIZE) {

        TRACE_ERROR("GMAC driver does not split send packets.");
        return GMACD_PARAM;
    }

    /* Pointers to the current TxTd */
    pTxTd = &pGmacd->pTxD[pGmacd->wTxHead];
    /* If no free TxTd, buffer can't be sent */
    if( GCIRC_SPACE(pGmacd->wTxHead, pGmacd->wTxTail, pGmacd->wTxListSize) == 0)
        return GMACD_TX_BUSY;
    /* Pointers to the current Tx Callback */
    pfTxCb = &pGmacd->fTxCbList[pGmacd->wTxHead];
    /* Sanity check */

    /* Setup/Copy data to transmition buffer */
    if (pBuffer && size) {
        // Driver manage the ring buffer
        memcpy((void *)pTxTd->addr, pBuffer, size);
    }
    /* Tx Callback */
    *pfTxCb = fTxCb;

    /* Update TD status. The buffer size defined is length of ethernet frame
      so it's always the last buffer of the frame. */
    if (pGmacd->wTxHead == pGmacd->wTxListSize-1) {
        pTxTd->status.val = 
            (size & GMAC_LENGTH_FRAME) | GMAC_TX_LAST_BUFFER_BIT | GMAC_TX_WRAP_BIT;
    }
    else {
        pTxTd->status.val = (size & GMAC_LENGTH_FRAME) | GMAC_TX_LAST_BUFFER_BIT;
    }
    
    GCIRC_INC(pGmacd->wTxHead, pGmacd->wTxListSize);
    
    //CP15_flush_dcache_for_dma ((uint32_t)(pTxTd), ((uint32_t)(pTxTd) + sizeof(pTxTd)));
    /* Tx packets count */

    /* Now start to transmit if it is not already done */
    GMAC_TransmissionStart(pHw);

    return GMACD_OK;
}


/**
 * Return current load of TX.
 * \param pGmacd   Pointer to GMAC Driver instance.
 */
uint32_t GMACD_TxLoad(sGmacd *pGmacd)
{
    uint16_t head = pGmacd->wTxHead;
    uint16_t tail = pGmacd->wTxTail;
    return GCIRC_CNT(head, tail, pGmacd->wTxListSize);
}

/**
 * \brief Receive a packet with GMAC.
 * If not enough buffer for the packet, the remaining data is lost but right
 * frame length is returned.
 *  \param pGmacd Pointer to GMAC Driver instance. 
 *  \param pFrame           Buffer to store the frame
 *  \param frameSize        Size of the frame
 *  \param pRcvSize         Received size
 *  \return                 OK, no data, or frame too small
 */
uint8_t GMACD_Poll(sGmacd * pGmacd, 
                  uint8_t *pFrame, 
                  uint32_t frameSize, 
                  uint32_t *pRcvSize)
{

    uint16_t bufferLength;
    uint32_t   tmpFrameSize = 0;
    uint8_t  *pTmpFrame = 0;
    uint32_t   tmpIdx = pGmacd->wRxI;
    volatile sGmacRxDescriptor *pRxTd = &pGmacd->pRxD[pGmacd->wRxI];
    uint8_t isFrame = 0;
    
    if (pFrame == NULL) return GMACD_PARAM;

    /* Set the default return value */
    *pRcvSize = 0;
    
    /* Process received RxTd */
    while ((pRxTd->addr.val & GMAC_RX_OWNERSHIP_BIT) == GMAC_RX_OWNERSHIP_BIT)
    {
        /* A start of frame has been received, discard previous fragments */
        if ((pRxTd->status.val & GMAC_RX_SOF_BIT) == GMAC_RX_SOF_BIT)
        {
            /* Skip previous fragment */
            while (tmpIdx != pGmacd->wRxI)
            {
                pRxTd = &pGmacd->pRxD[pGmacd->wRxI];
                pRxTd->addr.val &= ~(GMAC_RX_OWNERSHIP_BIT);
                GCIRC_INC(pGmacd->wRxI, pGmacd->wRxListSize);
            }
            pTmpFrame = pFrame;
            tmpFrameSize = 0;
            /* Start to gather buffers in a frame */
            isFrame = 1;
        }
        /* Increment the pointer */
        GCIRC_INC(tmpIdx, pGmacd->wRxListSize);
        asm("nop");
        /* Copy data in the frame buffer */
        if (isFrame) {
            if (tmpIdx == pGmacd->wRxI)
            {
                TRACE_INFO("no EOF (Invalid of buffers too small)\n\r");

                do {
                    pRxTd = &pGmacd->pRxD[pGmacd->wRxI];
                    pRxTd->addr.val &= ~(GMAC_RX_OWNERSHIP_BIT);
                    GCIRC_INC(pGmacd->wRxI, pGmacd->wRxListSize);
                } while(tmpIdx != pGmacd->wRxI);
                return GMACD_RX_NULL;
            }

            /* Copy the buffer into the application frame */
            bufferLength = GMAC_RX_UNITSIZE;
            if ((tmpFrameSize + bufferLength) > frameSize)
            {
                bufferLength = frameSize - tmpFrameSize;
            }
         
            memcpy(pTmpFrame, (void*)(pRxTd->addr.val & GMAC_ADDRESS_MASK), bufferLength);
            pTmpFrame += bufferLength;
            tmpFrameSize += bufferLength;

            /* An end of frame has been received, return the data */
            if ((pRxTd->status.val & GMAC_RX_EOF_BIT) == GMAC_RX_EOF_BIT)
            {
                /* Frame size from the GMAC */
                *pRcvSize = (pRxTd->status.val & GMAC_LENGTH_FRAME);

                /* Application frame buffer is too small all data have not been copied */
                if (tmpFrameSize < *pRcvSize) {
                    return GMACD_SIZE_TOO_SMALL;
                }
                TRACE_DEBUG("packet %d-%d (%d)\n\r", pGmacd->wRxI, tmpIdx, *pRcvSize);
                /* All data have been copied in the application frame buffer => release TD */
                while (pGmacd->wRxI != tmpIdx)
                {
                    pRxTd = &pGmacd->pRxD[pGmacd->wRxI];
                    pRxTd->addr.val &= ~(GMAC_RX_OWNERSHIP_BIT);
                    GCIRC_INC(pGmacd->wRxI, pGmacd->wRxListSize);
                }
                return GMACD_OK;
            }
        }
        
        /* SOF has not been detected, skip the fragment */
        else {
           pRxTd->addr.val &= ~(GMAC_RX_OWNERSHIP_BIT);
           pGmacd->wRxI = tmpIdx;
        }
       
        /* Process the next buffer */
        pRxTd = &pGmacd->pRxD[tmpIdx];
    }
    return GMACD_RX_NULL;
}

/**
 * \brief Registers pRxCb callback. Callback will be invoked after the next received
 * frame. When GMAC_Poll() returns GMAC_RX_NO_DATA the application task call GMAC_Set_RxCb()
 * to register pRxCb() callback and enters suspend state. The callback is in charge 
 * to resume the task once a new frame has been received. The next time GMAC_Poll()
 * is called, it will be successfull.
 *  \param pGmacd Pointer to GMAC Driver instance. 
 *  \param pRxCb   Pointer to callback function
 *  \return        OK, no data, or frame too small
 */

void GMACD_SetRxCallback(sGmacd * pGmacd, fGmacdTransferCallback fRxCb)
{
    Gmac *pHw = pGmacd->pHw;

    if (fRxCb == NULL)
    {
        GMAC_DisableIt(pHw, GMAC_IDR_RCOMP);
        pGmacd->fRxCb = NULL;
    }
    else
    {
        pGmacd->fRxCb = fRxCb;
        GMAC_EnableIt(pHw, GMAC_IER_RCOMP);
    }
}


/**
 * Register/Clear TX wakeup callback.
 *
 * When GMACD_Send() returns GMACD_TX_BUSY (all TD busy) the application 
 * task calls GMACD_SetTxWakeupCallback() to register fWakeup() callback and 
 * enters suspend state. The callback is in charge to resume the task once 
 * several TD have been released. The next time GMACD_Send() will be called,
 * it shall be successfull.
 *
 * This function is usually invoked with NULL callback from the TX wakeup
 * callback itself, to unregister. Once the callback has resumed the
 * application task, there is no need to invoke the callback again.
 *
 * \param pGmacd   Pointer to GMAC Driver instance.
 * \param fWakeup     Wakeup callback.
 * \param bThreshould Number of free TD before wakeup callback invoked.
 * \return GMACD_OK, GMACD_PARAM on parameter error.
 */
uint8_t GMACD_SetTxWakeupCallback(sGmacd * pGmacd,
                                  fGmacdWakeupCallback fWakeup,
                                  uint8_t bThreshold)
{
    if (fWakeup == NULL)
    {
        pGmacd->fWakupCb = NULL;
    }
    else
    {
        if (bThreshold <= pGmacd->wTxListSize)
        {
            pGmacd->fWakupCb = fWakeup;
            pGmacd->bWakeupThreshold = bThreshold;
        }
        else
        {
            return GMACD_PARAM;
        }
    }

    return GMACD_OK;
}
