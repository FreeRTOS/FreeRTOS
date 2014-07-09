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
 
/** \file */

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include <board.h>
#include <string.h>

/** \addtogroup EMACD_defines
    @{*/

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/

/** Error bits for TX */
#define EMAC_TX_ERR_BITS  \
    (EMAC_TXD_bmERROR | EMAC_TXD_bmUNDERRUN | EMAC_TXD_bmEXHAUSTED)

/*---------------------------------------------------------------------------
 * Circular buffer management
 *---------------------------------------------------------------------------*/

/** Return count in buffer */
#define CIRC_CNT(head,tail,size) (((head) - (tail)) % (size))

/** Return space available, 0..size-1. always leave one free char as a completely full buffer 
    has head == tail, which is the same as empty */
#define CIRC_SPACE(head,tail,size) CIRC_CNT((tail),((head)+1),(size))

/** Return count up to the end of the buffer. Carefully avoid accessing head and tail more than once,
    so they can change underneath us without returning inconsistent results */
#define CIRC_CNT_TO_END(head,tail,size) \
     ({int end = (size) - (tail); \
     int n = ((head) + end) % (size); \
     n < end ? n : end;})

/** Return space available up to the end of the buffer */
#define CIRC_SPACE_TO_END(head,tail,size) \
   ({int end = (size) - 1 - (head); \
     int n = (end + (tail)) % (size); \
     n <= end ? n : end+1;})

/** Increment head or tail */
#define CIRC_INC(headortail,size) \
        headortail++;             \
        if(headortail >= size) {  \
            headortail = 0;       \
        }

/** Circular buffer is empty ? */
#define CIRC_EMPTY(head, tail)     (head == tail)

/** Clear circular buffer */
#define CIRC_CLEAR(head, tail)  (head = tail = 0)

/** @}*/

/*----------------------------------------------------------------------------
 *         Internal variables
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------
 *         Internal functions
 *----------------------------------------------------------------------------*/

/**
 * Disable TX & reset registers and descriptor list
 * \param pDrv Pointer to EMAC Driver instance.
 */
static void EMACD_ResetTx(sEmacd *pDrv)
{
    Emac    *pHw = pDrv->pHw;
    uint8_t *pTxBuffer = pDrv->pTxBuffer;
    sEmacTxDescriptor *pTd = pDrv->pTxD;

    uint32_t Index;
    uint32_t Address;

    /* Disable TX */
    EMAC_TransmitEnable(pHw, 0);

    /* Setup the TX descriptors. */
    CIRC_CLEAR(pDrv->wTxHead, pDrv->wTxTail);
    for(Index = 0; Index < pDrv->wTxListSize; Index++)
    {
        Address = (uint32_t)(&(pTxBuffer[Index * EMAC_TX_UNITSIZE]));
        pTd[Index].addr = Address;
        pTd[Index].status.val = EMAC_TXD_bmUSED;
    }
    pTd[pDrv->wTxListSize - 1].status.val = EMAC_TXD_bmUSED | EMAC_TXD_bmWRAP;

    /* Transmit Buffer Queue Pointer Register */
    EMAC_SetTxQueue(pHw, (uint32_t)pTd);
}

/**
 * Disable RX & reset registers and descriptor list
 * \param pDrv Pointer to EMAC Driver instance.
 */
static void EMACD_ResetRx(sEmacd *pDrv)
{
    Emac    *pHw = pDrv->pHw;
    uint8_t *pRxBuffer = pDrv->pRxBuffer;
    sEmacRxDescriptor *pRd = pDrv->pRxD;

    uint32_t Index;
    uint32_t Address;

    /* Disable RX */
    EMAC_ReceiveEnable(pHw, 0);

    /* Setup the RX descriptors. */
    pDrv->wRxI = 0;
    for(Index = 0; Index < pDrv->wRxListSize; Index++)
    {
        Address = (uint32_t)(&(pRxBuffer[Index * EMAC_RX_UNITSIZE]));
        /* Remove EMAC_RXD_bmOWNERSHIP and EMAC_RXD_bmWRAP */
        pRd[Index].addr.val = Address & EMAC_RXD_ADDR_MASK;
        pRd[Index].status.val = 0;
    }
    pRd[pDrv->wRxListSize - 1].addr.val |= EMAC_RXD_bmWRAP;

    /* Receive Buffer Queue Pointer Register */
    EMAC_SetRxQueue(pHw, (uint32_t) pRd);
}

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/
 
/**
 * EMAC Interrupt handler
 */
void EMACD_Handler( sEmacd *pEmacd )
{
    Emac *pHw = pEmacd->pHw;
    uint32_t isr;
    uint32_t rsr;
    uint32_t tsr;
    sEmacTxDescriptor      *pTxTd;
    fEmacdTransferCallback *pTxCb = NULL;
    uint32_t rxStatusFlag;
    uint32_t txStatusFlag;

    isr = EMAC_GetItStatus(pHw);
    rsr = EMAC_GetRxStatus(pHw);
    tsr = EMAC_GetTxStatus(pHw);

    isr &= ~(EMAC_GetItMask(pHw) | 0xFFC300);

    /* RX packet */
    if ((isr & EMAC_ISR_RCOMP) || (rsr & EMAC_RSR_REC))
    {
        asm("nop");
        rxStatusFlag = EMAC_RSR_REC;
        /* Check OVR */
        if (rsr & EMAC_RSR_OVR)
        {
            rxStatusFlag |= EMAC_RSR_OVR;
        }
        /* Check BNA */
        if (rsr & EMAC_RSR_BNA)
        {
            rxStatusFlag |= EMAC_RSR_BNA;
        }
        /* Clear status */
        EMAC_ClearRxStatus(pHw, rxStatusFlag);

        /* Invoke callbacks */
        if (pEmacd->fRxCb)
        {
            pEmacd->fRxCb(rxStatusFlag);
        }
    }

    /* TX packet */
    if ((isr & EMAC_ISR_TCOMP) || (tsr & EMAC_TSR_COMP)) {
        asm("nop");
        txStatusFlag = EMAC_TSR_COMP;

        /* A frame transmitted */

        /* Check RLE */
        if (tsr & EMAC_TSR_RLES)
        {
            /* Status RLE & Number of discarded buffers */
            txStatusFlag = EMAC_TSR_RLES
                         | CIRC_CNT(pEmacd->wTxHead,
                                    pEmacd->wTxTail,
                                    pEmacd->wTxListSize)
                         ;
            pTxCb = &pEmacd->fTxCbList[pEmacd->wTxTail];
            EMACD_ResetTx(pEmacd);
            TRACE_INFO("Tx RLE!!\n\r");
            EMAC_TransmitEnable(pHw, 1);
        }
        /* Check COL */
        if (tsr & EMAC_TSR_COL)
        {
            txStatusFlag |= EMAC_TSR_COL;
        }
        /* Check BEX */
        if (tsr & EMAC_TSR_BEX)
        {
            txStatusFlag |= EMAC_TSR_BEX;
        }
        /* Check UND */
        if (tsr & EMAC_TSR_UND)
        {
            txStatusFlag |= EMAC_TSR_UND;
        }
        /* Clear status */
        EMAC_ClearTxStatus(pHw, txStatusFlag);

        if (!CIRC_EMPTY(pEmacd->wTxHead, pEmacd->wTxTail))
        {
            // Check the buffers
            do {
                pTxTd = &pEmacd->pTxD[pEmacd->wTxTail];
                pTxCb = &pEmacd->fTxCbList[pEmacd->wTxTail];
                /* Any error?
                   Exit if buffer has not been sent yet */
                if ((pTxTd->status.val & EMAC_TXD_bmUSED) == 0)
                {
                    break;
                }

                /* Notify upper layer that a packet has been sent */
                if (*pTxCb)
                {
                    (*pTxCb)(txStatusFlag);
                }

                CIRC_INC( pEmacd->wTxTail, pEmacd->wTxListSize );
            } while (CIRC_CNT(pEmacd->wTxHead, pEmacd->wTxTail, pEmacd->wTxListSize));
        }
        
        if (tsr & EMAC_TSR_RLES)
        {
            /* Notify upper layer RLE */
            if (*pTxCb)
            {
                (*pTxCb)(txStatusFlag);
            }
        }
        
        /* If a wakeup has been scheduled, notify upper layer that it can  
           send other packets, send will be successfull. */
        if( (CIRC_SPACE(pEmacd->wTxHead,
                        pEmacd->wTxTail,
                        pEmacd->wTxListSize) >= pEmacd->bWakeupThreshold)
          && pEmacd->fWakupCb)
        {
            pEmacd->fWakupCb();
        }
    }

    /* PAUSE Frame */
    if (isr & EMAC_ISR_PFRE)
    {
        TRACE_INFO("Pause!\n\r");
    }
    if (isr & EMAC_ISR_PTZ)
    {
        TRACE_INFO("Pause TO!\n\r");
    }
}

/**
 * Initialize the EMAC Driver with HW settings.
 * \param pEmacd Pointer to EMAC Driver instance.
 * \param pHw    Pointer to HW address for registers.
 * \param bID    HW ID for power management.
 * \param bCAF   Enable/Disable CopyAllFrame.
 * \param bNBC   Enable/Disable NoBroadCast.
 */
void EMACD_Init(sEmacd *pEmacd,
                Emac *pHw, uint8_t bID,
                uint8_t bCAF, uint8_t bNBC )
{

    TRACE_DEBUG("EMACD_Init\n\r");

    /* Initialize struct */
    pEmacd->pHw = pHw;
    pEmacd->bId = bID;

    /* Power ON */
    PMC_EnablePeripheral(bID);

    /* Disable TX & RX and more */
    EMAC_NetworkControl(pHw, 0);
    EMAC_DisableIt(pHw, ~0u);

    EMAC_ClearStatistics(pHw);

    /* Clear all status bits in the receive status register. */
    EMAC_ClearRxStatus(pHw, EMAC_RSR_OVR | EMAC_RSR_REC | EMAC_RSR_BNA);

    /* Clear all status bits in the transmit status register */
    EMAC_ClearTxStatus(pHw, EMAC_TSR_UBR | EMAC_TSR_COL | EMAC_TSR_RLES
                            | EMAC_TSR_BEX | EMAC_TSR_COMP | EMAC_TSR_UND);

    /* Clear interrupts */
    EMAC_GetItStatus(pHw);

    /* Enable the copy of data into the buffers
       ignore broadcasts, and don't copy FCS. */
    EMAC_Configure(pHw, EMAC_GetConfigure(pHw) | EMAC_NCFGR_DRFCS | EMAC_NCFGR_PAE);

    EMAC_CpyAllEnable(pHw, bCAF);
    EMAC_BroadcastDisable(pHw, bNBC);

}

/**
 * Initialize necessary allocated buffer lists for EMAC Driver to transfer data.
 * Must be invoked after EMACD_Init() but before RX/TX start.
 * \param pEmacd Pointer to EMAC Driver instance.
 * \param pRxBuffer Pointer to allocated buffer for RX. The address should
 *                  be 8-byte aligned and the size should be
 *                  EMAC_RX_UNITSIZE * wRxSize.
 * \param pRxD      Pointer to allocated RX descriptor list.
 * \param wRxSize   RX size, in number of registered units (RX descriptors).
 * \param pTxBuffer Pointer to allocated buffer for TX. The address should
 *                  be 8-byte aligned and the size should be
 *                  EMAC_TX_UNITSIZE * wTxSize.
 * \param pTxD      Pointer to allocated TX descriptor list.
 * \param pTxCb     Pointer to allocated TX callback list.
 * \param wTxSize   TX size, in number of registered units (TX descriptors).
 * \return EMACD_OK or EMACD_PARAM.
 * \note If input address is not 8-byte aligned the address is automatically
 *       adjusted and the list size is reduced by one.
 */
extern uint8_t EMACD_InitTransfer( sEmacd *pEmacd,
    uint8_t *pRxBuffer, sEmacRxDescriptor *pRxD,
    uint16_t wRxSize,
    uint8_t *pTxBuffer, sEmacTxDescriptor *pTxD, fEmacdTransferCallback *pTxCb,
    uint16_t wTxSize)
{
    Emac *pHw = pEmacd->pHw;

    if (wRxSize <= 1 || wTxSize <= 1 || pTxCb == NULL) return EMACD_PARAM;

    /* Assign RX buffers */
    if (   ((uint32_t)pRxBuffer & 0x7)
        || ((uint32_t)pRxD      & 0x7) )
    {
        wRxSize --;
        TRACE_DEBUG("RX list address adjusted\n\r");
    }
    pEmacd->pRxBuffer = (uint8_t*)((uint32_t)pRxBuffer & 0xFFFFFFF8);
    pEmacd->pRxD = (sEmacRxDescriptor*)((uint32_t)pRxD & 0xFFFFFFF8);
    pEmacd->wRxListSize = wRxSize;

    /* Assign TX buffers */
    if (   ((uint32_t)pTxBuffer & 0x7)
        || ((uint32_t)pTxD      & 0x7) )
    {
        wTxSize --;
        TRACE_DEBUG("TX list address adjusted\n\r");
    }
    pEmacd->pTxBuffer = (uint8_t*)((uint32_t)pTxBuffer & 0xFFFFFFF8);
    pEmacd->pTxD = (sEmacTxDescriptor*)((uint32_t)pTxD & 0xFFFFFFF8);
    pEmacd->wTxListSize = wTxSize;
    pEmacd->fTxCbList = pTxCb;

    /* Reset TX & RX */
    EMACD_ResetRx(pEmacd);
    EMACD_ResetTx(pEmacd);

    /* Enable Rx and Tx, plus the stats register. */
    EMAC_TransmitEnable(pHw, 1);
    EMAC_ReceiveEnable(pHw, 1);
    EMAC_StatisticsWriteEnable(pHw, 1);

    /* Setup the interrupts for TX (and errors) */
    EMAC_EnableIt(pHw,    EMAC_IER_RXUBR
                        | EMAC_IER_TUND
                        | EMAC_IER_RLE
                        | EMAC_IER_TXERR
                        | EMAC_IER_TCOMP
                        | EMAC_IER_ROVR
                        | EMAC_IER_HRESP
                        | EMAC_IER_PFR
                        | EMAC_IER_PTZ);
    return EMACD_OK;
}

/**
 * Reset TX & RX queue & statistics
 * \param pEmacd Pointer to EMAC Driver instance.
 */
void EMACD_Reset(sEmacd *pEmacd)
{
    Emac *pHw = pEmacd->pHw;

    EMACD_ResetRx(pEmacd);
    EMACD_ResetTx(pEmacd);
    EMAC_NetworkControl(pHw, EMAC_NCR_TE | EMAC_NCR_RE
                             | EMAC_NCR_WESTAT | EMAC_NCR_CLRSTAT);
}

/**
 *  Send a packet with EMAC.
 *  If the packet size is larger than transfer buffer size error returned.
 *  If packet transfer status is monitored, specify callback for each packet.
 *  \param pEmacd   Pointer to EMAC Driver instance.
 *  \param buffer   The buffer to be send
 *  \param size     The size of buffer to be send
 *  \param fTxCb    TX callback.
 *  \return         EMACD_OK, EMACD_PARAM or EMACD_TX_BUSY.
 */
uint8_t EMACD_Send( sEmacd *pEmacd,
                    void *pBuffer,
                    uint32_t size,
                    fEmacdTransferCallback fTxCb )
{
    Emac *pHw = pEmacd->pHw;

    volatile sEmacTxDescriptor      *pTxTd;
    volatile fEmacdTransferCallback *pfTxCb;

    TRACE_DEBUG("EMAC_Send\n\r");

    /* Check parameter */
    if (size > EMAC_TX_UNITSIZE) {
        TRACE_ERROR("EMAC driver does not split send packets.");
        TRACE_ERROR("%d bytes max in one packet (%u bytes requested)\n\r",
            EMAC_TX_UNITSIZE, (unsigned int)size);
        return EMACD_PARAM;
    }

    /* Pointers to the current TxTd */
    pTxTd = &pEmacd->pTxD[pEmacd->wTxHead];
    /* If no free TxTd, buffer can't be sent, schedule the wakeup callback */
    if( CIRC_SPACE(pEmacd->wTxHead, pEmacd->wTxTail, pEmacd->wTxListSize) == 0)
    {
        //if ((pTxTd->status & EMAC_TXD_bmUSED) != 0)
        {
            //EMAC_ResetTx();
            //TRACE_WARNING("Circ Full but FREE TD found\n\r");
            //AT91C_BASE_EMAC->EMAC_NCR |= AT91C_EMAC_TE;
        }
        //else
        {
            return EMACD_TX_BUSY;
        }
    }

    /* Pointers to the current Tx Callback */
    pfTxCb = &pEmacd->fTxCbList[pEmacd->wTxHead];
    /* Setup/Copy data to transmition buffer */
    if (pBuffer && size)
    {
        /* Driver manage the ring buffer */
        memcpy((void *)pTxTd->addr, pBuffer, size);
    }

    /* Tx Callback */
    *pfTxCb = fTxCb;
    /* Update TD status */

    /* The buffer size defined is length of ethernet frame
       so it's always the last buffer of the frame. */
    if (pEmacd->wTxHead == pEmacd->wTxListSize-1)
    {
        pTxTd->status.val = 
            (size & EMAC_TXD_LEN_MASK) | EMAC_TXD_bmLAST | EMAC_TXD_bmWRAP;
    }
    else
    {
        pTxTd->status.val = (size & EMAC_TXD_LEN_MASK) | EMAC_TXD_bmLAST;
    }
    
    CIRC_INC(pEmacd->wTxHead, pEmacd->wTxListSize);
    /* Now start to transmit if it is not already done */
    EMAC_TransmissionStart(pHw);
    return EMACD_OK;
}

/**
 * Return current load of TX.
 * \param pEmacd   Pointer to EMAC Driver instance.
 */
uint32_t EMACD_TxLoad(sEmacd *pEmacd)
{
    uint16_t head = pEmacd->wTxHead;
    uint16_t tail = pEmacd->wTxTail;
    return CIRC_CNT(head, tail, pEmacd->wTxListSize);
}

/**
 *  Receive a packet with EMAC
 *  If not enough buffer for the packet, the remaining data is lost but right
 *  frame length is returned.
 *  \param pEmacd   Pointer to EMAC Driver instance.
 *  \param pFrame           Buffer to store the frame
 *  \param frameSize        Size of the frame
 *  \param pRcvSize         Received size
 *  \return                 OK, no data, or frame too small
 */
uint8_t EMACD_Poll( sEmacd * pEmacd,
                    uint8_t *pFrame,
                    uint32_t frameSize,
                    uint32_t *pRcvSize)
{
    uint16_t bufferLength;
    uint32_t tmpFrameSize=0;
    uint8_t  *pTmpFrame=0;
    uint32_t tmpIdx = pEmacd->wRxI;
    volatile sEmacRxDescriptor *pRxTd = &pEmacd->pRxD[pEmacd->wRxI];
    char isFrame = 0;

    if (pFrame == NULL) return EMACD_PARAM;

    /* Set the default return value */
    *pRcvSize = 0;

    /* Process received RxTd */
    while ((pRxTd->addr.val & EMAC_RXD_bmOWNERSHIP) == EMAC_RXD_bmOWNERSHIP)
    {
        /* A start of frame has been received, discard previous fragments */
        if ((pRxTd->status.val & EMAC_RXD_bmSOF) == EMAC_RXD_bmSOF)
        {
            /* Skip previous fragment */
            while (tmpIdx != pEmacd->wRxI)
            {
                pRxTd = &pEmacd->pRxD[pEmacd->wRxI];
                pRxTd->addr.val &= ~(EMAC_RXD_bmOWNERSHIP);
                CIRC_INC(pEmacd->wRxI, pEmacd->wRxListSize);
            }
            /* Reset the temporary frame pointer */
            pTmpFrame = pFrame;
            tmpFrameSize = 0;
            /* Start to gather buffers in a frame */
            isFrame = 1;
        }

        /* Increment the pointer */
        CIRC_INC(tmpIdx, pEmacd->wRxListSize);
        asm("nop");
        /* Copy data in the frame buffer */
        if (isFrame)
        {
            if (tmpIdx == pEmacd->wRxI)
            {
                TRACE_INFO("no EOF (Invalid of buffers too small)\n\r");
                do
                {

                    pRxTd = &pEmacd->pRxD[pEmacd->wRxI];
                    pRxTd->addr.val &= ~(EMAC_RXD_bmOWNERSHIP);
                    CIRC_INC(pEmacd->wRxI, pEmacd->wRxListSize);
                } while(tmpIdx != pEmacd->wRxI);
                return EMACD_RX_NULL;
            }
            /* Copy the buffer into the application frame */
            bufferLength = EMAC_RX_UNITSIZE;
            if ((tmpFrameSize + bufferLength) > frameSize)
            {
                bufferLength = frameSize - tmpFrameSize;
            }

            memcpy(pTmpFrame, (void*)(pRxTd->addr.val & EMAC_RXD_ADDR_MASK), bufferLength);
            pTmpFrame += bufferLength;
            tmpFrameSize += bufferLength;
            
            /* An end of frame has been received, return the data */
            if ((pRxTd->status.val & EMAC_RXD_bmEOF) == EMAC_RXD_bmEOF)
            {

                /* Frame size from the EMAC */
                *pRcvSize = (pRxTd->status.val & EMAC_RXD_LEN_MASK);
                
                TRACE_INFO("packet %d-%d (%d)\n\r", pEmacd->wRxI, tmpIdx, *pRcvSize);
                /* All data have been copied in the application frame buffer => release TD */
                while (pEmacd->wRxI != tmpIdx)
                {
                    pRxTd = &pEmacd->pRxD[pEmacd->wRxI];
                    pRxTd->addr.val &= ~(EMAC_RXD_bmOWNERSHIP);
                    CIRC_INC(pEmacd->wRxI, pEmacd->wRxListSize);
                }

                /* Application frame buffer is too small all data have not been copied */
                if (tmpFrameSize < *pRcvSize)
                {
                    TRACE_INFO("size req %u size allocated %u\n\r", (unsigned int)(*pRcvSize), (unsigned int)frameSize);

                    return EMACD_SIZE_TOO_SMALL;
                }

                return EMACD_OK;
            }
        }
        /* SOF has not been detected, skip the fragment */
        else
        {
           pRxTd->addr.val &= ~(EMAC_RXD_bmOWNERSHIP);
           pEmacd->wRxI = tmpIdx;
        }
       
        /* Process the next buffer */
        pRxTd = &pEmacd->pRxD[tmpIdx];
    }
    return EMACD_RX_NULL;
}

/**
 * Register/Clear RX callback. Callback will be invoked after the next received
 * frame.
 *
 * When EMACD_Poll() returns EMACD_RX_NULL the application task call
 * EMACD_SetRxCallback() to register fRxCb() callback and enters suspend state.
 * The callback is in charge to resume the task once a new frame has been
 * received. The next time EMACD_Poll() is called, it will be successfull.
 *
 * This function is usually invoked from the RX callback itself with NULL
 * callback, to unregister. Once the callback has resumed the application task,
 * there is no need to invoke the callback again.
 *
 * \param pEmacd   Pointer to EMAC Driver instance.
 * \param fRxCb    RX callback.
 */
void EMACD_SetRxCallback(sEmacd * pEmacd, fEmacdTransferCallback fRxCb)
{
    Emac *pHw = pEmacd->pHw;

    if (fRxCb == NULL)
    {
        EMAC_DisableIt(pHw, EMAC_IDR_RCOMP);
        pEmacd->fRxCb = NULL;
    }
    else
    {
        pEmacd->fRxCb = fRxCb;
        EMAC_EnableIt(pHw, EMAC_IER_RCOMP);
    }
}

/**
 * Register/Clear TX wakeup callback.
 *
 * When EMACD_Send() returns EMACD_TX_BUSY (all TD busy) the application 
 * task calls EMACD_SetTxWakeupCallback() to register fWakeup() callback and 
 * enters suspend state. The callback is in charge to resume the task once 
 * several TD have been released. The next time EMACD_Send() will be called,
 * it shall be successfull.
 *
 * This function is usually invoked with NULL callback from the TX wakeup
 * callback itself, to unregister. Once the callback has resumed the
 * application task, there is no need to invoke the callback again.
 *
 * \param pEmacd   Pointer to EMAC Driver instance.
 * \param fWakeup     Wakeup callback.
 * \param bThreshould Number of free TD before wakeup callback invoked.
 * \return EMACD_OK, EMACD_PARAM on parameter error.
 */
uint8_t EMACD_SetTxWakeupCallback(sEmacd * pEmacd,
                                  fEmacdWakeupCallback fWakeup,
                                  uint8_t bThreshold)
{
    if (fWakeup == NULL)
    {
        pEmacd->fWakupCb = NULL;
    }
    else
    {
        if (bThreshold <= pEmacd->wTxListSize)
        {
            pEmacd->fWakupCb = fWakeup;
            pEmacd->bWakeupThreshold = bThreshold;
        }
        else
        {
            return EMACD_PARAM;
        }
    }

    return EMACD_OK;
}
