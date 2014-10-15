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

/** Memory barriers */

#define rmb()   __ASM("dsb ")

#if defined ( __ICCARM__ )
    #define wmb()   __ASM("dsb #st")
#else
    #define wmb()   __ASM("dsb st")
#endif

/** ISO/IEC 14882:2003(E) - 5.6 Multiplicative operators:
 * The binary / operator yields the quotient, and the binary % operator yields the remainder 
 * from the division of the first expression by the second. 
 * If the second operand of / or % is zero the behavior is undefined; otherwise (a/b)*b + a%b is equal to a.
 * If both operands are nonnegative then the remainder is nonnegative;
 * if not, the sign of the remainder is implementation-defined 74).
 */
static inline int fixed_mod(int a, int b)
{
    int rem = a % b;
    while (rem < 0)
        rem += b;

    return rem;
}

/** Return count in buffer */
#define GCIRC_CNT(head,tail,size)  fixed_mod((head) - (tail), (size))

/** Return space available, 0..size-1. always leave one free char as a completely full buffer 
    has head == tail, which is the same as empty */
#define GCIRC_SPACE(head,tail,size) GCIRC_CNT((tail),((head)+1),(size))

/** Return count up to the end of the buffer. Carefully avoid accessing head and tail more than once,
    so they can change underneath us without returning inconsistent results */
#define GCIRC_CNT_TO_END(head,tail,size) \
     ({int end = (size) - (tail); \
     int n = fixed_mod((head) + end, (size));	\
     n < end ? n : end;})

/** Return space available up to the end of the buffer */
#define GCIRC_SPACE_TO_END(head,tail,size) \
   ({int end = (size) - 1 - (head); \
     int n = fixed_mod(end + (tail), (size));	\
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

// Interrupt bits
#define GMAC_INT_RX_BITS  \
    (GMAC_IER_RCOMP | GMAC_IER_RXUBR | GMAC_IER_ROVR)
#define GMAC_INT_TX_ERR_BITS  \
    (GMAC_IER_TUR | GMAC_IER_RLEX | GMAC_IER_TFC)
#define GMAC_INT_TX_BITS  \
    (GMAC_INT_TX_ERR_BITS | GMAC_IER_TCOMP)

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


/**
 *  \brief Process successfully sent packets
 *  \param pGmacd Pointer to GMAC Driver instance.
 */
static void GMACD_TxCompleteHandler(sGmacd *pGmacd)
{
    Gmac                   *pHw = pGmacd->pHw;
    sGmacTxDescriptor      *pTxTd;
    fGmacdTransferCallback fTxCb;
    uint32_t               tsr;

    /* Clear status */
    tsr = GMAC_GetTxStatus(pHw);
    GMAC_ClearTxStatus(pHw, tsr);

    while (!GCIRC_EMPTY(pGmacd->wTxHead, pGmacd->wTxTail)) {
        pTxTd = &pGmacd->pTxD[pGmacd->wTxTail];

        /* Make hw descriptor updates visible to CPU */
        rmb();

        /* Exit if frame has not been sent yet:
         * On TX completion, the GMAC set the USED bit only into the
         * very first buffer descriptor of the sent frame.
         * Otherwise it updates this descriptor with status error bits.
         * This is the descriptor writeback.
         */
        if ((pTxTd->status.val & GMAC_TX_USED_BIT) == 0)
            break;

        /* Process all buffers of the current transmitted frame */
        while ((pTxTd->status.val & GMAC_TX_LAST_BUFFER_BIT) == 0) {
            GCIRC_INC(pGmacd->wTxTail, pGmacd->wTxListSize);
            pTxTd = &pGmacd->pTxD[pGmacd->wTxTail];
            rmb();
        }

        /* Notify upper layer that a frame has been sent */
        fTxCb = pGmacd->fTxCbList[pGmacd->wTxTail];
        if (fTxCb)
            fTxCb(tsr);

        /* Go to next frame */
        GCIRC_INC(pGmacd->wTxTail, pGmacd->wTxListSize);
    }

    /* If a wakeup has been scheduled, notify upper layer that it can
       send other packets, send will be successfull. */
    if (pGmacd->fWakupCb &&
        GCIRC_SPACE(pGmacd->wTxHead,
                    pGmacd->wTxTail,
                    pGmacd->wTxListSize) >= pGmacd->bWakeupThreshold)
        pGmacd->fWakupCb();
}


/**
 *  \brief Reset TX queue when errors are detected
 *  \param pGmacd Pointer to GMAC Driver instance.
 */
static void GMACD_TxErrorHandler(sGmacd *pGmacd)
{
    Gmac                   *pHw = pGmacd->pHw;
    sGmacTxDescriptor      *pTxTd;
    fGmacdTransferCallback fTxCb;
    uint32_t               tsr;

    /* Clear TXEN bit into the Network Configuration Register:
     * this is a workaround to recover from TX lockups that 
     * occur on sama5d3 gmac (r1p24f2) when using  scatter-gather.
     * This issue has never been seen on sama5d4 gmac (r1p31).
     */
    GMAC_TransmitEnable(pHw, 0);

    /* The following step should be optional since this function is called 
     * directly by the IRQ handler. Indeed, according to Cadence 
     * documentation, the transmission is halted on errors such as
     * too many retries or transmit under run.
     * However it would become mandatory if the call of this function
     * were scheduled as a task by the IRQ handler (this is how Linux 
     * driver works). Then this function might compete with GMACD_Send().
     *
     * Setting bit 10, tx_halt, of the Network Control Register is not enough:
     * We should wait for bit 3, tx_go, of the Transmit Status Register to 
     * be cleared at transmit completion if a frame is being transmitted.
     */
    GMAC_TransmissionHalt(pHw);
    while (GMAC_GetTxStatus(pHw) & GMAC_TSR_TXGO);

    /* Treat frames in TX queue including the ones that caused the error. */
    while (!GCIRC_EMPTY(pGmacd->wTxHead, pGmacd->wTxTail)) {
        int tx_completed = 0;
        pTxTd = &pGmacd->pTxD[pGmacd->wTxTail];

        /* Make hw descriptor updates visible to CPU */
        rmb();

        /* Check USED bit on the very first buffer descriptor to validate
         * TX completion.
         */
        if (pTxTd->status.val & GMAC_TX_USED_BIT)
            tx_completed = 1;

        /* Go to the last buffer descriptor of the frame */
        while ((pTxTd->status.val & GMAC_TX_LAST_BUFFER_BIT) == 0) {
            GCIRC_INC(pGmacd->wTxTail, pGmacd->wTxListSize);
            pTxTd = &pGmacd->pTxD[pGmacd->wTxTail];
            rmb();
        }

        /* Notify upper layer that a frame status */
        fTxCb = pGmacd->fTxCbList[pGmacd->wTxTail];
        if (fTxCb)
            fTxCb(tx_completed ? GMAC_TSR_TXCOMP : 0); // TODO: which error to notify?

        /* Go to next frame */
        GCIRC_INC(pGmacd->wTxTail, pGmacd->wTxListSize);
    }    

    /* Reset TX queue */
    GMACD_ResetTx(pGmacd);

    /* Clear status */
    tsr = GMAC_GetTxStatus(pHw);
    GMAC_ClearTxStatus(pHw, tsr);

    /* Now we are ready to start transmission again */
    GMAC_TransmitEnable(pHw, 1);
    if (pGmacd->fWakupCb)
        pGmacd->fWakupCb();
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
    uint32_t isr;
    uint32_t rsr;

    /* Interrupt Status Register is cleared on read */
    while ((isr = GMAC_GetItStatus(pHw)) != 0) {
        /* RX packet */
        if (isr & GMAC_INT_RX_BITS) {
            /* Clear status */
            rsr = GMAC_GetRxStatus(pHw);
            GMAC_ClearRxStatus(pHw, rsr);

            /* Invoke callback */
            if (pGmacd->fRxCb)
                pGmacd->fRxCb(rsr);
        }

        /* TX error */
        if (isr & GMAC_INT_TX_ERR_BITS) {
            GMACD_TxErrorHandler(pGmacd);
            break;
        }

        /* TX packet */
        if (isr & GMAC_IER_TCOMP)
            GMACD_TxCompleteHandler(pGmacd);

        if (isr & GMAC_IER_HRESP) {
            TRACE_ERROR("HRESP\n\r");
        }
    }
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

    /* Setup the interrupts for RX/TX completion (and errors) */
    GMAC_EnableIt(pHw,
                  GMAC_INT_RX_BITS |
                  GMAC_INT_TX_BITS |
                  GMAC_IER_HRESP);

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
 * \brief Send a frame splitted into buffers. If the frame size is larger than transfer buffer size
 * error returned. If frame transfer status is monitored, specify callback for each frame.
 *  \param pGmacd Pointer to GMAC Driver instance. 
 *  \param sgl Pointer to a scatter-gather list describing the buffers of the ethernet frame.
 */
uint8_t GMACD_SendSG(sGmacd *pGmacd,
                     const sGmacSGList *sgl,
                     fGmacdTransferCallback fTxCb)
{
    Gmac *pHw = pGmacd->pHw;
    sGmacTxDescriptor *pTxTd;
    uint16_t wTxPos, wTxHead;
    int i;

    TRACE_DEBUG("GMACD_SendSG\n\r");

    /* Check parameter */
    if (!sgl->len) {
        TRACE_ERROR("GMACD_SendSG: ethernet frame is empty.\r\n");
        return GMACD_PARAM;
    }
    if (sgl->len >= pGmacd->wTxListSize) {
        TRACE_ERROR("GMACD_SendSG: ethernet frame has too many buffers.\r\n");
        return GMACD_PARAM;
    }

    /* Check available space */
    if (GCIRC_SPACE(pGmacd->wTxHead, pGmacd->wTxTail, pGmacd->wTxListSize) < (int)sgl->len)
        return GMACD_TX_BUSY;

    /* Tag end of TX queue */
    wTxHead = fixed_mod(pGmacd->wTxHead + sgl->len, pGmacd->wTxListSize);
    wTxPos = wTxHead;
    pGmacd->fTxCbList[wTxPos] = NULL;
    pTxTd = &pGmacd->pTxD[wTxPos];
    pTxTd->status.val = GMAC_TX_USED_BIT;

    /* Update buffer descriptors in reverse order to avoid a race 
     * condition with hardware.
     */
    for (i = (int)(sgl->len-1); i >= 0; --i) {
        const sGmacSG *sg = &sgl->sg[i];
        uint32_t status;

        if (sg->size > GMAC_TX_UNITSIZE) {
            TRACE_ERROR("GMACD_SendSG: buffer size is too big.\r\n");
            return GMACD_PARAM;
        }

        if (wTxPos == 0)
            wTxPos = pGmacd->wTxListSize-1;
        else
            wTxPos--;

        /* Reset TX callback */
        pGmacd->fTxCbList[wTxPos] = NULL;

        pTxTd = &pGmacd->pTxD[wTxPos];
#ifdef GMAC_ZERO_COPY
        /** Update buffer descriptor address word:
         *  MUST be done before status word to avoid a race condition.
         */
        pTxTd->addr = (uint32_t)sg->pBuffer;
        wmb();
#else
        /* Copy data into transmittion buffer */
        if (sg->pBuffer && sg->size)
            memcpy((void *)pTxTd->addr, sg->pBuffer, sg->size);
#endif

        /* Compute buffer descriptor status word */
        status = sg->size & GMAC_LENGTH_FRAME;
        if (i == (int)(sgl->len-1)) {
            status |= GMAC_TX_LAST_BUFFER_BIT;
            pGmacd->fTxCbList[wTxPos] = fTxCb;
        }
        if (wTxPos == pGmacd->wTxListSize-1)
            status |= GMAC_TX_WRAP_BIT;

        /* Update buffer descriptor status word: clear USED bit */
        pTxTd->status.val = status;

        /* Make newly initialized descriptor visible to hardware */
        wmb();
    }

    /* Update TX ring buffer pointers */
    pGmacd->wTxHead = wTxHead;

    /* Now start to transmit if it is not already done */
    GMAC_TransmissionStart(pHw);

    return GMACD_OK;
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
                   fGmacdTransferCallback fTxCb)
{
    sGmacSGList sgl;
    sGmacSG sg;

    /* Init single entry scatter-gather list */
    sg.size = size;
    sg.pBuffer = pBuffer;
    sgl.len = 1;
    sgl.sg = &sg;

    return GMACD_SendSG(pGmacd, &sgl, fTxCb);
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
