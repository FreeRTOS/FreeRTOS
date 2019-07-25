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

#include "chip.h"
#include <string.h>

/** \addtogroup gmacd_defines
	@{*/

/*----------------------------------------------------------------------------
 *        Macro
 *----------------------------------------------------------------------------*/
#define GMAC_CACHE 
#if defined GMAC_CACHE 
	 #define GMAC_CACHE_COHERENCE {SCB_CleanInvalidateDCache();}
#else 
	 #define GMAC_CACHE_COHERENCE {}
#endif     

/** ISO/IEC 14882:2003(E) - 5.6 Multiplicative operators:
 * The binary / operator yields the quotient, and the binary % operator yields 
 * the remainder from the division of the first expression by the second. 
 * If the second operand of / or % is zero the behaviour is undefined; otherwise
 *  (a/b)*b + a%b is equal to a.
 * If both operands are non-negative then the remainder is non-negative;
 * if not, the sign of the remainder is implementation-defined 74).
 */
__STATIC_INLINE int fixed_mod(int a, int b)
{
	int rem = a % b;
	while (rem < 0)
		rem += b;

	return rem;
}

/** Return count in buffer */
#define GCIRC_CNT(head,tail,size)  fixed_mod((head) - (tail), (size))

/** Return space available, 0..size-1. always leave one free char as a 
	completely full buffer has head == tail, which is the same as empty */
#define GCIRC_SPACE(head,tail,size) GCIRC_CNT((tail),((head)+1),(size))

/** Return count up to the end of the buffer. Carefully avoid accessing head 
	and tail more than once, so they can change underneath us without returning 
	inconsistent results */
#define GCIRC_CNT_TO_END(head,tail,size) \
	 ({int end = (size) - (tail); \
	 int n = fixed_mod((head) + end, (size));    \
	 n < end ? n : end;})

/** Return space available up to the end of the buffer */
#define GCIRC_SPACE_TO_END(head,tail,size) \
   ({int end = (size) - 1 - (head); \
	 int n = fixed_mod(end + (tail), (size));    \
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

/* This variable holds the write index into gPtpMsgTxQue */
uint8_t ptpTxQueWriteIdx = 0u;
uint8_t ptpTxQueReadIdx = 0u;

/* This queue holds the transmit event messages */
ptpMsgType gPtpMsgTxQue[EFRS_BUFFER_LEN];
uint16_t gPtpMsgTxSeqId[EFRS_BUFFER_LEN];
   


const uint32_t isrMasks[] = { GMAC_IMR_SFT, GMAC_IMR_DRQFT, 
							GMAC_IMR_PDRQFT , GMAC_IMR_PDRSFT };

/*---------------------------------------------------------------------------
 *         Local functions
 *---------------------------------------------------------------------------*/

/**
 *  \brief Disable TX & reset registers and descriptor list
 *  \param pDrv Pointer to GMAC Driver instance.
 */
static void GMACD_ResetTx(sGmacd *pDrv, gmacQueList_t queIdx)
{
	Gmac *pHw = pDrv->pHw;
	uint8_t *pTxBuffer = pDrv->queueList[queIdx].pTxBuffer;
	sGmacTxDescriptor *pTd = pDrv->queueList[queIdx].pTxD;
	uint32_t Index;
	uint32_t Address;

	/* Disable TX */
	GMAC_TransmitEnable(pHw, 0);
	
	/* Setup the TX descriptors. */
	GCIRC_CLEAR(pDrv->queueList[queIdx].wTxHead, pDrv->queueList[queIdx].wTxTail);
	for(Index = 0; Index < pDrv->queueList[queIdx].wTxListSize; Index++) {
		Address = (uint32_t)(&(pTxBuffer[Index * 
					pDrv->queueList[queIdx].wTxBufferSize]));
		pTd[Index].addr = Address;
		pTd[Index].status.val = (uint32_t)GMAC_TX_USED_BIT;
	}
	
	pTd[pDrv->queueList[queIdx].wTxListSize - 1].status.val =
					GMAC_TX_USED_BIT | GMAC_TX_WRAP_BIT; 
	
	/* Transmit Buffer Queue Pointer Register */
	  
	GMAC_SetTxQueue(pHw, (uint32_t)pTd, queIdx);
}
	
/**
 *  \brief Disable RX & reset registers and descriptor list
 *  \param pDrv Pointer to GMAC Driver instance. 
 */
static void GMACD_ResetRx(sGmacd *pDrv, gmacQueList_t queIdx )
{
	Gmac    *pHw = pDrv->pHw;
	uint8_t *pRxBuffer = pDrv->queueList[queIdx].pRxBuffer;
	sGmacRxDescriptor *pRd = pDrv->queueList[queIdx].pRxD;

	uint32_t Index;
	uint32_t Address;

	/* Disable RX */
	GMAC_ReceiveEnable(pHw, 0);

	/* Setup the RX descriptors. */
	pDrv->queueList[queIdx].wRxI = 0;
	for(Index = 0; Index < pDrv->queueList[queIdx].wRxListSize; Index++) {
		Address = (uint32_t)(&(pRxBuffer[Index * 
				pDrv->queueList[queIdx].wRxBufferSize]));
		/* Remove GMAC_RXD_bmOWNERSHIP and GMAC_RXD_bmWRAP */
		pRd[Index].addr.val = Address & GMAC_ADDRESS_MASK;
		pRd[Index].status.val = 0;
	}
	
	pRd[pDrv->queueList[queIdx].wRxListSize - 1].addr.val |= GMAC_RX_WRAP_BIT;
	
	/* Receive Buffer Queue Pointer Register */ 
	GMAC_SetRxQueue(pHw, (uint32_t)pRd, queIdx);
}


/**
 *  \brief Process successfully sent packets
 *  \param pGmacd Pointer to GMAC Driver instance.
 */
static void GMACD_TxCompleteHandler(sGmacd *pGmacd, gmacQueList_t qId)
{
	Gmac                   *pHw = pGmacd->pHw;
	sGmacTxDescriptor      *pTxTd;
	fGmacdTransferCallback fTxCb;
	uint32_t               tsr;

	/* Clear status */
	tsr = GMAC_GetTxStatus(pHw);
	GMAC_ClearTxStatus(pHw, tsr);

	while (!GCIRC_EMPTY(
			pGmacd->queueList[qId].wTxHead, pGmacd->queueList[qId].wTxTail)) {
		pTxTd = &pGmacd->queueList[qId].pTxD[pGmacd->queueList[qId].wTxTail];

		/* Make hw descriptor updates visible to CPU */
		GMAC_CACHE_COHERENCE

		/* Exit if frame has not been sent yet:
		 * On TX completion, the GMAC set the USED bit only into the
		 * very first buffer descriptor of the sent frame.
		 * Otherwise it updates this descriptor with status error bits.
		 * This is the descriptor write back.
		 */
		if ((pTxTd->status.val & GMAC_TX_USED_BIT) == 0)
			break;

		/* Process all buffers of the current transmitted frame */
		while ((pTxTd->status.val & GMAC_TX_LAST_BUFFER_BIT) == 0) {
			GCIRC_INC(pGmacd->queueList[qId].wTxTail, 
					pGmacd->queueList[qId].wTxListSize);
			pTxTd = &pGmacd->queueList[qId].pTxD[pGmacd->queueList[qId].wTxTail];
			memory_sync();
		}

		/* Notify upper layer that a frame has been sent */
		fTxCb = pGmacd->queueList[qId].fTxCbList[pGmacd->queueList[qId].wTxTail];
		if (fTxCb)
			fTxCb(tsr);

		/* Go to next frame */
		GCIRC_INC(pGmacd->queueList[qId].wTxTail, pGmacd->queueList[qId].wTxListSize);
	}

	/* If a wakeup has been scheduled, notify upper layer that it can
	   send other packets, send will be successful. */
	if (pGmacd->queueList[qId].fWakupCb &&
		GCIRC_SPACE(pGmacd->queueList[qId].wTxHead,
					pGmacd->queueList[qId].wTxTail,
					pGmacd->queueList[qId].wTxListSize) >= 
						pGmacd->queueList[qId].bWakeupThreshold)
		pGmacd->queueList[qId].fWakupCb();
}


/**
 *  \brief Reset TX queue when errors are detected
 *  \param pGmacd Pointer to GMAC Driver instance.
 */
static void GMACD_TxErrorHandler(sGmacd *pGmacd, gmacQueList_t qId)
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
	while (!GCIRC_EMPTY(pGmacd->queueList[qId].wTxHead, 
			pGmacd->queueList[qId].wTxTail)) {
		int tx_completed = 0;
		pTxTd = &pGmacd->queueList[qId].pTxD[pGmacd->queueList[qId].wTxTail];

		/* Make hw descriptor updates visible to CPU */
		GMAC_CACHE_COHERENCE
		/* Check USED bit on the very first buffer descriptor to validate
		 * TX completion.
		 */
		if (pTxTd->status.val & GMAC_TX_USED_BIT)
			tx_completed = 1;

		/* Go to the last buffer descriptor of the frame */
		while ((pTxTd->status.val & GMAC_TX_LAST_BUFFER_BIT) == 0) {
			GCIRC_INC(pGmacd->queueList[qId].wTxTail, 
					pGmacd->queueList[qId].wTxListSize);
			pTxTd = &pGmacd->queueList[qId].pTxD[pGmacd->queueList[qId].wTxTail];
			GMAC_CACHE_COHERENCE
		}

		/* Notify upper layer that a frame status */
		fTxCb = pGmacd->queueList[qId].fTxCbList[pGmacd->queueList[qId].wTxTail];
		if (fTxCb)
			fTxCb(tx_completed ? GMAC_TSR_TXCOMP : 0); 
		// TODO: which error to notify?

		/* Go to next frame */
		GCIRC_INC(pGmacd->queueList[qId].wTxTail, pGmacd->queueList[qId].wTxListSize);
	}    

	/* Reset TX queue */
	GMACD_ResetTx(pGmacd, qId);
	
	/* Clear status */
	tsr = GMAC_GetTxStatus(pHw);
	GMAC_ClearTxStatus(pHw, tsr);

	/* Now we are ready to start transmission again */
	GMAC_TransmitEnable(pHw, 1);
	if (pGmacd->queueList[qId].fWakupCb)
		pGmacd->queueList[qId].fWakupCb();
}

 
/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/


#ifndef PTP_1588_TX_DISABLE  

void GMACD_TxPtpEvtMsgCBRegister (sGmacd * pGmacd, 
		fGmacdTxPtpEvtCallBack pTxPtpEvtCb, gmacQueList_t queIdx)  
{  
  pGmacd->queueList[queIdx].fTxPtpEvtCb = pTxPtpEvtCb;
} 

#endif   /* #ifdef PTP_1588_TX_DISABLE */  
 
/**
 *  \brief GMAC Interrupt handler
 *  \param pGmacd Pointer to GMAC Driver instance.
 */
void GMACD_Handler(sGmacd *pGmacd, gmacQueList_t queIdx)
{
	Gmac *pHw = pGmacd->pHw;
	uint32_t isr;
	uint32_t rsr;
	
	/* Interrupt Status Register is cleared on read */
	while ( (isr = GMAC_GetItStatus(pHw, queIdx)) !=0) {
		/*  Sync Frame Received - PTP */
		if(0u != (isr & GMAC_ISR_SFR)) {
			rsr = GMAC_ISR_SFR;
			memory_barrier();
			/* Invoke callbacks */
			if (pGmacd->queueList[queIdx].fRxCb) {
				pGmacd->queueList[queIdx].fRxCb(rsr);
			} else {
			}
		} else {
		}
		
		/* Peer Delay Request Frame Received - PTP */
		if (0u != (isr & GMAC_ISR_PDRQFR) ) {
			rsr = GMAC_ISR_PDRQFR;
			memory_barrier();
			
			/* Invoke callbacks */
			if (pGmacd->queueList[queIdx].fRxCb) {
				pGmacd->queueList[queIdx].fRxCb(rsr);
			} else {
			}
		} else {
		}

		/* Peer Delay Response Frame Received - PTP */
		if (0u != (isr & GMAC_ISR_PDRSFR) ) {
			
			rsr = GMAC_ISR_PDRSFR;
			memory_barrier();
			
			/* Invoke callbacks */
			if (pGmacd->queueList[queIdx].fRxCb) {
				pGmacd->queueList[queIdx].fRxCb(rsr);
			} else {
			}
		} else {
		}
	
		if( 0u != (isr & GMAC_ISR_TSU)) {
			/* Invoke call back with flag set to TSU comparison interrupt */
			rsr = GMAC_ISR_TSU;
			memory_barrier();
		
			/* Invoke callbacks */
			if (pGmacd->queueList[queIdx].fRxCb) { 
				pGmacd->queueList[queIdx].fRxCb(rsr);
			} else {
			}
		} else {
		}
		
		/* RX packet */
		if (isr & GMAC_INT_RX_BITS) {
			/* Clear status */
			rsr = GMAC_GetRxStatus(pHw);
			GMAC_ClearRxStatus(pHw, rsr);

			/* Invoke callback */
			if (pGmacd->queueList[queIdx].fRxCb)
				pGmacd->queueList[queIdx].fRxCb(rsr);
			}

			/* TX error */
			if (isr & GMAC_INT_TX_ERR_BITS) {
				GMACD_TxErrorHandler(pGmacd, queIdx);
				break;
			}
	
#ifndef PTP_1588_TX_DISABLE
			/* Transmit of SYNC / PDELAY_REQ / PDELAY_RSP */    
			if(0u != (isr & isrMasks[gPtpMsgTxQue[ptpTxQueReadIdx]])) {
			/* Invoke callback */
			/*  Check if it is possible for multiple messages to be triggered 
			within a single isr. If so, a loop may be needed to validate the top
			of the queue with the actual interrupt that has been triggered */
/* while(0u != (isr & (GMAC_IMR_SFT | GMAC_IMR_PDRQFT | GMAC_IMR_PDRSFT))) { */
			if (pGmacd->queueList[queIdx].fTxPtpEvtCb) {
				switch (gPtpMsgTxQue[ptpTxQueReadIdx]) {
				case SYNC_MSG_TYPE:
					pGmacd->queueList[queIdx].fTxPtpEvtCb 
									(gPtpMsgTxQue[ptpTxQueReadIdx], 
									GMAC_GetTxEvtFrameSec(pHw), 
									GMAC_GetTxEvtFrameNsec(pHw), 
									gPtpMsgTxSeqId[ptpTxQueReadIdx]);
					isr &= GMAC_IMR_SFT;
					break;
				case PDELAY_REQ_TYPE:
					pGmacd->queueList[queIdx].fTxPtpEvtCb 
									(gPtpMsgTxQue[ptpTxQueReadIdx], 
									GMAC_GetTxPeerEvtFrameSec(pHw), 
									GMAC_GetTxPeerEvtFrameNsec(pHw), 
									gPtpMsgTxSeqId[ptpTxQueReadIdx]);
					isr &= GMAC_IMR_PDRQFT;
					break;
				case PDELAY_RESP_TYPE:
					pGmacd->queueList[queIdx].fTxPtpEvtCb 
									(gPtpMsgTxQue[ptpTxQueReadIdx], 
									GMAC_GetTxPeerEvtFrameSec(pHw), 
									GMAC_GetTxPeerEvtFrameNsec(pHw), 
									gPtpMsgTxSeqId[ptpTxQueReadIdx]);
					isr &= GMAC_IMR_PDRSFT;
					break;
				default:
					/* Only for Peer messages & sync messages */
					break;
				};
		} else {
		}

			ptpTxQueReadIdx++;
			ptpTxQueReadIdx &= (EFRS_BUFFER_LEN-1);
			
			} else { 
				/* if(0u != (isr & isrMasks[gPtpMsgTxQue[ptpTxQueReadIdx]])) */
			}
#endif /* #ifndef PTP_1588_TX_DISABLE */
		/* TX packet */
		if (isr & GMAC_IER_TCOMP)
			GMACD_TxCompleteHandler(pGmacd, queIdx);
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
//    assert(GRX_BUFFERS * GMAC_RX_UNITSIZE > GMAC_FRAME_LENTGH_MAX);

	TRACE_DEBUG("GMAC_Init\n\r");

	/* Initialize struct */
	pGmacd->pHw = pHw;
	pGmacd->bId = bID;

	/* Power ON */
	PMC_EnablePeripheral(bID);

	/* Disable TX & RX and more */
	GMAC_NetworkControl(pHw, 0);
	GMAC_DisableAllQueueIt(pHw, ~0u);
	
	GMAC_ClearStatistics(pHw);
	/* Clear all status bits in the receive status register. */
	GMAC_ClearRxStatus(pHw, GMAC_RSR_RXOVR | GMAC_RSR_REC 
					| GMAC_RSR_BNA |GMAC_RSR_HNO);

	/* Clear all status bits in the transmit status register */
	GMAC_ClearTxStatus(pHw, GMAC_TSR_UBR | GMAC_TSR_COL | GMAC_TSR_RLE
							| GMAC_TSR_TXGO | GMAC_TSR_TFC | GMAC_TSR_TXCOMP
							| GMAC_TSR_HRESP );

	/* Clear All interrupts */
	GMAC_GetItStatus(pHw, GMAC_QUE_0);
	GMAC_GetItStatus(pHw, GMAC_QUE_1);
	GMAC_GetItStatus(pHw, GMAC_QUE_2);

	/* Enable the copy of data into the buffers
	   ignore broadcasts, and don't copy FCS. */
	dwNcfgr = GMAC_NCFGR_FD | GMAC_NCFGR_DBW(0) | GMAC_NCFGR_CLK_MCK_64 |
			  GMAC_NCFGR_MAXFS | GMAC_NCFGR_PEN | GMAC_NCFGR_RFCS;
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
 * Replace the deprecated GMACD_InitTransfer().
 * \param pGmacd Pointer to GMAC Driver instance.
 * \param pInit  Pointer to sGmacInit.
 * \param pInit  Pointer to gmacQueList_t for different queue.
 * \return GMACD_OK or GMACD_PARAM.
 * \note If input address is not 8-byte aligned the address is automatically
 *       adjusted and the list size is reduced by one.
 */
uint8_t GMACD_InitTransfer(sGmacd *pGmacd, const sGmacInit *pInit, 
							gmacQueList_t queIdx)
{
	Gmac *pHw = pGmacd->pHw;
	uint8_t *pRxBuffer = pInit->pRxBuffer;
	sGmacRxDescriptor *pRxD = pInit->pRxD;
	uint16_t wRxBufferSize = pInit->wRxBufferSize;
	uint16_t wRxSize = pInit->wRxSize;
	uint8_t *pTxBuffer = pInit->pTxBuffer;
	sGmacTxDescriptor *pTxD = pInit->pTxD;
	uint16_t wTxBufferSize = pInit->wTxBufferSize;
	uint16_t wTxSize = pInit->wTxSize;
	fGmacdTransferCallback *pTxCb = pInit->pTxCb;
	uint32_t dwDmaCfg;
	if (wRxSize <= 1 || wTxSize <= 1 || pTxCb == NULL) return GMACD_PARAM;

	if (!wRxBufferSize || wRxBufferSize > 16*1024 || wRxBufferSize & 0x3f)
		return GMACD_PARAM;

	if (!wTxBufferSize)
		return GMACD_PARAM;

	if (pInit->bIsGem) {
		if(!queIdx) {
			dwDmaCfg = (GMAC_DCFGR_DRBS(wRxBufferSize >> 6) ) 
				| GMAC_DCFGR_RXBMS(3) | GMAC_DCFGR_TXPBMS;
			switch (pInit->bDmaBurstLength) {
			case 16:
				dwDmaCfg |= GMAC_DCFGR_FBLDO_INCR16;
				break;
			case 8:
				dwDmaCfg |= GMAC_DCFGR_FBLDO_INCR8;
				break;
			case 4:
				dwDmaCfg |= GMAC_DCFGR_FBLDO_INCR4;
				break;
			case 1:
				dwDmaCfg |= GMAC_DCFGR_FBLDO_SINGLE;
				break;
			default:
				return GMACD_PARAM;
				break;
			}
		} else {
			dwDmaCfg = (GMAC_RBSRPQ_RBS(wRxBufferSize >> 6) );
		}
		GMAC_SetDMAConfig(pHw, dwDmaCfg, queIdx);
	}

	pGmacd->queueList[queIdx].wRxBufferSize = wRxBufferSize;
	pGmacd->queueList[queIdx].wTxBufferSize = wTxBufferSize;
	/* Assign RX buffers */
	if (((uint32_t)pRxBuffer & 0x7)
		|| ((uint32_t)pRxD & 0x7) ) {
		wRxSize --;
		TRACE_DEBUG("RX list address adjusted\n\r");
	}
	pGmacd->queueList[queIdx].pRxBuffer = (uint8_t*)((uint32_t)pRxBuffer & 0xFFFFFFF8);
	pGmacd->queueList[queIdx].pRxD = (sGmacRxDescriptor*)((uint32_t)pRxD & 0xFFFFFFF8);
	pGmacd->queueList[queIdx].wRxListSize = wRxSize;

	/* Assign TX buffers */
	if (   ((uint32_t)pTxBuffer & 0x7)
		|| ((uint32_t)pTxD & 0x7) ) {
		wTxSize --;
		TRACE_DEBUG("TX list address adjusted\n\r");
	}
	pGmacd->queueList[queIdx].pTxBuffer = (uint8_t*)((uint32_t)pTxBuffer & 0xFFFFFFF8);
	pGmacd->queueList[queIdx].pTxD = (sGmacTxDescriptor*)((uint32_t)pTxD & 0xFFFFFFF8);
	pGmacd->queueList[queIdx].wTxListSize = wTxSize;
	pGmacd->queueList[queIdx].fTxCbList = pTxCb;

	/* Reset TX & RX */
	GMACD_ResetRx(pGmacd, queIdx);
	GMACD_ResetTx(pGmacd, queIdx);

   /* Setup the interrupts for RX/TX completion (and errors) */
	switch(queIdx) {
	case GMAC_QUE_0:
		/* YBP: Que 0 should be configured last so as to enable transmit and
		Receive in the NCR register */
		
		/* Enable Rx and Tx, plus the status register. */
		GMAC_TransmitEnable(pHw, 1);
		GMAC_ReceiveEnable(pHw, 1);
		GMAC_StatisticsWriteEnable(pHw, 1);

		GMAC_EnableIt(pHw,
				  GMAC_INT_RX_BITS |
				  GMAC_INT_TX_BITS |
				  GMAC_INT_TX_ERR_BITS, GMAC_QUE_0);
		break;
		
	case GMAC_QUE_1:
		GMAC_EnableIt(pHw,
				  GMAC_INT_RX_BITS |
				  GMAC_INT_TX_BITS |
				  GMAC_INT_TX_ERR_BITS, GMAC_QUE_1);
		break;
	case GMAC_QUE_2:
		  GMAC_EnableIt(pHw,
				  GMAC_INT_RX_BITS |
				  GMAC_INT_TX_BITS |
				  GMAC_INT_TX_ERR_BITS, GMAC_QUE_2);
		break;
	};
	return GMACD_OK;
}


/**
 * Reset TX & RX queue & statistics
 * \param pGmacd Pointer to GMAC Driver instance.
 */
void GMACD_Reset(sGmacd *pGmacd)
{
	Gmac *pHw = pGmacd->pHw;

	GMACD_ResetRx(pGmacd, GMAC_QUE_0);
	GMACD_ResetRx(pGmacd, GMAC_QUE_1);
	GMACD_ResetRx(pGmacd, GMAC_QUE_2);
	
	GMACD_ResetTx(pGmacd, GMAC_QUE_0);
	GMACD_ResetTx(pGmacd, GMAC_QUE_1);
	GMACD_ResetTx(pGmacd, GMAC_QUE_2);
	
	//memset((void*)&GmacStatistics, 0x00, sizeof(GmacStats));
	GMAC_NetworkControl(pHw, GMAC_NCR_TXEN | GMAC_NCR_RXEN
							 | GMAC_NCR_WESTAT | GMAC_NCR_CLRSTAT);
}

/**
 * \brief Send a frame split into buffers. If the frame size is larger than 
 * transfer buffer size error returned. If frame transfer status is monitored, 
 * specify callback for each frame.
 *  \param pGmacd Pointer to GMAC Driver instance. 
 *  \param sgl Pointer to a scatter-gather list describing the buffers of the 
 * ethernet frame.
 *  \param fTxCb Pointer to callback function.
 */
uint8_t GMACD_SendSG(sGmacd *pGmacd,
					 const sGmacSGList *sgl,
					 fGmacdTransferCallback fTxCb,
					 gmacQueList_t queIdx)
{
	Gmac *pHw = pGmacd->pHw;
	sGmacTxDescriptor *pTd = pGmacd->queueList[queIdx].pTxD;
	sGmacTxDescriptor *pTxTd;
	uint16_t wTxPos, wTxHead;
	int i;

	TRACE_DEBUG("%s\n\r", __FUNCTION__);

	/* Check parameter */
	if (!sgl->len) {
		TRACE_ERROR("%s:: ethernet frame is empty.\r\n", __FUNCTION__);
		return GMACD_PARAM;
	}
	if (sgl->len >= pGmacd->queueList[queIdx].wTxListSize) {
		TRACE_ERROR("%s: ethernet frame has too many buffers.\r\n", __FUNCTION__);
		return GMACD_PARAM;
	}
	/* Check available space */
	if (GCIRC_SPACE(pGmacd->queueList[queIdx].wTxHead, 
			pGmacd->queueList[queIdx].wTxTail,
			pGmacd->queueList[queIdx].wTxListSize) < (int)sgl->len)
		return GMACD_TX_BUSY;

	/* Tag end of TX queue */
	wTxHead = fixed_mod(pGmacd->queueList[queIdx].wTxHead + sgl->len, 
			pGmacd->queueList[queIdx].wTxListSize);
	wTxPos = wTxHead;
	pGmacd->queueList[queIdx].fTxCbList[wTxPos] = NULL;
	pTxTd = &pTd[wTxPos];
	pTxTd->status.val = GMAC_TX_USED_BIT;
	/* Update buffer descriptors in reverse order to avoid a race 
	 * condition with hardware.
	 */
	for (i = (int)(sgl->len-1); i >= 0; --i) {
		const sGmacSG *sg = &sgl->sg[i];
		uint32_t status;

		if (sg->size > pGmacd->queueList[queIdx].wTxBufferSize) {
			TRACE_ERROR("%s: buffer size is too big.\r\n", __FUNCTION__);
			return GMACD_PARAM;
		}

		if (wTxPos == 0)
			wTxPos = pGmacd->queueList[queIdx].wTxListSize-1;
		else
			wTxPos--;

		/* Reset TX callback */
		pGmacd->queueList[queIdx].fTxCbList[wTxPos] = NULL;

		pTxTd = &pTd[wTxPos];
#ifdef GMAC_ZERO_COPY
		/** Update buffer descriptor address word:
		 *  MUST be done before status word to avoid a race condition.
		 */
		pTxTd->addr = (uint32_t)sg->pBuffer;
		
#else
		/* Copy data into transmission buffer */
		if (sg->pBuffer && sg->size){
			memcpy((void *)pTxTd->addr, sg->pBuffer, sg->size); 
		 }
#endif
		GMAC_CACHE_COHERENCE

		/* Compute buffer descriptor status word */
		status = sg->size & GMAC_LENGTH_FRAME;
		if (i == (int)(sgl->len-1)) {
			status |= GMAC_TX_LAST_BUFFER_BIT;
			pGmacd->queueList[queIdx].fTxCbList[wTxPos] = fTxCb;
		}
		if (wTxPos == pGmacd->queueList[queIdx].wTxListSize-1)
			status |= GMAC_TX_WRAP_BIT;

		/* Update buffer descriptor status word: clear USED bit */
		pTxTd->status.val = status;

		/* Make newly initialized descriptor visible to hardware */
		GMAC_CACHE_COHERENCE
	}

	/* Update TX ring buffer pointers */
	pGmacd->queueList[queIdx].wTxHead = wTxHead;
	/* Now start to transmit if it is not already done */
	
	GMAC_TransmissionStart(pHw);
	return GMACD_OK;
}

/**
 * \brief Send a packet with GMAC. If the packet size is larger than transfer 
 * buffer size error returned. If packet transfer status is monitored, specify
 * callback for each packet.
 *  \param pGmacd Pointer to GMAC Driver instance. 
 *  \param pBuffer   The buffer to be send
 *  \param size     The size of buffer to be send
 *  \param fTxCb Threshold Wakeup callback
 *  \return         OK, Busy or invalid packet
 */
uint8_t GMACD_Send(sGmacd *pGmacd,
				   void *pBuffer,
				   uint32_t size,
				   fGmacdTransferCallback fTxCb,
				   gmacQueList_t queIdx)
{
	sGmacSGList sgl;
	sGmacSG sg;
	
	uint8_t *msgPtr;
	ptpMsgType ptpMsg;
	/* Init single entry scatter-gather list */
	sg.size = size;
	sg.pBuffer = pBuffer;
	sgl.len = 1;
	sgl.sg = &sg;


	
#ifndef PTP_1588_TX_DISABLE

	msgPtr = (uint8_t *)pBuffer;
	if(0x88u == msgPtr[12] && 0xf7u == msgPtr[13]) {
		/* Extract Tx PTP message  type */
		ptpMsg = (ptpMsgType)(msgPtr[14] & 0x0F);
		if (ptpMsg == SYNC_MSG_TYPE || ptpMsg == PDELAY_REQ_TYPE 
			|| ptpMsg == PDELAY_RESP_TYPE) {
			/* Only add message to Tx queue of msg types that have 
				tx event ISRs enabled. */
			gPtpMsgTxQue[ptpTxQueWriteIdx] = ptpMsg;
			
			/* Copy the Sequence Id */
			gPtpMsgTxSeqId[ptpTxQueWriteIdx] = 
				(uint16_t)(((uint16_t)msgPtr[44] << 8) | msgPtr[45]);
			ptpTxQueWriteIdx++;
			ptpTxQueWriteIdx &= (EFRS_BUFFER_LEN-1u);
		} else { 
				/* if (ptpMsg == SYNC_MSG_TYPE || ptpMsg == PDELAY_REQ_TYPE\
				|| ptpMsg == PDELAY_RESP_TYPE) { */
		}
	} else { /* if(0x88 == msgPtr[12] && 0xf7 == msgPtr[13]) { */
	}  
#endif /* #ifndef PTP_1588_TX_DISABLE */
	return GMACD_SendSG(pGmacd, &sgl, fTxCb, queIdx);
}

/**
 * Return current load of TX.
 * \param pGmacd   Pointer to GMAC Driver instance.
 */
uint32_t GMACD_TxLoad(sGmacd *pGmacd, gmacQueList_t queIdx)
{
	uint16_t head = pGmacd->queueList[queIdx].wTxHead;
	uint16_t tail = pGmacd->queueList[queIdx].wTxTail;
	return GCIRC_CNT(head, tail, pGmacd->queueList[queIdx].wTxListSize);
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
				  uint32_t *pRcvSize,
				  gmacQueList_t queIdx)
{

	uint16_t bufferLength;
	uint32_t   tmpFrameSize = 0;
	uint8_t  *pTmpFrame = 0;
	uint32_t   tmpIdx = pGmacd->queueList[queIdx].wRxI;
	volatile sGmacRxDescriptor *pRxTd = 
		&pGmacd->queueList[queIdx].pRxD[pGmacd->queueList[queIdx].wRxI]; 

	uint8_t isFrame = 0;
	
	if (pFrame == NULL) return GMACD_PARAM;

	/* Set the default return value */
	*pRcvSize = 0;
	
	/* Process received RxTd */
	while ((pRxTd->addr.val & GMAC_RX_OWNERSHIP_BIT) == GMAC_RX_OWNERSHIP_BIT) {
		/* A start of frame has been received, discard previous fragments */
		if ((pRxTd->status.val & GMAC_RX_SOF_BIT) == GMAC_RX_SOF_BIT) {
			/* Skip previous fragment */
			while (tmpIdx != pGmacd->queueList[queIdx].wRxI) {
				pRxTd = 
					&pGmacd->queueList[queIdx].pRxD[pGmacd->queueList[queIdx].wRxI]; 
				pRxTd->addr.val &= ~(GMAC_RX_OWNERSHIP_BIT);
				GCIRC_INC(pGmacd->queueList[queIdx].wRxI, 
					pGmacd->queueList[queIdx].wRxListSize);
			}
			pTmpFrame = pFrame;
			tmpFrameSize = 0;
			/* Start to gather buffers in a frame */
			isFrame = 1;
		}
		/* Increment the pointer */
		GCIRC_INC(tmpIdx, pGmacd->queueList[queIdx].wRxListSize);
		
		/* Copy data in the frame buffer */
		if (isFrame) {
			if (tmpIdx == pGmacd->queueList[queIdx].wRxI) {
				TRACE_INFO("no EOF (Invalid of buffers too small)\n\r");
				do {
					pRxTd = 
						&pGmacd->queueList[queIdx].pRxD[pGmacd->queueList[queIdx].wRxI]; 
					pRxTd->addr.val &= ~(GMAC_RX_OWNERSHIP_BIT);
					GCIRC_INC(pGmacd->queueList[queIdx].wRxI, 
						pGmacd->queueList[queIdx].wRxListSize);
				} while(tmpIdx != pGmacd->queueList[queIdx].wRxI);
				return GMACD_RX_NULL;
			}

			/* Copy the buffer into the application frame */
			bufferLength = pGmacd->queueList[queIdx].wRxBufferSize;
			if ((tmpFrameSize + bufferLength) > frameSize) {
				bufferLength = frameSize - tmpFrameSize;
			}
			memcpy(pTmpFrame, (void*)(pRxTd->addr.val & GMAC_ADDRESS_MASK),
				bufferLength);
			pTmpFrame += bufferLength;
			tmpFrameSize += bufferLength;

			/* An end of frame has been received, return the data */
			if ((pRxTd->status.val & GMAC_RX_EOF_BIT) == GMAC_RX_EOF_BIT)
			{
				/* Frame size from the GMAC */
				*pRcvSize = (pRxTd->status.val & GMAC_LENGTH_FRAME);

				/* Application frame buffer is too small all data have not been
					copied */
				if (tmpFrameSize < *pRcvSize) {
					return GMACD_SIZE_TOO_SMALL;
				}
				TRACE_DEBUG("packet %d-%d (%d)\n\r",
					pGmacd->queueList[queIdx].wRxI, tmpIdx, *pRcvSize);
				/* All data have been copied in the application frame buffer
					=> release TD */
				while (pGmacd->queueList[queIdx].wRxI != tmpIdx) {
					pRxTd = 
						&pGmacd->queueList[queIdx].pRxD[pGmacd->queueList[queIdx].wRxI]; 
					pRxTd->addr.val &= ~(GMAC_RX_OWNERSHIP_BIT);
					GCIRC_INC(pGmacd->queueList[queIdx].wRxI, 
						pGmacd->queueList[queIdx].wRxListSize);
				}
				
				GMAC_CACHE_COHERENCE
				return GMACD_OK;
			}
		} else {
			/* SOF has not been detected, skip the fragment */
			pRxTd->addr.val &= ~(GMAC_RX_OWNERSHIP_BIT);
			pGmacd->queueList[queIdx].wRxI = tmpIdx;
			GMAC_CACHE_COHERENCE
		}
		/* Process the next buffer */
		pRxTd = &pGmacd->queueList[queIdx].pRxD[tmpIdx];
		GMAC_CACHE_COHERENCE
	}
	return GMACD_RX_NULL;
}

/**
 * \brief Registers pRxCb callback. Callback will be invoked after the next 
 * received frame. When GMAC_Poll() returns GMAC_RX_NO_DATA the application task 
 * call GMAC_Set_RxCb() to register pRxCb() callback and enters suspend state. 
 * The callback is in charge to resume the task once a new frame has been 
 * received. The next time GMAC_Poll() is called, it will be successful.
 *  \param pGmacd Pointer to GMAC Driver instance. 
 *  \param fRxCb   Pointer to callback function
 *  \return        OK, no data, or frame too small
 */

void GMACD_SetRxCallback(sGmacd * pGmacd, fGmacdTransferCallback fRxCb,
						gmacQueList_t queIdx)
{
	Gmac *pHw = pGmacd->pHw;
	if (fRxCb == NULL) {
		GMAC_DisableIt(pHw, GMAC_IDR_RCOMP, queIdx);
		pGmacd->queueList[queIdx].fRxCb = NULL;
	} else {
		pGmacd->queueList[queIdx].fRxCb = fRxCb;
		GMAC_EnableIt(pHw, GMAC_IER_RCOMP, queIdx);
	}
}

/**
 * Register/Clear TX wakeup callback.
 *
 * When GMACD_Send() returns GMACD_TX_BUSY (all TD busy) the application 
 * task calls GMACD_SetTxWakeupCallback() to register fWakeup() callback and 
 * enters suspend state. The callback is in charge to resume the task once 
 * several TD have been released. The next time GMACD_Send() will be called,
 * it shall be successful.
 *
 * This function is usually invoked with NULL callback from the TX wakeup
 * callback itself, to unregister. Once the callback has resumed the
 * application task, there is no need to invoke the callback again.
 *
 * \param pGmacd   Pointer to GMAC Driver instance.
 * \param fWakeup     Wakeup callback.
 * \param bThreshold  Number of free TD before wakeup callback invoked.
 * \return GMACD_OK, GMACD_PARAM on parameter error.
 */
uint8_t GMACD_SetTxWakeupCallback(sGmacd * pGmacd,
								  fGmacdWakeupCallback fWakeup,
								  uint8_t bThreshold,
								  gmacQueList_t queIdx)
{
	if (fWakeup == NULL) {
		pGmacd->queueList[queIdx].fWakupCb = NULL;
	} else {
		if (bThreshold <= pGmacd->queueList[queIdx].wTxListSize) {
			pGmacd->queueList[queIdx].fWakupCb = fWakeup;
			pGmacd->queueList[queIdx].bWakeupThreshold = bThreshold;
		} else {
			return GMACD_PARAM;
		}
	}
	return GMACD_OK;
}
