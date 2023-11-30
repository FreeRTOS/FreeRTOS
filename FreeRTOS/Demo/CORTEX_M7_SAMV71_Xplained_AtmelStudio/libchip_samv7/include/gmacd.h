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

/** \addtogroup gmacd_module
 * @{
 * Implement GMAC data transfer and PHY management functions.
 *
 * \section Usage
 * -# Implement GMAC interrupt handler, which must invoke GMACD_Handler()
 *    to handle GMAC interrupt events.
 * -# Implement sGmacd instance in application.
 * -# Initialize the instance with GMACD_Init() and GMACD_InitTransfer(),
 *    so that GMAC data can be transmitted/received.
 * -# Some management callbacks can be set by GMACD_SetRxCallback()
 *    and GMACD_SetTxWakeupCallback().
 * -# Send ethernet packets using GMACD_Send(), GMACD_TxLoad() is used
 *    to check the free space in TX queue.
 * -# Check and obtain received ethernet packets via GMACD_Poll().
 *
 * \sa \ref gmacb_module, \ref gmac_module
 *
 * Related files:\n
 * \ref gmacd.c\n
 * \ref gmacd.h.\n
 *
 *  \defgroup gmacd_defines GMAC Driver Defines
 *  \defgroup gmacd_types GMAC Driver Types
 *  \defgroup gmacd_functions GMAC Driver Functions
 */
/**@}*/

#ifndef _GMACD_H_
#define _GMACD_H_

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include "chip.h"


/*---------------------------------------------------------------------------
 *         Definitions
 *---------------------------------------------------------------------------*/
/** \addtogroup gmacd_defines
	@{*/


/** \addtogroup gmacd_rc GMACD Return Codes
		@{*/
#define GMACD_OK                0   /**< Operation OK */
#define GMACD_TX_BUSY           1   /**< TX in progress */
#define GMACD_RX_NULL           1   /**< No data received */
/** Buffer size not enough */
#define GMACD_SIZE_TOO_SMALL    2
/** Parameter error, TX packet invalid or RX size too small */
#define GMACD_PARAM             3
/** Transfer is not initialized */
#define GMACD_NOT_INITIALIZED   4
/**     @}*/

/** @}*/

/* Should be a power of 2. 
   - Buffer Length to store the timestamps of 1588 event messages 
*/
#define EFRS_BUFFER_LEN	(1u)

/*---------------------------------------------------------------------------
*             Types
*---------------------------------------------------------------------------*/ 
/** \addtogroup gmacd_types
	@{*/

typedef enum ptpMsgType_t  
{
	SYNC_MSG_TYPE = 0,
	DELAY_REQ_MSG_TYPE = 1,
	PDELAY_REQ_TYPE = 2,
	PDELAY_RESP_TYPE = 3,
	FOLLOW_UP_MSG_TYPE = 8,
	DELAY_RESP_MSG_TYPE = 9
}ptpMsgType; 
	


/** RX callback */
typedef void (*fGmacdTransferCallback)(uint32_t status);
/** Wakeup callback */
typedef void (*fGmacdWakeupCallback)(void);
/** Tx PTP message callback */
typedef void (*fGmacdTxPtpEvtCallBack) (ptpMsgType msg, uint32_t sec, \
					uint32_t nanosec, uint16_t seqId);

/**
 * GMAC scatter-gather entry.
 */
typedef struct _GmacSG {
	uint32_t size;
	void *pBuffer;
} sGmacSG;

/**
 * GMAC scatter-gather list.
 */
typedef struct _GmacSGList {
	uint32_t len;
	sGmacSG  *sg;
} sGmacSGList;

/**
 * GMAC Queue driver.
 */
typedef struct _GmacQueueDriver {
	uint8_t *pTxBuffer;
	/** Pointer to allocated RX buffer */
	uint8_t *pRxBuffer;

	/** Pointer to Rx TDs (must be 8-byte aligned) */
	sGmacRxDescriptor *pRxD;
	/** Pointer to Tx TDs (must be 8-byte aligned) */
	sGmacTxDescriptor *pTxD;

	/** Optional callback to be invoked once a frame has been received */
	fGmacdTransferCallback fRxCb;
	/** Optional callback to be invoked once several TD have been released */
	fGmacdWakeupCallback fWakupCb;
	/** Optional callback list to be invoked once TD has been processed */
	fGmacdTransferCallback *fTxCbList;

	/** Optional callback to be invoked on transmit of PTP Event messages */
	 fGmacdTxPtpEvtCallBack fTxPtpEvtCb;

	  /** RX TD list size */
	uint16_t wRxListSize;
	/** RX index for current processing TD */
	uint16_t wRxI;

	/** TX TD list size */
	uint16_t wTxListSize;
	/** Circular buffer head pointer by upper layer (buffer to be sent) */
	uint16_t wTxHead;
	/** Circular buffer tail pointer incremented by handlers (buffer sent) */
	uint16_t wTxTail;

	/** Number of free TD before wakeup callback is invoked */
	uint8_t  bWakeupThreshold;
	
   /** RX buffer size */
	uint16_t wTxBufferSize;
	uint16_t wRxBufferSize;
	
} sGmacQd;

/**
 * GMAC driver struct.
 */
typedef struct _GmacDriver {

	/** Pointer to HW register base */
	Gmac        *pHw;
	/** HW ID */
	uint8_t bId;
	/** Base Queue list params **/
	sGmacQd     queueList[NUM_GMAC_QUEUES];    
} sGmacd;

/**
 * GMAC driver init struct.
 */
typedef struct _GmacInit {
	uint32_t bIsGem:1;
	uint32_t reserved:31;

	uint8_t bDmaBurstLength;

	/** RX descriptor and data buffers */
	uint8_t *pRxBuffer;        
	/** RX data buffers: should be wRxBufferSize * wRxSize byte long in a DMA 
	capable memory region */
	sGmacRxDescriptor *pRxD;    
	/** RX buffer descriptors: should have wRxSize entries in a DMA 
	capable memory region */
	uint16_t wRxBufferSize;     /** size of a single RX data buffer */
	uint16_t wRxSize;           /** number of RX descriptor and data buffers */

	/** TX descriptor and data buffers */
	/** TX data buffers: should be wTxBufferSize * wTxSize byte long 
		in a DMA capable memory region */
	uint8_t *pTxBuffer;
	/** TX buffer descriptors: should have wTxSize entries
		in a DMA capable non-cached memory region */
	sGmacTxDescriptor *pTxD;
	/** size of a single TX data buffer */
	uint16_t wTxBufferSize;
	/** number of TX descriptor and data buffers */
	uint16_t wTxSize;

	fGmacdTransferCallback *pTxCb;      /** should have wTxSize entries */
} sGmacInit;
/** @}*/

/** \addtogroup gmacd_functions
	@{*/

/*---------------------------------------------------------------------------
 *         GMAC Exported functions
 *---------------------------------------------------------------------------*/

extern void GMACD_Handler(sGmacd *pGmacd , gmacQueList_t queIdx);

extern void GMACD_Init(sGmacd *pGmacd,
					   Gmac *pHw,
					   uint8_t bID, 
					   uint8_t enableCAF, 
					   uint8_t enableNBC );

extern uint8_t GMACD_InitTransfer(sGmacd *pGmacd,
								   const sGmacInit *pInit, gmacQueList_t queIdx);

extern void GMACD_Reset(sGmacd *pGmacd);

extern uint8_t GMACD_SendSG(sGmacd *pGmacd,
							const sGmacSGList *sgl,
							fGmacdTransferCallback fTxCb, 
							gmacQueList_t queIdx);

extern uint8_t GMACD_Send(sGmacd *pGmacd,
						 void *pBuffer,
						 uint32_t size,
						 fGmacdTransferCallback fTxCb, 
						 gmacQueList_t queIdx );

extern  uint32_t GMACD_TxLoad(sGmacd *pGmacd, gmacQueList_t queIdx);

extern  uint8_t GMACD_Poll(sGmacd * pGmacd, 
						  uint8_t *pFrame, 
						  uint32_t frameSize, 
						  uint32_t *pRcvSize, 
						  gmacQueList_t queIdx);

extern void GMACD_SetRxCallback(sGmacd * pGmacd, fGmacdTransferCallback 
		fRxCb, gmacQueList_t queIdx);

extern uint8_t GMACD_SetTxWakeupCallback(sGmacd * pGmacd,
										 fGmacdWakeupCallback fWakeup,
										 uint8_t bThreshold, 
										 gmacQueList_t queIdx);
 
extern void GMACD_TxPtpEvtMsgCBRegister (sGmacd * pGmacd, 
										  fGmacdTxPtpEvtCallBack pTxPtpEvtCb, 
										  gmacQueList_t queIdx);

/** @}*/

#endif // #ifndef _GMACD_H_
