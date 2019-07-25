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

#include <board.h>


/*---------------------------------------------------------------------------
 *         Definitions
 *---------------------------------------------------------------------------*/
/** \addtogroup gmacd_defines
    @{*/

/** \addtogroup gmacd_buf_size GMACD Default Buffer Size
        @{*/
#define GMAC_RX_UNITSIZE            128     /**< Fixed size for RX buffer  */
#define GMAC_TX_UNITSIZE            1518    /**< Size for ETH frame length */
/**     @}*/

/** \addtogroup gmacd_rc GMACD Return Codes
        @{*/
#define GMACD_OK                0   /**< Operation OK */
#define GMACD_TX_BUSY           1   /**< TX in progress */
#define GMACD_RX_NULL           1   /**< No data received */
/** Buffer size not enough */
#define GMACD_SIZE_TOO_SMALL    2
/** Parameter error, TX packet invalid or RX size too small */
#define GMACD_PARAM             3
/** Transter is not initialized */
#define GMACD_NOT_INITIALIZED   4
/**     @}*/

/** @}*/

/*---------------------------------------------------------------------------
 *         Types
 *---------------------------------------------------------------------------*/
/** \addtogroup gmacd_types
    @{*/

/** RX callback */
typedef void (*fGmacdTransferCallback)(uint32_t status);
/** Wakeup callback */
typedef void (*fGmacdWakeupCallback)(void);

/**
 * GMAC driver struct.
 */
typedef struct _GmacDriver {

    /** Pointer to HW register base */
    Gmac *pHw;

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
    /** HW ID */
    uint8_t bId;
} sGmacd;

/** @}*/

/** \addtogroup gmacd_functions
    @{*/

/*---------------------------------------------------------------------------
 *         GMAC Exported functions
 *---------------------------------------------------------------------------*/

extern void GMACD_Handler(sGmacd *pGmacd );

extern void GMACD_Init(sGmacd *pGmacd,
                       Gmac *pHw,
                       uint8_t bID, 
                       uint8_t enableCAF, 
                       uint8_t enableNBC );

extern uint8_t GMACD_InitTransfer( sGmacd *pGmacd,
                                   uint8_t *pRxBuffer, 
                                   sGmacRxDescriptor *pRxD,
                                   uint16_t wRxSize,
                                   uint8_t *pTxBuffer, 
                                   sGmacTxDescriptor *pTxD, 
                                   fGmacdTransferCallback *pTxCb,
                                   uint16_t wTxSize);

extern void GMACD_Reset(sGmacd *pGmacd);

extern uint8_t GMACD_Send(sGmacd *pGmacd,
                         void *pBuffer,
                         uint32_t size,
                         fGmacdTransferCallback fTxCb );

extern  uint32_t GMACD_TxLoad(sGmacd *pGmacd);

extern  uint8_t GMACD_Poll(sGmacd * pGmacd, 
                          uint8_t *pFrame, 
                          uint32_t frameSize, 
                          uint32_t *pRcvSize);

extern void GMACD_SetRxCallback(sGmacd * pGmacd, fGmacdTransferCallback fRxCb);

extern uint8_t GMACD_SetTxWakeupCallback(sGmacd * pGmacd,
                                         fGmacdWakeupCallback fWakeup,
                                         uint8_t bThreshold);

/** @}*/

#endif // #ifndef _GMACD_H_
