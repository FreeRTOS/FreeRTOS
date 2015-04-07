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

/** \addtogroup emacd_module
 * @{
 * Implement EMAC data transfer and PHY management functions.
 *
 * \section Usage
 * -# Implement EMAC interrupt handler, which must invoke EMACD_Handler()
 *    to handle EMAC interrupt events.
 * -# Implement sEmacd instance in application.
 * -# Initialize the instance with EMACD_Init() and EMACD_InitTransfer(),
 *    so that EMAC data can be transmitted/received.
 * -# Some management callbacks can be set by EMACD_SetRxCallback()
 *    and EMACD_SetTxWakeupCallback().
 * -# Send ethernet packets using EMACD_Send(), EMACD_TxLoad() is used
 *    to check the free space in TX queue.
 * -# Check and obtain received ethernet packets via EMACD_Poll().
 *
 * \sa \ref macb_module, \ref emac_module
 *
 * Related files:\n
 * \ref emacd.c\n
 * \ref emacd.h.\n
 *
 *  \defgroup emacd_defines EMAC Driver Defines
 *  \defgroup emacd_types EMAC Driver Types
 *  \defgroup emacd_functions EMAC Driver Functions
 */
/**@}*/

#ifndef _EMACD_H_
#define _EMACD_H_

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include <board.h>

/*---------------------------------------------------------------------------
 *         Definitions
 *---------------------------------------------------------------------------*/
/** \addtogroup emacd_defines
    @{*/

/** \addtogroup emacd_buf_size EMACD Default Buffer Size
        @{*/
#define EMAC_RX_UNITSIZE            128     /**< Fixed size for RX buffer  */
#define EMAC_TX_UNITSIZE            1518    /**< Size for ETH frame length */
/**     @}*/

/** \addtogroup emacd_rc EMACD Return Codes
        @{*/
#define EMACD_OK                0   /**< Operation OK */
#define EMACD_TX_BUSY           1   /**< TX in progress */
#define EMACD_RX_NULL           1   /**< No data received */
/** Buffer size not enough */
#define EMACD_SIZE_TOO_SMALL    2
/** Parameter error, TX packet invalid or RX size too small */
#define EMACD_PARAM             3
/** Transter is not initialized */
#define EMACD_NOT_INITIALIZED   4
/**     @}*/

/** @}*/
/*---------------------------------------------------------------------------
 *         Types
 *---------------------------------------------------------------------------*/
/** \addtogroup emacd_types
    @{*/

/** RX callback */
typedef void (*fEmacdTransferCallback)(uint32_t status);
/** Wakeup callback */
typedef void (*fEmacdWakeupCallback)(void);

/**
 * EMAC driver struct.
 */
typedef struct _EmacDriver {

    /** Pointer to HW register base */
    Emac *pHw;

    /** Pointer to allocated TX buffer
        Section 3.6 of AMBA 2.0 spec states that burst should not cross
        1K Boundaries.
        Receive buffer manager writes are burst of 2 words => 3 lsb bits
        of the address shall be set to 0
        */
    uint8_t *pTxBuffer;
    /** Pointer to allocated RX buffer */
    uint8_t *pRxBuffer;

    /** Pointer to Rx TDs (must be 8-byte aligned) */
    sEmacRxDescriptor *pRxD;
    /** Pointer to Tx TDs (must be 8-byte aligned) */
    sEmacTxDescriptor *pTxD;

    /** Optional callback to be invoked once a frame has been received */
    fEmacdTransferCallback fRxCb;
    /** Optional callback to be invoked once several TD have been released */
    fEmacdWakeupCallback fWakupCb;
    /** Optional callback list to be invoked once TD has been processed */
    fEmacdTransferCallback *fTxCbList;

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
} sEmacd;

/** @}*/

/** \addtogroup emacd_functions
    @{*/

/*---------------------------------------------------------------------------
 *         PHY Exported functions
 *---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------
 *         EMAC Exported functions
 *---------------------------------------------------------------------------*/

extern void EMACD_Init( sEmacd *pEmacd,
                        Emac   *pHw, uint8_t bID,
                        uint8_t bCAF, uint8_t bNBC);

extern uint8_t EMACD_InitTransfer( sEmacd *pEmacd,
    uint8_t *pRxBuffer, sEmacRxDescriptor *pRxD,
    uint16_t wRxSize,
    uint8_t *pTxBuffer, sEmacTxDescriptor *pTxD, fEmacdTransferCallback *pTxCb,
    uint16_t wTxSize);

extern void EMACD_SetRxCallback( sEmacd *pEmacd, fEmacdTransferCallback fRxCb);

extern uint8_t EMACD_SetTxWakeupCallback( sEmacd *pEmacd,
                                          fEmacdWakeupCallback fWakeup,
                                          uint8_t bThreshold );

extern void EMACD_Handler( sEmacd *pEmacd );

extern void EMACD_Reset( sEmacd * pEmacd );

extern uint8_t EMACD_Send(sEmacd * pEmacd,
                          void *pBuffer, 
                          uint32_t size, 
                          fEmacdTransferCallback fTxCallback);

extern uint32_t EMACD_TxLoad( sEmacd *pEmacd );

extern uint8_t EMACD_Poll(sEmacd * pEmacd,
                          uint8_t *pFrame,
                          uint32_t frameSize,
                          uint32_t *pRcvSize);

/** @}*/

#endif // #ifndef _EMACD_H_

