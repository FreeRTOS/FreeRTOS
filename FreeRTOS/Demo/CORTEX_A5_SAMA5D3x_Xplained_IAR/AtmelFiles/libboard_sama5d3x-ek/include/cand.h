/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
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
/**
 * \ingroup lib_board
 * \addtogroup cand_module CAN Driver
 *
 * \section Purpose
 *
 * Implement driver functions for CAN operations.
 *
 * \section cand_usage Usage
 *
 * Uses following functions for CAN operations.
 * -# Uses CAND_Handler() as peripheral interrupt handler.
 * -# Uses CAND_Init() to initialize the driver and peripheral.
 * -# Uses CAND_Activate() to enable the CAN interface. Then check
 *    CAND_IsReady() to find when CAN is synchronized for data transfer.
 * -# To send a CAN message you can:
 *    -# Initialize mailbox with CAND_ResetMailbox()
 *    -# Start data transfer with CAND_Transfer()
 * -# You can also start CAN message by:
 *    -# Initialize transfer with CAND_ConfigureTransfer(). Several
 *       transfers linked to different mailbox can be initialized.
 *    -# After configuration, transfers can be enabled by
 *       CAND_StartTransfers() at one time.
 * -# To check if the transfer is done, CAND_IsTransferDone() is used.
 *
 * The following structs should be instanced for driver operations.
 * -# \ref sCand : Driver instance struct.
 * -# \ref sCandMbCfg : Mailbox configuration parameters list.
 * -# \ref sCandTransfer : Message transfer operation parameters list.
 *
 */

#ifndef _CAND_H_
#define _CAND_H_
/**@{*/
/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include <chip.h>

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** \addtogroup cand_rc CAN Driver Status (Return Codes)
 *      @{*/
/** Operation success */
#define CAND_OK             0
/** The driver/mailbox is busy */
#define CAND_BUSY           1
/** General error */
#define CAND_ERROR          0x10
/** Bad operation because of wrong state */
#define CAND_ERR_STATE      0x11
/** Bad operation for parameter error */
#define CAND_ERR_PARAM      0xFE
/**     @}*/

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/* CAN Driver General callback */
//typedef void(*CandCallback)(uint8_t bEvent, void* pArg);

/** CAN Driver Mailbox settings */
typedef struct _CandMbCfg {
    uint32_t dwMsgMask;     /**< Message ID Mask _MAMx */
    uint8_t  bMsgType;      /**< Message type */
    uint8_t  bTxPriority;   /**< Priority for TX */
} sCandMbCfg;

/** CAN Driver Transfer Parameters */
typedef struct _CandTransfer {
    //void* fCallback;        /**< Callback function when transfer finished */
    //void* pArg;             /**< Callback arguments */

    uint32_t dwMsgID;       /**< Message ID _MIDx */
    uint32_t msgData[2];    /**< Message data */
    uint8_t bMailbox;       /**< Mailbox used */
    uint8_t bMsgLen;        /**< Message length */
    uint8_t bState;         /**< Transfer state */
    uint8_t bRC;            /**< Transfer return code */
} sCandTransfer;

/** CAN Driver Transfer callback */
typedef void(*CandTransferCallback)(sCandTransfer* pXfr);

/**
 * CAN Driver instance struct.
 */
typedef struct _Cand {
    Can* pHw;                   /**< Pointer to HW register base */

    //CandCallback fCallback;     /**< Pointer to Callback function */
    //void*        pArg;          /**< Pointer to Callback argument */

    sCandTransfer *pMbs[CAN_NUM_MAILBOX];   /**< Pointer list to mailboxes */

    uint32_t dwMck;             /**< MCK for baudrate calculating */
    uint16_t wBaudrate;         /**< Current working baudrate */

    uint8_t bID;                /**< Peripheral ID */
    uint8_t bState;             /**< CAN states */
} sCand;


/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern uint8_t CAND_Init(sCand * pCand,
                         Can * pHw,uint8_t bID,
                         uint16_t wBaudrate,uint32_t dwMck);
extern void CAND_Activate(sCand * pCand);
extern void CAND_Sleep(sCand * pCand);
extern uint8_t CAND_IsReady(sCand * pCand);
extern void CAND_Handler(sCand * pCand);
extern uint8_t CAND_IsMailboxReady(sCand * pCand,uint8_t bMb);
extern void CAND_ResetMailbox(sCand * pCand,uint8_t bMb,sCandMbCfg * pCfg);
extern uint8_t CAND_ConfigureTransfer(sCand * pCand,
                                      sCandMbCfg * pCfg,
                                      sCandTransfer * pXfr);
extern uint8_t CAND_Transfer(sCand * pCand,sCandTransfer * pXfr);
extern void CAND_StartTransfers(sCand * pCand,uint32_t bmMbs);
extern uint8_t CAND_IsTransferDone(sCandTransfer * pXfr);
/**@}*/
#endif /* #ifndef _CAN_H_ */
