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
/** \addtogroup cand_module
 *@{*/

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

#include <assert.h>

#if defined(REG_CAN0_MR) || defined(REG_CAN_MR)

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/

/** \addtogroup cand_states CAN Driver states
 *      @{*/
#define CAND_STATE_DISABLED     0 /**< Power-up reset, controller is disabled */
#define CAND_STATE_INIT         1 /**< Initializing */
#define CAND_STATE_SLEEP        2 /**< Low-power mode */
#define CAND_STATE_SYNC         3 /**< Synchronizating */
#define CAND_STATE_ERROR        4 /**< Error halt */
#define CAND_STATE_ACTIVATED    5 /**< Bus synchronization is done */
#define CAND_STATE_XFR          6 /**< Transfer in progress */
/**     @}*/

/** \addtogroup cand_xfr_states CAN Transfer states
 *      @{*/
#define CAND_XFR_DISABLED       0 /**< Transfer not used */
#define CAND_XFR_HALTED         1 /**< Error halt */
#define CAND_XFR_IDLE           2 /**< No transfer */
#define CAND_XFR_TX             3 /**< Transferring data */
/**     @}*/

/** \addtogroup cand_reg_bits CAN Register Bitfields
 *      @{*/
/** CAN mailbox event statuses bits */
#define CAN_MB_EVENTS       0xFF
/** CAN errors statuses bits */
#define CAN_ERRS    (0 \
                    /*|CAN_SR_ERRA*/ \
                    /*|CAN_SR_WARN*/ \
                    /*|CAN_SR_ERRP*/ \
                    /*|CAN_SR_BOFF*/ \
                    /*|CAN_SR_SLEEP*/ \
                    /*|CAN_SR_WAKEUP*/ \
                    /*|CAN_SR_TOVF*/ \
                    /*|CAN_SR_TSTP*/ \
                    |CAN_SR_CERR \
                    |CAN_SR_SERR \
                    |CAN_SR_AERR \
                    |CAN_SR_FERR \
                    |CAN_SR_BERR \
                    /*|CAN_SR_RBSY*/ \
                    /*|CAN_SR_TBSY*/ \
                    /*|CAN_SR_OVLSY*/ \
                    )
/** CAN mailbox ID mask */
#define CAN_ID_MASK (CAN_MID_MIDE | CAN_MID_MIDvA_Msk | CAN_MID_MIDvB_Msk)

#define CAN_MMR_MOT(x) (((x)<<CAN_MMR_MOT_Pos)&CAN_MMR_MOT_Msk)
/**     @}*/

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------
 *        Local Functions
 *----------------------------------------------------------------------------*/

/**
 * Check if the mailbox is ready to transfer
 * \param pMb The current mailbox transfer parameters.
 */
static uint8_t CAND_IsMbReady(sCandTransfer *pMb)
{
    /* MB has no transfer, OK */
    if (pMb == NULL) return 1;
    /* MB has transfer, NOK */
    if (pMb->bState == CAND_XFR_TX) return 0;
    /* MB in a state that acceps modification */
    return 1;
}

/**
 * Reset mailbox with specified configuration value.
 * \param pCand Pointer to CAN Driver instance.
 * \param pCfg  Pointer to list of configurations.
 */
static void CAND_ResetMb(sCand *pCand, uint8_t bMb, sCandMbCfg *pCfg)
{
    Can *pCan = pCand->pHw;
    CAN_DisableIt(pCan, (1 << bMb) & CAN_MB_EVENTS);
    CAN_MessageControl(pCan, bMb, 0);
    CAN_ConfigureMessageMode(pCan, bMb, 0);
    if (pCand->pMbs[bMb])
    {
        pCand->pMbs[bMb] = CAND_XFR_DISABLED;
        pCand->pMbs[bMb] = NULL;
    }
    if (pCfg)
    {
        CAN_ConfigureMessageAcceptanceMask(pCan, bMb, pCfg->dwMsgMask);
        CAN_ConfigureMessageMode(pCan, bMb, CAN_MMR_MOT(pCfg->bMsgType)
                                            | CAN_MMR_PRIOR(pCfg->bTxPriority));
    }
}

/**
 * Initialize transfer on specific Mailbox.
 * \param pCand  Pointer to CAN Driver instance.
 * \param pXfr   Pointer to CAN Transfer instance.
 * \param bStart Start transfer immediately.
 */
static void CAND_InitXfr(sCand *pCand, sCandTransfer *pXfr, uint8_t bStart)
{
    Can *pCan = pCand->pHw;
    uint8_t bMb = pXfr->bMailbox;
    uint32_t dwMmr = CAN_GetMessageMode(pCan, bMb);

    if (pXfr == NULL)
        return;
    /* Log tranfser */
    pCand->pMbs[bMb] = pXfr;
    /* Set transfer state */
    if (bStart)
    {
        pXfr->bState = CAND_XFR_TX;
        pCand->bState = CAND_STATE_XFR;
    }
    /* Reset transfer state */
    else
        pXfr->bState = CAND_XFR_IDLE;
    /* Fill ID */
    CAN_ConfigureMessageID(pCan, bMb, pXfr->dwMsgID);
    /* Fill data registers */
    CAN_SetMessage(pCan, bMb, pXfr->msgData);
    /* Start TX if not RX */
    if ((dwMmr & CAN_MMR_MOT_Msk) > CAN_MMR_MOT_MB_RX_OVERWRITE)
    {
        CAN_MessageControl(pCan, bMb,
                           CAN_MCR_MDLC(pXfr->bMsgLen)
                           | (bStart ? CAN_MCR_MTCR : 0) );
    }
}

/**
 * Finish transfer on specific Mailbox.
 * \param pCand  Pointer to CAN Driver instance.
 * \param pXfr   Pointer to CAN Transfer instance.
 * \param bSC    Status code.
 */
static void CAND_EndXfr(sCand *pCand, sCandTransfer *pXfr, uint8_t bSC)
{
    if (!pCand) return;
    /* Return status */
    pXfr->bRC = bSC;
    if (bSC >= CAND_ERROR)
        pXfr->bState = CAND_XFR_HALTED;
    else if(pXfr->bState == CAND_XFR_TX)
        pXfr->bState = CAND_XFR_IDLE;
    /* Invoke callbacks */
}

/**
 * Disable all mailboxes
 */
static void CAND_ResetMailboxes(sCand *pCand)
{
    uint32_t i;
    /* Reset all mailboxes */
    for (i = 0; i < CAN_NUM_MAILBOX; i ++)
    {
        CAND_ResetMb(pCand, i, NULL);
    }
    pCand->bState = CAND_STATE_INIT;
}

/**
 * Handler for CAN errors
 */
static void CAND_ErrorHandler(sCand *pCand, uint32_t dwErrS)
{
    pCand = pCand;
    uint32_t ecr;
    TRACE_INFO("CAN[%x]: 0x%08x\n\r", pCand->pHw, dwErrS);
    #if 1
    ecr = (pCand->pHw)->CAN_ECR;
    ecr = ecr; /*Dummy */
    if (dwErrS & CAN_SR_ERRA)
    {

        TRACE_ERROR_WP("-E- Active Mode: TEC %u, REC %u\n\r", 
                  (unsigned int)((ecr & CAN_ECR_TEC_Msk) >> CAN_ECR_TEC_Pos), 
                  (unsigned int)((ecr & CAN_ECR_REC_Msk) >> CAN_ECR_REC_Pos));
    }
    if (dwErrS & CAN_SR_WARN)
    {
        TRACE_ERROR_WP("Warning Limit: TEC %u, REC %u\n\r", 
                      (unsigned int)((ecr & CAN_ECR_TEC_Msk) >> CAN_ECR_TEC_Pos), 
                      (unsigned int)((ecr & CAN_ECR_REC_Msk) >> CAN_ECR_REC_Pos));
    }
    if (dwErrS & CAN_SR_ERRP)
    {
        TRACE_ERROR_WP("-E- Passive Mode: TEC %u, REC %u\n\r", 
                      (unsigned int)((ecr & CAN_ECR_TEC_Msk) >> CAN_ECR_TEC_Pos), 
                      (unsigned int)((ecr & CAN_ECR_REC_Msk) >> CAN_ECR_REC_Pos));
    }
    if (dwErrS & CAN_SR_BOFF)
    {
        TRACE_ERROR_WP("Bus Off Mode, TEC %u\n\r", (unsigned int)((((pCand->pHw)->CAN_ECR) & CAN_ECR_TEC_Msk) >> CAN_ECR_TEC_Pos));
    }
    #endif
    if (dwErrS & CAN_SR_CERR)
    {
        TRACE_ERROR_WP("-E- MB CRC\n\r");
    }
    if (dwErrS & CAN_SR_SERR)
    {
        TRACE_ERROR_WP("-E- MB Stuffing\n\r");
    }
    if (dwErrS & CAN_SR_AERR)
    {
        TRACE_ERROR_WP("-E- Ack\n\r");
    }
    if (dwErrS & CAN_SR_FERR)
    {
        TRACE_ERROR_WP("-E- Form\n\r");
    }
    if (dwErrS & CAN_SR_BERR)
    {
        TRACE_ERROR_WP("-E- Bit\n\r");
    }
}

/**
 * Handler for messages
 * \param pCand Pointer to CAN Driver instance.
 */
static void CAND_MessageHandler(sCand *pCand)
{
    Can *pCan = pCand->pHw;
    sCandTransfer *pXfr;
    uint8_t bMb;
    uint32_t dwMsr;
    for (bMb = 0; bMb < CAN_NUM_MAILBOX; bMb ++)
    {
        /* Mailbox used ? */
        pXfr = pCand->pMbs[bMb];
        if (pXfr == NULL)
            continue;
        /* Mailbox ready ? */
        dwMsr = CAN_GetMessageStatus(pCan, bMb);
        if ((dwMsr & CAN_MSR_MRDY) != CAN_MSR_MRDY)
            continue;
        /* Handle data */
        switch (CAN_GetMessageMode(pCan, bMb) & CAN_MMR_MOT_Msk)
        {
            case CAN_MMR_MOT_MB_RX_OVERWRITE: /** Next data overwrite current */
                /*pXfr->bState = CAND_XFR_RX_ONE;*/
            case CAN_MMR_MOT_MB_RX:
            case CAN_MMR_MOT_MB_CONSUMER:   /** TX then RX message */
                pXfr->bMsgLen = (dwMsr & CAN_MSR_MDLC_Msk) >> CAN_MSR_MDLC_Pos;
                CAN_GetMessage(pCan, bMb, pXfr->msgData);
                CAND_EndXfr(pCand, pXfr, CAND_OK);
                break;

            case CAN_MMR_MOT_MB_TX:
            case CAN_MMR_MOT_MB_PRODUCER:   /** RX then TX message */
                CAND_EndXfr(pCand, pXfr, CAND_OK);
                break;

            default:
                TRACE_ERROR("MB[%d] disabled\n\r", bMb);
                CAND_EndXfr(pCand, pXfr, CAND_ERROR);
                break;
        }
        /*if (pXfr->bState != CAND_XFR_RX_ONE)*/
        {
            /* Disable mailbox interrupt */
            CAN_DisableIt(pCan, 1 << bMb);
            /* Unlink transfer */
            pCand->pMbs[bMb] = NULL;
        }
    }
    /* All transfer finished ? */
    if ((CAN_GetItMask(pCan)&CAN_MB_EVENTS) == 0)
        pCand->bState = CAND_STATE_ACTIVATED;
}

/*----------------------------------------------------------------------------
 *        Exported Functions
 *----------------------------------------------------------------------------*/

/**
 * Initialize CAN Driver with specific baudrate.
 * \param pCand Pointer to CAN Driver instance.
 * \param pHw   Pointer to CAN controller HW base address.
 * \param bID   ID for CAN controller.
 * \param wBaudrate Expected baudrate.
 * \param dwMck     Current MCK used.
 */
uint8_t CAND_Init(sCand* pCand,
               Can *pHw, uint8_t bID,
               uint16_t wBaudrate, uint32_t dwMck)
{

    pCand->pHw = pHw;
    pCand->bID = bID;
    PMC_EnablePeripheral(pCand->bID);
    /* Reserved */
    //pCand->fCallback = NULL;
    //pCand->pArg = NULL;

    /* Disable all interrupts */
    CAN_DisableIt(pHw, 0xFFFFFFFF);

    /* (Re)initialize baudrate */
    if (wBaudrate)
    {
        pCand->dwMck = dwMck;
        pCand->wBaudrate = wBaudrate;
        if (!CAN_CalcBaudrate(pHw, wBaudrate, dwMck))
            return CAND_ERROR;
    }

    /* Reset CAN mode */
    CAN_ConfigureMode(pHw, 0);

    /* Reset all mailboxes */
    CAND_ResetMailboxes(pCand);

    /* Enable the interrupts for error cases */
    CAN_EnableIt(pHw, CAN_ERRS);

    return CAND_OK;
}

/**
 * Activate CAN.
 * \param pCand Pointer to CAN Driver instance.
 */
void CAND_Activate(sCand *pCand)
{
    Can *pCan = pCand->pHw;
    if (pCand->bState > CAND_STATE_SYNC)
        return;
    /* Disable low-power mode */    
    CAN_EnableLowPower(pCan, 0);
    /* Start sync state */
    pCand->bState = CAND_STATE_SYNC;
    /* Enable CAN and wait interrupt */
    CAN_EnableIt(pCan, CAN_IER_WAKEUP);
    CAN_Enable(pCan, 1);
}
#if 0
/**
 * Find good baudrate (activated).
 */
void CAND_AutoBaudrate(sCand *pCand, uint16_t *pBuadList, uint16_t wListSize)
{
}
#endif
/**
 * Put into sleep mode
 * \param pCand Pointer to CAN Driver instance.
 */
void CAND_Sleep(sCand *pCand)
{
    Can *pCan = pCand->pHw;
    CAN_EnableIt(pCan, CAN_IER_SLEEP);
    CAN_EnableLowPower(pCan, 1);
}

/**
 * Check if CAN is ready to transfer messages.
 * \param pCand Pointer to CAN Driver instance.
 */
uint8_t CAND_IsReady(sCand *pCand)
{
    return (pCand->bState >= CAND_STATE_ACTIVATED);
}

/**
 * Interrupt handler for CAN Driver.
 * \param pCand Pointer to CAN Driver instance.
 */
void CAND_Handler(sCand *pCand)
{
    Can *pHw = pCand->pHw;
    uint32_t dwSr = CAN_GetStatus(pHw);
    //uint32_t dwSm = CAN_GetItMask(pHw);
    TRACE_INFO("%d:%8x\n\r", (pHw==CAN0)?0:1, dwSr);
    /* Errors */
    if (dwSr & CAN_ERRS)
    {
        pCand->bState = CAND_STATE_ERROR;
        CAND_ErrorHandler(pCand, (dwSr & CAN_ERRS));
        CAN_DisableIt(pHw, dwSr & CAN_ERRS);
    }
    else
    {
        /* Wakeup and bus synchronization done */
        if (pCand->bState > CAND_STATE_ACTIVATED)
        {
            /* Mailbox events */
            if (dwSr & CAN_MB_EVENTS)
            {
                CAND_MessageHandler(pCand);
            }
        }
        else if (dwSr & CAN_SR_WAKEUP)
        {
            CAN_DisableIt(pHw, CAN_IDR_WAKEUP);
            pCand->bState = CAND_STATE_ACTIVATED;
        }
    }
    /* Low-power Mode enabled */
    if (dwSr & CAN_SR_SLEEP)
    {
        CAN_DisableIt(pHw, CAN_IDR_SLEEP);
        pCand->bState = CAND_STATE_SLEEP;
    }
    /* Timestamp */
    if (dwSr & CAN_SR_TSTP)
    {
    }
    /* Timer overflow */
    if (dwSr & CAN_SR_TOVF)
    {
    }
}

/**
 * Check if the mailbox is ready to configure or transfer.
 * \param pCand Pointer to CAN Driver instance.
 * \param bMb   Mailbox number.
 * \return 1 if mailbox is free.
 */
uint8_t CAND_IsMailboxReady(sCand *pCand, uint8_t bMb)
{
    return (CAND_IsMbReady(pCand->pMbs[bMb]));
}

/**
 * Reset the CAN Mailbox (with configuration).
 * \param pCand Pointer to CAN Driver instance.
 * \param bMb   Mailbox number.
 * \param pCfg  Pointer to Mailbox configuration instance.
 *              NULL to reset and disable the mailbox.
 */
void CAND_ResetMailbox(sCand *pCand, uint8_t bMb, sCandMbCfg *pCfg)
{
    CAND_ResetMb(pCand, bMb, pCfg);
}

/**
 * Configure the CAN Mailbox for message transfer.
 * \param pCand Pointer to CAN Driver instance.
 * \param pCfg  Pointer to Mailbox configuration instance.
 *              NULL to use old configuration.
 * \param pXfr  Pointer to transfer configuration instance.
 */
uint8_t CAND_ConfigureTransfer(sCand *pCand,
                               sCandMbCfg *pCfg,
                               sCandTransfer *pXfr)
{
    uint8_t bMb = pXfr->bMailbox;
    sCandTransfer *pTx = pCand->pMbs[bMb];

    if (!CAND_IsMbReady(pTx))
        return CAND_BUSY;
    if (pCfg)
        CAND_ResetMb(pCand, bMb, pCfg);
    CAND_InitXfr(pCand, pXfr, 0);
    return CAND_OK;
}

/**
 * Transfer CAN message through a configured mailbox.
 * The transfer will not start until it's started by CAND_StartTransfers().
 * \note For data receiving, if there is previous pending message in
 *       mailbox, the RX operation will return this message data.
 * \param pCand  Pointer to CAN Driver instance.
 * \param pXfr   Pointer to transfer configuration instance.
 * \param bStart 1 to start the transfer immediately.
 */
uint8_t CAND_Transfer(sCand *pCand, sCandTransfer *pXfr)
{
    Can *pCan = pCand->pHw;
    sCandTransfer *pTx;
    uint8_t bMb = pXfr->bMailbox;

    pTx = pCand->pMbs[bMb];
    if (!CAND_IsMbReady(pTx)) return CAND_BUSY;
    if (0 == CAN_GetMessageMode(pCan, bMb))
        return CAND_ERR_STATE;
    /* Configure and start transfer */
    CAND_InitXfr(pCand, pXfr, 1);
    /* Enable interrupts statuses */
    CAN_EnableIt(pCan, (CAN_ID_MASK & (1 << bMb))|CAN_ERRS);
    return CAND_OK;
}

/**
 * Start configured transfers (by CAND_ConfigureTransfer()).
 * \note For data receiving, if there is previous pending message in
 *       mailbox, the RX operation will return this message data.
 * \param pCand Pointer to CAN Driver instance.
 * \param bmMbs Mailbox bitmap.
 */
void CAND_StartTransfers(sCand *pCand, uint32_t bmMbs)
{
    Can *pCan = pCand->pHw;
    sCandTransfer *pTx;
    uint8_t bMb;
    uint32_t bmTx = 0;
    uint32_t  bmRx = 0;
    uint32_t dwMMR;
    /* Scan mailboxes that not started */
    for (bMb = 0; bMb < CAN_NUM_MAILBOX; bMb ++)
    {
        if ((bmMbs & (1 << bMb)) == 0)
            continue;
        /* Check if the mailbox is ready to transfer */
        pTx = pCand->pMbs[bMb];
        if (pTx == NULL)
        {
            /* Ignore the mailbox */
            bmMbs &= ~(1 << bMb);
            continue;
        }
        if (pTx->bState > CAND_XFR_IDLE)
        {
            /* Ignore the mailbox */
            bmMbs &= ~(1 << bMb);
            continue;
        }
        dwMMR = CAN_GetMessageMode(pCan, bMb);
        /* Disabled ? */
        if ( 0 == dwMMR )
        {
            /* Ignore the mailbox */
            bmMbs &= ~(1 << bMb);
            continue;
        }
        /* RX ? */
        else if ((dwMMR & CAN_MMR_MOT_Msk) <= CAN_MMR_MOT_MB_RX_OVERWRITE)
        {
            bmRx |= 1 << bMb;
        }
        /* TX ! */
        else
        {
            bmTx |= 1 << bMb;
        }

        /* Change transfer state */
        pTx->bState = CAND_XFR_TX;

        /* Nothing to start */
        if (bmMbs == 0)
            return;
    }
    /* Change CAN state */
    pCand->bState = CAND_STATE_XFR;
    /* Start transfers */
    CAN_Command(pCan, bmTx);
    /* Enable interrupts */
    CAN_EnableIt(pCan, bmMbs | CAN_ERRS);
}

/**
 * Check if the transfer is finished.
 * \return 1 if it's ready to transfer data.
 */
uint8_t CAND_IsTransferDone(sCandTransfer *pXfr)
{
    return CAND_IsMbReady(pXfr);
}

#endif
/**@}*/

