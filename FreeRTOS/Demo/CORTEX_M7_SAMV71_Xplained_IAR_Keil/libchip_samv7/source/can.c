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

/** \file
 *  Implements functions for Controller Area Network (CAN)
 *  peripheral operations.
 */
/** \addtogroup can_module
 *@{*/

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <assert.h>

#if defined(REG_CAN0_MR) || defined(REG_CAN_MR)

/* ----------- CAN_MR Operations --------------- */
/**
 * \brief Set CAN Mode Register (CAN_MR)
 * \param pCan Pointer to Can instance.
 * \param dwMr Mode register settings.
 */
void CAN_ConfigureMode(Can *pCan, uint32_t dwMr)
{
    pCan->CAN_MR = dwMr;
}

/**
 * \brief CAN Controller Enable/Disable
 * \param pCan   Pointer to Can instance.
 * \param bEnDis 1 to enable and 0 to disable.
 */
void CAN_Enable(Can *pCan, uint8_t bEnDis)
{
    if (bEnDis) pCan->CAN_MR |=  CAN_MR_CANEN;
    else        pCan->CAN_MR &= ~CAN_MR_CANEN;
}

/**
 * \brief CAN Low Power Mode Enable/Disable
 * \param pCan   Pointer to Can instance.
 * \param bEnDis 1 to enable and 0 to disable.
 */
void CAN_EnableLowPower(Can *pCan, uint8_t bEnDis)
{
    if (bEnDis) pCan->CAN_MR |=  CAN_MR_LPM;
    else        pCan->CAN_MR &= ~CAN_MR_LPM;
}

/**
 * \brief CAN Autobaud/Listen mode
 * \param pCan   Pointer to Can instance.
 * \param bEnDis 1 to enable and 0 to disable.
 */
void CAN_EnableAutobaud(Can *pCan, uint8_t bEnDis)
{
    if (bEnDis) pCan->CAN_MR |=  CAN_MR_ABM;
    else        pCan->CAN_MR &= ~CAN_MR_ABM;
}

/**
 * \brief CAN Overload Frame Enable/Disable
 * \param pCan   Pointer to Can instance.
 * \param bEnDis 1 to enable and 0 to disable.
 */
void CAN_EnableOverloadFrame(Can *pCan, uint8_t bEnDis)
{
    if (bEnDis) pCan->CAN_MR |=  CAN_MR_OVL;
    else        pCan->CAN_MR &= ~CAN_MR_OVL;
}

/**
 * \brief CAN Timestamp capture mode (@EOF/@SOF).
 * \param pCan      Pointer to Can instance.
 * \param bEofSof   1 for EOF/0 for SOF.
 */
void CAN_EnableTimeStampEof(Can *pCan, uint8_t bEofSof)
{
    if (bEofSof) pCan->CAN_MR |=  CAN_MR_TEOF;
    else         pCan->CAN_MR &= ~CAN_MR_TEOF;
}

/**
 * \brief CAN Time Triggered Mode Enable/Disable
 * \param pCan      Pointer to Can instance.
 * \param bEnDis    Enable/Disable Time Trigger Mode.
 */
void CAN_EnableTimeTriggerMode(Can *pCan, uint8_t bEnDis)
{
    if (bEnDis) pCan->CAN_MR |=  CAN_MR_TTM;
    else        pCan->CAN_MR &= ~CAN_MR_TTM;
}

/**
 * \brief CAN Timer Freeze Enable/Disable
 * \param pCan      Pointer to Can instance.
 * \param bEnDis    Enable/Disable Timer Freeze.
 */
void CAN_EnableTimerFreeze(Can *pCan, uint8_t bEnDis)
{
    if (bEnDis) pCan->CAN_MR |=  CAN_MR_TIMFRZ;
    else        pCan->CAN_MR &= ~CAN_MR_TIMFRZ;
}

/**
 * \brief CAN Repeat Disable/Enable.
 * \param pCan      Pointer to Can instance.
 * \param bEnDis    Disable/Enable Repeat.
 */
void CAN_DisableRepeat(Can *pCan, uint8_t bDisEn)
{
    if (bDisEn) pCan->CAN_MR |=  CAN_MR_DRPT;
    else        pCan->CAN_MR &= ~CAN_MR_DRPT;
}

/* ---------- Interrupt settings ------------- */

/**
 * \brief CAN Interrupts Enable
 * \param pCan      Pointer to Can instance.
 * \param dwSources Interrupt sources bits.
 */
void CAN_EnableIt(Can *pCan, uint32_t dwSources)
{
    pCan->CAN_IER = dwSources;
}

/**
 * \brief CAN Interrupts Disable
 * \param pCan      Pointer to Can instance.
 * \param dwSources Interrupt sources bits.
 */
void CAN_DisableIt(Can *pCan, uint32_t dwSources)
{
    pCan->CAN_IDR = dwSources;
}

/**
 * \brief Return CAN Interrupts Masks
 * \param pCan      Pointer to Can instance.
 */
uint32_t CAN_GetItMask(Can *pCan)
{
    return pCan->CAN_IMR;
}

/**
 * \brief Return CAN Statuses
 * \param pCan      Pointer to Can instance.
 */
uint32_t CAN_GetStatus(Can *pCan)
{
    return pCan->CAN_SR;
}

/**
 * \brief Calculate and configure the baudrate
 * \param pCan       Pointer to Can instance.
 * \param dwBaudrate Baudrate value (kB/s)
 *                   allowed: 100, 800, 500, 250, 125, 50, 25, 10
 * \param dwMck      MCK.
 * \return 1 in success, otherwise return 0.
 */
uint8_t CAN_CalcBaudrate(Can *pCan, uint32_t dwBaudrate, uint32_t dwMck)
{
    uint32_t BRP, PROPAG, PHASE1, PHASE2, SJW;
    uint8_t  TQ;
    uint32_t t1t2;
    uint32_t maxClock;
    uint32_t id = ID_CAN0;

    if ((uint32_t)pCan == (uint32_t)CAN0) id = ID_CAN0;
       else if ((uint32_t)pCan == (uint32_t)CAN1) id = ID_CAN1;
    maxClock = PMC_SetPeriMaxClock(id, dwMck);

    if (dwBaudrate >= 1000) TQ = 8;
    else                    TQ = 16;
    BRP = (maxClock / (dwBaudrate * 1000 * TQ)) - 1;
    if (BRP == 0) {
        return 0;
    }

    /* Timing delay:
       Delay Bus Driver     - 50ns
       Delay Receiver       - 30ns
       Delay Bus Line (20m) - 110ns */
    if ( (TQ * dwBaudrate * 2 * (50+30+110)/1000000) >= 1 )
        PROPAG = (TQ * dwBaudrate * 2 * (50+30+110)/1000000) - 1;
    else
        PROPAG = 0;
    t1t2 = TQ - 1 - (PROPAG + 1);

    if ( (t1t2 & 0x01) == 0x01 ) {
        PHASE1 = ((t1t2 - 1) / 2) - 1;
        PHASE2 = PHASE1 + 1;
    }
    else {
        PHASE1 = ((t1t2) / 2) - 1;
        PHASE2 = PHASE1;
    }

    if ( 1 > (4/(PHASE1 + 1)) ) SJW = 3;
    else                        SJW = PHASE1;

    if ( (PROPAG + PHASE1 + PHASE2) != (uint32_t)(TQ - 4) ) {
        return 0;
    }

    pCan->CAN_BR = CAN_BR_PHASE2(PHASE2)
                 | CAN_BR_PHASE1(PHASE1)
                 | CAN_BR_PROPAG(PROPAG)
                 | CAN_BR_SJW(SJW)
                 | CAN_BR_BRP(BRP)
                 | CAN_BR_SMP_ONCE;
    return 1;
}

/**
 * \brief Set CAN baudrate register
 * \param pCan      Pointer to Can instance.
 * \param dwBr      Setting value for CAN_BR.
 */
void CAN_ConfigureBaudrate(Can *pCan, uint32_t dwBr)
{
    pCan->CAN_BR = dwBr;
}

/**
 * \brief Set CAN Sampling Mode
 * \param pCan      Pointer to Can instance.
 * \param bAvg3     Sample 3 times/sample once at sample point.
 */
void CAN_SetSamplingMode(Can *pCan, uint8_t bAvg3)
{
    if (bAvg3) pCan->CAN_BR |=  CAN_BR_SMP;
    else       pCan->CAN_BR &= ~CAN_BR_SMP;
}

/**
 * \brief Return CAN Timer Register
 * \param pCan      Pointer to Can instance.
 */
uint32_t CAN_GetTimer(Can *pCan)
{
    return pCan->CAN_TIM;
}

/**
 * \brief Return CAN TimeStamp Register
 * \param pCan      Pointer to Can instance.
 */
uint32_t CAN_GetTimestamp(Can *pCan)
{
    return pCan->CAN_TIMESTP;
}

/**
 * \brief Return Error Count (TEC << 16) + REC
 * \param pCan      Pointer to Can instance.
 */
uint32_t CAN_GetErrorCount(Can *pCan)
{
    return pCan->CAN_ECR;
}

/**
 * \brief Return Receive Error Count
 * \param pCan      Pointer to Can instance.
 */
uint32_t CAN_GetRxErrorCount(Can *pCan)
{
    return (pCan->CAN_ECR & CAN_ECR_REC_Msk) >> CAN_ECR_REC_Pos;
}

/**
 * \brief Return Transmit Error Count
 * \param pCan      Pointer to Can instance.
 */
uint32_t CAN_GetTxErrorCount(Can *pCan)
{
    return (pCan->CAN_ECR & CAN_ECR_TEC_Msk) >> CAN_ECR_TEC_Pos;
}

/**
 * \brief Set Transfer Command Register to initialize transfer requests.
 * \param pCan       Pointer to Can instance.
 * \param dwRequests Transfer Command Requests.
 */
void CAN_Command(Can *pCan, uint32_t dwRequests)
{
    pCan->CAN_TCR = dwRequests;
}

/**
 * \brief Resets CAN internal timer counter.
 * \param pCan       Pointer to Can instance.
 */
void CAN_ResetTimer(Can *pCan)
{
    pCan->CAN_TCR = CAN_TCR_TIMRST;
}

/**
 * \brief Request transfer on mailbox.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
void CAN_Tx(Can *pCan, uint8_t bMb)
{
    pCan->CAN_TCR = CAN_TCR_MB0 << bMb;
}

/**
 * \brief Abort transfer on several mailboxes.
 * \param pCan       Pointer to Can instance.
 * \param dwAborts   Abort requests.
 */
void CAN_Abort(Can *pCan, uint32_t dwAborts)
{
    pCan->CAN_ACR = dwAborts;
}

/**
 * \brief Abort transfer on single mailbox.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
void CAN_AbortMailbox(Can *pCan, uint8_t bMb)
{
    pCan->CAN_ACR = CAN_ACR_MB0 << bMb;
}

/**
 * \brief Configure CAN Message Mode (_MMRx)
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param dwMr       Mode settings.
 */
void CAN_ConfigureMessageMode(Can *pCan, uint8_t bMb, uint32_t dwMr)
{
    pCan->CAN_MB[bMb].CAN_MMR = dwMr;
}

/**
 * \brief Return CAN Message Mode (_MMRx)
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
uint32_t CAN_GetMessageMode(Can *pCan, uint8_t bMb)
{
    return pCan->CAN_MB[bMb].CAN_MMR;
}

/**
 * \brief Set Mailbox Timemark for Time Triggered Mode.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param bTimemarks Mailbox timemarks.
 */
void CAN_SetTimemark(Can *pCan, uint8_t bMb, uint8_t bTimemarks)
{
    uint32_t dwMmr = (pCan->CAN_MB[bMb].CAN_MMR) & (~0xFFu);
    pCan->CAN_MB[bMb].CAN_MMR = dwMmr | ((bTimemarks << 0) & 0xFF);
}

/**
 * \brief Set Mailbox Priority.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param bPriority  Mailbox Priority.
 */
void CAN_SetPriority(Can *pCan, uint8_t bMb, uint8_t bPriority)
{
    uint32_t dwMmr = (pCan->CAN_MB[bMb].CAN_MMR & ~CAN_MMR_PRIOR_Msk);
    pCan->CAN_MB[bMb].CAN_MMR = dwMmr | CAN_MMR_PRIOR(bPriority);
}

/**
 * \brief Set Mailbox Object Type.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param bType      Mailbox Object Type.
 */
void CAN_SetObjectType(Can *pCan, uint8_t bMb, uint8_t bType)
{
    uint32_t dwMr = (pCan->CAN_MB[bMb].CAN_MMR & CAN_MMR_MOT_Msk) >> CAN_MMR_MOT_Pos;
    pCan->CAN_MB[bMb].CAN_MMR |= dwMr | ((bType << CAN_MMR_MOT_Pos) & CAN_MMR_MOT_Msk);
}

/**
 * \brief Configure CAN Message Acceptance Mask (_MAMx)
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param dwMam      The setting value for _MAMx.
 */
void CAN_ConfigureMessageAcceptanceMask(Can *pCan, uint8_t bMb, uint32_t dwMAM)
{
    pCan->CAN_MB[bMb].CAN_MAM = dwMAM;
}

/**
 * \brief Return CAN Message Acceptance Mask (_MAMx)
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
uint32_t CAN_GetMessageAcceptanceMask(Can *pCan, uint8_t bMb)
{
    return pCan->CAN_MB[bMb].CAN_MAM;
}

/**
 * \brief Configure Identifier Version in CAN Message Acceptance Mask (_MAMx)
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param bIdCfg     IDvA and IDvB/IDvA only Identify.
 */
void CAN_ConfigureIdentifierMask(Can *pCan, uint8_t bMb, uint8_t bIdCfg)
{
    if (bIdCfg) pCan->CAN_MB[bMb].CAN_MAM |=  CAN_MAM_MIDE;
    else        pCan->CAN_MB[bMb].CAN_MAM &= ~CAN_MAM_MIDE;
}

/**
 * \brief Set Identifier for standard frame mode (MIDvA) mask
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param dwMIDvA    Identifier for standard frame mode.
 */
void CAN_SetMIDvAMask(Can *pCan, uint8_t bMb, uint32_t dwIDvA)
{
    uint32_t dwMam = pCan->CAN_MB[bMb].CAN_MAM & CAN_MAM_MIDvA_Msk;
    pCan->CAN_MB[bMb].CAN_MAM = dwMam | CAN_MAM_MIDvA(dwIDvA);
}

/**
 * \brief Set Complementary bits for identifier in extended frame mode (MIDvB) mask
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param dwMIDvB    Identifier for extended frame mode.
 */
void CAN_SetMIDvBMask(Can *pCan, uint8_t bMb, uint32_t dwIDvA)
{
    uint32_t dwMam = pCan->CAN_MB[bMb].CAN_MAM & CAN_MAM_MIDvB_Msk;
    pCan->CAN_MB[bMb].CAN_MAM = dwMam | CAN_MAM_MIDvB(dwIDvA);
}

/**
 * \brief Configure CAN Message ID (_MIDx)
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param dwMID      The setting value for _MIDx.
 */
void CAN_ConfigureMessageID(Can *pCan, uint8_t bMb, uint32_t dwMID)
{
    pCan->CAN_MB[bMb].CAN_MID = dwMID;
}

/**
 * \brief Return CAN Message ID (_MIDx)
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
uint32_t CAN_GetMessageID(Can *pCan, uint8_t bMb)
{
    return pCan->CAN_MB[bMb].CAN_MID;
}

/**
 * \brief Configure Identifier Version in CAN Message ID register (_MIDx)
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param bIdVer     2.0 Part B/2.0 Part A.
 */
void CAN_ConfigureIdVer(Can *pCan, uint8_t bMb, uint8_t bIdVer)
{
    uint32_t dwMid = pCan->CAN_MB[bMb].CAN_MID & CAN_MID_MIDE;
    pCan->CAN_MB[bMb].CAN_MID = dwMid | (bIdVer ? CAN_MID_MIDE : 0);
}

/**
 * \brief Set Identifier for standard frame mode (MIDvA) value
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param dwMIDvA    Identifier for standard frame mode.
 */
void CAN_SetMIDvA(Can *pCan, uint8_t bMb, uint32_t dwIDvA)
{
    uint32_t dwMam = pCan->CAN_MB[bMb].CAN_MID & CAN_MID_MIDvA_Msk;
    pCan->CAN_MB[bMb].CAN_MID = dwMam | CAN_MID_MIDvA(dwIDvA);
}

/**
 * \brief Set Complementary bits for identifier in extended frame mode (MIDvB) value
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param dwMIDvB    Identifier for extended frame mode.
 */
void CAN_SetMIDvB(Can *pCan, uint8_t bMb, uint32_t dwIDvA)
{
    uint32_t dwMam = pCan->CAN_MB[bMb].CAN_MID & CAN_MID_MIDvB_Msk;
    pCan->CAN_MB[bMb].CAN_MID = dwMam | CAN_MID_MIDvB(dwIDvA);
}

/**
 * \brief Return CAN Message Family ID (Masked ID)
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
uint32_t CAN_GetFamilyID(Can *pCan, uint8_t bMb)
{
    return pCan->CAN_MB[bMb].CAN_MFID;
}

/**
 * \brief Return CAN Message Status
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
uint32_t CAN_GetMessageStatus(Can *pCan, uint8_t bMb)
{
    return pCan->CAN_MB[bMb].CAN_MSR;
}

/**
 * \brief Return CAN Message Data Low
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
uint32_t CAN_GetMessageDataL(Can *pCan, uint8_t bMb)
{
    return pCan->CAN_MB[bMb].CAN_MDL;
}

/**
 * \brief Set CAN Message Data Low
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param dwL        Data Low Value.
 */
void CAN_SetMessageDataL(Can *pCan, uint8_t bMb, uint32_t dwL)
{
    pCan->CAN_MB[bMb].CAN_MDL = dwL;
}

/**
 * \brief Set CAN Message Data High
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param dwH        Data High Value.
 */
void CAN_SetMessageDataH(Can *pCan, uint8_t bMb, uint32_t dwH)
{
    pCan->CAN_MB[bMb].CAN_MDH = dwH;
}

/**
 * \brief Return CAN Message Data High
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
uint32_t CAN_GetMessageDataH(Can *pCan, uint8_t bMb)
{
    return pCan->CAN_MB[bMb].CAN_MDH;
}

/**
 * \brief Copy DW array to CAN Message Data.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param pDwData    Pointer to a buffer for data.
 */
void CAN_SetMessage(Can *pCan, uint8_t bMb, uint32_t *pDwData)
{
    pCan->CAN_MB[bMb].CAN_MDL = pDwData[0];
    pCan->CAN_MB[bMb].CAN_MDH = pDwData[1];
}

/**
 * \brief Copy CAN Message Data to DW array.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param pDwData    Pointer to a buffer for data.
 */
void CAN_GetMessage(Can *pCan, uint8_t bMb, uint32_t *pDwData)
{
    pDwData[0] = pCan->CAN_MB[bMb].CAN_MDL;
    pDwData[1] = pCan->CAN_MB[bMb].CAN_MDH;
}

/**
 * \brief Set CAN Message Data in u64
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
void CAN_SetMessageData64(Can *pCan, uint8_t bMb, uint64_t u64)
{
    pCan->CAN_MB[bMb].CAN_MDL = (uint32_t)u64;
    pCan->CAN_MB[bMb].CAN_MDH = (u64 >> 32);
}

/**
 * \brief Return CAN Message Data in u64
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
uint64_t CAN_GetMessageData64(Can *pCan, uint8_t bMb)
{
    uint64_t ddwMd = (uint64_t)pCan->CAN_MB[bMb].CAN_MDH << 32;
    ddwMd += pCan->CAN_MB[bMb].CAN_MDL;
    return ddwMd;
}

/**
 * \brief Set CAN Message Control Register (_MCRx).
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param dwCtrl     Control value.
 */
void CAN_MessageControl(Can *pCan, uint8_t bMb, uint32_t dwCtrl)
{
    pCan->CAN_MB[bMb].CAN_MCR = dwCtrl;
}

/**
 * \brief Start remote frame.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
void CAN_MessageRemote(Can *pCan, uint8_t bMb)
{
    pCan->CAN_MB[bMb].CAN_MCR = CAN_MCR_MRTR;
}

/**
 * \brief Abort transmission.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
void CAN_MessageAbort(Can *pCan, uint8_t bMb)
{
    pCan->CAN_MB[bMb].CAN_MCR = CAN_MCR_MACR;
}

/**
 * \brief Start transmission.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 * \param bLen       Message length.
 */
void CAN_MessageTx(Can *pCan, uint8_t bMb, uint8_t bLen)
{
    pCan->CAN_MB[bMb].CAN_MCR = CAN_MCR_MTCR | CAN_MCR_MDLC(bLen);
}

/**
 * \brief Start reception.
 * \param pCan       Pointer to Can instance.
 * \param bMb        Mailbox number.
 */
void CAN_MessageRx(Can *pCan, uint8_t bMb)
{
    pCan->CAN_MB[bMb].CAN_MCR = CAN_MCR_MTCR;
}

#endif
/**@}*/

