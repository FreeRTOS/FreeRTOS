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

/** \addtogroup emac_functions
 *@{
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

/*----------------------------------------------------------------------------
 *       Exported functions
 *----------------------------------------------------------------------------*/

/**
 * Write control value
 */
void EMAC_NetworkControl(Emac *pEmac, uint32_t bmNCR)
{
    pEmac->EMAC_NCR = bmNCR;
}

uint32_t EMAC_GetNetworkControl(Emac *pEmac)
{
    return pEmac->EMAC_NCR;
}

/**
 * Enable/Disable EMAC receive.
 */
void EMAC_ReceiveEnable(Emac* pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCR |=  EMAC_NCR_RE;
    else         pEmac->EMAC_NCR &= ~EMAC_NCR_RE;
}

/**
 * Enable/Disable EMAC transmit.
 */
void EMAC_TransmitEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCR |=  EMAC_NCR_TE;
    else         pEmac->EMAC_NCR &= ~EMAC_NCR_TE;
}

/**
 * Enable/Disable EMAC management.
 */
void EMAC_ManagementEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCR |=  EMAC_NCR_MPE;
    else         pEmac->EMAC_NCR &= ~EMAC_NCR_MPE;
}

/**
 * Clear all statistics registers
 */
void EMAC_ClearStatistics(Emac *pEmac)
{
    pEmac->EMAC_NCR |=  EMAC_NCR_CLRSTAT;
    //pEmac->EMAC_NCR &= ~EMAC_NCR_CLRSTAT;
}

/**
 * Increase all statistics registers
 */
void EMAC_IncreaseStatistics(Emac *pEmac)
{
    pEmac->EMAC_NCR |=  EMAC_NCR_INCSTAT;
    //pEmac->EMAC_NCR &= ~EMAC_NCR_INCSTAT;
}

/**
 * Enable/Disable statistics registers writing.
 */
void EMAC_StatisticsWriteEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCR |=  EMAC_NCR_WESTAT;
    else         pEmac->EMAC_NCR &= ~EMAC_NCR_WESTAT;
}

/**
 * In half-duplex mode, forces collisions on all received frames.
 */
void EMAC_BackPressureEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCR |=  EMAC_NCR_BP;
    else         pEmac->EMAC_NCR &= ~EMAC_NCR_BP;
}

/**
 * Start transmission
 */
void EMAC_TransmissionStart(Emac *pEmac)
{
    pEmac->EMAC_NCR |= EMAC_NCR_TSTART;
}

/**
 * Halt transmission
 */
void EMAC_TransmissionHalt(Emac *pEmac)
{
    pEmac->EMAC_NCR |= EMAC_NCR_THALT;
}

/**
 * Setup network configuration register
 */
void EMAC_Configure(Emac *pEmac, uint32_t dwCfg)
{
    pEmac->EMAC_NCFGR = dwCfg;
}

/**
 * Return network configuration.
 */
uint32_t EMAC_GetConfigure(Emac *pEmac)
{
    return pEmac->EMAC_NCFGR;
}

/**
 * Set speed.
 * \param bSpeed 1 to indicate 100Mbps, 0 for 10Mbps.
 */
void EMAC_SetSpeed(Emac *pEmac, uint8_t bSpeed)
{
    if (bSpeed) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_SPD;
    else        pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_SPD;
}


/**
 * Enable/Disable Full-Duplex mode
 */
void EMAC_FullDuplexEnable(Emac *pEmac, uint8_t bFD)
{
    if (bFD) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_FD;
    else     pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_FD;
}

/**
 * Enable/Disable Copy(Receive) All Valid Frames
 */
void EMAC_CpyAllEnable(Emac *pEmac, uint8_t bCAF)
{
    if (bCAF) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_CAF;
    else      pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_CAF;
}

/**
 * Enable/Disable jumbo frames (up to 10240 bytes).
 */
void EMAC_JumboFrameEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_JFRAME;
    else         pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_JFRAME;
}

/**
 * Disable/Enable broadcase receiving.
 */
void EMAC_BroadcastDisable(Emac *pEmac, uint8_t bDisEna)
{
    if (bDisEna) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_NBC;
    else         pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_NBC;
}

/**
 * Enable/Disable multicast hash
 */
void EMAC_MulticastHashEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_UNI;
    else         pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_UNI;
}

/**
 * Enable/Disable big frames (over 1518, up to 1536)
 */
void EMAC_BigFrameEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_BIG;
    else         pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_BIG;
}

/**
 * Set MDC clock divider
 * \return 1 if success.
 */
uint8_t EMAC_SetClock(Emac *pEmac, uint32_t dwMck)
{
    uint8_t bCLK = 0;

    /* Not supported */
    if (dwMck > 160*1000*1000)
    {
        return 0;
    }
    else if (dwMck > 80*1000*1000)
    {
        bCLK = 3;
    }
    else if (dwMck > 40*1000*1000)
    {
        bCLK = 2;
    }
    else if (dwMck > 20*1000*1000)
    {
        bCLK = 1;
    }

    pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_CLK_Msk;
    pEmac->EMAC_NCFGR |=  (EMAC_NCFGR_CLK_Msk & ((bCLK) << EMAC_NCFGR_CLK_Pos));

    return 1;
}

/**
 * Enable/Disable retry test
 */
void EMAC_RetryTestEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_RTY;
    else         pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_RTY;
}

/**
 * Enable/Disable pause (when a valid pause frame received).
 */
void EMAC_PauseFrameEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_PAE;
    else         pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_PAE;
}

/**
 * Set receive buffer offset to 0 ~ 3.
 */
void EMAC_SetRxBufferOffset(Emac *pEmac, uint8_t bOffset)
{
    pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_RBOF_Msk;
    pEmac->EMAC_NCFGR |=  (EMAC_NCFGR_RBOF_Msk & ((bOffset) << EMAC_NCFGR_RBOF_Pos));
}

/**
 * Enable/Disable receive length field checking
 */
void EMAC_RxLenthCheckEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_RLCE;
    else         pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_RLCE;
}

/**
 * Enable/Disable discarding FCS field of received frames.
 */
void EMAC_DiscardFCSEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_DRFCS;
    else         pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_DRFCS;
}


/**
 * Enable/Disable frames to be received in half-duplex mode
 * while transmitting.
 */
void EMAC_EFRHD(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_EFRHD;
    else         pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_EFRHD;
}

/**
 * Enable/Disable ignore RX FCS
 */
void EMAC_IRXFCS(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_NCFGR |=  EMAC_NCFGR_IRXFCS;
    else         pEmac->EMAC_NCFGR &= ~EMAC_NCFGR_IRXFCS;
}

/**
 * Return Network Status
 */
uint32_t EMAC_GetStatus(Emac *pEmac)
{
    return pEmac->EMAC_NSR;
}

/**
 * Return mdio_in pin status
 */
uint8_t EMAC_GetMDIO(Emac *pEmac)
{
    return ((pEmac->EMAC_NSR & EMAC_NSR_MDIO) > 0);
}

/**
 * Return 1 if PHY is idle
 */
uint8_t EMAC_IsIdle(Emac *pEmac)
{
    return ((pEmac->EMAC_NSR & EMAC_NSR_IDLE) > 0);
}

/**
 * Return transmit status
 */
uint32_t EMAC_GetTxStatus(Emac *pEmac)
{
    return pEmac->EMAC_TSR;
}

/**
 * Clear transmit status
 */
void EMAC_ClearTxStatus(Emac *pEmac, uint32_t dwStatus)
{
    pEmac->EMAC_TSR = dwStatus;
}

/**
 * Return receive status
 */
uint32_t EMAC_GetRxStatus(Emac *pEmac)
{
    return pEmac->EMAC_RSR;
}

/**
 * Clear receive status
 */
void EMAC_ClearRxStatus(Emac *pEmac, uint32_t dwStatus)
{
    pEmac->EMAC_RSR = dwStatus;
}

/**
 * Set Rx Queue
 */
void EMAC_SetRxQueue(Emac *pEmac, uint32_t dwAddr)
{
    pEmac->EMAC_RBQP = EMAC_RBQP_ADDR_Msk & dwAddr;
}

/**
 * Get Rx Queue Address
 */
uint32_t EMAC_GetRxQueue(Emac *pEmac)
{
    return pEmac->EMAC_RBQP;
}

/**
 * Set Tx Queue
 */
void EMAC_SetTxQueue(Emac *pEmac, uint32_t dwAddr)
{
    pEmac->EMAC_TBQP = EMAC_TBQP_ADDR_Msk & dwAddr;
}

/**
 * Get Tx Queue
 */
uint32_t EMAC_GetTxQueue(Emac *pEmac)
{
    return pEmac->EMAC_TBQP;
}

/**
 * Enable interrupt(s).
 */
void EMAC_EnableIt(Emac *pEmac, uint32_t dwSources)
{
    pEmac->EMAC_IER = dwSources;
}

/**
 * Disable interrupt(s).
 */
void EMAC_DisableIt(Emac *pEmac, uint32_t dwSources)
{
    pEmac->EMAC_IDR = dwSources;
}

/**
 * Return interrupt status.
 */
uint32_t EMAC_GetItStatus(Emac *pEmac)
{
    return pEmac->EMAC_ISR;
}

/**
 * Return interrupt mask.
 */
uint32_t EMAC_GetItMask(Emac *pEmac)
{
    return pEmac->EMAC_IMR;
}

/**
 * Execute PHY maintanance command
 */
void EMAC_PHYMaintain(Emac      *pEmac,
                      uint8_t   bPhyAddr,
                      uint8_t   bRegAddr,
                      uint8_t   bRW,
                      uint16_t  wData)
{
    /* Wait until bus idle */
    while((pEmac->EMAC_NSR & EMAC_NSR_IDLE) == 0);
    /* Write maintain register */
    pEmac->EMAC_MAN = EMAC_MAN_CODE(0x02) | EMAC_MAN_SOF(0x1)
                    | EMAC_MAN_PHYA(bPhyAddr)
                    | EMAC_MAN_REGA(bRegAddr)
                    | EMAC_MAN_RW((bRW ? 0x2 : 0x1))
                    | EMAC_MAN_DATA(wData)
                    ;
}

/**
 * Return PHY maintainance data returned
 */
uint16_t EMAC_PHYData(Emac *pEmac)
{
    /* Wait until bus idle */
    while((pEmac->EMAC_NSR & EMAC_NSR_IDLE) == 0);
    /* Return data */
    return (uint16_t)(pEmac->EMAC_MAN & EMAC_MAN_DATA_Msk);
}

/**
 * Set pause time.
 */
void EMAC_SetPauseTime(Emac *pEmac, uint16_t wPTime)
{
    pEmac->EMAC_PTR = wPTime;
}

/**
 * Set Hash
 */
void EMAC_SetHash(Emac *pEmac, uint32_t dwHashTop, uint32_t dwHashBottom)
{
    pEmac->EMAC_HRB = dwHashBottom;
    pEmac->EMAC_HRT = dwHashTop;
}

/**
 * Set Hash
 */
void EMAC_SetHash64(Emac *pEmac, uint64_t ddwHash)
{
    pEmac->EMAC_HRB = (uint32_t)ddwHash;
    pEmac->EMAC_HRT = (uint32_t)(ddwHash >> 32);
}

/**
 * Set MAC Address
 */
void EMAC_SetAddress(Emac *pEmac, uint8_t bIndex, uint8_t *pMacAddr)
{
    pEmac->EMAC_SA[bIndex].EMAC_SAxB = (pMacAddr[3] << 24)
                                     | (pMacAddr[2] << 16)
                                     | (pMacAddr[1] <<  8)
                                     | (pMacAddr[0]      )
                                     ;
    pEmac->EMAC_SA[bIndex].EMAC_SAxT = (pMacAddr[5] <<  8)
                                     | (pMacAddr[4]      )
                                     ;
}

/**
 * Set MAC Address via 2 DW
 */
void EMAC_SetAddress32(Emac *pEmac, uint8_t bIndex, uint32_t dwMacT, uint32_t dwMacB)
{
    pEmac->EMAC_SA[bIndex].EMAC_SAxB = dwMacB;
    pEmac->EMAC_SA[bIndex].EMAC_SAxT = dwMacT;
}

/**
 * Set MAC Address via int64
 */
void EMAC_SetAddress64(Emac *pEmac, uint8_t bIndex, uint64_t ddwMac)
{
    pEmac->EMAC_SA[bIndex].EMAC_SAxB = (uint32_t)ddwMac;
    pEmac->EMAC_SA[bIndex].EMAC_SAxT = (uint32_t)(ddwMac >> 32);    
}

/**
 * Set Type ID
 */
void EMAC_SetTypeID(Emac *pEmac, uint16_t wTID)
{
    pEmac->EMAC_TID = EMAC_TID_TID(wTID);
}

/**
 * Get Type ID
 */
uint16_t EMAC_GetTypeID(Emac *pEmac)
{
    return (pEmac->EMAC_TID & EMAC_TID_TID_Msk);
}

/**
 * Enable/Disable RMII
 */
void EMAC_RMIIEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_USRIO |=  EMAC_USRIO_RMII;
    else         pEmac->EMAC_USRIO &= ~EMAC_USRIO_RMII;
}

/**
 * Enable/Disable transceiver input clock
 */
void EMAC_TransceiverClockEnable(Emac *pEmac, uint8_t bEnaDis)
{
    if (bEnaDis) pEmac->EMAC_USRIO |=  EMAC_USRIO_CLKEN;
    else         pEmac->EMAC_USRIO &= ~EMAC_USRIO_CLKEN;
}

/**@}*/

