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

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include <stdio.h>
#include <string.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/
/** The buffer addresses written into the descriptors must be aligned so the
    last few bits are zero.  These bits have special meaning for the GMAC
     peripheral and cannot be used as part of the address.*/

#define GMAC_ADDRESS_MASK   ((uint32_t)0xFFFFFFFC)
#define GMAC_LENGTH_FRAME   ((uint32_t)0x3FFF)      /** Length of frame mask */
/** receive buffer descriptor bits */
#define GMAC_RX_OWNERSHIP_BIT   (1 <<  0)
#define GMAC_RX_WRAP_BIT        (1 <<  1)
#define GMAC_RX_SOF_BIT         (1 << 14)
#define GMAC_RX_EOF_BIT         (1 << 15)

/** Transmit buffer descriptor bits */
#define GMAC_TX_LAST_BUFFER_BIT (1 << 15)
#define GMAC_TX_WRAP_BIT        (1 << 30)
#define GMAC_TX_USED_BIT        (1 << 31)
#define GMAC_TX_RLE_BIT         (1 << 29) /** Retry Limit Exceeded */
#define GMAC_TX_UND_BIT         (1 << 28) /** Tx Buffer Underrun */
#define GMAC_TX_ERR_BIT         (1 << 27) /** Exhausted in mid-frame */
#define GMAC_TX_ERR_BITS  \
    (GMAC_TX_RLE_BIT | GMAC_TX_UND_BIT | GMAC_TX_ERR_BIT)

/*----------------------------------------------------------------------------
 *        Internal functions
 *----------------------------------------------------------------------------*/
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
 
/**
 * Return 1 if PHY is idle
 */
uint8_t GMAC_IsIdle(Gmac *pGmac)
{
    return ((pGmac->GMAC_NSR & GMAC_NSR_IDLE) > 0);
}


/**
 * Execute PHY maintanance command
 */
void GMAC_PHYMaintain(Gmac      *pGmac,
                      uint8_t   bPhyAddr,
                      uint8_t   bRegAddr,
                      uint8_t   bRW,
                      uint16_t  wData)
{
    /* Wait until bus idle */
    while((pGmac->GMAC_NSR & GMAC_NSR_IDLE) == 0);
    /* Write maintain register */
    pGmac->GMAC_MAN = (~GMAC_MAN_WZO & GMAC_MAN_CLTTO)
                      | (GMAC_MAN_OP(bRW ? 0x2 : 0x1))
                      | GMAC_MAN_WTN(0x02)
                      | GMAC_MAN_PHYA(bPhyAddr)
                      | GMAC_MAN_REGA(bRegAddr)
                      | GMAC_MAN_DATA(wData) ;
}

/**
 * Return PHY maintainance data returned
 */
uint16_t GMAC_PHYData(Gmac *pGmac)
{
    /* Wait until bus idle */
    while((pGmac->GMAC_NSR & GMAC_NSR_IDLE) == 0);
    /* Return data */
    return (uint16_t)(pGmac->GMAC_MAN & GMAC_MAN_DATA_Msk);
}

/**
 *  \brief Set MDC clock according to current board clock. Per 802.3, MDC should be 
 *  less then 2.5MHz.
 *  \param pGmac Pointer to an Gmac instance. 
 *  \param mck Mdc clock
 *  \return 1 if successfully, 0 if MDC clock not found.
 */
uint8_t GMAC_SetMdcClock( Gmac *pGmac, uint32_t mck )
{
    uint32_t clock_dividor;
    pGmac->GMAC_NCR &=  ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);
    if (mck <= 20000000) {
        clock_dividor = GMAC_NCFGR_CLK_MCK_8;          // MDC clock = MCK/8
    }
    else if (mck <= 40000000) {
        clock_dividor = GMAC_NCFGR_CLK_MCK_16;         // MDC clock = MCK/16
    }
    else if (mck <= 80000000) {
        clock_dividor = GMAC_NCFGR_CLK_MCK_32;         // MDC clock = MCK/32
    }
    else if (mck <= 160000000) {
        clock_dividor = GMAC_NCFGR_CLK_MCK_64;         // MDC clock = MCK/64
    }
    else if (mck <= 240000000) {
        clock_dividor = GMAC_NCFGR_CLK_MCK_96;         // MDC clock = MCK/96
    }
    else if (mck <= 320000000) {
        clock_dividor = GMAC_NCFGR_CLK_MCK_128;        // MDC clock = MCK/128
    }
    else if (mck <= 540000000) {
        clock_dividor = GMAC_NCFGR_CLK_MCK_224;        // MDC clock = MCK/224
    }    
    else {
        TRACE_ERROR("E: No valid MDC clock.\n\r");
        return 0;
    }
    pGmac->GMAC_NCFGR = (pGmac->GMAC_NCFGR & (~GMAC_NCFGR_CLK_Msk)) | clock_dividor;
    pGmac->GMAC_NCR |=  (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
    return 1;
}

/**
 *  \brief Enable MDI with PHY
 *  \param pGmac Pointer to an Gmac instance.
 */
void GMAC_EnableMdio( Gmac *pGmac )
{
    pGmac->GMAC_NCR &=  ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);
    pGmac->GMAC_NCR |= GMAC_NCR_MPE;
    pGmac->GMAC_NCR |=  (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

/**
 *  \brief Enable MDI with PHY
 *  \param pGmac Pointer to an Gmac instance.
 */
void GMAC_DisableMdio( Gmac *pGmac )
{
    pGmac->GMAC_NCR &=  ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);
    pGmac->GMAC_NCR &= ~GMAC_NCR_MPE;
    pGmac->GMAC_NCR |=  (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

/**
 *  \brief Enable MII mode for GMAC, called once after autonegotiate
 *  \param pGmac Pointer to an Gmac instance.
 */
void GMAC_EnableMII( Gmac *pGmac )
{
    pGmac->GMAC_NCR &=  ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);
    pGmac->GMAC_UR &= ~GMAC_UR_RGMII;
    /*Gigabit Mode disable */
    pGmac->GMAC_NCFGR &= ~GMAC_NCFGR_GBE;
    pGmac->GMAC_NCR |=  (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

/**
 *  \brief Enable GMII mode for GMAC, called once after autonegotiate
 *  \param pGmac Pointer to an Gmac instance.
 */
void GMAC_EnableGMII( Gmac *pGmac )
{
    pGmac->GMAC_NCR &=  ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);
    /* Gigabit Mode enable */
    pGmac->GMAC_NCFGR |= GMAC_NCFGR_GBE;
    /* RGMII disable */
    pGmac->GMAC_UR &= ~GMAC_UR_RGMII;
    pGmac->GMAC_NCR |=  (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}


/**
 *  \brief Enable RGMII mode for GMAC, called once after autonegotiate
 *  \param pGmac Pointer to an Gmac instance.
 *  \param duplex: 1 full duplex 0 half duplex
 *  \param speed:   0 10M 1 100M 2 1000M
 */
void GMAC_EnableRGMII(Gmac *pGmac, uint32_t duplex, uint32_t speed)
{
    pGmac->GMAC_NCR &=  ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);
    pGmac->GMAC_NCFGR &= ~GMAC_NCFGR_GBE;
    if (duplex == GMAC_DUPLEX_HALF)
    {
        pGmac->GMAC_NCFGR &= ~GMAC_NCFGR_FD;
    }
    else 
    {
        pGmac->GMAC_NCFGR |= GMAC_NCFGR_FD;
    }


    if (speed == GMAC_SPEED_10M)
    {
        pGmac->GMAC_NCFGR &= ~GMAC_NCFGR_SPD;
    }
    else if(speed == GMAC_SPEED_100M) 
    {
        pGmac->GMAC_NCFGR |= GMAC_NCFGR_SPD;
    }
    else
    {
        pGmac->GMAC_NCFGR |= GMAC_NCFGR_GBE;
    }
  
    /* RGMII enable */
    pGmac->GMAC_UR |= GMAC_UR_RGMII;
    return;
}

/**
 *  \brief Setup the GMAC for the link : speed 100M/10M and Full/Half duplex
 *  \param pGmac Pointer to an Gmac instance.
 *  \param speed        Link speed, 0 for 10M, 1 for 100M, 2 for 1000M
 *  \param fullduplex   1 for Full Duplex mode
 */
void GMAC_SetLinkSpeed(Gmac *pGmac, uint8_t speed, uint8_t fullduplex)
{
    uint32_t ncfgr;
    ncfgr = pGmac->GMAC_NCFGR;
    ncfgr &= ~(GMAC_NCFGR_SPD | GMAC_NCFGR_FD);
    if (speed) {

        ncfgr |= GMAC_NCFGR_SPD;
    }
    if (fullduplex) {

        ncfgr |= GMAC_NCFGR_FD;
    }
    pGmac->GMAC_NCFGR = ncfgr;
    pGmac->GMAC_NCR |=  (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

/**
 *  \brief set local loop back
 *  \param pGmac Pointer to an Gmac instance.
 */
uint32_t GMAC_SetLocalLoopBack(Gmac *pGmac)
{
    pGmac->GMAC_NCR |= GMAC_NCR_LBL;
    return 0;
}

/**
 * Return interrupt mask.
 */
uint32_t GMAC_GetItMask(Gmac *pGmac)
{
    return pGmac->GMAC_IMR;
}


/**
 * Return transmit status
 */
uint32_t GMAC_GetTxStatus(Gmac *pGmac)
{
    return pGmac->GMAC_TSR;
}

/**
 * Clear transmit status
 */
void GMAC_ClearTxStatus(Gmac *pGmac, uint32_t dwStatus)
{
    pGmac->GMAC_TSR = dwStatus;
}

/**
 * Return receive status
 */
uint32_t GMAC_GetRxStatus(Gmac *pGmac)
{
    return pGmac->GMAC_RSR;
}

/**
 * Clear receive status
 */
void GMAC_ClearRxStatus(Gmac *pGmac, uint32_t dwStatus)
{
    pGmac->GMAC_RSR = dwStatus;
}


/**
 * Enable/Disable GMAC receive.
 */
void GMAC_ReceiveEnable(Gmac* pGmac, uint8_t bEnaDis)
{
    if (bEnaDis) pGmac->GMAC_NCR |=  GMAC_NCR_RXEN;
    else         pGmac->GMAC_NCR &= ~GMAC_NCR_RXEN;
}

/**
 * Enable/Disable GMAC transmit.
 */
void GMAC_TransmitEnable(Gmac *pGmac, uint8_t bEnaDis)
{
    if (bEnaDis) pGmac->GMAC_NCR |=  GMAC_NCR_TXEN;
    else         pGmac->GMAC_NCR &= ~GMAC_NCR_TXEN;
}
 

/**
 * Set Rx Queue
 */
void GMAC_SetRxQueue(Gmac *pGmac, uint32_t dwAddr)
{
    pGmac->GMAC_RBQB = GMAC_RBQB_ADDR_Msk & dwAddr;
}
           
/**
 * Get Rx Queue Address
 */
uint32_t GMAC_GetRxQueue(Gmac *pGmac)
{
    return pGmac->GMAC_RBQB;
}

/**
 * Set Tx Queue
 */
void GMAC_SetTxQueue(Gmac *pGmac, uint32_t dwAddr)
{
    pGmac->GMAC_TBQB = GMAC_TBQB_ADDR_Msk & dwAddr;
}

/**
 * Get Tx Queue
 */
uint32_t GMAC_GetTxQueue(Gmac *pGmac)
{
    return pGmac->GMAC_TBQB;
}


/**
 * Write control value
 */
void GMAC_NetworkControl(Gmac *pGmac, uint32_t bmNCR)
{
    pGmac->GMAC_NCR = bmNCR;
}


/**
 * Get control value
 */
uint32_t GMAC_GetNetworkControl(Gmac *pGmac)
{
    return pGmac->GMAC_NCR;
}


/**
 * Enable interrupt(s).
 */
void GMAC_EnableIt(Gmac *pGmac, uint32_t dwSources)
{
    pGmac->GMAC_IER = dwSources;
}

/**
 * Disable interrupt(s).
 */
void GMAC_DisableIt(Gmac *pGmac, uint32_t dwSources)
{
    pGmac->GMAC_IDR = dwSources;
}

/**
 * Return interrupt status.
 */
uint32_t GMAC_GetItStatus(Gmac *pGmac)
{
    return pGmac->GMAC_ISR;
}


/**
 * Set MAC Address
 */
void GMAC_SetAddress(Gmac *pGmac, uint8_t bIndex, uint8_t *pMacAddr)
{
    pGmac->GMAC_SA[bIndex].GMAC_SAB = (pMacAddr[3] << 24)
                                     | (pMacAddr[2] << 16)
                                     | (pMacAddr[1] <<  8)
                                     | (pMacAddr[0]      )
                                     ;
    pGmac->GMAC_SA[bIndex].GMAC_SAT = (pMacAddr[5] <<  8)
                                     | (pMacAddr[4]      )
                                     ;
}

/**
 * Set MAC Address via 2 DW
 */
void GMAC_SetAddress32(Gmac *pGmac, uint8_t bIndex, uint32_t dwMacT, uint32_t dwMacB)
{
    pGmac->GMAC_SA[bIndex].GMAC_SAB = dwMacB;
    pGmac->GMAC_SA[bIndex].GMAC_SAT = dwMacT;
}

/**
 * Set MAC Address via int64
 */
void GMAC_SetAddress64(Gmac *pGmac, uint8_t bIndex, uint64_t ddwMac)
{
    pGmac->GMAC_SA[bIndex].GMAC_SAB = (uint32_t)ddwMac;
    pGmac->GMAC_SA[bIndex].GMAC_SAT = (uint32_t)(ddwMac >> 32);
}


/**
 * Clear all statistics registers
 */
void GMAC_ClearStatistics(Gmac *pGmac)
{
    pGmac->GMAC_NCR |=  GMAC_NCR_CLRSTAT;
}

/**
 * Increase all statistics registers
 */
void GMAC_IncreaseStatistics(Gmac *pGmac)
{
    pGmac->GMAC_NCR |=  GMAC_NCR_INCSTAT;
}

/**
 * Enable/Disable statistics registers writing.
 */
void GMAC_StatisticsWriteEnable(Gmac *pGmac, uint8_t bEnaDis)
{
    if (bEnaDis) pGmac->GMAC_NCR |=  GMAC_NCR_WESTAT;
    else         pGmac->GMAC_NCR &= ~GMAC_NCR_WESTAT;
}


/**
 * Setup network configuration register
 */
void GMAC_Configure(Gmac *pGmac, uint32_t dwCfg)
{
    pGmac->GMAC_NCFGR = dwCfg;
}

/**
 * Return network configuration.
 */
uint32_t GMAC_GetConfigure(Gmac *pGmac)
{
    return pGmac->GMAC_NCFGR;
}


/**
 * Start transmission
 */
void GMAC_TransmissionStart(Gmac *pGmac)
{
    pGmac->GMAC_NCR |= GMAC_NCR_TSTART;
}

/**
 * Halt transmission
 */
void GMAC_TransmissionHalt(Gmac *pGmac)
{
    pGmac->GMAC_NCR |= GMAC_NCR_THALT;
}
