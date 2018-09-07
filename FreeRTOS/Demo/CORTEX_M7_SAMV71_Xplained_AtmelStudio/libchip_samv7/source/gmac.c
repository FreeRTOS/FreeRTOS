/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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
 * Execute PHY maintenance command
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
 * Return PHY maintenance data returned
 */
uint16_t GMAC_PHYData(Gmac *pGmac)
{
	/* Wait until bus idle */
	while((pGmac->GMAC_NSR & GMAC_NSR_IDLE) == 0);
	/* Return data */
	return (uint16_t)(pGmac->GMAC_MAN & GMAC_MAN_DATA_Msk);
}

/**
 *  \brief Set MDC clock according to current board clock. Per 802.3, MDC should 
 *  be less then 2.5MHz.
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
	} else if (mck <= 40000000) {
		clock_dividor = GMAC_NCFGR_CLK_MCK_16;         // MDC clock = MCK/16
	} else if (mck <= 80000000) {
		clock_dividor = GMAC_NCFGR_CLK_MCK_32;         // MDC clock = MCK/32
	} else if (mck <= 160000000) {
		clock_dividor = GMAC_NCFGR_CLK_MCK_64;         // MDC clock = MCK/64
	} else if (mck <= 240000000) {
		clock_dividor = GMAC_NCFGR_CLK_MCK_96;         // MDC clock = MCK/96
	} else {
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
 *  \brief Enable MII mode for GMAC, called once after auto negotiate
 *  \param pGmac Pointer to an Gmac instance.
 */
void GMAC_EnableMII( Gmac *pGmac )
{
	pGmac->GMAC_NCR &=  ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);
	pGmac->GMAC_UR &= ~GMAC_UR_RMII;
	pGmac->GMAC_NCR |=  (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

/**
 *  \brief Enable GMII mode for GMAC, called once after auto negotiate
 *  \param pGmac Pointer to an Gmac instance.
 */
void GMAC_EnableGMII( Gmac *pGmac )
{
	pGmac->GMAC_NCR &=  ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);
	/* RGMII disable */
	pGmac->GMAC_UR &= ~GMAC_UR_RMII;
	pGmac->GMAC_NCR |=  (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

#define GMAC_NCFGR_GBE (0x1u << 10)
/**
 *  \brief Enable RGMII mode for GMAC, called once after auto negotiate
 *  \param pGmac Pointer to an Gmac instance.
 *  \param duplex: 1 full duplex 0 half duplex
 *  \param speed:   0 10M 1 100M 
 */
void GMAC_EnableRGMII(Gmac *pGmac, uint32_t duplex, uint32_t speed)
{
	pGmac->GMAC_NCR &=  ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);
	if (duplex == GMAC_DUPLEX_HALF) {
		pGmac->GMAC_NCFGR &= ~GMAC_NCFGR_FD;
	} else {
		pGmac->GMAC_NCFGR |= GMAC_NCFGR_FD;
	}


	if (speed == GMAC_SPEED_10M) {
		pGmac->GMAC_NCFGR &= ~GMAC_NCFGR_SPD;
	} else if(speed == GMAC_SPEED_100M) {
		pGmac->GMAC_NCFGR |= GMAC_NCFGR_SPD;
	} else {
		pGmac->GMAC_NCFGR |= GMAC_NCFGR_SPD;
	}
  
	/* RGMII enable */
	pGmac->GMAC_UR = 0;
	pGmac->GMAC_NCFGR &= ~GMAC_NCFGR_GBE;
	pGmac->GMAC_NCR |=  (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
	return;
}

/**
 *  \brief Setup the GMAC for the link : speed 100M/10M and Full/Half duplex
 *  \param pGmac Pointer to an Gmac instance.
 *  \param speed        Link speed, 0 for 10M, 1 for 100M
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
uint32_t GMAC_GetItMask(Gmac *pGmac, gmacQueList_t queueIdx)
{
	if(!queueIdx) {
		return pGmac->GMAC_IMR;
	} else {
	  return pGmac->GMAC_IMRPQ[queueIdx -1];
	}
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
void GMAC_SetRxQueue(Gmac *pGmac, uint32_t dwAddr, gmacQueList_t queueIdx)
{
	if(!queueIdx) {
		pGmac->GMAC_RBQB = GMAC_RBQB_ADDR_Msk & dwAddr;
	} else {
		pGmac->GMAC_RBQBAPQ[queueIdx - 1] = GMAC_RBQB_ADDR_Msk & dwAddr;
	}
}

/**
 * Get Rx Queue Address
 */
uint32_t GMAC_GetRxQueue(Gmac *pGmac, gmacQueList_t queueIdx)
{
	if(!queueIdx) {
		return pGmac->GMAC_RBQB;
	} else {
		return pGmac->GMAC_RBQBAPQ[queueIdx - 1];
	}
}

/**
 * Set Tx Queue
 */
void GMAC_SetTxQueue(Gmac *pGmac, uint32_t dwAddr, gmacQueList_t queueIdx)
{
	if(!queueIdx) {
		pGmac->GMAC_TBQB = GMAC_TBQB_ADDR_Msk & dwAddr;
	} else {
		pGmac->GMAC_TBQBAPQ[queueIdx - 1] = GMAC_TBQB_ADDR_Msk & dwAddr;
	}
}

/**
 * Get Tx Queue
 */
uint32_t GMAC_GetTxQueue(Gmac *pGmac, gmacQueList_t queueIdx)
{
	if(!queueIdx) {
		return pGmac->GMAC_TBQB;
	} else {
		return pGmac->GMAC_TBQBAPQ[queueIdx - 1];
	}
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
void GMAC_EnableIt(Gmac *pGmac, uint32_t dwSources, gmacQueList_t queueIdx)
{
	if(!queueIdx) {
		pGmac->GMAC_IER = dwSources;
	} else {
		pGmac->GMAC_IERPQ[queueIdx-1] = dwSources;
	}
}

/**
 * Disable interrupt(s).
 */
void GMAC_DisableAllQueueIt(Gmac *pGmac, uint32_t dwSources)
{
	pGmac->GMAC_IDR = dwSources;
	pGmac->GMAC_IDRPQ[0] = dwSources;
	pGmac->GMAC_IDRPQ[1] = dwSources;
}

/**
 * Disable interrupt(s).
 */
void GMAC_EnableAllQueueIt(Gmac *pGmac, uint32_t dwSources)
{
	pGmac->GMAC_IER = dwSources;
	pGmac->GMAC_IERPQ[0] = dwSources;
	pGmac->GMAC_IERPQ[1] = dwSources;
}

/**
 * Disable interrupt(s).
 */
void GMAC_DisableIt(Gmac *pGmac, uint32_t dwSources, gmacQueList_t queueIdx)
{
	if(!queueIdx) {
		pGmac->GMAC_IDR = dwSources;
	} else {
		pGmac->GMAC_IDRPQ[queueIdx-1] = dwSources;
	}
}

/**
 * Return interrupt status.
 */
uint32_t GMAC_GetItStatus(Gmac *pGmac, gmacQueList_t queueIdx)
{
	if(!queueIdx) {
		return pGmac->GMAC_ISR;
	} else {
		return pGmac->GMAC_ISRPQ[queueIdx-1];
	}
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
	pGmac->GMAC_SA[bIndex].GMAC_SAT = (uint32_t)(ddwMac >32);
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
 * Setup DMA configuration register
 */
void GMAC_SetDMAConfig(Gmac *pGmac, uint32_t dwDmaCfg, gmacQueList_t queueIdx)
{
	if(!queueIdx) {
		pGmac->GMAC_DCFGR = dwDmaCfg;
	} else {
		pGmac->GMAC_RBSRPQ[queueIdx-1] = dwDmaCfg;
	}
}

/**
 * Return DMA configuration register
 */
uint32_t GMAC_GetDMAConfig(Gmac *pGmac, gmacQueList_t queueIdx)
{
	if(!queueIdx) {
		return pGmac->GMAC_DCFGR;
	} else {
		return pGmac->GMAC_RBSRPQ[queueIdx-1];
	};
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


/* Screener Register configurations */
void GMAC_ClearScreener1Reg (Gmac *pGmac, gmacQueList_t queueIdx)
{
	pGmac->GMAC_ST1RPQ[queueIdx] = 0u;
}

void GMAC_WriteScreener1Reg(Gmac *pGmac, gmacQueList_t queueIdx, uint32_t regVal)
{
	pGmac->GMAC_ST1RPQ[queueIdx] = regVal;
}

void GMAC_ClearScreener2Reg (Gmac *pGmac, gmacQueList_t queueIdx)
{
	pGmac->GMAC_ST2RPQ[queueIdx] = 0u;
}

void GMAC_WriteScreener2Reg (Gmac *pGmac, gmacQueList_t queueIdx, uint32_t regVal)
{
	pGmac->GMAC_ST2RPQ[queueIdx] = regVal;
}

void GMAC_WriteEthTypeReg (Gmac *pGmac, gmacQueList_t queueIdx,  uint16_t etherType)
{
	pGmac->GMAC_ST2ER[queueIdx] = (uint32_t)etherType;
}

void GMAC_WriteCompareReg(Gmac *pGmac, gmacQueList_t queueIdx, uint32_t c0Reg,
						uint16_t c1Reg)
{
	pGmac->GMAC_ST2COMP[queueIdx].GMAC_ST2COM0 = c0Reg; 
	pGmac->GMAC_ST2COMP[queueIdx].GMAC_ST2COM1 = (uint32_t)c1Reg; 
	memory_barrier();
}

/* CBS queue control APIs */
void GMAC_EnableCbsQueA(Gmac *pGmac)
{
	pGmac->GMAC_CBSCR |= GMAC_CBSCR_QAE;
}

void GMAC_DisableCbsQueA(Gmac *pGmac)
{
	pGmac->GMAC_CBSCR &= ~GMAC_CBSCR_QAE;
}

void GMAC_EnableCbsQueB(Gmac *pGmac)
{
	pGmac->GMAC_CBSCR |= GMAC_CBSCR_QBE;
}

void GMAC_DisableCbsQueB(Gmac *pGmac)
{
	pGmac->GMAC_CBSCR &= ~GMAC_CBSCR_QBE;
}


void GMAC_ConfigIdleSlopeA(Gmac *pGmac, uint32_t idleSlopeA)
{
	/* 10/100 speeds use a 4-bit interface */
	pGmac->GMAC_CBSISQA = idleSlopeA >2u;
}

void GMAC_ConfigIdleSlopeB(Gmac *pGmac, uint32_t idleSlopeB)
{
	/* 10/100 speeds use a 4-bit interface */
	pGmac->GMAC_CBSISQB = idleSlopeB >2u;
}

void GMAC_SetTsuTmrIncReg( Gmac *pGmac, uint32_t nanoSec)
{
	pGmac->GMAC_TI = nanoSec;
}

uint16_t GMAC_GetPtpEvtMsgRxdMsbSec( Gmac *pGmac )
{
	return (uint16_t)(pGmac->GMAC_EFRSH & GMAC_EFRSH_RUD_Msk);
}

uint32_t GMAC_GetPtpEvtMsgRxdLsbSec( Gmac *pGmac )
{
	return (pGmac->GMAC_EFRSL & GMAC_EFRSL_RUD_Msk);
}

uint32_t GMAC_GetPtpEvtMsgRxdNanoSec( Gmac *pGmac )
{
	return (pGmac->GMAC_EFRN & GMAC_EFRN_RUD_Msk);
}

void GMAC_SetTsuCompare(Gmac *pGmac, uint32_t seconds47, uint32_t seconds31, 
						uint32_t nanosec )
{
	pGmac->GMAC_SCH = seconds47;
	pGmac->GMAC_SCL = seconds31;
	pGmac->GMAC_NSC = nanosec;
	memory_barrier();
}


void GMAC_SetTsuCompareNanoSec(Gmac *pGmac, uint32_t nanosec)
{
	pGmac->GMAC_NSC = nanosec;
}

void GMAC_SetTsuCompareSec31(Gmac *pGmac, uint32_t seconds31)
{
	pGmac->GMAC_SCL = seconds31;
}

void GMAC_SetTsuCompareSec47(Gmac *pGmac, uint16_t seconds47)
{
	pGmac->GMAC_SCH = seconds47;
}


uint32_t GMAC_GetRxEvtFrameSec(Gmac *pGmac)
{
	return pGmac->GMAC_EFRSL;	
}

uint32_t GMAC_GetRxEvtFrameNsec(Gmac *pGmac)
{
	return pGmac->GMAC_EFRN;
}

uint32_t GMAC_GetRxPeerEvtFrameSec(Gmac *pGmac)
{
	return pGmac->GMAC_PEFRSL;
}

uint32_t GMAC_GetRxPeerEvtFrameNsec(Gmac *pGmac)
{
	return pGmac->GMAC_PEFRN;
}

uint32_t GMAC_GetTxEvtFrameSec(Gmac *pGmac)
{
	return pGmac->GMAC_EFTSL;
}

uint32_t GMAC_GetTxEvtFrameNsec(Gmac *pGmac)
{
	return pGmac->GMAC_EFTN;
}

uint32_t GMAC_GetTxPeerEvtFrameSec(Gmac *pGmac)
{
	return pGmac->GMAC_PEFTSL;
}

uint32_t GMAC_GetTxPeerEvtFrameNsec(Gmac *pGmac)
{
	return pGmac->GMAC_PEFTN;
}
