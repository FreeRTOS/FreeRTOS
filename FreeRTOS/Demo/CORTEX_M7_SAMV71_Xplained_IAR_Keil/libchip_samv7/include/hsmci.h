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

/** \addtogroup hsmci_module Working with HSMCI
 *  \ingroup mcid_module
 *
 * \section Purpose
 *
 * The HSMCI driver provides the interface to configure and use the HSMCI
 * peripheral.
 *
 * \section Usage
 *
 * -# HSMCI_Enable(), MCI_Disable(): Enable/Disable HSMCI interface.
 * -# HSMCI_Reset(): Reset HSMCI interface.
 * -# HSMCI_Select(): HSMCI slot and buswidth selection
 *                    (\ref Hsmci::HSMCI_SDCR).
 * -# HSMCI_ConfigureMode(): Configure the  MCI CLKDIV in the _MR register
 *                           (\ref Hsmci::HSMCI_MR).
 * -# HSMCI_EnableIt(), HSMCI_DisableIt(), HSMCI_GetItMask(), HSMCI_GetStatus()
 *      HSMCI Interrupt control (\ref Hsmci::HSMCI_IER, \ref Hsmci::HSMCI_IDR,
 *      \ref Hsmci::HSMCI_IMR, \ref Hsmci::HSMCI_SR).
 * -# HSMCI_ConfigureTransfer(): Setup block length and count for MCI transfer
 *                               (\ref Hsmci::HSMCI_BLKR).
 * -# HSMCI_SendCmd(): Send SD/MMC command with argument
 *                     (\ref Hsmci::HSMCI_ARGR, \ref Hsmci::HSMCI_CMDR).
 * -# HSMCI_GetResponse(): Get SD/MMC response after command finished
 *                         (\ref Hsmci::HSMCI_RSPR).
 * -# HSMCI_ConfigureDma(): Configure MCI DMA transfer
 *                          (\ref Hsmci::HSMCI_DMA).
 * -# HSMCI_Configure(): Configure the HSMCI interface (\ref Hsmci::HSMCI_CFG).
 * -# HSMCI_HsEnable(), HSMCI_IsHsEnabled(): High Speed control.
 *
 * For more accurate information, please look at the HSMCI section of the
 * Datasheet.
 *
 * \sa \ref mcid_module
 *
 * Related files :\n
 * \ref hsmci.h\n
 * \ref hsmci.c.\n
 */

#ifndef HSMCID_H
#define HSMCID_H
/** \addtogroup hsmci_module
 *@{
 */

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>

/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/
/** \addtogroup hsmci_functions HSMCI Functions
 *      @{
 */

extern void HSMCI_Enable(Hsmci* pRMci);
extern void HSMCI_Disable(Hsmci* pRMci);
extern void HSMCI_Reset(Hsmci* pRMci, uint8_t bBackup);

extern void HSMCI_Select(Hsmci * pRMci,uint8_t bSlot,uint8_t bBusWidth);
extern void HSMCI_SetSlot(Hsmci * pRMci,uint8_t bSlot);
extern void HSMCI_SetBusWidth(Hsmci * pRMci,uint8_t bBusWidth);
extern uint8_t HSMCI_GetBusWidth(Hsmci * pRMci);

extern void HSMCI_ConfigureMode(Hsmci *pRMci, uint32_t dwMode);
extern uint32_t HSMCI_GetMode(Hsmci *pRMci);
extern void HSMCI_ProofEnable(Hsmci *pRMci, uint8_t bRdProof, uint8_t bWrProof);
extern void HSMCI_PadvCtl(Hsmci *pRMci, uint8_t bPadv);
extern void HSMCI_FByteEnable(Hsmci *pRMci, uint8_t bFByteEn);
extern uint8_t HSMCI_IsFByteEnabled(Hsmci * pRMci);
extern void HSMCI_DivCtrl(Hsmci *pRMci, uint32_t bClkDiv, uint8_t bPwsDiv);

extern void HSMCI_EnableIt(Hsmci *pRMci, uint32_t dwSources);
extern void HSMCI_DisableIt(Hsmci *pRMci, uint32_t dwSources);
extern uint32_t HSMCI_GetItMask(Hsmci *pRMci);

extern void HSMCI_ConfigureTransfer(Hsmci * pRMci,uint16_t wBlkLen,uint16_t wCnt);
extern void HSMCI_SetBlockLen(Hsmci * pRMci,uint16_t wBlkSize);
extern void HSMCI_SetBlockCount(Hsmci * pRMci,uint16_t wBlkCnt);

extern void HSMCI_ConfigureCompletionTO(Hsmci *pRMci, uint32_t dwConfigure);
extern void HSMCI_ConfigureDataTO(Hsmci *pRMci, uint32_t dwConfigure);

extern void HSMCI_SendCmd(Hsmci * pRMci,uint32_t dwCmd,uint32_t dwArg);
extern uint32_t HSMCI_GetResponse(Hsmci *pRMci);
extern uint32_t HSMCI_Read(Hsmci *pRMci);
extern void HSMCI_ReadFifo(Hsmci *pRMci, uint8_t *pdwData, uint32_t dwSize);
extern void HSMCI_Write(Hsmci *pRMci, uint32_t dwData);
extern void HSMCI_WriteFifo(Hsmci *pRMci, uint8_t *pdwData, uint32_t dwSize);

extern uint32_t HSMCI_GetStatus(Hsmci *pRMci);

extern void HSMCI_ConfigureDma(Hsmci *pRMci, uint32_t dwConfigure);
extern void HSMCI_EnableDma(Hsmci * pRMci,uint8_t bEnable);

extern void HSMCI_Configure(Hsmci *pRMci, uint32_t dwConfigure);
extern void HSMCI_HsEnable(Hsmci *pRMci, uint8_t bHsEnable);
extern uint8_t HSMCI_IsHsEnabled(Hsmci *pRMci);

extern void HSMCI_BusWidthCtl(Hsmci *pRMci, uint8_t bBusWidth);
extern void HSMCI_SlotCtl(Hsmci *pRMci, uint8_t bSlot);
extern uint8_t HSMCI_GetSlot(Hsmci *pRMci);

extern void HSMCI_ConfigureWP(Hsmci *pRMci, uint32_t dwConfigure);
extern uint32_t HSMCI_GetWPStatus(Hsmci *pRMci);

#ifdef __cplusplus
}
#endif

/**     @}*/
/**@}*/
#endif //#ifndef HSMCID_H

