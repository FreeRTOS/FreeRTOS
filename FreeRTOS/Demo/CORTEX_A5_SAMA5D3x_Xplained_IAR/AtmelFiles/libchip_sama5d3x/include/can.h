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

/** \file
 *  Definitions and prototypes for Controller Area Network (CAN)
 *  peripheral operations.
 */

/** \ingroup lib_chip
 *  \ingroup cand_module
 *  \addtogroup can_module Working with CAN
 *
 *  \section Purpose
 *  Interface for Controller Area Network (CAN).
 *
 *  \section Usage
 *
 *  Before CAN operation, its peripheral clock should be enabled, see
 *  PMC_EnablePeripheral().
 *
 *  Modify CAN registers or register fields with API functions:
 *  - Modify CAN Mode register with CAN_ConfigureMode().
 *    - Enable/Disable CAN with CAN_Enable().
 *  - Change CAN interrupt settings with CAN_EnableIt(), CAN_DisableIt(),
 *    get interrupt mask by CAN_GetItMask().
 *  - Get CAN status with CAN_GetStatus().
 *  - Setup CAN baudrate via CAN_CalcBaudrate().
 *  - Start several mailbox transmition through CAN_Command().
 *  - The following functions setup mailboxes for message transfer:
 *    - CAN_ConfigureMessageMode() : setup _MMRx.
 *    - CAN_ConfigureMessageAcceptanceMask() : setup _MARx.
 *    - CAN_ConfigureMessageID() : setup _MIDx.
 *    - CAN_SetMessage() : setup _MDLx and _MDHx.
 *    - CAN_MessageControl() : setup _MCRx.
 *  - The following get status and data from mailbox:
 *    - CAN_GetMessage() : 
 *    - CAN_GetMessageStatus() : 
 */

#ifndef _CAN_H_
#define _CAN_H_
/**@{*/

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** Number of mailboxes in a CAN controller */
#define CAN_NUM_MAILBOX     8

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

void CAN_ConfigureMode(Can * pCan,uint32_t dwMr);
void CAN_Enable(Can * pCan,uint8_t bEnDis);
void CAN_EnableLowPower(Can * pCan,uint8_t bEnDis);
void CAN_EnableAutobaud(Can * pCan,uint8_t bEnDis);
void CAN_EnableOverloadFrame(Can * pCan,uint8_t bEnDis);
void CAN_EnableTimeStampEof(Can * pCan,uint8_t bEofSof);
void CAN_EnableTimeTriggerMode(Can * pCan,uint8_t bEnDis);
void CAN_EnableTimerFreeze(Can * pCan,uint8_t bEnDis);
void CAN_DisableRepeat(Can * pCan,uint8_t bDisEn);

void CAN_EnableIt(Can * pCan,uint32_t dwSources);
void CAN_DisableIt(Can * pCan,uint32_t dwSources);
uint32_t CAN_GetItMask(Can * pCan);
uint32_t CAN_GetStatus(Can * pCan);

uint8_t CAN_CalcBaudrate(Can * pCan, uint32_t dwBaud, uint32_t dwMck);
void CAN_ConfigureBaudrate(Can * pCan,uint32_t dwBr);
void CAN_SetSamplingMode(Can * pCan,uint8_t bAvg3);

uint32_t CAN_GetTimer(Can * pCan);
uint32_t CAN_GetTimestamp(Can * pCan);

uint32_t CAN_GetErrorCount(Can * pCan);
uint32_t CAN_GetRxErrorCount(Can * pCan);
uint32_t CAN_GetTxErrorCount(Can * pCan);

void CAN_Command(Can * pCan,uint32_t dwRequests);
void CAN_ResetTimer(Can * pCan);
void CAN_Tx(Can * pCan,uint8_t bMb);

void CAN_Abort(Can * pCan,uint32_t dwAborts);
void CAN_AbortMailbox(Can * pCan,uint8_t bMb);

void CAN_ConfigureMessageMode(Can * pCan,uint8_t bMb,uint32_t dwMr);
uint32_t CAN_GetMessageMode(Can * pCan,uint8_t bMb);
void CAN_SetTimemark(Can * pCan,uint8_t bMb,uint8_t bTimemarks);
void CAN_SetPriority(Can * pCan,uint8_t bMb,uint8_t bPriority);
void CAN_SetObjectType(Can * pCan,uint8_t bMb,uint8_t bType);

void CAN_ConfigureMessageAcceptanceMask(Can * pCan,uint8_t bMb,uint32_t dwMAM);
uint32_t CAN_GetMessageAcceptanceMask(Can * pCan,uint8_t bMb);
void CAN_ConfigureIdentifierMask(Can * pCan,uint8_t bMb,uint8_t bIdCfg);
void CAN_SetMIDvAMask(Can * pCan,uint8_t bMb,uint32_t dwIDvA);
void CAN_SetMIDvBMask(Can * pCan,uint8_t bMb,uint32_t dwIDvA);

void CAN_ConfigureMessageID(Can * pCan,uint8_t bMb,uint32_t dwMID);
uint32_t CAN_GetMessageID(Can * pCan,uint8_t bMb);
void CAN_ConfigureIdVer(Can * pCan,uint8_t bMb,uint8_t bIdVer);
void CAN_SetMIDvA(Can * pCan,uint8_t bMb,uint32_t dwIDvA);
void CAN_SetMIDvB(Can * pCan,uint8_t bMb,uint32_t dwIDvA);

uint32_t CAN_GetFamilyID(Can * pCan,uint8_t bMb);

uint32_t CAN_GetMessageStatus(Can * pCan,uint8_t bMb);

void CAN_SetMessageDataL(Can * pCan,uint8_t bMb,uint32_t dwL);
uint32_t CAN_GetMessageDataL(Can * pCan,uint8_t bMb);
void CAN_SetMessageDataH(Can * pCan,uint8_t bMb,uint32_t dwH);
uint32_t CAN_GetMessageDataH(Can * pCan,uint8_t bMb);
void CAN_SetMessage(Can * pCan,uint8_t bMb,uint32_t * pDwData);
void CAN_GetMessage(Can * pCan,uint8_t bMb,uint32_t * pDwData);
void CAN_SetMessageData64(Can * pCan,uint8_t bMb,uint64_t u64);
uint64_t CAN_GetMessageData64(Can * pCan,uint8_t bMb);

void CAN_MessageControl(Can * pCan,uint8_t bMb,uint32_t dwCtrl);
void CAN_MessageRemote(Can * pCan,uint8_t bMb);
void CAN_MessageAbort(Can * pCan,uint8_t bMb);
void CAN_MessageTx(Can * pCan,uint8_t bMb,uint8_t bLen);
void CAN_MessageRx(Can * pCan,uint8_t bMb);

/**@}*/
#endif /* #ifndef _CAN_H_ */
