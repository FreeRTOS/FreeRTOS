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

/** \addtogroup gmacb_module Ethernet GMACB Driver
 *@{
 *  Implement GEMAC PHY driver, that initialize the PHY to prepare for
 *  Ethernet transfer.
 *
 *  \section Usage
 *  -# EMAC related pins and Driver should be initialized at first.
 *  -# Initialize GMACB Driver instance by invoking GMACB_Init().
 *  -# Initialize PHY connected via GMACB_InitPhy(), PHY address is
 *     automatically adjusted by attempt to read.
 *  -# Perform PHY auto negotiate through GMACB_AutoNegotiate(), so
 *     connection established.
 *
 *
 *  Related files:\n
 *  \ref gmacb.h\n
 *  \ref gmacb.c\n
 *  \ref gmii.h.\n
 *
 */
/**@}*/

#ifndef _GMACB_PHY_H
#define _GMACB_PHY_H


/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include "board.h"

/*---------------------------------------------------------------------------
 *         Definitions
 *---------------------------------------------------------------------------*/

/** The reset length setting for external reset configuration */
#define GMACB_RESET_LENGTH         0xD

/*---------------------------------------------------------------------------
 *         Types
 *---------------------------------------------------------------------------*/
 
 
/** The DM9161 instance */
typedef struct _GMacb {
				/**< Driver */
				sGmacd *pGmacd;
				/** The retry & timeout settings */
				uint32_t retryMax;
				/** PHY address ( pre-defined by pins on reset ) */
				uint8_t phyAddress;
		} GMacb;

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/
extern void GMACB_SetupTimeout(GMacb *pMacb, uint32_t toMax);

extern void GMACB_Init(GMacb *pMacb, sGmacd *pGmacd, uint8_t phyAddress);

extern uint8_t GMACB_InitPhy(
				GMacb *pMacb, 
				uint32_t mck,
				const Pin *pResetPins,
				uint32_t nbResetPins,
				const Pin *pEmacPins,
				uint32_t nbEmacPins);

extern uint8_t GMACB_AutoNegotiate(GMacb *pMacb);

extern uint8_t GMACB_GetLinkSpeed(GMacb *pMacb, uint8_t applySettings);

extern uint8_t GMACB_Send(GMacb *pMacb, void *pBuffer, uint32_t size);

extern uint32_t GMACB_Poll(GMacb *pMacb, uint8_t *pBuffer, uint32_t size);

extern void GMACB_DumpRegisters(GMacb *pMacb);

extern uint8_t GMACB_ResetPhy(GMacb *pMacb);

#endif // #ifndef _GMACB_H

