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

/** \addtogroup macb_module Ethernet MACB Driver
 *@{
 *  Implement EMAC PHY driver, that initialize the PHY to prepare for
 *  ethernet transfer.
 *
 *  \section Usage
 *  -# EMAC related pins and Driver should be initialized at first.
 *  -# MAC address is set via EMAC_SetAddress().
 *  -# Initialize MACB Driver instance by invoking MACB_Init().
 *  -# Initialize PHY connected via MACB_InitPhy(), PHY address is
 *     automatically adjusted by attempt to read.
 *  -# Perform PHY auto negotiate through MACB_AutoNegotiate(), so
 *     connection established.
 *  -# Setup link speed by MACB_GetLinkSpeed() so link speed and
 *     duplex mode is desided.
 *  -# Now its time to send/receive ethernet packets via EMAC Driver
 *     - EMACD_Poll(): Polling received packets.
 *     - EMACD_Send(): Send a packet.
 *
 *  \sa \ref emacd_module
 *
 *  Related files:\n
 *  \ref macb.h\n
 *  \ref macb.c\n
 *  \ref mii.h.\n
 *
 *  \defgroup eth_phy_mii MII/RMII Mode for PHY connection
 *  \defgroup macb_defines MACB Defines
 *  \defgroup macb_structs MACB Structs
 *  \defgroup macb_functions MACB Functions
 */
/**@}*/

#ifndef _MACB_H
#define _MACB_H

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include <board.h>

/*---------------------------------------------------------------------------
 *         Definitions
 *---------------------------------------------------------------------------*/
/** \addtogroup macb_defines
    @{*/

/** The reset length setting for external reset configuration */
#define MACB_RESET_LENGTH         0xD

/** @}*/
/*---------------------------------------------------------------------------
 *         Types
 *---------------------------------------------------------------------------*/
/** \addtogroup macb_structs
    @{*/

/** The DM9161 instance */
typedef struct _Macb {
    sEmacd *pEmacd;     /**< Driver */
    uint32_t retryMax;  /**< The retry & timeout settings */
    uint8_t phyAddress; /**< PHY address ( pre-defined by pins on reset ) */
    uint8_t speed;      /**< 100M/10M speed */
    uint8_t fullDuplex; /**< Full duplex mode */
    uint8_t RMII;       /**< RMII/MII mode */
} Macb;

/** @}*/
/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/
/** \addtogroup macb_functions
    @{*/

extern void MACB_SetupTimeout(Macb *pMacb, uint32_t toMax);

extern void MACB_Init(Macb *pMacb, sEmacd *pEmacd, uint8_t phyAddress);

extern uint8_t MACB_InitPhy(Macb *pMacb, 
                            uint32_t mck,
                            const Pin *pResetPins,
                            uint32_t nbResetPins,
                            const Pin *pEmacPins,
                            uint32_t nbEmacPins);

extern uint8_t MACB_FindValidPhy(Macb * pMacb,uint8_t addrStart);

extern uint8_t MACB_ResetPhy(Macb * pMacb);

extern uint8_t MACB_AutoNegotiate(Macb *pMacb, uint8_t rmiiMode);

extern uint8_t MACB_GetLinkSpeed(Macb *pMacb,
                                 uint8_t applySettings);

extern void MACB_DumpRegisters(Macb * pMacb);

/** @}*/
#endif // #ifndef _MACB_H

