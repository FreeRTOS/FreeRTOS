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
 * \ingroup sdmmc_hal
 * \addtogroup mcid_module MCI Driver (HAL for SD/MMC Lib)
 *
 * \section Purpose
 *
 * This driver implements SD(IO)/MMC command operations and MCI configuration
 * routines to perform SD(IO)/MMC access. It's used for upper layer
 * (\ref libsdmmc_module "SD/MMC driver") to perform SD/MMC operations.
 *
 * \section Usage
 *
 * -# MCID_Init(): Initializes a MCI driver instance and the underlying
 *                 peripheral.
 * -# MCID_SendCmd(): Starts a MCI transfer which described by
 *                    \ref sSdmmcCommand.
 * -# MCID_CancelCmd(): Cancel a pending command.
 * -# MCID_IsCmdCompleted(): Check if MCI transfer is finished.
 * -# MCID_Handler(): Interrupt handler which is called by ISR handler.
 * -# MCID_IOCtrl(): IO control function to report HW attributes to upper
 *                   layer driver and modify HW settings (such as clock
 *                   frequency, High-speed support, etc. See
 *                   \ref sdmmc_ioctrls).
 *
 * \sa \ref dmad_module "DMA Driver", \ref hsmci_module "HSMCI",
 *     \ref libsdmmc_module "SD/MMC Library"
 *
 * Related files:\n
 * \ref mcid.h\n
 * \ref mcid_dma.c.\n
 */

#ifndef MCID_H
#define MCID_H
/** \addtogroup mcid_module
 *@{
 */

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>
#include <stdio.h>

/** \addtogroup mcid_defines MCI Driver Defines
 *      @{*/

/*----------------------------------------------------------------------------
 *         Constants
 *----------------------------------------------------------------------------*/

/** MCI States */
#define MCID_IDLE   0       /**< Idle */
#define MCID_LOCKED 1       /**< Locked for specific slot */
#define MCID_CMD    2       /**< Processing the command */
#define MCID_ERROR  3       /**< Command error */

/** MCI Initialize clock 400K Hz */
#define MCI_INITIAL_SPEED   400000

/**     @}*/

/*----------------------------------------------------------------------------
 *         Types
 *----------------------------------------------------------------------------*/
/** \addtogroup mcid_structs MCI Driver Data Structs
 *      @{
 */
#ifdef __cplusplus
 extern "C" {
#endif

/**
 *  \brief MCI Driver
 */
typedef struct _Mcid
{
    /** Pointer to a MCI peripheral. */
    Hsmci         *pMciHw;
    /** Pointer to a DMA driver */
    sXdmad         *pXdmad;
    /** Pointer to currently executing command. */
    void          *pCmd;
    /** MCK source, Hz */
    uint32_t       dwMck;
    /** DMA transfer channel */
    uint32_t       dwDmaCh;
    /** DMA transferred data index (bytes) */
    uint32_t       dwXfrNdx;
    /** DMA transfer size (bytes) */
    uint32_t       dwXSize;
    /** MCI peripheral identifier. */
    uint8_t        bID;
    /** Polling mode */
    uint8_t        bPolling;
    /** Reserved */
    uint8_t        reserved;
    /** state. */
    volatile uint8_t bState;
} sMcid;

/**     @}*/
/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/
/** \addtogroup mcid_functions MCI Driver Functions
        @{*/
extern void MCID_Init(sMcid * pMcid,
                      Hsmci * pMci, uint8_t bID, uint32_t dwMck,
                      sXdmad * pXdmad,
                      uint8_t bPolling);

extern void MCID_Reset(sMcid * pMcid);

extern void MCID_SetSlot(Hsmci *pMci, uint8_t slot);

extern uint32_t MCID_Lock(sMcid * pMcid, uint8_t bSlot);

extern uint32_t MCID_Release(sMcid * pMcid);

extern void MCID_Handler(sMcid * pMcid);

extern uint32_t MCID_SendCmd(sMcid * pMcid, void * pCmd);

extern uint32_t MCID_CancelCmd(sMcid * pMcid);

extern uint32_t MCID_IsCmdCompleted(sMcid * pMcid);

extern uint32_t MCID_IOCtrl(sMcid * pMcid,uint32_t bCtl,uint32_t param);

#ifdef __cplusplus
}
#endif
/**     @}*/
/**@}*/
#endif //#ifndef HSMCID_H

