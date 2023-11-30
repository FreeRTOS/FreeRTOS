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

/**
 * \file
 *
 * \section Purpose
 *
 * Interface for configuration the Enhanced Embedded Flash Controller (EEFC) 
 * peripheral.
 *
 * \section Usage
 *
 * -# Enable/disable %flash ready interrupt sources using EFC_EnableFrdyIt()
 *    and EFC_DisableFrdyIt().
 * -# Translates the given address into which EEFC, page and offset values
 *    for difference density %flash memory using EFC_TranslateAddress().
 * -# Computes the address of a %flash access given the EFC, page and offset
 *    for difference density %flash memory using EFC_ComputeAddress().
 * -# Start the executing command with EFC_PerformCommand()
 * -# Retrieve the current status of the EFC using EFC_GetStatus().
 * -# Retrieve the result of the last executed command with EFC_GetResult().
 */

#ifndef _EEFC_
#define _EEFC_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "chip.h"

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/
/* TODO: Temporary definition for missing symbol in header file */
#define IFLASH_SECTOR_SIZE      65536u


/* EFC command */
#define EFC_FCMD_GETD    0x00 /* Get Flash Descriptor */
#define EFC_FCMD_WP      0x01 /* Write page */
#define EFC_FCMD_WPL     0x02 /* Write page and lock */
#define EFC_FCMD_EWP     0x03 /* Erase page and write page */
#define EFC_FCMD_EWPL    0x04 /* Erase page and write page then lock */
#define EFC_FCMD_EA      0x05 /* Erase all */
#define EFC_FCMD_EPA     0x07 /* Erase pages */
#define EFC_FCMD_SLB     0x08 /* Set Lock Bit */
#define EFC_FCMD_CLB     0x09 /* Clear Lock Bit */
#define EFC_FCMD_GLB     0x0A /* Get Lock Bit */
#define EFC_FCMD_SFB     0x0B /* Set GPNVM Bit */
#define EFC_FCMD_CFB     0x0C /* Clear GPNVM Bit */
#define EFC_FCMD_GFB     0x0D /* Get GPNVM Bit */
#define EFC_FCMD_STUI    0x0E /* Start unique ID */
#define EFC_FCMD_SPUI    0x0F /* Stop unique ID */
#define EFC_FCMD_GCALB   0x10 /* Get CALIB Bit */
#define EFC_FCMD_ES      0x11 /* Erase Sector */
#define EFC_FCMD_WUS     0x12 /* Write User Signature */
#define EFC_FCMD_EUS     0x13 /* Erase User Signature */
#define EFC_FCMD_STUS    0x14 /* Start Read User Signature */
#define EFC_FCMD_SPUS    0x15 /* Stop Read User Signature */

/* The IAP function entry addreass */
#define CHIP_FLASH_IAP_ADDRESS  (0x00800008)

#ifdef __cplusplus
 extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern void EFC_EnableFrdyIt( Efc* efc ) ;

extern void EFC_DisableFrdyIt( Efc* efc ) ;

extern void EFC_SetWaitState( Efc* efc, uint8_t cycles ) ;

extern void EFC_TranslateAddress( Efc** pEfc, uint32_t dwAddress, 
		uint16_t *pwPage, uint16_t *pwOffset ) ;

extern void EFC_ComputeAddress( Efc* efc, uint16_t wPage, uint16_t wOffset, 
		uint32_t *pdwAddress ) ;

extern uint32_t EFC_PerformCommand( Efc* efc, uint32_t dwCommand, 
		uint32_t dwArgument, uint32_t dwUseIAP ) ;

extern uint32_t EFC_GetStatus( Efc* efc ) ;

extern uint32_t EFC_GetResult( Efc* efc ) ;

extern void EFC_SetFlashAccessMode(Efc* efc, uint32_t dwMode) ;

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _EEFC_ */

