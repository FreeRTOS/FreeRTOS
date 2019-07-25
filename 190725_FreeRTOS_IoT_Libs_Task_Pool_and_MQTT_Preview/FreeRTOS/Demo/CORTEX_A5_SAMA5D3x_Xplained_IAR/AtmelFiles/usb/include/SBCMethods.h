/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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
 * \section Purpose
 *
 * SCSI commands implementation.
 *
 * section Usage
 *
 * -# After a CBW is received from host, use SBC_GetCommandInformation to check
 *    if the command is supported, and get the command length and type
 *    information before processing it.
 * -# Then SBC_ProcessCommand can be used to handle a valid command, to
 *    perform the command operations.
 * -# SBC_UpdateSenseData is used to update the sense data that will be sent
 *    to host.
 */

#ifndef SBCMETHODS_H
#define SBCMETHODS_H

/** \addtogroup usbd_msd
 *@{
 */

/*------------------------------------------------------------------------------
 *        Headers
 *------------------------------------------------------------------------------*/

#include "SBC.h"
#include "MSDLun.h"
#include "MSDDStateMachine.h"

/*------------------------------------------------------------------------------
 *      Definitions
 *------------------------------------------------------------------------------*/

/** \addtogroup usbd_sbc_command_state SBC Command States
 *      @{
 * This page lists the possible states of a SBC command.
 *
 * \section States
 * - SBC_STATE_READ
 * - SBC_STATE_WAIT_READ
 * - SBC_STATE_WRITE
 * - SBC_STATE_WAIT_WRITE
 * - SBC_STATE_NEXT_BLOCK
 */

/** Start of reading bulk data */
#define SBC_STATE_READ                          0x01
/** Waiting for the bulk data reading complete */
#define SBC_STATE_WAIT_READ                     0x02
/** Read error state */
#define SBC_STATE_READ_ERROR                    0x03
/** Start next read block */
#define SBC_STATE_NEXT_READ                     0x04
/** Start writing bulk data to host */
#define SBC_STATE_WRITE                         0x05
/** Waiting for the bulk data sending complete */
#define SBC_STATE_WAIT_WRITE                    0x06
/** Write error state */
#define SBC_STATE_WRITE_ERROR                   0x07
/** Start next write block */
#define SBC_STATE_NEXT_WRITE                    0x08
/** Start next command block */
#define SBC_STATE_NEXT_BLOCK                    0x09
/**      @}*/

/*------------------------------------------------------------------------------
 *      Exported functions
 *------------------------------------------------------------------------------*/

void SBC_UpdateSenseData(SBCRequestSenseData *requestSenseData,
                         unsigned char senseKey,
                         unsigned char additionalSenseCode,
                         unsigned char additionalSenseCodeQualifier);

unsigned char SBC_GetCommandInformation(void          *command,
                               unsigned int  *length,
                               unsigned char *type,
                               MSDLun         *lun);

unsigned char SBC_ProcessCommand(MSDLun               *lun,
                                 MSDCommandState *commandState);

/**@}*/

#endif /*#ifndef SBCMETHODS_H */


