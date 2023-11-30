/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support  -  ROUSSET  -
 * ----------------------------------------------------------------------------
 * Copyright (c) 2006, Atmel Corporation

 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * - Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the disclaimer below in the documentation and/or
 * other materials provided with the distribution.
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

#ifndef MCI_H
#define MCI_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <board.h>

//------------------------------------------------------------------------------
//         Constants
//------------------------------------------------------------------------------

/// Transfer is pending.
#define MCI_STATUS_PENDING      1
/// Transfer has been aborted because an error occured.
#define MCI_STATUS_ERROR        2
/// Card did not answer command.
#define MCI_STATUS_NORESPONSE   3

/// MCI driver is currently in use.
#define MCI_ERROR_LOCK    1

/// MCI configuration with 1-bit data bus on slot A (for MMC cards).
#define MCI_MMC_SLOTA	        0
/// MCI configuration with 1-bit data bus on slot B (for MMC cards).
#define MCI_MMC_SLOTB	        1
/// MCI configuration with 4-bit data bus on slot A (for SD cards).
#define MCI_SD_SLOTA	        AT91C_MCI_SCDBUS
/// MCI configuration with 4-bit data bus on slot B (for SD cards).
#define MCI_SD_SLOTB	        (AT91C_MCI_SCDBUS | 1)

/// Start new data transfer
#define MCI_NEW_TRANSFER        0
/// Continue data transfer
#define MCI_CONTINUE_TRANSFER   1

/// MCI SD Bus Width 1-bit
#define MCI_SDCBUS_1BIT (0 << 7)
/// MCI SD Bus Width 4-bit
#define MCI_SDCBUS_4BIT (1 << 7)

//------------------------------------------------------------------------------
//         Types
//------------------------------------------------------------------------------

/// MCI end-of-transfer callback function.
typedef void (*MciCallback)(unsigned char status, void *pCommand);

//------------------------------------------------------------------------------
/// MCI Transfer Request prepared by the application upper layer. This structure
/// is sent to the MCI_SendCommand function to start the transfer. At the end of 
/// the transfer, the callback is invoked by the interrupt handler.
//------------------------------------------------------------------------------
typedef struct _MciCmd {

    /// Command status.
	volatile char status;
    /// Command code.
	unsigned int cmd;
    /// Command argument.
	unsigned int arg;
    /// Data buffer.
	unsigned char *pData;
    /// Size of data buffer in bytes.
	unsigned short blockSize;
	/// Number of blocks to be transfered
	unsigned short nbBlock;
	/// Indicate if continue to transfer data
	unsigned char conTrans;
    /// Indicates if the command is a read operation.
	unsigned char isRead;
    /// Response buffer.
    unsigned int  *pResp;
    /// Size of SD card response in bytes.
	unsigned char  resSize;
	/// Optional user-provided callback function.
	MciCallback callback;
    /// Optional argument to the callback function.
	void *pArg;

} MciCmd;

//------------------------------------------------------------------------------
/// MCI driver structure. Holds the internal state of the MCI driver and
/// prevents parallel access to a MCI peripheral.
//------------------------------------------------------------------------------
typedef struct {

    /// Pointer to a MCI peripheral.
	AT91S_MCI *pMciHw;
    /// MCI peripheral identifier.
    unsigned char mciId;
    /// Pointer to currently executing command.
	MciCmd *pCommand;
	/// Mutex.
	volatile char semaphore;

} Mci;

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void MCI_Init(
    Mci *pMci,
    AT91PS_MCI pMciHw,
    unsigned char mciId,
    unsigned int mode);

extern void MCI_SetSpeed(Mci *pMci, unsigned int mciSpeed);

extern unsigned char MCI_SendCommand(Mci *pMci, MciCmd *pMciCmd);

extern void MCI_Handler(Mci *pMci);

extern unsigned char MCI_IsTxComplete(MciCmd *pMciCmd);

extern unsigned char MCI_CheckBusy(Mci *pMci);

extern void MCI_Close(Mci *pMci);

extern void MCI_SetBusWidth(Mci *pMci, unsigned char busWidth);

#endif //#ifndef MCI_H

