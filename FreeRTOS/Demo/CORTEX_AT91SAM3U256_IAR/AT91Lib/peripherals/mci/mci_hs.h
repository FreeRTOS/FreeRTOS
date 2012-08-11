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

//------------------------------------------------------------------------------
/// \page "mci"
///
/// !Purpose
///  
/// mci-interface driver
///
/// !Usage
///
/// -# MCI_Init: Initializes a MCI driver instance and the underlying peripheral.
/// -# MCI_SetSpeed : Configure the  MCI CLKDIV in the MCI_MR register.
/// -# MCI_SendCommand: Starts a MCI  transfer.
/// -# MCI_Handler : Interrupt handler which is called by ISR handler.
/// -# MCI_SetBusWidth : Configure the  MCI SDCBUS in the MCI_SDCR register.
//------------------------------------------------------------------------------


#ifndef MCI_HS_H
#define MCI_HS_H

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
#define MCI_MMC_SLOTA           (AT91C_MCI_SCDSEL_SLOTA | AT91C_MCI_SCDBUS_1BIT)
/// MCI configuration with 4-bit data bus on slot A (for SD cards).
#define MCI_SD_SLOTA            (AT91C_MCI_SCDSEL_SLOTA | AT91C_MCI_SCDBUS_4BITS)
#ifdef AT91C_MCI_SCDBUS_8BITS
/// MCI configuration with 1-bit data bus on slot A (for MMC cards).
#define MCI_MMC4_SLOTA          (AT91C_MCI_SCDSEL_SLOTA | AT91C_MCI_SCDBUS_8BITS)
#endif
#ifdef AT91C_MCI_SCDSEL_SLOTB
/// MCI configuration with 1-bit data bus on slot B (for MMC cards).
#define MCI_MMC_SLOTB           (AT91C_MCI_SCDSEL_SLOTB | AT91C_MCI_SCDBUS_1BIT)
/// MCI configuration with 4-bit data bus on slot B (for SD cards).
#define MCI_SD_SLOTB            (AT91C_MCI_SCDSEL_SLOTB | AT91C_MCI_SCDBUS_4BITS)
#ifdef AT91C_MCI_SCDBUS_8BITS
/// MCI configuration with 1-bit data bus on slot A (for MMC cards).
#define MCI_MMC4_SLOTB          (AT91C_MCI_SCDSEL_SLOTB | AT91C_MCI_SCDBUS_8BITS)
#endif
#else
#define MCI_MMC_SLOTB           MCI_MMC_SLOTA
#define MCI_SD_SLOTB            MCI_SD_SLOTA
#endif

/// Start new data transfer
#define MCI_NEW_TRANSFER        0
/// Continue data transfer
#define MCI_CONTINUE_TRANSFER   1
/// Stop data transfer
#define MCI_STOP_TRANSFER       2

/// MCI SD Bus Width 1-bit
#define MCI_SDCBUS_1BIT (0 << 7)
/// MCI SD Bus Width 4-bit
#define MCI_SDCBUS_4BIT (1 << 7)
/// MCI SD Bus Width 8-bit
#define MCI_SDCBUS_8BIT (3 << 6)

/// The MCI Clock Speed after initialize (400K)
#define MCI_INITIAL_SPEED       400000

/// MCI using DMA?
#define MCI_DMA_ENABLE          1

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

    /// Command code.
    unsigned int cmd;
    /// Command argument.
    unsigned int arg;
    /// Data buffer.
    unsigned char *pData;
    /// Size of data block in bytes.
    unsigned short blockSize;
    /// Number of blocks to be transfered
    unsigned short nbBlock;
    /// Response buffer.
    unsigned int  *pResp;
    /// Optional user-provided callback function.
    MciCallback callback;
    /// Optional argument to the callback function.
    void *pArg;
    /// SD card response type.
    unsigned char  resType;
    /// Indicate if there is data transfer
    unsigned char dataTran;
    /// Indicate if continue to transfer data
    unsigned char tranType;
    /// Indicates if the command is a read operation.
    unsigned char isRead;

    /// Command status.
    volatile int status;
} MciCmd;

//------------------------------------------------------------------------------
/// MCI driver structure. Holds the internal state of the MCI driver and
/// prevents parallel access to a MCI peripheral.
//------------------------------------------------------------------------------
typedef struct {

    /// Pointer to a MCI peripheral.
    AT91S_MCI *pMciHw;
    /// Pointer to currently executing command.
    MciCmd *pCommand;
    /// MCI peripheral identifier.
    unsigned char mciId;
    /// MCI HW mode
    unsigned char mciMode;
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
extern unsigned int MCI_GetSpeed(Mci *pMci, unsigned int *mciDiv);

extern unsigned int MCI_SetSpeed(Mci *pMci,
                                 unsigned int mciSpeed,
                                 unsigned int mciLimit);

extern unsigned char MCI_SendCommand(Mci *pMci, MciCmd *pMciCmd);

extern void MCI_Handler(Mci *pMci);

extern unsigned char MCI_IsTxComplete(MciCmd *pMciCmd);

extern unsigned char MCI_CheckBusy(Mci *pMci);

extern void MCI_Close(Mci *pMci);

extern void MCI_EnableHsMode(Mci * pMci, unsigned char hsEnable);

extern void MCI_SetBusWidth(Mci *pMci, unsigned char busWidth);

extern unsigned int MCI_FifoTransfer(Mci * pMci, MciCmd * pCommand);

#endif //#ifndef MCI_HS_H

