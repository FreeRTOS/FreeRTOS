/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2010, Atmel Corporation
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
 * Interface for the S25fl1 SPI driver.
 *
 */

#ifndef S25FL1_SPI_H
#define S25FL1_SPI_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include <board.h>

/*----------------------------------------------------------------------------
 *        Macros
 *----------------------------------------------------------------------------*/

#define S25FL1_Size(pS25fl1)            ((pS25fl1)->pDesc->size)
#define S25FL1_PageSize(pS25fl1)        ((pS25fl1)->pDesc->pageSize)
#define S25FL1_BlockSize(pS25fl1)       ((pS25fl1)->pDesc->blockSize)
#define S25FL1_Name(pS25fl1)            ((pS25fl1)->pDesc->name)
#define S25FL1_ManId(pS25fl1)           (((pS25fl1)->pDesc->jedecId) & 0xFF)
#define S25FL1_PageNumber(pS25fl1)      (S25FL1_Size(pS25FL1) / S25FL1_PageSize(pS25fl1))
#define S25FL1_BlockNumber(pS25fl1)     (S25FL1_Size(pS25fl1) / S25FL1_BlockSize(pS25fl1))
#define S25FL1_PagePerBlock(pS25fl1)    (S25FL1_BlockSize(pS25fl1) / S25FL1_PageSize(pS25fl1))
#define S25FL1_BlockEraseCmd(pS25fl1)   ((pS25fl1)->pDesc->blockEraseCmd)

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/

/** Device is protected, operation cannot be carried out. */
#define S25FL1_ERROR_PROTECTED        1
/** Device is busy executing a command. */
#define S25FL1_ERROR_BUSY             2
/** There was a problem while trying to program page data. */
#define S25FL1_ERROR_PROGRAM          3
/** There was an SPI communication error. */
#define S25FL1_ERROR_SPI              4

/** Device ready/busy status bit. */
#define S25FL1_STATUS_RDYBSY          (1 << 0)
/** Device is ready. */
#define S25FL1_STATUS_RDYBSY_READY    (0 << 0)
/** Device is busy with internal operations. */
#define S25FL1_STATUS_RDYBSY_BUSY     (1 << 0)
/** Write enable latch status bit. */
#define S25FL1_STATUS_WEL             (1 << 1)
/** Device is not write enabled. */
#define S25FL1_STATUS_WEL_DISABLED    (0 << 1)
/** Device is write enabled. */
#define S25FL1_STATUS_WEL_ENABLED     (1 << 1)
/** Software protection status bitfield. */
#define S25FL1_STATUS_SWP             (3 << 2)
/** All sectors are software protected. */
#define S25FL1_STATUS_SWP_PROTALL     (3 << 2)
/** Some sectors are software protected. */
#define S25FL1_STATUS_SWP_PROTSOME    (1 << 2)
/** No sector is software protected. */
#define S25FL1_STATUS_SWP_PROTNONE    (0 << 2)
/** Write protect pin status bit. */
#define S25FL1_STATUS_WPP             (1 << 4)
/** Write protect signal is not asserted. */
#define S25FL1_STATUS_WPP_NOTASSERTED (0 << 4)
/** Write protect signal is asserted. */
#define S25FL1_STATUS_WPP_ASSERTED    (1 << 4)
/** Erase/program error bit. */
#define S25FL1_STATUS_EPE             (1 << 5)
/** Erase or program operation was successful. */
#define S25FL1_STATUS_EPE_SUCCESS     (0 << 5)
/** Erase or program error detected. */
#define S25FL1_STATUS_EPE_ERROR       (1 << 5)
/** Sector protection registers locked bit. */
#define S25FL1_STATUS_SPRL            (1 << 7)
/** Sector protection registers are unlocked. */
#define S25FL1_STATUS_SPRL_UNLOCKED   (0 << 7)
/** Sector protection registers are locked. */
#define S25FL1_STATUS_SPRL_LOCKED     (1 << 7)

/** Read array command code. */
#define S25FL1_READ_ARRAY             0x0B
/** Read array (low frequency) command code. */
#define S25FL1_READ_ARRAY_LF          0x03
/** Block erase command code (4K block). */
#define S25FL1_BLOCK_ERASE_4K         0x20
/** Block erase command code (32K block). */
#define S25FL1_BLOCK_ERASE_32K        0x52
/** Block erase command code (64K block). */
#define S25FL1_BLOCK_ERASE_64K        0xD8
/** Chip erase command code 1. */
#define S25FL1_CHIP_ERASE_1           0x60
/** Chip erase command code 2. */
#define S25FL1_CHIP_ERASE_2           0xC7
/** Byte/page program command code. */
#define S25FL1_BYTE_PAGE_PROGRAM      0x02
/** Sequential program mode command code 1. */
#define S25FL1_SEQUENTIAL_PROGRAM_1   0xAD
/** Sequential program mode command code 2. */
#define S25FL1_SEQUENTIAL_PROGRAM_2   0xAF
/** Write enable command code. */
#define S25FL1_WRITE_ENABLE           0x06
/** Write disable command code. */
#define S25FL1_WRITE_DISABLE          0x04
/** Protect sector command code. */
#define S25FL1_PROTECT_SECTOR         0x36
/** Unprotect sector command code. */
#define S25FL1_UNPROTECT_SECTOR       0x39
/** Read sector protection registers command code. */
#define S25FL1_READ_SECTOR_PROT       0x3C
/** Read status register command code. */
#define S25FL1_READ_STATUS            0x05
/** Write status register command code. */
#define S25FL1_WRITE_STATUS           0x01
/** Read manufacturer and device ID command code. */
#define S25FL1_READ_JEDEC_ID          0x9F
/** Deep power-down command code. */
#define S25FL1_DEEP_PDOWN             0xB9
/** Resume from deep power-down command code. */
#define S25FL1_RES_DEEP_PDOWN         0xAB

/* Enter 4-BYTE ADDRESS mode  */
#define S25FL1_ENTER_4ADDR_MODE       0xB7
/* Exit 4-BYTE ADDRESS mode  */
#define S25FL1_EXIT_4ADDR_MODE        0xE9

/** SPI Flash Manufacturer JEDEC ID */
#define ATMEL_SPI_FLASH             0x1F
#define ST_SPI_FLASH                0x20
#define WINBOND_SPI_FLASH           0xEF
#define MACRONIX_SPI_FLASH          0xC2
#define SST_SPI_FLASH               0xBF

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** Describes a serial firmware flash device parameters. */
typedef struct _S25fl1Desc {

    /** Device string name. */
    const char *name;
    /** JEDEC ID of device. */
    uint32_t jedecId;
    /** Size of device in bytes. */
    uint32_t size;
    /** Size of one page in bytes. */
    uint32_t pageSize;
    /** Block erase size in bytes. */
    uint32_t blockSize;
    /** Block erase command. */
    uint32_t blockEraseCmd;

} S25fl1Desc;

/**
 * Serial flash driver structure. Holds the current state of the driver,
 * including the current command and the descriptor for the underlying device.
 */
typedef struct _S25fl1 {

    /** Pointer to the underlying QSPI driver. */
    Qspid *pQspid;
    /** Current command sent to the QSPI driver. */
    QspidCmd command;
    /** Pointer to a descriptor for the serial firmware flash device. */
    const S25fl1Desc *pDesc;
    /** Qspi Command buffer. */
    qspiFrame CmdBuffer;
    /** Polling mode */
    uint32_t pollingMode;
    /** Support for 4 byte address mode */
    uint32_t fourbytemode;
} S25fl1;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern void S25fl1_Configure(S25fl1 *pS25fl1,
                           Qspid *pQspid,
                           uint8_t cs,
                           uint8_t polling);

extern uint8_t S25fl1_SendCommand(
    S25fl1 *pS25fl1,
    uint8_t cmd,
    uint8_t cmdSize,
    uint8_t *pData,
    uint32_t dataSize,
    uint32_t address,
    QspidCallback callback,
    void *pArgument);

extern uint8_t S25fl1_IsBusy(S25fl1 *pS25fl1);

extern const S25fl1Desc * S25fl1_FindDevice(
    S25fl1 *pS25fl1,
    uint32_t jedecId);

#endif /*#ifndef S25FL1_SPI_H */

