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
 * Interface for the AT25 SPI driver.
 *
 */

#ifndef AT25_SPI_H
#define AT25_SPI_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include <board.h>

/*----------------------------------------------------------------------------
 *        Macros
 *----------------------------------------------------------------------------*/

#define AT25_Size(pAt25)            ((pAt25)->pDesc->size)
#define AT25_PageSize(pAt25)        ((pAt25)->pDesc->pageSize)
#define AT25_BlockSize(pAt25)       ((pAt25)->pDesc->blockSize)
#define AT25_Name(pAt25)            ((pAt25)->pDesc->name)
#define AT25_ManId(pAt25)           (((pAt25)->pDesc->jedecId) & 0xFF)
#define AT25_PageNumber(pAt25)      (AT25_Size(pAt25) / AT25_PageSize(pAt25))
#define AT25_BlockNumber(pAt25)     (AT25_Size(pAt25) / AT25_BlockSize(pAt25))
#define AT25_PagePerBlock(pAt25)    (AT25_BlockSize(pAt25) / AT25_PageSize(pAt25))
#define AT25_BlockEraseCmd(pAt25)   ((pAt25)->pDesc->blockEraseCmd)

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/

/** Device is protected, operation cannot be carried out. */
#define AT25_ERROR_PROTECTED        1
/** Device is busy executing a command. */
#define AT25_ERROR_BUSY             2
/** There was a problem while trying to program page data. */
#define AT25_ERROR_PROGRAM          3
/** There was an SPI communication error. */
#define AT25_ERROR_SPI              4

/** Device ready/busy status bit. */
#define AT25_STATUS_RDYBSY          (1 << 0)
/** Device is ready. */
#define AT25_STATUS_RDYBSY_READY    (0 << 0)
/** Device is busy with internal operations. */
#define AT25_STATUS_RDYBSY_BUSY     (1 << 0)
/** Write enable latch status bit. */
#define AT25_STATUS_WEL             (1 << 1)
/** Device is not write enabled. */
#define AT25_STATUS_WEL_DISABLED    (0 << 1)
/** Device is write enabled. */
#define AT25_STATUS_WEL_ENABLED     (1 << 1)
/** Software protection status bitfield. */
#define AT25_STATUS_SWP             (3 << 2)
/** All sectors are software protected. */
#define AT25_STATUS_SWP_PROTALL     (3 << 2)
/** Some sectors are software protected. */
#define AT25_STATUS_SWP_PROTSOME    (1 << 2)
/** No sector is software protected. */
#define AT25_STATUS_SWP_PROTNONE    (0 << 2)
/** Write protect pin status bit. */
#define AT25_STATUS_WPP             (1 << 4)
/** Write protect signal is not asserted. */
#define AT25_STATUS_WPP_NOTASSERTED (0 << 4)
/** Write protect signal is asserted. */
#define AT25_STATUS_WPP_ASSERTED    (1 << 4)
/** Erase/program error bit. */
#define AT25_STATUS_EPE             (1 << 5)
/** Erase or program operation was successful. */
#define AT25_STATUS_EPE_SUCCESS     (0 << 5)
/** Erase or program error detected. */
#define AT25_STATUS_EPE_ERROR       (1 << 5)
/** Sector protection registers locked bit. */
#define AT25_STATUS_SPRL            (1 << 7)
/** Sector protection registers are unlocked. */
#define AT25_STATUS_SPRL_UNLOCKED   (0 << 7)
/** Sector protection registers are locked. */
#define AT25_STATUS_SPRL_LOCKED     (1 << 7)

/** Read array command code. */
#define AT25_READ_ARRAY             0x0B
/** Read array (low frequency) command code. */
#define AT25_READ_ARRAY_LF          0x03
/** Block erase command code (4K block). */
#define AT25_BLOCK_ERASE_4K         0x20
/** Block erase command code (32K block). */
#define AT25_BLOCK_ERASE_32K        0x52
/** Block erase command code (64K block). */
#define AT25_BLOCK_ERASE_64K        0xD8
/** Chip erase command code 1. */
#define AT25_CHIP_ERASE_1           0x60
/** Chip erase command code 2. */
#define AT25_CHIP_ERASE_2           0xC7
/** Byte/page program command code. */
#define AT25_BYTE_PAGE_PROGRAM      0x02
/** Sequential program mode command code 1. */
#define AT25_SEQUENTIAL_PROGRAM_1   0xAD
/** Sequential program mode command code 2. */
#define AT25_SEQUENTIAL_PROGRAM_2   0xAF
/** Write enable command code. */
#define AT25_WRITE_ENABLE           0x06
/** Write disable command code. */
#define AT25_WRITE_DISABLE          0x04
/** Protect sector command code. */
#define AT25_PROTECT_SECTOR         0x36
/** Unprotect sector command code. */
#define AT25_UNPROTECT_SECTOR       0x39
/** Read sector protection registers command code. */
#define AT25_READ_SECTOR_PROT       0x3C
/** Read status register command code. */
#define AT25_READ_STATUS            0x05
/** Write status register command code. */
#define AT25_WRITE_STATUS           0x01
/** Read manufacturer and device ID command code. */
#define AT25_READ_JEDEC_ID          0x9F
/** Deep power-down command code. */
#define AT25_DEEP_PDOWN             0xB9
/** Resume from deep power-down command code. */
#define AT25_RES_DEEP_PDOWN         0xAB


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
typedef struct _At25Desc {

    /** Device string name. */
    const char *name;
    /** JEDEC ID of device. */
    unsigned int jedecId;
    /** Size of device in bytes. */
    unsigned int size;
    /** Size of one page in bytes. */
    unsigned int pageSize;
    /** Block erase size in bytes. */
    unsigned int blockSize;
    /** Block erase command. */
    unsigned int blockEraseCmd;

} At25Desc;

/**
 * Serial flash driver structure. Holds the current state of the driver,
 * including the current command and the descriptor for the underlying device.
 */
typedef struct _At25 {

    /** Pointer to the underlying SPI driver. */
    Spid *pSpid;
    /** Current SPI command sent to the SPI driver. */
    SpidCmd command;
    /** Pointer to a descriptor for the serial firmware flash device. */
    const At25Desc *pDesc;
    /** Command buffer. */
    unsigned int pCmdBuffer[2];

} At25;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern void AT25_Configure(At25 *pAt25, Spid *pSpid, unsigned char cs);

extern unsigned char AT25_SendCommand(
    At25 *pAt25,
    unsigned char cmd,
    unsigned char cmdSize,
    unsigned char *pData,
    unsigned int dataSize,
    unsigned int address,
    SpidCallback callback,
    void *pArgument);

extern unsigned char AT25_IsBusy(At25 *pAt25);

extern const At25Desc * AT25_FindDevice(
    At25 *pAt25,
    unsigned int jedecId);

#endif /*#ifndef AT25_SPI_H */

