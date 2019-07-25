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

/**
 * \file
 *
 * Interface for the S25fl1 Serial Flash driver.
 *
 */

#ifndef S25FL1_H
#define S25FL1_H
#define USE_QSPI_DMA
/*----------------------------------------------------------------------------
 *        Macros
 *----------------------------------------------------------------------------*/

#define Size(pAt25)            ((pAt25)->pDesc->size)
#define PageSize(pAt25)        ((pAt25)->pDesc->pageSize)
#define BlockSize(pAt25)       ((pAt25)->pDesc->blockSize)
#define Name(pAt25)            ((pAt25)->pDesc->name)
#define ManId(pAt25)           (((pAt25)->pDesc->jedecId) & 0xFF)
#define PageNumber(pAt25)      (Size(pAt25) / PageSize(pAt25))
#define BlockNumber(pAt25)     (Size(pAt25) / BlockSize(pAt25))
#define PagePerBlock(pAt25)    (BlockSize(pAt25) / PageSize(pAt25))
#define BlockEraseCmd(pAt25)   ((pAt25)->pDesc->blockEraseCmd)

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/

/** Device is protected, operation cannot be carried out. */
#define ERROR_PROTECTED        1
/** Device is busy executing a command. */
#define ERROR_BUSY             2
/** There was a problem while trying to program page data. */
#define ERROR_PROGRAM          3
/** There was an SPI communication error. */
#define ERROR_SPI              4

/** Device ready/busy status bit. */
#define STATUS_RDYBSY          (1 << 0)
/** Device is ready. */
#define STATUS_RDYBSY_READY    (0 << 0)
/** Device is busy with internal operations. */
#define STATUS_RDYBSY_BUSY     (1 << 0)
/** Write enable latch status bit. */
#define STATUS_WEL             (1 << 1)
/** Device is not write enabled. */
#define STATUS_WEL_DISABLED    (0 << 1)
/** Device is write enabled. */
#define STATUS_WEL_ENABLED     (1 << 1)
/** Software protection status bit-field. */
#define STATUS_SWP             (3 << 2)
/** All sectors are software protected. */
#define STATUS_SWP_PROTALL     (3 << 2)
/** Some sectors are software protected. */
#define STATUS_SWP_PROTSOME    (1 << 2)
/** No sector is software protected. */
#define STATUS_SWP_PROTNONE    (0 << 2)
/** Write protect pin status bit. */
#define STATUS_WPP             (1 << 4)
/** Write protect signal is not asserted. */
#define STATUS_WPP_NOTASSERTED (0 << 4)
/** Write protect signal is asserted. */
#define STATUS_WPP_ASSERTED    (1 << 4)
/** Erase/program error bit. */
#define STATUS_EPE             (1 << 5)
/** Erase or program operation was successful. */
#define STATUS_EPE_SUCCESS     (0 << 5)
/** Erase or program error detected. */
#define STATUS_EPE_ERROR       (1 << 5)
/** Sector protection registers locked bit. */
#define STATUS_SPRL            (1 << 7)
/** Sector protection registers are unlocked. */
#define STATUS_SPRL_UNLOCKED   (0 << 7)
/** Sector protection registers are locked. */
#define STATUS_SPRL_LOCKED     (1 << 7)
   
/** Quad enable bit */
#define STATUS_QUAD_ENABLE     (1 << 1)
   /** Quad enable bit */
#define STATUS_WRAP_ENABLE     (0 << 4)
   
   /** Latency control bits */
#define STATUS_LATENCY_CTRL    (0xF << 0)   
   
#define STATUS_WRAP_BYTE       (1 << 5)
   
#define BLOCK_PROTECT_Msk      (7 << 2)
   
#define TOP_BTM_PROTECT_Msk    (1 << 5)
   
#define SEC_PROTECT_Msk        (1 << 6)   
   
#define CHIP_PROTECT_Msk       (0x1F << 2)    

/** Read array command code. */
#define READ_ARRAY             0x0B
/** Read array (low frequency) command code. */
#define READ_ARRAY_LF          0x03
/** Fast Read array  command code. */
#define READ_ARRAY_DUAL        0x3B
/** Fast Read array  command code. */
#define READ_ARRAY_QUAD        0x6B   
/** Fast Read array  command code. */
#define READ_ARRAY_DUAL_IO     0xBB
/** Fast Read array  command code. */
#define READ_ARRAY_QUAD_IO     0xEB   
/** Block erase command code (4K block). */
#define BLOCK_ERASE_4K         0x20
/** Block erase command code (32K block). */
#define BLOCK_ERASE_32K        0x52
/** Block erase command code (64K block). */
#define BLOCK_ERASE_64K        0xD8
/** Chip erase command code 1. */
#define CHIP_ERASE_1           0x60
/** Chip erase command code 2. */
#define CHIP_ERASE_2           0xC7
/** Byte/page program command code. */
#define BYTE_PAGE_PROGRAM      0x02
/** Sequential program mode command code 1. */
#define SEQUENTIAL_PROGRAM_1   0xAD
/** Sequential program mode command code 2. */
#define SEQUENTIAL_PROGRAM_2   0xAF
/** Write enable command code. */
#define WRITE_ENABLE           0x06
/** Write disable command code. */
#define WRITE_DISABLE          0x04
/** Protect sector command code. */
#define PROTECT_SECTOR         0x36
/** Unprotected sector command code. */
#define UNPROTECT_SECTOR       0x39
/** Read sector protection registers command code. */
#define READ_SECTOR_PROT       0x3C
/** Read status register command code. */
#define READ_STATUS_1          0x05
   /** Read status register command code. */
#define READ_STATUS_2          0x35
   /** Read status register command code. */
#define READ_STATUS_3          0x33
/** Write status register command code. */
#define WRITE_STATUS           0x01
/** Read manufacturer and device ID command code. */
#define READ_JEDEC_ID          0x9F
/** Deep power-down command code. */
#define DEEP_PDOWN             0xB9
/** Resume from deep power-down command code. */
#define RES_DEEP_PDOWN         0xAB
/** Resume from deep power-down command code. */
#define SOFT_RESET_ENABLE      0x66
/** Resume from deep power-down command code. */
#define SOFT_RESET             0x99
/** Resume from deep power-down command code. */
#define WRAP_ENABLE            0x77

/** SPI Flash Manufacturer JEDEC ID */
#define ATMEL_SPI_FLASH             0x1F
#define ST_SPI_FLASH                0x20
#define WINBOND_SPI_FLASH           0xEF
#define MACRONIX_SPI_FLASH          0xC2
#define SST_SPI_FLASH               0xBF

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

uint32_t S25FL1D_ReadJedecId(void);

void S25FL1D_InitFlashInterface(uint8_t Mode);

void S25FL1D_SoftReset(void);

unsigned char S25FL1D_Unprotect(void);

unsigned char S25FL1D_Protect(uint32_t StartAddr, uint32_t Size);

void S25FL1D_QuadMode(uint8_t Enable);

void S25FL1D_EnableWrap(uint8_t ByetAlign);

void S25FL1D_SetReadLatencyControl(uint8_t Latency);

unsigned char S25FL1D_EraseChip(void);

unsigned char S25FL1D_EraseSector( unsigned int address);

unsigned char S25FL1D_Erase64KBlock(  unsigned int address);

unsigned char S25FL1D_Write(
				uint32_t *pData,
				uint32_t size,
				uint32_t address,
				uint8_t Secure);

extern unsigned char S25FL1D_Read(
				uint32_t *pData,
				uint32_t size,
				uint32_t address);

extern unsigned char S25FL1D_ReadDual(
				uint32_t *pData,
				uint32_t size,
				uint32_t address);

extern unsigned char S25FL1D_ReadQuad(
				uint32_t *pData,
				uint32_t size,
				uint32_t address);

extern unsigned char S25FL1D_ReadDualIO(
				uint32_t *pData,
				uint32_t size,
				uint32_t address,
				uint8_t ContMode,
				uint8_t Secure);

extern unsigned char S25FL1D_ReadQuadIO(
				uint32_t *pData,
				uint32_t size,
				uint32_t address,
				uint8_t ContMode,
				uint8_t Secure);

#endif // #ifndef S25FL1_H

