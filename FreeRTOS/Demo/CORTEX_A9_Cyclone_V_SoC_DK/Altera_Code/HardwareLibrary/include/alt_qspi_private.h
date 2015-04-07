/******************************************************************************
 *
 * Copyright 2013 Altera Corporation. All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of the author may not be used to endorse or promote products
 * derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
 * EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 ******************************************************************************/

/*! \file
 *  Altera - QSPI Flash Controller Module
 */

#ifndef __ALT_QSPI_PRIVATE_H__
#define __ALT_QSPI_PRIVATE_H__

#include "socal/socal.h"

//
// This section provisions support for various flash devices.
//

#define ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT 1

/////

#define ALT_QSPI_PAGE_ADDR_MSK          0xFFFFFF00
#define ALT_QSPI_PAGE_SIZE              0x00000100 // 256 B
#define ALT_QSPI_SUBSECTOR_ADDR_MSK     0xFFFFF000
#define ALT_QSPI_SUBSECTOR_SIZE         0x00001000 // 4096 B
#define ALT_QSPI_SECTOR_ADDR_MSK        0xFFFF0000
#define ALT_QSPI_SECTOR_SIZE            0x00010000 // 64 KiB
#define ALT_QSPI_BANK_ADDR_MSK          0xFF000000
#define ALT_QSPI_BANK_SIZE              0x01000000 // 16 MiB

#if ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT
#define ALT_QSPI_N25Q_DIE_ADDR_MSK      0xFE000000
#define ALT_QSPI_N25Q_DIE_SIZE          0x02000000 // 32 MiB
#endif

/////

// Default delay timing (in ns) for N25Q.
// These values are from the N25Q handbook. The timing correctness is difficult
// to test because the test setup does not feature mutliple chips.
#define ALT_QSPI_TSHSL_NS_DEF       (50)
#define ALT_QSPI_TSD2D_NS_DEF       (0)
#define ALT_QSPI_TCHSH_NS_DEF       (4)
#define ALT_QSPI_TSLCH_NS_DEF       (4)

/*
// Default delay timing (in ns)
#define ALT_QSPI_TSHSL_NS_DEF       (200)
#define ALT_QSPI_TSD2D_NS_DEF       (255)
#define ALT_QSPI_TCHSH_NS_DEF       (20)
#define ALT_QSPI_TSLCH_NS_DEF       (20)
*/

// Flash commands
#define ALT_QSPI_STIG_OPCODE_READ                 (0x03)
#define ALT_QSPI_STIG_OPCODE_4BYTE_READ           (0x13)
#define ALT_QSPI_STIG_OPCODE_FASTREAD             (0x0B)
#define ALT_QSPI_STIG_OPCODE_FASTREAD_DUAL_OUTPUT (0x3B)
#define ALT_QSPI_STIG_OPCODE_FASTREAD_QUAD_OUTPUT (0x6B)
#define ALT_QSPI_STIG_OPCODE_FASTREAD_DUAL_IO     (0xBB)
#define ALT_QSPI_STIG_OPCODE_FASTREAD_QUAD_IO     (0xEB)
#define ALT_QSPI_STIG_OPCODE_PP                   (0x02)
#define ALT_QSPI_STIG_OPCODE_DUAL_PP              (0xA2)
#define ALT_QSPI_STIG_OPCODE_QUAD_PP              (0x32)
#define ALT_QSPI_STIG_OPCODE_RDID                 (0x9F)
#define ALT_QSPI_STIG_OPCODE_WREN                 (0x06)
#define ALT_QSPI_STIG_OPCODE_WRDIS                (0x04)
#define ALT_QSPI_STIG_OPCODE_RDSR                 (0x05)
#define ALT_QSPI_STIG_OPCODE_WRSR                 (0x01)
#define ALT_QSPI_STIG_OPCODE_SUBSEC_ERASE         (0x20)
#define ALT_QSPI_STIG_OPCODE_SEC_ERASE            (0xD8)
#define ALT_QSPI_STIG_OPCODE_BULK_ERASE           (0xC7)
#define ALT_QSPI_STIG_OPCODE_DIE_ERASE            (0xC4)
#define ALT_QSPI_STIG_OPCODE_CHIP_ERASE           (0x60)
#define ALT_QSPI_STIG_OPCODE_RD_EXT_REG           (0xC8)
#define ALT_QSPI_STIG_OPCODE_WR_EXT_REG           (0xC5)
#define ALT_QSPI_STIG_OPCODE_RD_STAT_REG          (0x05)
#define ALT_QSPI_STIG_OPCODE_WR_STAT_REG          (0x01)
#define ALT_QSPI_STIG_OPCODE_ENTER_4BYTE_MODE     (0xB7)
#define ALT_QSPI_STIG_OPCODE_EXIT_4BYTE_MODE      (0xE9)

// Micron commands, for 512 Mib, 1 Gib (64 MiB, 128 MiB) parts.
#if ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT
#define ALT_QSPI_STIG_OPCODE_RESET_EN             (0x66)
#define ALT_QSPI_STIG_OPCODE_RESET_MEM            (0x99)
#define ALT_QSPI_STIG_OPCODE_RDFLGSR              (0x70)
#define ALT_QSPI_STIG_OPCODE_CLRFLGSR             (0x50)
#define ALT_QSPI_STIG_OPCODE_DISCVR_PARAM         (0x5A)
#endif

// Spansion commands
// #define OPCODE_ECRM                 (0xFF) // Exit continuous read mode

#define QSPI_READ_CLK_MHZ           (50)
#define QSPI_FASTREAD_CLK_MHZ       (100)

// Manufacturer ID
#define ALT_QSPI_STIG_RDID_JEDECID_MICRON      (0x20)
#define ALT_QSPI_STIG_RDID_JEDECID_NUMONYX     (0x20) // Same as Micron
#define ALT_QSPI_STIG_RDID_JEDECID_SPANSION    (0xEF)
#define ALT_QSPI_STIG_RDID_JEDECID_WINBOND     (0xEF) // Same as Spansion
#define ALT_QSPI_STIG_RDID_JEDECID_MACRONIC    (0xC2)
#define ALT_QSPI_STIG_RDID_JEDECID_ATMEL       (0x1F)

#define ALT_QSPI_STIG_RDID_JEDECID_GET(value)    ((value >>  0) & 0xff)
#define ALT_QSPI_STIG_RDID_CAPACITYID_GET(value) ((value >> 16) & 0xff)

#define ALT_QSPI_STIG_FLAGSR_ERASEPROGRAMREADY_GET(value) ((value >> 7) & 0x1)
#define ALT_QSPI_STIG_FLAGSR_ERASEREADY_GET(value)        ((value >> 7) & 0x1)
#define ALT_QSPI_STIG_FLAGSR_PROGRAMREADY_GET(value)      ((value >> 7) & 0x1)
#define ALT_QSPI_STIG_FLAGSR_ERASEERROR_GET(value)        ((value >> 5) & 0x1)
#define ALT_QSPI_STIG_FLAGSR_PROGRAMERROR_GET(value)      ((value >> 4) & 0x1)
#define ALT_QSPI_STIG_FLAGSR_ADDRESSINGMODE_GET(value)    ((value >> 1) & 0x1)
#define ALT_QSPI_STIG_FLAGSR_PROTECTIONERROR_GET(value)   ((value >> 0) & 0x1)

#define ALT_QSPI_STIG_SR_BUSY_GET(value)       		  	  ((value >> 0) & 0x1)

/////

#define ALT_QSPI_TIMEOUT_INFINITE (0xffffffff)

ALT_STATUS_CODE alt_qspi_replace(uint32_t dst, const void * src, size_t size);

ALT_STATUS_CODE alt_qspi_stig_cmd(uint32_t opcode, uint32_t dummy, uint32_t timeout);
ALT_STATUS_CODE alt_qspi_stig_rd_cmd(uint8_t opcode, uint32_t dummy,
                                     uint32_t num_bytes, uint32_t * output,
                                     uint32_t timeout);
ALT_STATUS_CODE alt_qspi_stig_wr_cmd(uint8_t opcode, uint32_t dummy,
                                     uint32_t num_bytes, const uint32_t * input,
                                     uint32_t timeout);
ALT_STATUS_CODE alt_qspi_stig_addr_cmd(uint8_t opcode, uint32_t dummy,
                                       uint32_t address,
                                       uint32_t timeout);

ALT_STATUS_CODE alt_qspi_device_wren(void);
ALT_STATUS_CODE alt_qspi_device_wrdis(void);
ALT_STATUS_CODE alt_qspi_device_rdid(uint32_t * rdid);
ALT_STATUS_CODE alt_qspi_discovery_parameter(uint32_t * param);
ALT_STATUS_CODE alt_qspi_device_bank_select(uint32_t bank);

#endif // __ALT_PRIVATE_QSPI_H__
