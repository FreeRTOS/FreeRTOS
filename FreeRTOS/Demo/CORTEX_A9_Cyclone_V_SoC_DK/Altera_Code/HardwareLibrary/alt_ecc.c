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

#include <stdio.h>
#include "alt_ecc.h"
#include "socal/alt_sysmgr.h"
#include "socal/hps.h"
#include "socal/socal.h"

/////

// NOTE: To enable debugging output, delete the next line and uncomment the
//   line after.
#define dprintf(...)
// #define dprintf(fmt, ...) printf(fmt, ##__VA_ARGS__)

/////

#ifndef ALT_MMU_SMALL_PAGE_SIZE
#define ALT_MMU_SMALL_PAGE_SIZE (4 * 1024)
#endif

//
// This block of memory is scratch space used to scrub any ECC protected memory. It
// is the size of the largest block of memory required aligned to the strictest
// alignment.
//  - L2 Data : Up to size of L2 way + size of L1 => 64 KiB + 32 KiB. Must be
//    aligned to MMU small page boundary to be properly pageable. (largest RAM,
//    strictest alignment)
//  - OCRAM   : Size of OCRAM => 64 KiB.
//  - DMA     : 0B.
//  - QSPI    : 2 KiB.
//
static char block[(64 + 32) * 1024] __attribute__ ((aligned (ALT_MMU_SMALL_PAGE_SIZE)));

__attribute__((weak)) ALT_STATUS_CODE alt_cache_l2_ecc_start(void * block, size_t size)
{
    return ALT_E_SUCCESS;
}

static ALT_STATUS_CODE alt_ocram_ecc_start(void * block, size_t size);

__attribute__((weak)) ALT_STATUS_CODE alt_dma_ecc_start(void * block, size_t size)
{
    return ALT_E_SUCCESS;
}

__attribute__((weak)) ALT_STATUS_CODE alt_qspi_ecc_start(void * block, size_t size)
{
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_ecc_start(const ALT_ECC_RAM_ENUM_t ram_block)
{
    void *   ecc_addr;
    uint32_t ecc_bits;

    switch (ram_block)
    {
    case ALT_ECC_RAM_L2_DATA:
        return alt_cache_l2_ecc_start(block, sizeof(block));

    case ALT_ECC_RAM_OCRAM:
        return alt_ocram_ecc_start(block, sizeof(block));

    case ALT_ECC_RAM_USB0:
        ecc_addr = ALT_SYSMGR_ECC_USB0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_USB0_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_USB1:
        ecc_addr = ALT_SYSMGR_ECC_USB1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_USB1_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_EMAC0:
        ecc_addr = ALT_SYSMGR_ECC_EMAC0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_EMAC0_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_EMAC1:
        ecc_addr = ALT_SYSMGR_ECC_EMAC1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_EMAC1_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_DMA:
        return alt_dma_ecc_start(block, sizeof(block));

    case ALT_ECC_RAM_CAN0:
        ecc_addr = ALT_SYSMGR_ECC_CAN0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_CAN0_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_CAN1:
        ecc_addr = ALT_SYSMGR_ECC_CAN1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_CAN1_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_NAND:
        ecc_addr = ALT_SYSMGR_ECC_NAND_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_NAND_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_QSPI:
        return alt_qspi_ecc_start(block, sizeof(block));

    case ALT_ECC_RAM_SDMMC:
        ecc_addr = ALT_SYSMGR_ECC_SDMMC_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_SDMMC_EN_SET_MSK;
        break;
    default:
        return ALT_E_ERROR;
    }

    alt_setbits_word(ecc_addr, ecc_bits);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_ecc_stop(const ALT_ECC_RAM_ENUM_t ram_block)
{
    void *   ecc_addr;
    uint32_t ecc_bits;

    switch (ram_block)
    {
    case ALT_ECC_RAM_L2_DATA:
        ecc_addr = ALT_SYSMGR_ECC_L2_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_L2_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_OCRAM:
        ecc_addr = ALT_SYSMGR_ECC_OCRAM_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_OCRAM_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_USB0:
        ecc_addr = ALT_SYSMGR_ECC_USB0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_USB0_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_USB1:
        ecc_addr = ALT_SYSMGR_ECC_USB1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_USB1_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_EMAC0:
        ecc_addr = ALT_SYSMGR_ECC_EMAC0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_EMAC0_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_EMAC1:
        ecc_addr = ALT_SYSMGR_ECC_EMAC1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_EMAC1_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_DMA:
        ecc_addr = ALT_SYSMGR_ECC_DMA_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_DMA_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_CAN0:
        ecc_addr = ALT_SYSMGR_ECC_CAN0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_CAN0_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_CAN1:
        ecc_addr = ALT_SYSMGR_ECC_CAN1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_CAN1_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_NAND:
        ecc_addr = ALT_SYSMGR_ECC_NAND_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_NAND_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_QSPI:
        ecc_addr = ALT_SYSMGR_ECC_QSPI_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_QSPI_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_SDMMC:
        ecc_addr = ALT_SYSMGR_ECC_SDMMC_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_SDMMC_EN_SET_MSK;
        break;
    default:
        return ALT_E_ERROR;
    }

    alt_clrbits_word(ecc_addr, ecc_bits);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_ecc_is_enabled(const ALT_ECC_RAM_ENUM_t ram_block)
{
    void *   ecc_addr;
    uint32_t ecc_bits;

    switch (ram_block)
    {
    case ALT_ECC_RAM_L2_DATA:
        ecc_addr = ALT_SYSMGR_ECC_L2_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_L2_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_OCRAM:
        ecc_addr = ALT_SYSMGR_ECC_OCRAM_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_OCRAM_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_USB0:
        ecc_addr = ALT_SYSMGR_ECC_USB0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_USB0_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_USB1:
        ecc_addr = ALT_SYSMGR_ECC_USB1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_USB1_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_EMAC0:
        ecc_addr = ALT_SYSMGR_ECC_EMAC0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_EMAC0_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_EMAC1:
        ecc_addr = ALT_SYSMGR_ECC_EMAC1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_EMAC1_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_DMA:
        ecc_addr = ALT_SYSMGR_ECC_DMA_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_DMA_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_CAN0:
        ecc_addr = ALT_SYSMGR_ECC_CAN0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_CAN0_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_CAN1:
        ecc_addr = ALT_SYSMGR_ECC_CAN1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_CAN1_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_NAND:
        ecc_addr = ALT_SYSMGR_ECC_NAND_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_NAND_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_QSPI:
        ecc_addr = ALT_SYSMGR_ECC_QSPI_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_QSPI_EN_SET_MSK;
        break;
    case ALT_ECC_RAM_SDMMC:
        ecc_addr = ALT_SYSMGR_ECC_SDMMC_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_SDMMC_EN_SET_MSK;
        break;
    default:
        return ALT_E_ERROR;
    }

    if (alt_read_word(ecc_addr) & ecc_bits)
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

/////

ALT_STATUS_CODE alt_ecc_status_get(const ALT_ECC_RAM_ENUM_t ram_block,
                                   uint32_t *status)
{
    uint32_t ecc_bits;
    uint32_t ecc_mask = 0;

    switch (ram_block)
    {
//    case ALT_ECC_RAM_L2_DATA:

    case ALT_ECC_RAM_OCRAM:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_OCRAM_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_OCRAM_SERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_OCRAM_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_OCRAM_DERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_OCRAM_DERR;
        }
        break;

    case ALT_ECC_RAM_USB0:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_USB0_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_USB0_SERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_USB0_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_USB0_DERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_USB0_DERR;
        }
        break;

    case ALT_ECC_RAM_USB1:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_USB1_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_USB1_SERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_USB1_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_USB1_DERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_USB1_DERR;
        }
        break;

    case ALT_ECC_RAM_EMAC0:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_EMAC0_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_EMAC0_TXFIFOSERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_EMAC0_TX_FIFO_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_EMAC0_TXFIFODERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_EMAC0_TX_FIFO_DERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_EMAC0_RXFIFOSERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_EMAC0_RX_FIFO_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_EMAC0_RXFIFODERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_EMAC0_RX_FIFO_DERR;
        }
        break;

    case ALT_ECC_RAM_EMAC1:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_EMAC1_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_EMAC1_TXFIFOSERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_EMAC1_TX_FIFO_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_EMAC1_TXFIFODERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_EMAC1_TX_FIFO_DERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_EMAC1_RXFIFOSERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_EMAC1_RX_FIFO_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_EMAC1_RXFIFODERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_EMAC1_RX_FIFO_DERR;
        }
        break;

    case ALT_ECC_RAM_DMA:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_DMA_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_DMA_SERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_DMA_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_DMA_DERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_DMA_DERR;
        }
        break;

    case ALT_ECC_RAM_CAN0:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_CAN0_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_CAN0_SERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_CAN0_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_CAN0_DERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_CAN0_DERR;
        }
        break;

    case ALT_ECC_RAM_CAN1:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_CAN1_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_CAN1_SERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_CAN1_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_CAN1_DERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_CAN1_DERR;
        }
        break;

    case ALT_ECC_RAM_NAND:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_NAND_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_NAND_ECCBUFSERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_NAND_BUFFER_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_NAND_ECCBUFDERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_NAND_BUFFER_DERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_NAND_WRFIFOSERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_NAND_WR_FIFO_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_NAND_WRFIFODERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_NAND_WR_FIFO_DERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_NAND_RDFIFOSERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_NAND_RD_FIFO_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_NAND_RDFIFODERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_NAND_RD_FIFO_DERR;
        }
        break;

    case ALT_ECC_RAM_QSPI:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_QSPI_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_QSPI_SERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_QSPI_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_QSPI_DERR_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_QSPI_DERR;
        }
        break;

    case ALT_ECC_RAM_SDMMC:
        ecc_bits = alt_read_word(ALT_SYSMGR_ECC_SDMMC_ADDR);
        if (ecc_bits & ALT_SYSMGR_ECC_SDMMC_SERRPORTA_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_SDMMC_PORT_A_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_SDMMC_DERRPORTA_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_SDMMC_PORT_A_DERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_SDMMC_SERRPORTB_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_SDMMC_PORT_B_SERR;
        }
        if (ecc_bits & ALT_SYSMGR_ECC_SDMMC_DERRPORTB_SET_MSK)
        {
            ecc_mask |= ALT_ECC_ERROR_SDMMC_PORT_B_DERR;
        }
        break;

    default:
        return ALT_E_ERROR;
    }

    *status = ecc_mask;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_ecc_status_clear(const ALT_ECC_RAM_ENUM_t ram_block, 
                                     const uint32_t ecc_mask)
{
    void *   ecc_addr;
    uint32_t ecc_bits = 0;

    switch (ram_block)
    {
//    case ALT_ECC_RAM_L2_DATA:

    case ALT_ECC_RAM_OCRAM:
        ecc_addr = ALT_SYSMGR_ECC_OCRAM_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_OCRAM_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_OCRAM_SERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_OCRAM_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_OCRAM_DERR_SET_MSK;
        }
        break;

    case ALT_ECC_RAM_USB0:
        ecc_addr = ALT_SYSMGR_ECC_USB0_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_USB0_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_USB0_SERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_USB0_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_USB0_DERR_SET_MSK;
        }
        break;

    case ALT_ECC_RAM_USB1:
        ecc_addr = ALT_SYSMGR_ECC_USB1_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_USB1_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_USB1_SERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_USB1_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_USB1_DERR_SET_MSK;
        }
        break;

    case ALT_ECC_RAM_EMAC0:
        ecc_addr = ALT_SYSMGR_ECC_EMAC0_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_EMAC0_TX_FIFO_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_EMAC0_TXFIFOSERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_EMAC0_TX_FIFO_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_EMAC0_TXFIFODERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_EMAC0_RX_FIFO_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_EMAC0_RXFIFOSERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_EMAC0_RX_FIFO_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_EMAC0_RXFIFODERR_SET_MSK;
        }
        break;

    case ALT_ECC_RAM_EMAC1:
        ecc_addr = ALT_SYSMGR_ECC_EMAC1_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_EMAC1_TX_FIFO_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_EMAC1_TXFIFOSERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_EMAC1_TX_FIFO_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_EMAC1_TXFIFODERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_EMAC1_RX_FIFO_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_EMAC1_RXFIFOSERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_EMAC1_RX_FIFO_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_EMAC1_RXFIFODERR_SET_MSK;
        }
        break;

    case ALT_ECC_RAM_DMA:
        ecc_addr = ALT_SYSMGR_ECC_DMA_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_DMA_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_DMA_SERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_DMA_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_DMA_DERR_SET_MSK;
        }
        break;

    case ALT_ECC_RAM_CAN0:
        ecc_addr = ALT_SYSMGR_ECC_CAN0_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_CAN0_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_CAN0_SERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_CAN0_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_CAN0_DERR_SET_MSK;
        }
        break;

    case ALT_ECC_RAM_CAN1:
        ecc_addr = ALT_SYSMGR_ECC_CAN1_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_CAN1_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_CAN1_SERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_CAN1_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_CAN1_DERR_SET_MSK;
        }
        break;

    case ALT_ECC_RAM_NAND:
        ecc_addr = ALT_SYSMGR_ECC_NAND_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_NAND_BUFFER_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_NAND_ECCBUFSERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_NAND_BUFFER_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_NAND_ECCBUFDERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_NAND_WR_FIFO_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_NAND_WRFIFOSERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_NAND_WR_FIFO_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_NAND_WRFIFODERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_NAND_RD_FIFO_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_NAND_RDFIFOSERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_NAND_RD_FIFO_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_NAND_RDFIFODERR_SET_MSK;
        }
        break;

    case ALT_ECC_RAM_QSPI:
        ecc_addr = ALT_SYSMGR_ECC_QSPI_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_QSPI_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_QSPI_SERR_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_QSPI_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_QSPI_DERR_SET_MSK;
        }
        break;

    case ALT_ECC_RAM_SDMMC:
        ecc_addr = ALT_SYSMGR_ECC_SDMMC_ADDR;

        if (ecc_mask & ALT_ECC_ERROR_SDMMC_PORT_A_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_SDMMC_SERRPORTA_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_SDMMC_PORT_A_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_SDMMC_DERRPORTA_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_SDMMC_PORT_B_SERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_SDMMC_SERRPORTB_SET_MSK;
        }
        if (ecc_mask & ALT_ECC_ERROR_SDMMC_PORT_B_DERR)
        {
            ecc_bits |= ALT_SYSMGR_ECC_SDMMC_DERRPORTB_SET_MSK;
        }
        break;

    default:
        return ALT_E_ERROR;
    }

    // Bit 1 is always ECC enable.
    // Be sure not to clear other conditions that may be active but not requested to be cleared.
    alt_write_word(ecc_addr, (alt_read_word(ecc_addr) & (1 << 0)) | ecc_bits);

    return ALT_E_SUCCESS;
}

/////

ALT_STATUS_CODE alt_ecc_serr_inject(const ALT_ECC_RAM_ENUM_t ram_block)
{
    void *   ecc_addr;
    uint32_t ecc_bits;

    switch (ram_block)
    {
    case ALT_ECC_RAM_L2_DATA:
        ecc_addr = ALT_SYSMGR_ECC_L2_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_L2_INJS_SET_MSK;
        break;
    case ALT_ECC_RAM_OCRAM:
        ecc_addr = ALT_SYSMGR_ECC_OCRAM_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_OCRAM_INJS_SET_MSK;
        break;
    case ALT_ECC_RAM_USB0:
        ecc_addr = ALT_SYSMGR_ECC_USB0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_USB0_INJS_SET_MSK;
        break;
    case ALT_ECC_RAM_USB1:
        ecc_addr = ALT_SYSMGR_ECC_USB1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_USB1_INJS_SET_MSK;
        break;
    case ALT_ECC_RAM_EMAC0:
        ecc_addr = ALT_SYSMGR_ECC_EMAC0_ADDR;
        ecc_bits =   ALT_SYSMGR_ECC_EMAC0_TXFIFOINJS_SET_MSK
                   | ALT_SYSMGR_ECC_EMAC0_RXFIFOINJS_SET_MSK;
        break;
    case ALT_ECC_RAM_EMAC1:
        ecc_addr = ALT_SYSMGR_ECC_EMAC1_ADDR;
        ecc_bits =   ALT_SYSMGR_ECC_EMAC1_TXFIFOINJS_SET_MSK
                   | ALT_SYSMGR_ECC_EMAC1_RXFIFOINJS_SET_MSK;
        break;
    case ALT_ECC_RAM_DMA:
        ecc_addr = ALT_SYSMGR_ECC_DMA_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_DMA_INJS_SET_MSK;
        break;
    case ALT_ECC_RAM_CAN0:
        ecc_addr = ALT_SYSMGR_ECC_CAN0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_CAN0_INJS_SET_MSK;
        break;
    case ALT_ECC_RAM_CAN1:
        ecc_addr = ALT_SYSMGR_ECC_CAN1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_CAN1_INJS_SET_MSK;
        break;
    case ALT_ECC_RAM_NAND:
        ecc_addr = ALT_SYSMGR_ECC_NAND_ADDR;
        ecc_bits =   ALT_SYSMGR_ECC_NAND_ECCBUFINJS_SET_MSK
                   | ALT_SYSMGR_ECC_NAND_WRFIFOINJS_SET_MSK
                   | ALT_SYSMGR_ECC_NAND_RDFIFOINJS_SET_MSK;
        break;
    case ALT_ECC_RAM_QSPI:
        ecc_addr = ALT_SYSMGR_ECC_QSPI_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_QSPI_INJS_SET_MSK;
        break;
    case ALT_ECC_RAM_SDMMC:
        ecc_addr = ALT_SYSMGR_ECC_SDMMC_ADDR;
        ecc_bits =   ALT_SYSMGR_ECC_SDMMC_INJSPORTA_SET_MSK
                   | ALT_SYSMGR_ECC_SDMMC_INJSPORTB_SET_MSK;
        break;
    default:
        return ALT_E_ERROR;
    }

    uint32_t reg = alt_read_word(ecc_addr);
    alt_write_word(ecc_addr, reg | ecc_bits);
    alt_write_word(ecc_addr, reg);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_ecc_derr_inject(const ALT_ECC_RAM_ENUM_t ram_block)
{
    void *   ecc_addr;
    uint32_t ecc_bits;

    switch (ram_block)
    {
    case ALT_ECC_RAM_L2_DATA:
        ecc_addr = ALT_SYSMGR_ECC_L2_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_L2_INJD_SET_MSK;
        break;
    case ALT_ECC_RAM_OCRAM:
        ecc_addr = ALT_SYSMGR_ECC_OCRAM_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_OCRAM_INJD_SET_MSK;
        break;
    case ALT_ECC_RAM_USB0:
        ecc_addr = ALT_SYSMGR_ECC_USB0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_USB0_INJD_SET_MSK;
        break;
    case ALT_ECC_RAM_USB1:
        ecc_addr = ALT_SYSMGR_ECC_USB1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_USB1_INJD_SET_MSK;
        break;
    case ALT_ECC_RAM_EMAC0:
        ecc_addr = ALT_SYSMGR_ECC_EMAC0_ADDR;
        ecc_bits =   ALT_SYSMGR_ECC_EMAC0_TXFIFOINJD_SET_MSK
                   | ALT_SYSMGR_ECC_EMAC0_RXFIFOINJD_SET_MSK;
        break;
    case ALT_ECC_RAM_EMAC1:
        ecc_addr = ALT_SYSMGR_ECC_EMAC1_ADDR;
        ecc_bits =   ALT_SYSMGR_ECC_EMAC1_TXFIFOINJD_SET_MSK
                   | ALT_SYSMGR_ECC_EMAC1_RXFIFOINJD_SET_MSK;
        break;
    case ALT_ECC_RAM_DMA:
        ecc_addr = ALT_SYSMGR_ECC_DMA_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_DMA_INJD_SET_MSK;
        break;
    case ALT_ECC_RAM_CAN0:
        ecc_addr = ALT_SYSMGR_ECC_CAN0_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_CAN0_INJD_SET_MSK;
        break;
    case ALT_ECC_RAM_CAN1:
        ecc_addr = ALT_SYSMGR_ECC_CAN1_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_CAN1_INJD_SET_MSK;
        break;
    case ALT_ECC_RAM_NAND:
        ecc_addr = ALT_SYSMGR_ECC_NAND_ADDR;
        ecc_bits =   ALT_SYSMGR_ECC_NAND_ECCBUFINJD_SET_MSK
                   | ALT_SYSMGR_ECC_NAND_WRFIFOINJD_SET_MSK
                   | ALT_SYSMGR_ECC_NAND_RDFIFOINJD_SET_MSK;
        break;
    case ALT_ECC_RAM_QSPI:
        ecc_addr = ALT_SYSMGR_ECC_QSPI_ADDR;
        ecc_bits = ALT_SYSMGR_ECC_QSPI_INJD_SET_MSK;
        break;
    case ALT_ECC_RAM_SDMMC:
        ecc_addr = ALT_SYSMGR_ECC_SDMMC_ADDR;
        ecc_bits =   ALT_SYSMGR_ECC_SDMMC_INJDPORTA_SET_MSK
                   | ALT_SYSMGR_ECC_SDMMC_INJDPORTB_SET_MSK;
        break;
    default:
        return ALT_E_ERROR;
    }

    uint32_t reg = alt_read_word(ecc_addr);
    alt_write_word(ecc_addr, reg | ecc_bits);
    alt_write_word(ecc_addr, reg);

    return ALT_E_SUCCESS;
}

/////

static ALT_STATUS_CODE alt_ocram_ecc_start(void * block, size_t size)
{
    // CASE 163685: Overflow in ALT_OCRAM_UB_ADDR.
    // const uint32_t ocram_size = ((uint32_t)ALT_OCRAM_UB_ADDR - (uint32_t)ALT_OCRAM_LB_ADDR) + 1;
    const uint32_t ocram_size = ((uint32_t)0xffffffff - (uint32_t)ALT_OCRAM_LB_ADDR) + 1;
    dprintf("DEBUG[ECC][OCRAM]: OCRAM Size = 0x%lx.\n", ocram_size);

    // Verify buffer is large enough to contain the entire contents of OCRAM.
    if (size < ocram_size)
    {
        return ALT_E_ERROR;
    }

    // Verify buffer is word aligned.
    if ((uintptr_t)block & (sizeof(uint32_t) - 1))
    {
        return ALT_E_ERROR;
    }

    // Read the contents of OCRAM into the provided buffer

    uint32_t * block_iter = block;
    uint32_t * ocram_iter = ALT_OCRAM_ADDR;
    uint32_t   size_counter = ocram_size;

    while (size_counter)
    {
        *block_iter = alt_read_word(ocram_iter);
        ++block_iter;
        ++ocram_iter;
        size_counter -= sizeof(*ocram_iter);
    }

    // Enable ECC

    alt_setbits_word(ALT_SYSMGR_ECC_OCRAM_ADDR, ALT_SYSMGR_ECC_OCRAM_EN_SET_MSK);

    // Write back contents of OCRAM from buffer to OCRAM

    block_iter   = block;
    ocram_iter   = ALT_OCRAM_ADDR;
    size_counter = ocram_size;

    while (size_counter)
    {
        alt_write_word(ocram_iter, *block_iter);
        ++block_iter;
        ++ocram_iter;
        size_counter -= sizeof(*ocram_iter);
    }

    // Clear any pending spurious interrupts

    alt_write_word(ALT_SYSMGR_ECC_OCRAM_ADDR,
                     ALT_SYSMGR_ECC_OCRAM_EN_SET_MSK
                   | ALT_SYSMGR_ECC_OCRAM_SERR_SET_MSK
                   | ALT_SYSMGR_ECC_OCRAM_DERR_SET_MSK);

    return ALT_E_SUCCESS;
}
