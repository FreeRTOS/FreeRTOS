/******************************************************************************
*
* alt_qspi.c - API for the Altera SoC FPGA QSPI device.
*
******************************************************************************/

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

#include <string.h>
#include <stdio.h>
#include <inttypes.h>
#include "hwlib.h"
#include "alt_clock_manager.h"
#include "alt_qspi.h"
#include "alt_qspi_private.h"
#include "socal/alt_qspi.h"
#include "socal/alt_rstmgr.h"
#include "socal/alt_sysmgr.h"
#include "socal/hps.h"
#include "socal/socal.h"

/////

// NOTE: To enable debugging output, delete the next line and uncomment the
//   line after.
#define dprintf(...)
// #define dprintf printf

/////

#define MIN(a, b) ((a) > (b) ? (b) : (a))

// qspi_clk operating frequency range.
#define ALT_QSPI_CLK_FREQ_MIN ((alt_freq_t)0)
#define ALT_QSPI_CLK_FREQ_MAX ((alt_freq_t)432000000)

// The set of all valid QSPI controller interrupt status mask values.
#define ALT_QSPI_INT_STATUS_ALL ( \
        ALT_QSPI_INT_STATUS_MODE_FAIL         | \
        ALT_QSPI_INT_STATUS_UFL               | \
        ALT_QSPI_INT_STATUS_IDAC_OP_COMPLETE  | \
        ALT_QSPI_INT_STATUS_IDAC_OP_REJECT    | \
        ALT_QSPI_INT_STATUS_WR_PROT_VIOL      | \
        ALT_QSPI_INT_STATUS_ILL_AHB_ACCESS    | \
        ALT_QSPI_INT_STATUS_IDAC_WTRMK_TRIG   | \
        ALT_QSPI_INT_STATUS_RX_OVF            | \
        ALT_QSPI_INT_STATUS_TX_FIFO_NOT_FULL  | \
        ALT_QSPI_INT_STATUS_TX_FIFO_FULL      | \
        ALT_QSPI_INT_STATUS_RX_FIFO_NOT_EMPTY | \
        ALT_QSPI_INT_STATUS_RX_FIFO_FULL      | \
        ALT_QSPI_INT_STATUS_IDAC_RD_FULL        \
        )

static uint32_t qspi_device_size = 0;

/////

static ALT_STATUS_CODE alt_qspi_device_status(uint32_t * status)
{
    // Read flag status register through STIG
    return alt_qspi_stig_rd_cmd(ALT_QSPI_STIG_OPCODE_RDSR, 0, 1, status, 10000);
}

#if ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT
static ALT_STATUS_CODE alt_qspi_N25Q_device_flag(uint32_t * flagsr)
{
    if (qspi_device_size < 0x4000000)
    {
        return ALT_E_SUCCESS;
    }

    // Read flag status register through STIG
    return alt_qspi_stig_rd_cmd(ALT_QSPI_STIG_OPCODE_RDFLGSR, 0, 1, flagsr, 10000);
}

// NOTE: This must be called after QSPI has been enabled. Communications with
//   the device will not happen until QSPI is enabled.
static inline ALT_STATUS_CODE alt_qspi_N25Q_enable(void)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Reset the volatile memory on the N25Q

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_stig_cmd(ALT_QSPI_STIG_OPCODE_RESET_EN, 0, 10000);
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_stig_cmd(ALT_QSPI_STIG_OPCODE_RESET_MEM, 0, 10000);
    }

    /////

    if (status == ALT_E_SUCCESS)
    {
        ALT_QSPI_DEV_INST_CONFIG_t cfg =
        {
            .op_code        = ALT_QSPI_STIG_OPCODE_FASTREAD_QUAD_IO,
            .inst_type      = ALT_QSPI_MODE_SINGLE, // RDID does not support QUAD.
            .addr_xfer_type = ALT_QSPI_MODE_QUAD,
            .data_xfer_type = ALT_QSPI_MODE_QUAD,
            .dummy_cycles   = 10
        };

        status = alt_qspi_device_read_config_set(&cfg);
    }

/*
    // CASE 157096: Investigate using QUAD for writes.
    if (status == ALT_E_SUCCESS)
    {
        ALT_QSPI_DEV_INST_CONFIG_t cfg =
        {
            .op_code        = ALT_QSPI_STIG_OPCODE_PP,
            .inst_type      = ALT_QSPI_MODE_SINGLE,
            .addr_xfer_type = ALT_QSPI_MODE_QUAD,
            .data_xfer_type = ALT_QSPI_MODE_QUAD,
            .dummy_cycles   = 0
        };

        status = alt_qspi_device_write_config_set(&cfg);
    }
*/

    return status;
}

static ALT_STATUS_CODE alt_qspi_N25Q_flag_wait_for_program(uint32_t timeout)
{
    // The flag status register is only available on the 512 Mib and 1 Gib
    // (64 MiB and 128 MiB) Micron parts.
    if (qspi_device_size < 0x4000000)
    {
        return ALT_E_SUCCESS;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t time_out = timeout;
    uint32_t stat = 0;
    bool infinite = (timeout == ALT_QSPI_TIMEOUT_INFINITE);

    do
    {
        status = alt_qspi_device_status(&stat);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }
        if (!ALT_QSPI_STIG_SR_BUSY_GET(stat))
        {
            break;
        }
    }
    while (time_out-- || infinite);

    if (time_out == (uint32_t)-1 && !infinite)
    {
        status = ALT_E_TMO;
    }

    if (status == ALT_E_SUCCESS)
    {
        uint32_t flagsr = 0;

        do
        {
            status = alt_qspi_N25Q_device_flag(&flagsr);
            if (status != ALT_E_SUCCESS)
            {
                break;
            }
            if (ALT_QSPI_STIG_FLAGSR_PROGRAMREADY_GET(flagsr))
            {
                break;
            }
        }
        while (timeout-- || infinite);

        if (timeout == (uint32_t)-1 && !infinite)
        {
            status = ALT_E_TMO;
        }

        if (status == ALT_E_SUCCESS)
        {
            if (ALT_QSPI_STIG_FLAGSR_PROGRAMERROR_GET(flagsr))
            {
                status = ALT_E_ERROR;
            }
        }
    }
    return status;
}

static ALT_STATUS_CODE alt_qspi_N25Q_flag_wait_for_erase(uint32_t timeout)
{
    // The flag status register is only available on the 512 Mib and 1 Gib
    // (64 MiB and 128 MiB) Micron parts.
    if (qspi_device_size < 0x4000000)
    {
        return ALT_E_SUCCESS;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t time_out = timeout;
    uint32_t stat = 0;
    bool infinite = (timeout == ALT_QSPI_TIMEOUT_INFINITE);

    do
    {
        status = alt_qspi_device_status(&stat);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }
        if (!ALT_QSPI_STIG_SR_BUSY_GET(stat))
        {
            break;
        }
    }
    while (time_out-- || infinite);

    if (time_out == (uint32_t)-1 && !infinite)
    {
        status = ALT_E_TMO;
    }

    if (status == ALT_E_SUCCESS)
    {

        uint32_t flagsr = 0;

        do
        {
            status = alt_qspi_N25Q_device_flag(&flagsr);
            if (status != ALT_E_SUCCESS)
            {
                break;
            }
            if (ALT_QSPI_STIG_FLAGSR_ERASEREADY_GET(flagsr))
            {
                break;
            }
        }
        while (timeout-- || infinite);

        if (timeout == (uint32_t)-1 && !infinite)
        {
            status = ALT_E_TMO;
        }

        if (status == ALT_E_SUCCESS)
        {
            if (ALT_QSPI_STIG_FLAGSR_ERASEERROR_GET(flagsr))
            {
                status = ALT_E_ERROR;
            }
        }
    }
 
    return status;
}
#endif

//
// A helper function which converts a ns interval into a delay interval for a given MHz.
// The +999 is there to round up the result.
//
static inline int alt_qspi_ns_to_multiplier(int ns, int mhz)
{
    return ((ns * mhz) + 999) / 1000;
}

ALT_STATUS_CODE alt_qspi_init(void)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    alt_freq_t qspi_clk_freq = 0;

    // Validate QSPI module input clocks.
    //  - pclk    - l4_mp_clk
    //  - hclk    - l4_mp_clk
    //  - ref_clk - qspi_clk

    // Check and validate the QSPI ref_clk which is connected to the HPS qspi_clk.
    if (status == ALT_E_SUCCESS)
    {
        if (alt_clk_is_enabled(ALT_CLK_QSPI) != ALT_E_TRUE)
        {
            status = ALT_E_BAD_CLK;
        }
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_clk_freq_get(ALT_CLK_QSPI, &qspi_clk_freq);
        if (status == ALT_E_SUCCESS)
        {
            if (qspi_clk_freq > ALT_QSPI_CLK_FREQ_MAX)
            {
                return ALT_E_BAD_CLK;
            }
        }
    }

    int qspi_clk_mhz = qspi_clk_freq / 1000000;

    /////

    // Take QSPI controller out of reset.
    alt_clrbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_QSPI_SET_MSK);

    /////

    // Configure the device timing

    if (status == ALT_E_SUCCESS)
    {
        ALT_QSPI_TIMING_CONFIG_t timing_cfg =
        {
            .clk_phase  = (ALT_QSPI_CLK_PHASE_t)ALT_QSPI_CFG_SELCLKPHASE_RESET,
            .clk_pol    = (ALT_QSPI_CLK_POLARITY_t)ALT_QSPI_CFG_SELCLKPOL_RESET,
            .cs_da      = alt_qspi_ns_to_multiplier(ALT_QSPI_TSHSL_NS_DEF, qspi_clk_mhz),
            .cs_dads    = alt_qspi_ns_to_multiplier(ALT_QSPI_TSD2D_NS_DEF, qspi_clk_mhz),
            .cs_eot     = alt_qspi_ns_to_multiplier(ALT_QSPI_TCHSH_NS_DEF, qspi_clk_mhz),
            .cs_sot     = alt_qspi_ns_to_multiplier(ALT_QSPI_TSLCH_NS_DEF, qspi_clk_mhz),
            .rd_datacap = 1
        };

        dprintf("DEBUG[QSPI]: cs_da   = %" PRIu32 ".\n", timing_cfg.cs_da);
        dprintf("DEBUG[QSPI]: cs_dads = %" PRIu32 ".\n", timing_cfg.cs_dads);
        dprintf("DEBUG[QSPI]: cs_eot  = %" PRIu32 ".\n", timing_cfg.cs_eot);
        dprintf("DEBUG[QSPI]: cs_sot  = %" PRIu32 ".\n", timing_cfg.cs_sot);

        status = alt_qspi_timing_config_set(&timing_cfg);
    }

    /////

    // Configure the remap address register, no remap

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_ahb_remap_address_set(0);
    }

    // Configure the interrupt mask register, disabled all first

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_int_disable(ALT_QSPI_INT_STATUS_ALL);
    }

    // Configure the baud rate divisor
    // CASE 157095: Investigate using 108 MHz, and tweaking the rd_datacap param.

    if (status == ALT_E_SUCCESS)
    {
        uint32_t device_sclk_mhz = 54;
        uint32_t div_actual = (qspi_clk_mhz + (device_sclk_mhz - 1)) / device_sclk_mhz;
        dprintf("DEBUG[QSPI]: div_actual = %" PRIu32 ".\n", div_actual);

        ALT_QSPI_BAUD_DIV_t div_bits = (ALT_QSPI_BAUD_DIV_t)(((div_actual + 1) / 2) - 1);
        status = alt_qspi_baud_rate_div_set(div_bits);
    }

    return status;
}

ALT_STATUS_CODE alt_qspi_uninit(void)
{
    // Put QSPI controller into reset.
    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_QSPI_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_disable(void)
{
    alt_clrbits_word(ALT_QSPI_CFG_ADDR, ALT_QSPI_CFG_EN_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_enable(void)
{
    alt_setbits_word(ALT_QSPI_CFG_ADDR, ALT_QSPI_CFG_EN_SET_MSK);

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    /////

    // Device specific configuration

#if ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT
    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_N25Q_enable();
    }
#endif

    uint32_t rdid = 0;

    // Query device capabilities
    // This requires QSPI to be enabled.

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_device_rdid(&rdid);
    }

    if (status == ALT_E_SUCCESS)
    {
        // NOTE: The size code seems to be a form of BCD (binary coded decimal).
        //   The first nibble is the 10's digit and the second nibble is the 1's
        //   digit in the number of bytes.

        // Capacity ID samples:
        //  0x15 :   16 Mb =>   2 MiB => 1 << 21 ; BCD=15
        //  0x16 :   32 Mb =>   4 MiB => 1 << 22 ; BCD=16
        //  0x17 :   64 Mb =>   8 MiB => 1 << 23 ; BCD=17
        //  0x18 :  128 Mb =>  16 MiB => 1 << 24 ; BCD=18
        //  0x19 :  256 Mb =>  32 MiB => 1 << 25 ; BCD=19
        //  0x1a
        //  0x1b
        //  0x1c
        //  0x1d
        //  0x1e
        //  0x1f
        //  0x20 :  512 Mb =>  64 MiB => 1 << 26 ; BCD=20
        //  0x21 : 1024 Mb => 128 MiB => 1 << 27 ; BCD=21

        int cap_code = ALT_QSPI_STIG_RDID_CAPACITYID_GET(rdid);

        if ( ((cap_code >> 4) > 0x9) || ((cap_code & 0xf) > 0x9))
        {
            // If a non-valid BCD value is detected at the top or bottom nibble, chances
            // are that the chip has a problem.

            dprintf("DEBUG[QSPI]: Invalid CapacityID encountered: 0x%02x.\n", cap_code);
            status = ALT_E_ERROR;
        }
        else
        {
            int cap_decoded = ((cap_code >> 4) * 10) + (cap_code & 0xf);

            qspi_device_size = 1 << (cap_decoded + 6);

            dprintf("DEBUG[QSPI]: Device size = 0x%" PRIx32 ".\n", qspi_device_size);
        }
    }

    // Configure the device size and address bytes

    if (status == ALT_E_SUCCESS)
    {
        ALT_QSPI_DEV_SIZE_CONFIG_t size_cfg =
        {
            .block_size         = ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_RESET,  // 0x10  => 2^16 = 64 KiB
            .page_size          = ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_RESET, // 0x100 => 256 B
            .addr_size          = ALT_QSPI_DEVSZ_NUMADDRBYTES_RESET,       // 0x2   => 3 bytes or 0x00ffffff mask.
            .lower_wrprot_block = 0,
            .upper_wrprot_block = (qspi_device_size - 1) >> 16,
            .wrprot_enable      = ALT_QSPI_WRPROT_EN_RESET
        };

        status = alt_qspi_device_size_config_set(&size_cfg);
    }

    /////

    // Configure the DMA parameters

    // This will allow DMA to work well without much intervention by users.

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_dma_config_set(4, 32);
    }

    /////

    return status;
}

/////

uint32_t alt_qspi_int_status_get(void)
{
    // Read and return the value of the QSPI controller Interrupt Status
    // Register (irqstat).
    return alt_read_word(ALT_QSPI_IRQSTAT_ADDR);
}

ALT_STATUS_CODE alt_qspi_int_clear(const uint32_t mask)
{
    // Check that the [mask] contains valid interrupt status conditions values.
    if ((ALT_QSPI_INT_STATUS_ALL & mask) == 0)
    {
        return ALT_E_BAD_ARG;
    }

    // Write 1's to clear the desired interrupt status condition(s).
    alt_write_word(ALT_QSPI_IRQSTAT_ADDR, mask);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_int_disable(const uint32_t mask)
{
    if (alt_qspi_is_idle() == false)
    {
        return ALT_E_ERROR;
    }

    // Check that the [mask] contains valid interrupt status conditions values.
    if ((ALT_QSPI_INT_STATUS_ALL & mask) == 0)
    {
        return ALT_E_BAD_ARG;
    }

    // Write 0's to disable the desired interrupt status condition(s).
    alt_clrbits_word(ALT_QSPI_IRQMSK_ADDR, mask);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_int_enable(const uint32_t mask)
{
    if (alt_qspi_is_idle() == false)
    {
        return ALT_E_ERROR;
    }

    // Check that the [mask] contains valid interrupt status conditions values.
    if ((ALT_QSPI_INT_STATUS_ALL & mask) == 0)
    {
        return ALT_E_BAD_ARG;
    }

    // Write 1's to enable the desired interrupt status condition(s).
    alt_setbits_word(ALT_QSPI_IRQMSK_ADDR, mask);

    return ALT_E_SUCCESS;
}

/////

bool alt_qspi_is_idle(void)
{
    // If the idle field of the QSPI configuration register is 1 then the serial
    // interface and QSPI pipeline is idle.
    return ALT_QSPI_CFG_IDLE_GET(alt_read_word(ALT_QSPI_CFG_ADDR)) == 1;
}

/////

static ALT_STATUS_CODE alt_qspi_indirect_write_start_bank(uint32_t dst, size_t length);

static ALT_STATUS_CODE alt_qspi_indirect_page_bound_write_helper(uint32_t dst, const char * src, size_t length)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_indirect_write_start_bank(dst, length);
    }

    if (status == ALT_E_SUCCESS)
    {
        uint32_t write_count = 0;
        uint32_t write_capacity = ALT_QSPI_SRAM_FIFO_ENTRY_COUNT - alt_qspi_sram_partition_get();

        while (write_count < length)
        {
            uint32_t space = write_capacity - alt_qspi_indirect_write_fill_level();
            space = MIN(space, (length - write_count)/ sizeof(uint32_t));

            const uint32_t * data = (const uint32_t *)(src + write_count);
            for (uint32_t i = 0; i < space; ++i)
            {
                alt_write_word(ALT_QSPIDATA_ADDR, *data++);
            }

            write_count += space * sizeof(uint32_t);
        }
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_indirect_write_finish();
    }

    return status;
}

static ALT_STATUS_CODE alt_qspi_indirect_subsector_aligned_write_helper(const char * data, uint32_t subsec_addr)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    for (int i = 0; i < ALT_QSPI_SUBSECTOR_SIZE / ALT_QSPI_PAGE_SIZE; i++)
    {
        int offset = i * ALT_QSPI_PAGE_SIZE;

        status = alt_qspi_indirect_page_bound_write_helper(subsec_addr + offset, data + offset, ALT_QSPI_PAGE_SIZE);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }
    }

    return status;
}

static ALT_STATUS_CODE alt_qspi_indirect_read_start_bank(uint32_t src, size_t size);

//
// This helper function reads a segment of data, which is limited to 1 bank
// (24 bits of addressing).
//
static ALT_STATUS_CODE alt_qspi_read_bank(char * dst, uint32_t src, size_t size)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_indirect_read_start_bank(src, size);
    }

    if (status == ALT_E_SUCCESS)
    {
        uint32_t read_count = 0;

        while (!alt_qspi_indirect_read_is_complete())
        {
            uint32_t level = alt_qspi_indirect_read_fill_level();
//            level = MIN(level, (size - read_count) / sizeof(uint32_t));

            uint32_t * data = (uint32_t *)(dst + read_count);
            for (uint32_t i = 0; i < level; ++i)
            {
                *data++ = alt_read_word(ALT_QSPIDATA_ADDR);
            }

            read_count += level * sizeof(uint32_t);
        }
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_indirect_read_finish();
    }

    return status;
}

ALT_STATUS_CODE alt_qspi_read(void * dst, uint32_t src, size_t size)
{
    if (src >= qspi_device_size)
    {
        return ALT_E_ERROR;
    }

    if (src + size - 1 >= qspi_device_size)
    {
        return ALT_E_ERROR;
    }

    if (size == 0)
    {
        return ALT_E_SUCCESS;
    }

    if ((uintptr_t)dst & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (src & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (size & 0x3)
    {
        return ALT_E_ERROR;
    }

    /////

    // Verify that there is not already a read in progress.
    if (ALT_QSPI_INDRD_RD_STAT_GET(alt_read_word(ALT_QSPI_INDRD_ADDR)))
    {
        return ALT_E_ERROR;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    //
    // bank_count : The number of bank(s) affected, including partial banks.
    // bank_addr  : The aligned address of the first affected bank, including partial bank(s).
    // bank_ofst  : The offset of the bank to read. Only used when reading the first bank.
    //
    uint32_t bank_count = ((src + size - 1) >> 24) - (src >> 24) + 1;
    uint32_t bank_addr  = src & ALT_QSPI_BANK_ADDR_MSK;
    uint32_t bank_ofst  = src & (ALT_QSPI_BANK_SIZE - 1);

    char * data = (char *)dst;

    uint32_t copy_length = MIN(size, ALT_QSPI_BANK_SIZE - bank_ofst);

    dprintf("DEBUG[QSPI]: read(): bulk: mem_addr = %p; flash_addr = 0x%" PRIx32 ".\n", data, src);
    dprintf("DEBUG[QSPI]: read(): bulk: bank_count = 0x%" PRIx32 ", bank_ofst = 0x%" PRIx32 ".\n", bank_count, bank_ofst);

    for (uint32_t i = 0; i < bank_count; ++i)
    {
        dprintf("DEBUG[QSPI]: read(): bank 0x%" PRIx32 "; copy_length = 0x%" PRIx32 ".\n", bank_addr >> 24, copy_length);

        status = alt_qspi_device_bank_select(bank_addr >> 24);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        status = alt_qspi_read_bank(dst, bank_ofst, copy_length);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        bank_addr += ALT_QSPI_BANK_SIZE;
        data += copy_length;
        size -= copy_length;

        copy_length = MIN(size, ALT_QSPI_BANK_SIZE);
    }

    return status;
}

static ALT_STATUS_CODE alt_qspi_write_bank(uint32_t dst, const char * src, size_t size)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    /////

    uint32_t page_ofst  = dst & (ALT_QSPI_PAGE_SIZE - 1);
    uint32_t write_size = MIN(size, ALT_QSPI_PAGE_SIZE - page_ofst);

    while (size)
    {
        dprintf("DEBUG[QSPI]: write(): flash dst = 0x%" PRIx32 ", mem src = %p, write size = 0x%" PRIx32 ", size left = 0x%x.\n", dst, src, write_size, size);

        status = alt_qspi_indirect_page_bound_write_helper(dst, src, write_size);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        dst  += write_size;
        src  += write_size;
        size -= write_size;

        write_size = MIN(size, ALT_QSPI_PAGE_SIZE);
    }

    return status;
}

ALT_STATUS_CODE alt_qspi_write(uint32_t dst, const void * src, size_t size)
{
    if (dst >= qspi_device_size)
    {
        return ALT_E_ERROR;
    }

    if (dst + size - 1 >= qspi_device_size)
    {
        return ALT_E_ERROR;
    }

    if (size == 0)
    {
        return ALT_E_SUCCESS;
    }

    if ((uintptr_t)src & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (dst & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (size & 0x3)
    {
        return ALT_E_ERROR;
    }

    /////

    // Verify that there is not already a write in progress.
    if (ALT_QSPI_INDWR_RDSTAT_GET(alt_read_word(ALT_QSPI_INDWR_ADDR)))
    {
        return ALT_E_ERROR;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t bank_count = ((dst + size - 1) >> 24) - (dst >> 24) + 1;
    uint32_t bank_addr  = dst & ALT_QSPI_BANK_ADDR_MSK;
    uint32_t bank_ofst  = dst & (ALT_QSPI_BANK_SIZE - 1);

    const char * data  = src;

    uint32_t copy_length = MIN(size, ALT_QSPI_BANK_SIZE - bank_ofst);

    dprintf("DEBUG[QSPI]: write(): bulk: flash_addr = 0x%" PRIx32 "; mem_addr = %p.\n", dst, data);
    dprintf("DEBUG[QSPI]: write(): bulk: bank_count = 0x%" PRIx32 ", bank_ofst = 0x%" PRIx32 ".\n", bank_count, bank_ofst);

    for (uint32_t i = 0; i < bank_count; ++i)
    {
        dprintf("DEBUG[QSPI]: write(): bank 0x%" PRIx32 "; copy_length = 0x%" PRIx32 ".\n", bank_addr >> 24, copy_length);

        status = alt_qspi_device_bank_select(bank_addr >> 24);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        status = alt_qspi_write_bank(bank_ofst, data, copy_length);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        bank_addr += ALT_QSPI_BANK_SIZE;
        data += copy_length;
        size -= copy_length;

        copy_length = MIN(size, ALT_QSPI_BANK_SIZE);
    }

    return status;
}

static ALT_STATUS_CODE alt_qspi_erase_subsector_bank(uint32_t addr);

static ALT_STATUS_CODE alt_qspi_replace_bank(uint32_t dst, const char * src, size_t size)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    //
    // subsec_count        : The total number of affected subsector(s),
    //                       including partial subsector(s).
    // subsec_addr         : The aligned address of the next affected subsector,
    //                       including partial subsector(s).
    // subsec_partial_head : The number of subsector unaligned data to be
    //                       written out at the start of the flash write
    //                       request. This data ends at the end of the subsector
    //                       or earlier depending on the number of data to be
    //                       written.
    // subsec_partial_tail : The number of subsector unaligned data to be
    //                       written out at the end of the flash write request.
    //                       This data starts at the start of the subsector. If
    //                       only a single subsector is written (partial or
    //                       full), this value will be zero.
    //

    uint32_t subsec_count = ((dst + size - 1) >> 12) - (dst >> 12) + 1;
    uint32_t subsec_addr  = dst & ALT_QSPI_SUBSECTOR_ADDR_MSK;

    uint32_t subsec_partial_head = MIN(ALT_QSPI_SUBSECTOR_SIZE - (dst & (ALT_QSPI_SUBSECTOR_SIZE - 1)), size) & (ALT_QSPI_SUBSECTOR_SIZE - 1);
    uint32_t subsec_partial_tail = (size - subsec_partial_head) & (ALT_QSPI_SUBSECTOR_SIZE - 1);

    dprintf("DEBUG[QSPI]: replace(): report: dst = 0x%" PRIx32 "; size = 0x%x.\n",
            dst, size);
    dprintf("DEBUG[QSPI]: replace(): report: subsec_count = 0x%" PRIx32 "; subsec_addr = 0x%" PRIx32 ".\n",
            subsec_count, subsec_addr);
    dprintf("DEBUG[QSPI]: replace(): report: partial_head = 0x%" PRIx32 "; partial_tail = 0x%" PRIx32 ".\n",
            subsec_partial_head, subsec_partial_tail);

    // Write the first subsector, partial case.

    if (subsec_partial_head)
    {
        // The write request is not aligned to a subsector so we must do the
        // Read-Modify-Write cycle to preserve the existing data at the head of
        // the subsector not affected by the write.

        char subsec_buf[ALT_QSPI_SUBSECTOR_SIZE];

        uint32_t subsec_ofst = dst & ~ALT_QSPI_SUBSECTOR_ADDR_MSK;

        // - Read the subsector into buffer
        // - Erase that subsector
        // - Copy in the user data into buffer
        // - Write out buffer to subsector

        if (status == ALT_E_SUCCESS)
        {
            status = alt_qspi_read_bank(subsec_buf, subsec_addr, subsec_ofst);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_qspi_erase_subsector_bank(subsec_addr);
        }
        if (status == ALT_E_SUCCESS)
        {
            memcpy(subsec_buf + subsec_ofst, src, subsec_partial_head);
            status = alt_qspi_indirect_subsector_aligned_write_helper(subsec_buf, subsec_addr);
        }

        // Do some bookkeeping on the user buffer information
        src  += subsec_partial_head;
        size -= subsec_partial_head;

        // Do some bookkeeping on the subsector tracking
        subsec_count--;
        subsec_addr += ALT_QSPI_SUBSECTOR_SIZE;

        dprintf("DEBUG[QSPI]: replace(): partial head: subsec_ofst = 0x%" PRIx32 "; size left = 0x%x; status = %" PRIi32 ".\n",
                subsec_ofst, size, status);
    }

    // If there is a partial tail, then take 1 off the subsec_count. This way
    // the following loop will write out all the complete subsectors. The tail
    // will be written out afterwards.
    
    if (subsec_partial_tail)
    {
        subsec_count--;
    }

    // Write the aligned subsectors following any partial subsectors.

    for (uint32_t i = 0; i < subsec_count; ++i)
    {
        // - Erase subsector
        // - Write out buffer to subsector

        if (status == ALT_E_SUCCESS)
        {
            status = alt_qspi_erase_subsector_bank(subsec_addr);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_qspi_indirect_subsector_aligned_write_helper(src, subsec_addr);
        }

        src  += ALT_QSPI_SUBSECTOR_SIZE;
        size -= ALT_QSPI_SUBSECTOR_SIZE;

        // Don't modify subsec_count as it's being used by the loop.
        subsec_addr += ALT_QSPI_SUBSECTOR_SIZE;

        dprintf("DEBUG[QSPI]: replace(): subsec aligned: size left = 0x%x, status = %" PRIi32 ".\n",
                size, status);
    }

    // Write the last subsector, partial case.

    if (subsec_partial_tail)
    {
        // The write request is not aligned to a subsector so we must do the
        // Read-Modify-Write cycle to preserve the existing data at the end of
        // the subsector not affected by the write.

        char subsec_buf[ALT_QSPI_SUBSECTOR_SIZE];

        // - Read the subsector into buffer
        // - Erase that subsector
        // - Copy in the user data into buffer
        // - Write out buffer to subsector

        if (status == ALT_E_SUCCESS)
        {
            status = alt_qspi_read_bank(subsec_buf  + subsec_partial_tail,
                                        subsec_addr + subsec_partial_tail,
                                        ALT_QSPI_SUBSECTOR_SIZE - subsec_partial_tail);
        }
        if (status == ALT_E_SUCCESS)
        {
            status = alt_qspi_erase_subsector_bank(subsec_addr);
        }
        if (status == ALT_E_SUCCESS)
        {
            memcpy(subsec_buf, src, subsec_partial_tail);
            status = alt_qspi_indirect_subsector_aligned_write_helper(subsec_buf, subsec_addr);
        }

        src  += subsec_partial_tail;
        size -= subsec_partial_tail;

        dprintf("DEBUG[QSPI]: replace(): partial tail: size left = 0x%x, status = %" PRIi32 ".\n",
                size, status);
    }

    return status;
}

ALT_STATUS_CODE alt_qspi_replace(uint32_t dst, const void * src, size_t size)
{
    if (dst >= qspi_device_size)
    {
        return ALT_E_ERROR;
    }

    if (dst + size - 1 >= qspi_device_size)
    {
        return ALT_E_ERROR;
    }

    if (size == 0)
    {
        return ALT_E_SUCCESS;
    }

    if ((uintptr_t)src & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (dst & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (size & 0x3)
    {
        return ALT_E_ERROR;
    }

    /////

    // Verify that there is not already a read in progress.
    if (ALT_QSPI_INDRD_RD_STAT_GET(alt_read_word(ALT_QSPI_INDRD_ADDR)))
    {
        return ALT_E_ERROR;
    }

    // Verify that there is not already a write in progress.
    if (ALT_QSPI_INDWR_RDSTAT_GET(alt_read_word(ALT_QSPI_INDWR_ADDR)))
    {
        return ALT_E_ERROR;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t bank_count = ((dst + size - 1) >> 24) - (dst >> 24) + 1;
    uint32_t bank_addr  = dst & ALT_QSPI_BANK_ADDR_MSK;
    uint32_t bank_ofst  = dst & (ALT_QSPI_BANK_SIZE - 1);

    const char * data = (const char *)src;

    uint32_t copy_length = MIN(size, ALT_QSPI_BANK_SIZE - bank_ofst);

    dprintf("DEBUG[QSPI]: replace(): bulk: flash_addr = 0x%" PRIx32 "; mem_addr = %p.\n", dst, data);
    dprintf("DEBUG[QSPI]: replace(): bulk: bank_count = 0x%" PRIx32 ", bank_ofst = 0x%" PRIx32 ".\n", bank_count, bank_ofst);

    for (uint32_t i = 0; i < bank_count; ++i)
    {
        dprintf("DEBUG[QSPI]: replace(): bank 0x%" PRIx32 "; copy_length = 0x%" PRIx32 ".\n", bank_addr >> 24, copy_length);

        status = alt_qspi_device_bank_select(bank_addr >> 24);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        status = alt_qspi_replace_bank(bank_ofst, data, copy_length);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        bank_addr += ALT_QSPI_BANK_SIZE;
        data += copy_length;
        size -= copy_length;

        copy_length = MIN(size, ALT_QSPI_BANK_SIZE);
    }

    return status;
}

/////

ALT_QSPI_BAUD_DIV_t alt_qspi_baud_rate_div_get(void)
{
    uint32_t baud_rate_div = ALT_QSPI_CFG_BAUDDIV_GET(alt_read_word(ALT_QSPI_CFG_ADDR));
    return (ALT_QSPI_BAUD_DIV_t) baud_rate_div;
}

ALT_STATUS_CODE alt_qspi_baud_rate_div_set(const ALT_QSPI_BAUD_DIV_t baud_rate_div)
{
    if (0xf < (uint32_t)baud_rate_div)
    {
        // Invalid baud rate divisor value.
        return ALT_E_BAD_ARG;
    }

    // Set the Master Mode Baud Rate Divisor Field of the QSPI Configuration Register.
    alt_replbits_word(ALT_QSPI_CFG_ADDR,
                      ALT_QSPI_CFG_BAUDDIV_SET_MSK,
                      ALT_QSPI_CFG_BAUDDIV_SET(baud_rate_div));

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_chip_select_config_get(uint32_t* cs,
                                                ALT_QSPI_CS_MODE_t* cs_mode)
{
    uint32_t cfg = alt_read_word(ALT_QSPI_CFG_ADDR);

    *cs      = ALT_QSPI_CFG_PERCSLINES_GET(cfg);
    *cs_mode = (ALT_QSPI_CS_MODE_t) ALT_QSPI_CFG_PERSELDEC_GET(cfg);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_chip_select_config_set(const uint32_t cs,
                                                const ALT_QSPI_CS_MODE_t cs_mode)
{
    // chip select cs:
    // four bit value, bit 0 = cs0, bit 1 = cs1, bit 2 = cs2, bit 3 = cs3
    // since cs is low true, the value of each bit should be zero if enable the cs.
    // 
    // also allows multiple cs line enabled together.
 
    if (cs > ((1 << ALT_QSPI_CFG_PERCSLINES_WIDTH) - 1))
    {
        // [cs] not within possible 4 bit chip select line value range.
        return ALT_E_ARG_RANGE;
    }

    if ((cs_mode != ALT_QSPI_CS_MODE_SINGLE_SELECT) && (cs_mode != ALT_QSPI_CS_MODE_DECODE))
    {
        return ALT_E_INV_OPTION;
    }

    // Update the Peripheral Chip Select Lines and Peripheral Select Decode
    // Fields of the QSPI Configuration Register value with the chip select
    // options.
    uint32_t cfg = alt_read_word(ALT_QSPI_CFG_ADDR);
    cfg &= ALT_QSPI_CFG_PERCSLINES_CLR_MSK & ALT_QSPI_CFG_PERSELDEC_CLR_MSK;
    cfg |= ALT_QSPI_CFG_PERCSLINES_SET(cs) | ALT_QSPI_CFG_PERSELDEC_SET(cs_mode);
    alt_write_word(ALT_QSPI_CFG_ADDR, cfg);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_mode_bit_disable(void)
{
    // Clear the Mode Bit Enable Field of the Device Read Instruction Register
    // to disable mode bits from being sent after the address bytes.
    alt_clrbits_word(ALT_QSPI_DEVRD_ADDR, ALT_QSPI_DEVRD_ENMODBITS_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_mode_bit_enable(void)
{
    // Set the Mode Bit Enable Field of the Device Read Instruction Register
    // to enable mode bits to be sent after the address bytes.
    alt_setbits_word(ALT_QSPI_DEVRD_ADDR, ALT_QSPI_DEVRD_ENMODBITS_SET_MSK);

    return ALT_E_SUCCESS;
}

uint32_t alt_qspi_mode_bit_config_get(void)
{
    // Return the 8 bit value from the Mode Field of the Mode Bit Configuration
    // Register.
    return ALT_QSPI_MODBIT_MOD_GET(alt_read_word(ALT_QSPI_MODBIT_ADDR));
}

ALT_STATUS_CODE alt_qspi_mode_bit_config_set(const uint32_t mode_bits)
{
    if (alt_qspi_is_idle() == false)
    {
        return ALT_E_ERROR;
    }

    if (mode_bits > ((1 << ALT_QSPI_MODBIT_MOD_WIDTH) - 1))
    {
        // 'mode_bits' not within possible 8 bit mode value range.
        return ALT_E_ARG_RANGE;
    }

    // Set the 8 bit value in the Mode Field of the Mode Bit Configuration
    // Register.
    alt_replbits_word(ALT_QSPI_MODBIT_ADDR,
                      ALT_QSPI_MODBIT_MOD_SET_MSK,
                      ALT_QSPI_MODBIT_MOD_SET(mode_bits));

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_device_size_config_get(ALT_QSPI_DEV_SIZE_CONFIG_t * cfg)
{
    // Although not required, it is recommended that the write protect feature
    // be enabled prior to enabling the QSPI controller. This will block any AHB
    // writes from taking effect. This also means the write protection registers
    // (Lower Write Protection, Upper Write Protection, and Write Protection)
    // should be setup and the number of bytes per device block in the device
    // size configuration register should be setup prior to enabling the QSPI
    // controller.

    // Read Device Size Register and get the Number of Bytes per Block, Number
    // of Bytes per Device, and Number of Address Bytes Fields.

    uint32_t devsz = alt_read_word(ALT_QSPI_DEVSZ_ADDR);

    cfg->block_size = ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_GET(devsz);
    cfg->page_size  = ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_GET(devsz);
    cfg->addr_size  = ALT_QSPI_DEVSZ_NUMADDRBYTES_GET(devsz);

    // Read Lower Write Protection, Upper Write Protection, and Write Protection
    // Registers.

    cfg->lower_wrprot_block = ALT_QSPI_LOWWRPROT_SUBSECTOR_GET(alt_read_word(ALT_QSPI_LOWWRPROT_ADDR));
    cfg->upper_wrprot_block = ALT_QSPI_UPPWRPROT_SUBSECTOR_GET(alt_read_word(ALT_QSPI_UPPWRPROT_ADDR));
    cfg->wrprot_enable      = ALT_QSPI_WRPROT_EN_GET(alt_read_word(ALT_QSPI_WRPROT_ADDR));

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_device_size_config_set(const ALT_QSPI_DEV_SIZE_CONFIG_t * cfg)
{
    if (cfg->block_size > ((1 << ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_WIDTH) - 1))
    {
        return ALT_E_ARG_RANGE;
    }

    if (cfg->page_size > ((1 << ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_WIDTH) - 1))
    {
        return ALT_E_ARG_RANGE;
    }

    if (cfg->addr_size > ((1 << ALT_QSPI_DEVSZ_NUMADDRBYTES_WIDTH) - 1))
    {
        return ALT_E_ARG_RANGE;
    }

    if (cfg->lower_wrprot_block > cfg->upper_wrprot_block)
    {
        // Null write protection regions are not allowed.
        return ALT_E_ARG_RANGE;
    }

    /////

    uint32_t value = ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_SET(cfg->block_size) |
                     ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_SET(cfg->page_size) |
                     ALT_QSPI_DEVSZ_NUMADDRBYTES_SET(cfg->addr_size);

    alt_write_word(ALT_QSPI_DEVSZ_ADDR, value);

    if (cfg->wrprot_enable)
    {
        alt_write_word(ALT_QSPI_LOWWRPROT_ADDR, cfg->lower_wrprot_block);
        alt_write_word(ALT_QSPI_UPPWRPROT_ADDR, cfg->upper_wrprot_block);
    }

    // Read Upper Write Protection Register - uppwrprot.
    // Set the Write Protection Enable Bit Field of the Write Protection
    // Register accordingly.
    if (cfg->wrprot_enable)
    {
        alt_setbits_word(ALT_QSPI_WRPROT_ADDR, ALT_QSPI_WRPROT_EN_SET(1));
    }
    else
    {
        alt_clrbits_word(ALT_QSPI_WRPROT_ADDR, ALT_QSPI_WRPROT_EN_SET(1));
    }
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_device_read_config_get(ALT_QSPI_DEV_INST_CONFIG_t * cfg)
{
    // Read the Device Read Instruction Register - devrd.
    uint32_t devrd = alt_read_word(ALT_QSPI_DEVRD_ADDR);

    cfg->op_code        = ALT_QSPI_DEVRD_RDOPCODE_GET(devrd);
    cfg->inst_type      = (ALT_QSPI_MODE_t) ALT_QSPI_DEVRD_INSTWIDTH_GET(devrd);
    cfg->addr_xfer_type = (ALT_QSPI_MODE_t) ALT_QSPI_DEVRD_ADDRWIDTH_GET(devrd);
    cfg->data_xfer_type = (ALT_QSPI_MODE_t) ALT_QSPI_DEVRD_DATAWIDTH_GET(devrd);
    cfg->dummy_cycles   = ALT_QSPI_DEVRD_DUMMYRDCLKS_GET(devrd);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_device_read_config_set(const ALT_QSPI_DEV_INST_CONFIG_t * cfg)
{
    if (alt_qspi_is_idle() == false)
    {
        return ALT_E_ERROR;
    }

    // Validate input

    if (cfg->op_code > ((1 << ALT_QSPI_DEVRD_RDOPCODE_WIDTH) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    switch (cfg->inst_type)
    {
    case ALT_QSPI_MODE_SINGLE:
    case ALT_QSPI_MODE_DUAL:
    case ALT_QSPI_MODE_QUAD:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    switch (cfg->addr_xfer_type)
    {
    case ALT_QSPI_MODE_SINGLE:
    case ALT_QSPI_MODE_DUAL:
    case ALT_QSPI_MODE_QUAD:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    switch (cfg->data_xfer_type)
    {
    case ALT_QSPI_MODE_SINGLE:
    case ALT_QSPI_MODE_DUAL:
    case ALT_QSPI_MODE_QUAD:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    if (cfg->dummy_cycles > ((1 << ALT_QSPI_DEVRD_DUMMYRDCLKS_WIDTH) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    /////

    // Read the Device Read Instruction Register - devrd.
    uint32_t devrd = alt_read_word(ALT_QSPI_DEVRD_ADDR);

    devrd &= ALT_QSPI_DEVRD_RDOPCODE_CLR_MSK &
             ALT_QSPI_DEVRD_INSTWIDTH_CLR_MSK &
             ALT_QSPI_DEVRD_ADDRWIDTH_CLR_MSK &
             ALT_QSPI_DEVRD_DATAWIDTH_CLR_MSK &
             ALT_QSPI_DEVRD_DUMMYRDCLKS_CLR_MSK;

    devrd |= ALT_QSPI_DEVRD_RDOPCODE_SET(cfg->op_code) |
             ALT_QSPI_DEVRD_INSTWIDTH_SET(cfg->inst_type) |
             ALT_QSPI_DEVRD_ADDRWIDTH_SET(cfg->addr_xfer_type) |
             ALT_QSPI_DEVRD_DATAWIDTH_SET(cfg->data_xfer_type) |
             ALT_QSPI_DEVRD_DUMMYRDCLKS_SET(cfg->dummy_cycles);

    alt_write_word(ALT_QSPI_DEVRD_ADDR, devrd);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_device_write_config_get(ALT_QSPI_DEV_INST_CONFIG_t * cfg)
{
    // Device Write Instruction Register - devwr.
    uint32_t devwr = alt_read_word(ALT_QSPI_DEVWR_ADDR);

    cfg->op_code        = ALT_QSPI_DEVWR_WROPCODE_GET(devwr);
    // The Instruction Type field in the Device READ Instruction Register only appears
    // once and applies to both READ and WRITE opertions. it is not included in the
    // Device WRITE Instruction Register.
    cfg->inst_type      = (ALT_QSPI_MODE_t) ALT_QSPI_DEVRD_INSTWIDTH_GET(alt_read_word(ALT_QSPI_DEVRD_ADDR));
    cfg->addr_xfer_type = (ALT_QSPI_MODE_t) ALT_QSPI_DEVWR_ADDRWIDTH_GET(devwr);
    cfg->data_xfer_type = (ALT_QSPI_MODE_t) ALT_QSPI_DEVWR_DATAWIDTH_GET(devwr);
    cfg->dummy_cycles   = ALT_QSPI_DEVWR_DUMMYWRCLKS_GET(devwr);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_device_write_config_set(const ALT_QSPI_DEV_INST_CONFIG_t * cfg)
{
    if (alt_qspi_is_idle() == false)
    {
        return ALT_E_ERROR;
    }

    // Validate input

    if (cfg->op_code > ((1 << ALT_QSPI_DEVWR_WROPCODE_WIDTH) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    switch (cfg->inst_type)
    {
    case ALT_QSPI_MODE_SINGLE:
    case ALT_QSPI_MODE_DUAL:
    case ALT_QSPI_MODE_QUAD:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    switch (cfg->addr_xfer_type)
    {
    case ALT_QSPI_MODE_SINGLE:
    case ALT_QSPI_MODE_DUAL:
    case ALT_QSPI_MODE_QUAD:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    switch (cfg->data_xfer_type)
    {
    case ALT_QSPI_MODE_SINGLE:
    case ALT_QSPI_MODE_DUAL:
    case ALT_QSPI_MODE_QUAD:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    if (cfg->dummy_cycles > ((1 << ALT_QSPI_DEVWR_DUMMYWRCLKS_WIDTH) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    /////

    // Read the Device Write Instruction Register - devwr.
    uint32_t devwr = alt_read_word(ALT_QSPI_DEVWR_ADDR);

    devwr &= ALT_QSPI_DEVWR_WROPCODE_CLR_MSK &
             ALT_QSPI_DEVWR_ADDRWIDTH_CLR_MSK &
             ALT_QSPI_DEVWR_DATAWIDTH_CLR_MSK &
             ALT_QSPI_DEVWR_DUMMYWRCLKS_CLR_MSK;

    devwr |= ALT_QSPI_DEVWR_WROPCODE_SET(cfg->op_code) |
             ALT_QSPI_DEVWR_ADDRWIDTH_SET(cfg->addr_xfer_type) |
             ALT_QSPI_DEVWR_DATAWIDTH_SET(cfg->data_xfer_type) |
             ALT_QSPI_DEVWR_DUMMYWRCLKS_SET(cfg->dummy_cycles);

    alt_write_word(ALT_QSPI_DEVWR_ADDR, devwr);

    // The Instruction Type field in the Device READ Instruction Register only appears
    // once and applies to both READ and WRITE operations - it is not included in the
    // Device WRITE Instruction Register. Therefore, modify the Instruction Type
    // Field in the Device Read Register.
    alt_replbits_word(ALT_QSPI_DEVRD_ADDR,
                      ALT_QSPI_DEVRD_INSTWIDTH_SET_MSK,
                      ALT_QSPI_DEVRD_INSTWIDTH_SET((uint32_t) cfg->inst_type));

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_timing_config_get(ALT_QSPI_TIMING_CONFIG_t * cfg)
{
    // QSPI Configuration Register - cfg
    uint32_t cfgreg = alt_read_word(ALT_QSPI_CFG_ADDR);
    cfg->clk_phase  = (ALT_QSPI_CLK_PHASE_t) ALT_QSPI_CFG_SELCLKPHASE_GET(cfgreg);
    cfg->clk_pol    = (ALT_QSPI_CLK_POLARITY_t) ALT_QSPI_CFG_SELCLKPOL_GET(cfgreg);

    // QSPI Device Delay Register
    uint32_t delayreg = alt_read_word(ALT_QSPI_DELAY_ADDR);
    cfg->cs_sot  = ALT_QSPI_DELAY_INIT_GET(delayreg);
    cfg->cs_eot  = ALT_QSPI_DELAY_AFTER_GET(delayreg);
    cfg->cs_dads = ALT_QSPI_DELAY_BTWN_GET(delayreg);
    cfg->cs_da   = ALT_QSPI_DELAY_NSS_GET(delayreg);

    // Read Data Capture Register
    cfg->rd_datacap = ALT_QSPI_RDDATACAP_DELAY_GET(alt_read_word(ALT_QSPI_RDDATACAP_ADDR));

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_timing_config_set(const ALT_QSPI_TIMING_CONFIG_t * cfg)
{
    if (alt_qspi_is_idle() == false)
    {
        return ALT_E_ERROR;
    }

    // Validate parameter(s)

    switch (cfg->clk_phase)
    {
    case ALT_QSPI_CLK_PHASE_ACTIVE:
    case ALT_QSPI_CLK_PHASE_INACTIVE:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    switch (cfg->clk_pol)
    {
    case ALT_QSPI_CLK_POLARITY_LOW:
    case ALT_QSPI_CLK_POLARITY_HIGH:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    if (cfg->cs_da > ((1 << ALT_QSPI_DELAY_NSS_WIDTH) - 1))
    {
        return ALT_E_BAD_ARG;
    }
    if (cfg->cs_dads > ((1 << ALT_QSPI_DELAY_BTWN_WIDTH) - 1))
    {
        return ALT_E_BAD_ARG;
    }
    if (cfg->cs_eot > ((1 << ALT_QSPI_DELAY_AFTER_WIDTH) - 1))
    {
        return ALT_E_BAD_ARG;
    }
    if (cfg->cs_sot > ((1 << ALT_QSPI_DELAY_INIT_WIDTH) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    if (cfg->rd_datacap > ((1 << ALT_QSPI_RDDATACAP_DELAY_WIDTH) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    /////

    // QSPI Configuration Register - cfg
    uint32_t cfgreg = alt_read_word(ALT_QSPI_CFG_ADDR);
    cfgreg &= ALT_QSPI_CFG_SELCLKPHASE_CLR_MSK &
              ALT_QSPI_CFG_SELCLKPOL_CLR_MSK;
    cfgreg |= ALT_QSPI_CFG_SELCLKPHASE_SET(cfg->clk_phase) |
              ALT_QSPI_CFG_SELCLKPOL_SET(cfg->clk_pol);
    alt_write_word(ALT_QSPI_CFG_ADDR, cfgreg);

    // QSPI Device Delay Register
    uint32_t delayreg = ALT_QSPI_DELAY_INIT_SET(cfg->cs_sot)  |
                        ALT_QSPI_DELAY_AFTER_SET(cfg->cs_eot) |
                        ALT_QSPI_DELAY_BTWN_SET(cfg->cs_dads) |
                        ALT_QSPI_DELAY_NSS_SET(cfg->cs_da);
    alt_write_word(ALT_QSPI_DELAY_ADDR, delayreg);

    // Read Data Capture Register

    alt_write_word(ALT_QSPI_RDDATACAP_ADDR,
                   ALT_QSPI_RDDATACAP_BYP_SET(1) | 
                   ALT_QSPI_RDDATACAP_DELAY_SET(cfg->rd_datacap));

    return ALT_E_SUCCESS;
}

/////

ALT_STATUS_CODE alt_qspi_direct_disable(void)
{
    // Clear (set to 0) the Enable Direct Access Controller Field of the QSPI
    // Configuration Register to disable the Direct Access Controller.
    alt_clrbits_word(ALT_QSPI_CFG_ADDR, ALT_QSPI_CFG_ENDIRACC_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_direct_enable(void)
{
    // Set (set to 1) the Enable Direct Access Controller Field of the QSPI
    // Configuration Register to enable the Direct Access Controller.
    alt_setbits_word(ALT_QSPI_CFG_ADDR, ALT_QSPI_CFG_ENDIRACC_SET_MSK);

    return ALT_E_SUCCESS;
}

uint32_t alt_qspi_ahb_remap_address_get(void)
{
    // Read and return the value of the Remap Address Register.
    return ALT_QSPI_REMAPADDR_VALUE_GET(alt_read_word(ALT_QSPI_REMAPADDR_ADDR));
}

ALT_STATUS_CODE alt_qspi_ahb_remap_address_set(const uint32_t ahb_remap_addr)
{
    if (alt_qspi_is_idle() == false)
    {
        return ALT_E_ERROR;
    }

    // Read and return the value of the Remap Address Register.
    alt_setbits_word(ALT_QSPI_REMAPADDR_ADDR, ALT_QSPI_REMAPADDR_VALUE_SET(ahb_remap_addr));

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_ahb_address_remap_disable(void)
{
    // Clear (set to 0) the Enable AHB Address Remapping Field of the QSPI
    // Configuration Register to disable AHB address remapping.
    alt_clrbits_word(ALT_QSPI_CFG_ADDR, ALT_QSPI_CFG_ENAHBREMAP_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_ahb_address_remap_enable(void)
{
    // Set (set to 1) the Enable AHB Address Remapping Field of the QSPI
    // Configuration Register to enable AHB address remapping.
    alt_setbits_word(ALT_QSPI_CFG_ADDR, ALT_QSPI_CFG_ENAHBREMAP_SET_MSK);

    return ALT_E_SUCCESS;
}

/////

static ALT_STATUS_CODE alt_qspi_indirect_read_start_bank(uint32_t flash_addr,
                                                         size_t num_bytes)
{
    alt_write_word(ALT_QSPI_INDRDSTADDR_ADDR, flash_addr);
    alt_write_word(ALT_QSPI_INDRDCNT_ADDR, num_bytes);
    alt_write_word(ALT_QSPI_INDRD_ADDR, ALT_QSPI_INDRD_START_SET_MSK |
                                        ALT_QSPI_INDRD_IND_OPS_DONE_STAT_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_indirect_read_start(const uint32_t flash_addr,
                                             const size_t num_bytes)
{
    // flash_addr and num_bytes restriction is to prevent possible unaligned
    // exceptions.

    if (flash_addr & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (num_bytes & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (num_bytes == 0)
    {
        // Do not report this as a success. If a indirect read was not
        // previously completed, it may be cleared already, at which point
        // alt_qspi_indirect_read_is_complete() will never report true.
        return ALT_E_ERROR;
    }

    if (flash_addr > qspi_device_size)
    {
        return ALT_E_ERROR;
    }

    if (flash_addr + num_bytes > qspi_device_size)
    {
        return ALT_E_ERROR;
    }

    // Verify request does not cross bank boundary.
    // This limitation is due to the 3-byte addressing limitation.
    if ((flash_addr & ALT_QSPI_BANK_ADDR_MSK) != ((flash_addr + num_bytes - 1) & ALT_QSPI_BANK_ADDR_MSK))
    {
        return ALT_E_ERROR;
    }

    // Verify that there is not already a read in progress.
    if (ALT_QSPI_INDRD_RD_STAT_GET(alt_read_word(ALT_QSPI_INDRD_ADDR)))
    {
        return ALT_E_ERROR;
    }

    /////

    ALT_STATUS_CODE status;
    status = alt_qspi_device_bank_select(flash_addr >> 24);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    /////

    return alt_qspi_indirect_read_start_bank(flash_addr,
                                             num_bytes);

}

ALT_STATUS_CODE alt_qspi_indirect_read_finish(void)
{
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_indirect_read_cancel(void)
{
    // An indirect operation may be cancelled at any time by setting Indirect
    // Transfer Control Register bit [1].
    alt_write_word(ALT_QSPI_INDRD_ADDR, ALT_QSPI_INDRD_CANCEL_SET_MSK);

    return ALT_E_SUCCESS;
}

uint32_t alt_qspi_indirect_read_fill_level(void)
{
    // Return the SRAM Fill Level (Indirect Read Partition) Field of the SRAM
    // Fill Register to get the SRAM Fill Level for the Indirect Read Partition
    // in units of SRAM Words (4 bytes).
    return ALT_QSPI_SRAMFILL_INDRDPART_GET(alt_read_word(ALT_QSPI_SRAMFILL_ADDR));
}

uint32_t alt_qspi_indirect_read_watermark_get(void)
{
    // Return the Watermark value in the Indirect Read Transfer Watermark Register.
    return alt_read_word(ALT_QSPI_INDRDWATER_ADDR);
}

ALT_STATUS_CODE alt_qspi_indirect_read_watermark_set(const uint32_t watermark)
{
    // Verify that there is not already a read in progress.
    if (ALT_QSPI_INDRD_RD_STAT_GET(alt_read_word(ALT_QSPI_INDRD_ADDR)))
    {
        return ALT_E_ERROR;
    }

    // Set the Watermark value in the Indirect Read Transfer Watermark Register.
    alt_write_word(ALT_QSPI_INDRDWATER_ADDR, watermark);

    return ALT_E_SUCCESS;
}

bool alt_qspi_indirect_read_is_complete(void)
{
    // The value of the Indirect Completion Status Field of the Indirect Read
    // Transfer Control Register is set by hardware when an indirect read
    // operation has completed.
    return (alt_read_word(ALT_QSPI_INDRD_ADDR) & ALT_QSPI_INDRD_IND_OPS_DONE_STAT_SET_MSK) != 0;
}

static ALT_STATUS_CODE alt_qspi_indirect_write_start_bank(uint32_t flash_addr,
                                                          size_t num_bytes)
{
    alt_write_word(ALT_QSPI_INDWRSTADDR_ADDR, flash_addr);
    alt_write_word(ALT_QSPI_INDWRCNT_ADDR, num_bytes);
    alt_write_word(ALT_QSPI_INDWR_ADDR, ALT_QSPI_INDWR_START_SET_MSK |
                                        ALT_QSPI_INDWR_INDDONE_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_indirect_write_start(const uint32_t flash_addr,
                                              const size_t num_bytes)
{
    // flash_addr and num_bytes restriction is to prevent possible unaligned
    // exceptions.

    if (flash_addr & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (num_bytes & 0x3)
    {
        return ALT_E_ERROR;
    }

    if (num_bytes == 0)
    {
        // Do not report this as a success. If a indirect write was not
        // previously completed, it may be cleared already, at which point
        // alt_qspi_indirect_write_is_complete() will never report true.
        return ALT_E_ERROR;
    }

    if (num_bytes > 256)
    {
        // The Micron part can only write up to 256 bytes at a time.
        return ALT_E_ERROR;
    }

    if (flash_addr > qspi_device_size)
    {
        return ALT_E_ERROR;
    }

    if (flash_addr + num_bytes > qspi_device_size)
    {
        return ALT_E_ERROR;
    }

/*
    // Verify request does not cross bank boundary.
    // This limitation is due to the 3-byte addressing limitation.
    if ((flash_addr & ALT_QSPI_BANK_ADDR_MSK) != ((flash_addr + num_bytes - 1) & ALT_QSPI_BANK_ADDR_MSK))
    {
        return ALT_E_ERROR;
    }
*/
    // Verify request does not cross page boundary.
    // This limitation is in place for the Micron part used.
    if ((flash_addr & ALT_QSPI_PAGE_ADDR_MSK) != ((flash_addr + num_bytes - 1) & ALT_QSPI_PAGE_ADDR_MSK))
    {
        return ALT_E_ERROR;
    }

    // Verify that there is not already a write in progress.
    if (ALT_QSPI_INDWR_RDSTAT_GET(alt_read_word(ALT_QSPI_INDWR_ADDR)))
    {
        return ALT_E_ERROR;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    status = alt_qspi_device_bank_select(flash_addr >> 24);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    /////

    return alt_qspi_indirect_write_start_bank(flash_addr,
                                              num_bytes);
}

ALT_STATUS_CODE alt_qspi_indirect_write_finish(void)
{
#if ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT
    return alt_qspi_N25Q_flag_wait_for_program(ALT_QSPI_TIMEOUT_INFINITE);
#else
    return ALT_E_SUCCESS;
#endif
}

ALT_STATUS_CODE alt_qspi_indirect_write_cancel(void)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

#if ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT
    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_N25Q_flag_wait_for_program(ALT_QSPI_TIMEOUT_INFINITE);
    }
#endif

    if (status == ALT_E_SUCCESS)
    {
        // An indirect operation may be cancelled at any time by setting Indirect
        // Transfer Control Register bit [1].
        alt_write_word(ALT_QSPI_INDWR_ADDR, ALT_QSPI_INDWR_CANCEL_SET_MSK);
    }

    return status;
}

uint32_t alt_qspi_indirect_write_fill_level(void)
{
    // Return the SRAM Fill Level (Indirect Write Partition) Field of the SRAM
    // Fill Register to get the SRAM Fill Level for the Indirect Write Partition
    // in units of SRAM Words (4 bytes).
    return ALT_QSPI_SRAMFILL_INDWRPART_GET(alt_read_word(ALT_QSPI_SRAMFILL_ADDR));
}

uint32_t alt_qspi_indirect_write_watermark_get(void)
{
    // Return the Watermark value in the Indirect Write Transfer Watermark Register.
    return alt_read_word(ALT_QSPI_INDWRWATER_ADDR);
}

ALT_STATUS_CODE alt_qspi_indirect_write_watermark_set(const uint32_t watermark)
{
    // Verify that there is not already a write in progress.
    if (ALT_QSPI_INDWR_RDSTAT_GET(alt_read_word(ALT_QSPI_INDWR_ADDR)))
    {
        return ALT_E_ERROR;
    }

    // Set the Watermark value in the Indirect Write Transfer Watermark Register.
    alt_write_word(ALT_QSPI_INDWRWATER_ADDR, watermark);

    return ALT_E_SUCCESS;
}

bool alt_qspi_indirect_write_is_complete(void)
{
    // The value of the Indirect Completion Status Field of the Indirect Write
    // Transfer Control Register is set by hardware when an indirect write
    // operation has completed.
    return (alt_read_word(ALT_QSPI_INDWR_ADDR) & ALT_QSPI_INDWR_INDDONE_SET_MSK) != 0;
}

/////

uint32_t alt_qspi_sram_partition_get(void)
{
    // The number of locations allocated to indirect read is equal to the value
    // of the SRAM partition register. See the documentation for this function
    // regarding the + 1 in the IP documentation. This way the get() and set()
    // will be symmetrical.

    return ALT_QSPI_SRAMPART_ADDR_GET(alt_read_word(ALT_QSPI_SRAMPART_ADDR));
}

ALT_STATUS_CODE alt_qspi_sram_partition_set(const uint32_t read_part_size)
{
    if (read_part_size > ((1 << ALT_QSPI_SRAMPART_ADDR_WIDTH) - 1))
    {
        return ALT_E_ARG_RANGE;
    }

    alt_replbits_word(ALT_QSPI_SRAMPART_ADDR,
                      ALT_QSPI_SRAMPART_ADDR_SET_MSK,
                      ALT_QSPI_SRAMPART_ADDR_SET(read_part_size));

    return ALT_E_SUCCESS;
}

/////


static ALT_STATUS_CODE alt_qspi_erase_subsector_bank(uint32_t addr)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_device_wren();
    }
    
    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_stig_addr_cmd(ALT_QSPI_STIG_OPCODE_SUBSEC_ERASE, 0, addr, 10000);
    }

#if ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT
    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_N25Q_flag_wait_for_erase(ALT_QSPI_TIMEOUT_INFINITE);
    }
#endif

    return status;
}

ALT_STATUS_CODE alt_qspi_erase_subsector(const uint32_t addr)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_device_bank_select(addr >> 24);
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_erase_subsector_bank(addr);
    }

    return status;
}

ALT_STATUS_CODE alt_qspi_erase_sector(const uint32_t addr)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_device_bank_select(addr >> 24);
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_device_wren();
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_stig_addr_cmd(ALT_QSPI_STIG_OPCODE_SEC_ERASE, 0, addr, ALT_QSPI_TIMEOUT_INFINITE);
    }

#if ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT
    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_N25Q_flag_wait_for_erase(ALT_QSPI_TIMEOUT_INFINITE);
    }
#endif

    return status;
}

ALT_STATUS_CODE alt_qspi_erase_chip(void)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (qspi_device_size >= (2 * ALT_QSPI_N25Q_DIE_SIZE))
    {
        // NOTE: This path is specifically for 512 Mib and 1 Gib Micron N25Q
        //   chips only.

        dprintf("DEBUG[QSPI]: erase[chip]: FYI, wait time is ~800s for 128 MiB.\n");

        uint32_t die_count = qspi_device_size / ALT_QSPI_N25Q_DIE_SIZE;

        for (int i = 0; i < die_count; ++i)
        {
            if (status != ALT_E_SUCCESS)
            {
                break;
            }

            dprintf("DEBUG[QSPI]: Erase chip: die = %d, total = %" PRIu32 ".\n", i, die_count);

            if (status == ALT_E_SUCCESS)
            {
                status = alt_qspi_device_bank_select(i * (ALT_QSPI_N25Q_DIE_SIZE / ALT_QSPI_BANK_SIZE));
            }

            if (status == ALT_E_SUCCESS)
            {
                status = alt_qspi_device_wren(); 
            }

            if (status == ALT_E_SUCCESS)
            {
                status = alt_qspi_stig_addr_cmd(ALT_QSPI_STIG_OPCODE_DIE_ERASE, 0,
                                                i * ALT_QSPI_N25Q_DIE_SIZE,
                                                ALT_QSPI_TIMEOUT_INFINITE);
            }

#if ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT
            if (status == ALT_E_SUCCESS)
            {
                status = alt_qspi_N25Q_flag_wait_for_erase(ALT_QSPI_TIMEOUT_INFINITE);
            }
#endif
        }
    }
    else
    {
        // NOTE: Untested path.

        dprintf("DEBUG[QSPI]: Bulk erase.\n");

        if (status == ALT_E_SUCCESS)
        {
            status = alt_qspi_device_bank_select(0);
        }

        if (status == ALT_E_SUCCESS)
        {
            status = alt_qspi_device_wren();
        }

        if (status == ALT_E_SUCCESS)
        {
            // If BULK_ERASE is like other ERASE, it needs the address command.
            status = alt_qspi_stig_addr_cmd(ALT_QSPI_STIG_OPCODE_BULK_ERASE, 0,
                                            0,
                                            ALT_QSPI_TIMEOUT_INFINITE);
        }

#if ALT_QSPI_PROVISION_MICRON_N25Q_SUPPORT
        if (status == ALT_E_SUCCESS)
        {
            status = alt_qspi_N25Q_flag_wait_for_erase(ALT_QSPI_TIMEOUT_INFINITE);
        }
#endif
    }

    return status;
}

/////

ALT_STATUS_CODE alt_qspi_dma_disable(void)
{
    // Clear (set to 0) the Enable DMA Peripheral Interface Field of the QSPI
    // Configuration Register to disable the DMA peripheral interface.
    alt_clrbits_word(ALT_QSPI_CFG_ADDR, ALT_QSPI_CFG_ENDMA_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_dma_enable(void)
{
    // Set (set to 1) the Enable DMA Peripheral Interface Field of the QSPI
    // Configuration Register to enable the DMA peripheral interface.
    alt_setbits_word(ALT_QSPI_CFG_ADDR, ALT_QSPI_CFG_ENDMA_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_dma_config_get(uint32_t * single_type_sz,
                                        uint32_t * burst_type_sz)
{
    // Get the current value of the DMA Peripheral Register - dmaper
    uint32_t dmaper = alt_read_word(ALT_QSPI_DMAPER_ADDR);

    // For both values, a programmed value of 0 represents a single byte. The
    // actual number of bytes used is 2 ** (value in this register field).
    *single_type_sz = 1 << ALT_QSPI_DMAPER_NUMSGLREQBYTES_GET(dmaper);
    *burst_type_sz  = 1 << ALT_QSPI_DMAPER_NUMBURSTREQBYTES_GET(dmaper);

    return ALT_E_SUCCESS;
}

//
// Returns true if [n] is a power of 2 value otherwise returns false.
//
static bool is_pow_2(uint32_t n)
{
    return ((n > 0) && ((n & (n - 1)) == 0));
}

//
// Return the log base 2 value of a number that is known to be a power of 2.
//
static uint32_t log2u(uint32_t value)
{
    uint32_t exp = 0;
    while ((exp < 32) && (value != (1 << exp)))
    {
        ++exp;
    }
    return exp;
}

ALT_STATUS_CODE alt_qspi_dma_config_set(const uint32_t single_type_sz,
                                        const uint32_t burst_type_sz)
{
    if (alt_qspi_is_idle() == false)
    {
        return ALT_E_ERROR;
    }

    if (single_type_sz < 4)
    {
        return ALT_E_ERROR;
    }

    if (burst_type_sz < 4)
    {
        return ALT_E_ERROR;
    }

    if (burst_type_sz < single_type_sz)
    {
        return ALT_E_ERROR;
    }

    const uint32_t single_type_sz_max = 1 << ((1 << ALT_QSPI_DMAPER_NUMSGLREQBYTES_WIDTH) - 1);
    const uint32_t burst_type_sz_max  = 1 << ((1 << ALT_QSPI_DMAPER_NUMBURSTREQBYTES_WIDTH) - 1);

    // Both parameter values must be a power of 2 between 1 and 32728.
    if (  (single_type_sz > single_type_sz_max) || !is_pow_2(single_type_sz)
       || (burst_type_sz  > burst_type_sz_max)  || !is_pow_2(burst_type_sz)
       )
    {
        return ALT_E_ARG_RANGE;
    }

    // Get the current value of the DMA Peripheral Register - dmaper
    uint32_t dmaper = alt_read_word(ALT_QSPI_DMAPER_ADDR);
    dmaper &= ALT_QSPI_DMAPER_NUMBURSTREQBYTES_CLR_MSK &
              ALT_QSPI_DMAPER_NUMSGLREQBYTES_CLR_MSK;
    dmaper |= ALT_QSPI_DMAPER_NUMBURSTREQBYTES_SET(log2u(burst_type_sz)) |
              ALT_QSPI_DMAPER_NUMSGLREQBYTES_SET(log2u(single_type_sz));
    alt_write_word(ALT_QSPI_DMAPER_ADDR, dmaper);

    return ALT_E_SUCCESS;
}

/////

//
// Private STIG and device commands
//

static ALT_STATUS_CODE alt_qspi_stig_cmd_helper(uint32_t reg_value, uint32_t timeout)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    bool infinite = (timeout == ALT_QSPI_TIMEOUT_INFINITE);

    alt_write_word(ALT_QSPI_FLSHCMD_ADDR, reg_value);
    alt_write_word(ALT_QSPI_FLSHCMD_ADDR, reg_value | ALT_QSPI_FLSHCMD_EXECCMD_E_EXECUTE);

    do
    {
        reg_value = alt_read_word(ALT_QSPI_FLSHCMD_ADDR);
        if (!(reg_value & ALT_QSPI_FLSHCMD_CMDEXECSTAT_SET_MSK))
        {
            break;
        }

    } while (timeout-- || infinite);

    if (timeout == (uint32_t)-1 && !infinite)
    {
        status = ALT_E_TMO;
    }

    return status;
}

ALT_STATUS_CODE alt_qspi_stig_cmd(uint32_t opcode, uint32_t dummy, uint32_t timeout)
{
    if (dummy > ((1 << ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_WIDTH) - 1))
    {
        return ALT_E_ERROR;
    }

    uint32_t reg = ALT_QSPI_FLSHCMD_CMDOPCODE_SET(opcode) |
                   ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_SET(dummy);

    return alt_qspi_stig_cmd_helper(reg, timeout);
}

ALT_STATUS_CODE alt_qspi_stig_rd_cmd(uint8_t opcode,
                                     uint32_t dummy,
                                     uint32_t num_bytes,
                                     uint32_t * output,
                                     uint32_t timeout)
{
    if (dummy > ((1 << ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_WIDTH) - 1))
    {
        return ALT_E_ERROR;
    }

    // STIG read can only return up to 8 bytes.
    if ((num_bytes > 8) || (num_bytes == 0))
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t reg_value = 
        ALT_QSPI_FLSHCMD_CMDOPCODE_SET(opcode)                              |
        ALT_QSPI_FLSHCMD_ENRDDATA_SET(ALT_QSPI_FLSHCMD_ENRDDATA_E_EN)       |
        ALT_QSPI_FLSHCMD_NUMRDDATABYTES_SET(num_bytes - 1)                  |
        ALT_QSPI_FLSHCMD_ENCMDADDR_SET(ALT_QSPI_FLSHCMD_ENCMDADDR_E_DISD)   |
        ALT_QSPI_FLSHCMD_ENMODBIT_SET(ALT_QSPI_FLSHCMD_ENMODBIT_E_DISD)     |
        ALT_QSPI_FLSHCMD_NUMADDRBYTES_SET(0)                                |
        ALT_QSPI_FLSHCMD_ENWRDATA_SET(ALT_QSPI_FLSHCMD_ENWRDATA_E_NOACTION) |
        ALT_QSPI_FLSHCMD_NUMWRDATABYTES_SET(0)                              |
        ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_SET(dummy);

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    status = alt_qspi_stig_cmd_helper(reg_value, timeout);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    output[0] = alt_read_word(ALT_QSPI_FLSHCMDRDDATALO_ADDR);

    if (num_bytes > 4)
    {
        output[1] = alt_read_word(ALT_QSPI_FLSHCMDRDDATAUP_ADDR);
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_qspi_stig_wr_cmd(uint8_t opcode,
                                     uint32_t dummy,
                                     uint32_t num_bytes, 
                                     const uint32_t * input,
                                     uint32_t timeout)
{
    if (dummy > ((1 << ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_WIDTH) - 1))
    {
        return ALT_E_ERROR;
    }

    // STIG can only write up to 8 bytes.
    if ((num_bytes > 8) || (num_bytes == 0))
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t reg_value =
        ALT_QSPI_FLSHCMD_CMDOPCODE_SET(opcode)                                 |
        ALT_QSPI_FLSHCMD_ENRDDATA_SET(ALT_QSPI_FLSHCMD_ENRDDATA_E_NOACTION)    |
        ALT_QSPI_FLSHCMD_NUMRDDATABYTES_SET(0)                                 |
        ALT_QSPI_FLSHCMD_ENCMDADDR_SET(ALT_QSPI_FLSHCMD_ENCMDADDR_E_DISD)      |
        ALT_QSPI_FLSHCMD_ENMODBIT_SET(ALT_QSPI_FLSHCMD_ENMODBIT_E_DISD)        |
        ALT_QSPI_FLSHCMD_NUMADDRBYTES_SET(0)                                   |
        ALT_QSPI_FLSHCMD_ENWRDATA_SET(ALT_QSPI_FLSHCMD_ENWRDATA_E_WRDATABYTES) |
        ALT_QSPI_FLSHCMD_NUMWRDATABYTES_SET(num_bytes - 1)                     |
        ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_SET(dummy);

    alt_write_word(ALT_QSPI_FLSHCMDWRDATALO_ADDR, input[0]);

    if (num_bytes > 4)
    {
        alt_write_word(ALT_QSPI_FLSHCMDWRDATAUP_ADDR, input[1]);
    }

    return alt_qspi_stig_cmd_helper(reg_value, timeout);
}

ALT_STATUS_CODE alt_qspi_stig_addr_cmd(uint8_t opcode,
                                       uint32_t dummy,
                                       uint32_t address,
                                       uint32_t timeout)
{
    if (dummy > ((1 << ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_WIDTH) - 1))
    {
        return ALT_E_ERROR;
    }

    uint32_t reg = ALT_QSPI_FLSHCMD_CMDOPCODE_SET(opcode) |
                   ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_SET(dummy);

    reg |= ALT_QSPI_FLSHCMD_ENCMDADDR_SET(ALT_QSPI_FLSHCMD_ENCMDADDR_E_END);
    reg |= ALT_QSPI_FLSHCMD_NUMADDRBYTES_SET(ALT_QSPI_FLSHCMD_NUMADDRBYTES_E_ADDRBYTE3);

    alt_write_word(ALT_QSPI_FLSHCMDADDR_ADDR, address);

    return alt_qspi_stig_cmd_helper(reg, timeout);
}

/////

ALT_STATUS_CODE alt_qspi_device_wren(void) 
{
    // Write enable through STIG (not required, auto send by controller during write)
    return alt_qspi_stig_cmd(ALT_QSPI_STIG_OPCODE_WREN, 0, 10000);
}

ALT_STATUS_CODE alt_qspi_device_wrdis(void) 
{
    // Write disable through STIG (not required, auto send by controller during write)
    return alt_qspi_stig_cmd(ALT_QSPI_STIG_OPCODE_WRDIS, 0, 10000);
}

ALT_STATUS_CODE alt_qspi_device_rdid(uint32_t * rdid)
{
    // Read flash device ID through STIG
    return alt_qspi_stig_rd_cmd(ALT_QSPI_STIG_OPCODE_RDID, 0, 4, rdid, 10000);
}

ALT_STATUS_CODE alt_qspi_discovery_parameter(uint32_t * param)
{
    // Read flash discovery parameters through STIG

    return alt_qspi_stig_rd_cmd(ALT_QSPI_STIG_OPCODE_DISCVR_PARAM, 8, 8, param, 10000);
}

ALT_STATUS_CODE alt_qspi_device_bank_select(uint32_t bank) 
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    dprintf("DEBUG[QSPI]: bank_select(): switching to bank 0x%" PRIu32 ".\n", bank);

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_device_wren();
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_stig_wr_cmd(ALT_QSPI_STIG_OPCODE_WR_EXT_REG, 0, 1, &bank, 10000);
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_qspi_device_wrdis();
    }

    return status;
}

/////

static bool alt_qspi_is_enabled(void)
{
    uint32_t cfg = alt_read_word(ALT_QSPI_CFG_ADDR);

    if (cfg & ALT_QSPI_CFG_EN_SET_MSK)
    {
        return true;
    }
    else
    {
        return false;
    }
}

ALT_STATUS_CODE alt_qspi_ecc_start(void * block, size_t size)
{
    if (size < (ALT_QSPI_PAGE_SIZE * 8))
    {
        return ALT_E_ERROR;
    }

    if (alt_qspi_is_enabled() == false)
    {
        return ALT_E_ERROR;
    }

    if (alt_qspi_is_idle() == false)
    {
        return ALT_E_ERROR;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // 1. Configure SRAM Partition Register to 126 words for read, 2 words for write.
    // 2. Enable ECC on QSPI RAM
    // 3. Trigger an indirect read transfer that will fill up 126 words in FIFO by
    //    monitoring read FIFO fill level; Do not read out data through AHB.
    // 4. Start AHB read and start indirect write operation to write back to the same
    //    device location, this will fill up and initilaize the write partition RAM.
    // 5. To clear spurious interrupts, reset the QSPI controller.

    // Save the previous partition size

    uint32_t sram_orig = alt_qspi_sram_partition_get();
    dprintf("DEBUG[QSPI][ECC]: Save original SRAM as %" PRIu32 ".\n", sram_orig);

    // Step 1

    uint32_t sram_fill = (1 << ALT_QSPI_SRAMPART_ADDR_WIDTH) - 2;
    alt_qspi_sram_partition_set(sram_fill);
    dprintf("DEBUG[QSPI][ECC]: Set new SRAM as %" PRIu32 ".\n", sram_fill);

    // Step 2

    dprintf("DEBUG[QSPI][ECC]: Enable ECC in SysMgr.\n");
    alt_write_word(ALT_SYSMGR_ECC_QSPI_ADDR, ALT_SYSMGR_ECC_QSPI_EN_SET_MSK);

    // Step 3

    // Issue a read ~ 2x larger than the read partition. We will read out 1 page,
    // which will be used as the buffer to write back to QSPI. This way no data
    // actually changes thus no erase will be needed.

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DEBUG[QSPI][ECC]: Start indirect read PAGE * 8.\n");
        status = alt_qspi_indirect_read_start(0x0, ALT_QSPI_PAGE_SIZE * 8);
    }

    // Read out 1 page for the write data

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DEBUG[QSPI][ECC]: Reading out 1 page ...\n");

        uint32_t read_size = 0;
        char *   buffer    = block;
        while (read_size < ALT_QSPI_PAGE_SIZE)
        {
            uint32_t level = alt_qspi_indirect_read_fill_level();
            level = MIN(level, (ALT_QSPI_PAGE_SIZE - read_size) / sizeof(uint32_t));

            uint32_t * data = (uint32_t *)(&buffer[read_size]);
            for (uint32_t i = 0; i < level; ++i)
            {
                *data = alt_read_word(ALT_QSPIDATA_ADDR);
                ++data;
            }

            read_size += level * sizeof(uint32_t);
        }

        if (read_size != ALT_QSPI_PAGE_SIZE)
        {
            status = ALT_E_ERROR;
        }
    }

    // Wait for read FIFO to report it is up to the specified fill level.

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DEBUG[QSPI][ECC]: Waiting for read fill level ...\n");

        uint32_t timeout = 10000;

        while (alt_qspi_indirect_read_fill_level() < sram_fill)
        {
            if (--timeout == 0)
            {
                dprintf("DEBUG[QSPI][ECC]: Waiting for read fill timeout !!!\n");
                status = ALT_E_TMO;
                break;
            }
        }
    }

    // Step 4

    // Issue a write of 1 page of the same data from 0x0.

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DEBUG[QSPI][ECC]: Start indirect write PAGE.\n");
        status = alt_qspi_indirect_write_start(0x0, ALT_QSPI_PAGE_SIZE);
    }

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DEBUG[QSPI][ECC]: Writing in 1 page ...\n");

        uint32_t write_size = 0;
        char *   buffer     = block;

        while (write_size < ALT_QSPI_PAGE_SIZE)
        {
            uint32_t space = 2 - alt_qspi_indirect_write_fill_level();
            if (space == 0)
            {
                dprintf("DEBUG[QSPI][ECC]: Write FIFO filled at write_size = %" PRIu32 ".\n", write_size);
                // Space = 0; which means all 2 positions in the write FIFO is filled,
                // meaning it has been initialized with respect to ECC.
                break;
            }

            space = MIN(space, (ALT_QSPI_PAGE_SIZE - write_size) / sizeof(uint32_t));

            uint32_t * data = (uint32_t *)(&buffer[write_size]);
            for (uint32_t i = 0; i < space; ++i)
            {
                alt_write_word(ALT_QSPIDATA_ADDR, *data);
                ++data;
            }

            write_size += space * sizeof(uint32_t);
        }

        if (write_size != ALT_QSPI_PAGE_SIZE)
        {
            dprintf("DEBUG[QSPI][ECC]: Cancel indirect write.\n");
            status = alt_qspi_indirect_write_cancel();
        }
    }

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DEBUG[QSPI][ECC]: Finish indirect write.\n");
        status = alt_qspi_indirect_write_finish();
    }

    // Cancel the indirect read as it has initialized the read FIFO partition.

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DEBUG[QSPI][ECC]: Cancel indirect read.\n");
        status = alt_qspi_indirect_read_cancel();
    }

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DEBUG[QSPI][ECC]: Finish indirect read.\n");
        status = alt_qspi_indirect_read_finish();
    }

    // Step 5

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DEBUG[QSPI][ECC]: Clear any pending spurious QSPI ECC interrupts.\n");

        alt_write_word(ALT_SYSMGR_ECC_QSPI_ADDR,
                         ALT_SYSMGR_ECC_QSPI_EN_SET_MSK
                       | ALT_SYSMGR_ECC_QSPI_SERR_SET_MSK
                       | ALT_SYSMGR_ECC_QSPI_DERR_SET_MSK);
    }

    /////

    // Restore original partition

    if (status == ALT_E_SUCCESS)
    {
        dprintf("DEBUG[QSPI][ECC]: Restore original SRAM as %" PRIu32 ".\n", sram_orig);
        status = alt_qspi_sram_partition_set(sram_orig);
    }

    return status;
}
