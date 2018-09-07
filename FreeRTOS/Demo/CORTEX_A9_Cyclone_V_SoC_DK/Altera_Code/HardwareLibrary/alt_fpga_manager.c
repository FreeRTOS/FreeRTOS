
/******************************************************************************
*
* alt_fpga_manager.c - API for the Altera SoC FPGA manager.
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

#include "alt_fpga_manager.h"
#include "socal/socal.h"
#include "socal/hps.h"
#include "socal/alt_fpgamgr.h"
#include <string.h>
#include <stdbool.h>
#include "hwlib.h"

// NOTE: To enable debugging output, delete the next line and uncomment the
//   line after.
#define dprintf(...)
// #define dprintf(fmt, ...) printf(fmt, __VA_ARGS__)


// This is the timeout used when waiting for a state change in the FPGA monitor.
#define _ALT_FPGA_TMO_STATE     2048

// This is the timeout used when waiting for the DCLK countdown to complete.
// The time to wait a constant + DCLK * multiplier.
#define _ALT_FPGA_TMO_DCLK_CONST 2048
#define _ALT_FPGA_TMO_DCLK_MUL   2

#define _ALT_FPGA_TMO_CONFIG     8192

// This define is used to control whether to use the Configuration with DCLK steps
#ifndef _ALT_FPGA_USE_DCLK
#define _ALT_FPGA_USE_DCLK 0
#endif

/////

// This is used in the FGPA reconfiguration streaming interface. Because FPGA
// images are commonly stored on disk, the chunk size is that of the disk size.
// We cannot choose too large a chunk size because the stack size is fairly
// small.
#define DISK_SECTOR_SIZE    512
#define ISTREAM_CHUNK_SIZE  DISK_SECTOR_SIZE

/////

//
// FPGA Data Type identifier enum
//
typedef enum FPGA_DATA_TYPE_e
{
    FPGA_DATA_FULL    = 1,
    FPGA_DATA_ISTREAM = 2
} FPGA_DATA_TYPE_t;

//
// FPGA Data, for Full Stream or IStream configuration
//
typedef struct FPGA_DATA_s
{
    FPGA_DATA_TYPE_t type;
    
    union
    {
        // For FPGA_DATA_FULL
        struct
        {
            const void * buffer;
            size_t       length;
        } full;
        
        // FPGA_DATA_ISTREAM
        struct
        {
            alt_fpga_istream_t stream;
            void *             data;
        } istream;
    } mode;

#if ALT_FPGA_ENABLE_DMA_SUPPORT
    bool use_dma;
    ALT_DMA_CHANNEL_t dma_channel;
#endif

} FPGA_DATA_t;

#if ALT_FPGA_ENABLE_DMA_SUPPORT
static ALT_STATUS_CODE alt_dma_channel_wait_for_state(ALT_DMA_CHANNEL_t channel,
                                                      ALT_DMA_CHANNEL_STATE_t state,
                                                      uint32_t count)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    ALT_DMA_CHANNEL_STATE_t current;

    uint32_t i = count;
    while (--i)
    {
        status = alt_dma_channel_state_get(channel, &current);
        if (status != ALT_E_SUCCESS)
        {
            break;
        }
        if (current == state)
        {
            break;
        }
    }

    if (i == 0)
    {
        dprintf("FPGA[AXI]: Timeout [count=%u] waiting for DMA state [%d]. Last state was [%d]",
                (unsigned)count,
                (int)state, (int)current);
        status = ALT_E_TMO;
    }

    return status;
}
#endif

//
// Helper function which handles writing data to the AXI bus.
//
static ALT_STATUS_CODE alt_fpga_internal_writeaxi(const char * cfg_buf, uint32_t cfg_buf_len
#if ALT_FPGA_ENABLE_DMA_SUPPORT
                                                  ,
                                                  bool use_dma, ALT_DMA_CHANNEL_t dma_channel
#endif
    )
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

#if ALT_FPGA_ENABLE_DMA_SUPPORT
    // Use DMA if requested.
    if (use_dma)
    {
        ALT_DMA_PROGRAM_t program;

        if (status == ALT_E_SUCCESS)
        {
            dprintf("FPGA[AXI]: DMA mem-to-reg ...\n");
            status = alt_dma_memory_to_register(dma_channel, &program,
                                                ALT_FPGAMGRDATA_ADDR,
                                                cfg_buf,
                                                cfg_buf_len >> 2, // we need the number uint32_t's
                                                32,
                                                false, ALT_DMA_EVENT_0);
        }
        if (status == ALT_E_SUCCESS)
        {
            dprintf("FPGA[AXI]: Wait for channel to stop\n");

            // NOTE: Polling this register is much better than polling the
            //   FPGA status register. Thus ensure the DMA is complete here.
            status = alt_dma_channel_wait_for_state(dma_channel, ALT_DMA_CHANNEL_STATE_STOPPED, cfg_buf_len);
        }
    }
    else
#endif
    {
        dprintf("FPGA[AXI]: PIO memcpy() ...\n");

        size_t i = 0;

        // Write out as many complete 32-bit chunks.
        const uint32_t * buffer_32 = (const uint32_t *) cfg_buf;
        while (cfg_buf_len >= sizeof(uint32_t))
        {
            alt_write_word(ALT_FPGAMGRDATA_ADDR, buffer_32[i++]);
            cfg_buf_len -= sizeof(uint32_t);
        }
    }

    // Write out remaining non 32-bit chunks.
    if ((status == ALT_E_SUCCESS) && (cfg_buf_len & 0x3))
    {
        dprintf("FPGA[AXI]: Copy non-aligned data ...\n");

        const uint32_t * buffer_32 = (const uint32_t *) (cfg_buf + (cfg_buf_len & ~0x3));

        switch (cfg_buf_len & 0x3)
        {
        case 3:
            alt_write_word(ALT_FPGAMGRDATA_ADDR, *buffer_32 & 0x00ffffff);
            break;
        case 2:
            alt_write_word(ALT_FPGAMGRDATA_ADDR, *buffer_32 & 0x0000ffff);
            break;
        case 1:
            alt_write_word(ALT_FPGAMGRDATA_ADDR, *buffer_32 & 0x000000ff);
            break;
        default:
            // This will never happen.
            break;
        }
    }

    return status;
}

/////

//
// Helper function which sets the DCLKCNT, waits for DCLKSTAT to report the
// count completed, and clear the complete status.
// Returns:
//  - ALT_E_SUCCESS if the FPGA DCLKSTAT reports that the DCLK count is done.
//  - ALT_E_TMO     if the number of polling cycles exceeds the timeout value.
//
static ALT_STATUS_CODE dclk_set_and_wait_clear(uint32_t count, uint32_t timeout)
{
    ALT_STATUS_CODE status = ALT_E_TMO;

    // Clear any existing DONE status. This can happen if a previous call to
    // this function returned timeout. The counter would complete later on but
    // never be cleared.
    if (alt_read_word(ALT_FPGAMGR_DCLKSTAT_ADDR))
    {
        alt_write_word(ALT_FPGAMGR_DCLKSTAT_ADDR, ALT_FPGAMGR_DCLKSTAT_DCNTDONE_E_DONE);
    }

    // Issue the DCLK count.
    alt_write_word(ALT_FPGAMGR_DCLKCNT_ADDR, count);

    // Poll DCLKSTAT to see if it completed in the timeout period specified.
    do
    {
        dprintf(".");

        uint32_t done = alt_read_word(ALT_FPGAMGR_DCLKSTAT_ADDR);

        if (done == ALT_FPGAMGR_DCLKSTAT_DCNTDONE_E_DONE)
        {
            // Now that it is done, clear the DONE status.
            alt_write_word(ALT_FPGAMGR_DCLKSTAT_ADDR, ALT_FPGAMGR_DCLKSTAT_DCNTDONE_E_DONE);

            status = ALT_E_SUCCESS;
            break;
        }
    }
    while (timeout--);

    dprintf("\n");

    return status;
}

//
// Helper function which waits for the FPGA to enter the specified state.
// Returns:
//  - ALT_E_SUCCESS if successful
//  - ALT_E_TMO     if the number of polling cycles exceeds the timeout value.
//
static ALT_STATUS_CODE wait_for_fpga_state(ALT_FPGA_STATE_t state, uint32_t timeout)
{
    ALT_STATUS_CODE status = ALT_E_TMO;

    // Poll on the state to see if it matches the requested state within the
    // timeout period specified.
    do
    {
        dprintf(".");

        ALT_FPGA_STATE_t current = alt_fpga_state_get();

        if (current == state)
        {
            status = ALT_E_SUCCESS;
            break;
        }
    }
    while (timeout--);

    dprintf("\n");

    return status;
}

//
// Waits for the FPGA CB monitor to report the FPGA configuration status by
// polling that both CONF_DONE and nSTATUS or neither flags are set.
//
// Returns:
//  - ALT_E_SUCCESS  if CB monitor reports configuration successful.
//  - ALT_E_FPGA_CFG if CB monitor reports configuration failure.
//  - ALT_E_FPGA_CRC if CB monitor reports a CRC error.
//  - ALT_E_TMO      if CONF_DONE and nSTATUS fails to "settle" in the number
//                   of polling cycles specified by the timeout value.
//
static ALT_STATUS_CODE wait_for_config_done(uint32_t timeout)
{
    ALT_STATUS_CODE retval = ALT_E_TMO;

    // Poll on the CONF_DONE and nSTATUS both being set within the timeout
    // period specified.
    do
    {
        dprintf(".");

        uint32_t status = alt_fpga_mon_status_get();

        // Detect CRC problems with the FGPA configuration
        if (status & ALT_FPGA_MON_CRC_ERROR)
        {
            retval = ALT_E_FPGA_CRC;
            break;
        }

        bool conf_done = (status & ALT_FPGA_MON_CONF_DONE) != 0;
        bool nstatus   = (status & ALT_FPGA_MON_nSTATUS)   != 0;

        if (conf_done == nstatus)
        {
            if (conf_done)
            {
                retval = ALT_E_SUCCESS;
            }
            else
            {
                retval = ALT_E_FPGA_CFG;
            }
            break;
        }
    }
    while (timeout--);

    dprintf("\n");

    return retval;
}

/////

ALT_STATUS_CODE alt_fpga_init(void)
{
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_fpga_uninit(void)
{
    return ALT_E_SUCCESS;
}

/////

ALT_STATUS_CODE alt_fpga_control_enable(void)
{
    // Simply set CTRL.EN to allow HPS to control the FPGA control block.
    alt_setbits_word(ALT_FPGAMGR_CTL_ADDR, ALT_FPGAMGR_CTL_EN_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_fpga_control_disable(void)
{
    // Simply clear CTRL.EN to allow HPS to control the FPGA control block.
    alt_clrbits_word(ALT_FPGAMGR_CTL_ADDR, ALT_FPGAMGR_CTL_EN_SET_MSK);

    return ALT_E_SUCCESS;
}

bool alt_fpga_control_is_enabled(void)
{
    // Check if CTRL.EN is set or not.
    if ((alt_read_word(ALT_FPGAMGR_CTL_ADDR) & ALT_FPGAMGR_CTL_EN_SET_MSK) != 0)
    {
        return true;
    }
    else
    {
        return false;
    }
}

ALT_FPGA_STATE_t alt_fpga_state_get(void)
{
    // Detect FPGA power status.
    // NOTE: Do not use alt_fpga_state_get() to look for ALT_FPGA_STATE_PWR_OFF.
    //   This is a bit of a misnomer in that the ALT_FPGA_STATE_PWR_OFF really means
    //   FPGA is powered off or idle (which happens just out of being reset by the
    //   reset manager).
    if ((alt_fpga_mon_status_get() & ALT_FPGA_MON_FPGA_POWER_ON) == 0)
    {
        return ALT_FPGA_STATE_POWER_OFF;
    }

    // The fpgamgrreg::stat::mode bits maps to the FPGA state enum.
    return (ALT_FPGA_STATE_t) ALT_FPGAMGR_STAT_MOD_GET(alt_read_word(ALT_FPGAMGR_STAT_ADDR));
}

uint32_t alt_fpga_mon_status_get(void)
{
    return alt_read_word(ALT_FPGAMGR_MON_GPIO_EXT_PORTA_ADDR) & ((1 << 12) - 1);
}

ALT_STATUS_CODE alt_fgpa_reset_assert(void)
{
    // Verify that HPS has control of the FPGA control block.
    if (alt_fpga_control_is_enabled() != true)
    {
        return ALT_E_FPGA_NO_SOC_CTRL;
    }

    // Detect FPGA power status.
    if (alt_fpga_state_get() == ALT_FPGA_STATE_POWER_OFF)
    {
        return ALT_E_FPGA_PWR_OFF;
    }

    // Set the nCONFIGPULL to put the FPGA into reset.
    alt_setbits_word(ALT_FPGAMGR_CTL_ADDR, ALT_FPGAMGR_CTL_NCFGPULL_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_fgpa_reset_deassert(void)
{
    // Verify that HPS has control of the FPGA control block.
    if (alt_fpga_control_is_enabled() != true)
    {
        return ALT_E_FPGA_NO_SOC_CTRL;
    }

    // Detect FPGA power status.
    if (alt_fpga_state_get() == ALT_FPGA_STATE_POWER_OFF)
    {
        return ALT_E_FPGA_PWR_OFF;
    }

    // Clear the nCONFIGPULL to release the FPGA from reset.
    alt_clrbits_word(ALT_FPGAMGR_CTL_ADDR, ALT_FPGAMGR_CTL_NCFGPULL_SET_MSK);

    return ALT_E_SUCCESS;
}

ALT_FPGA_CFG_MODE_t alt_fpga_cfg_mode_get(void)
{
    uint32_t msel = ALT_FPGAMGR_STAT_MSEL_GET(alt_read_word(ALT_FPGAMGR_STAT_ADDR));

    switch (msel)
    {
    case ALT_FPGAMGR_STAT_MSEL_E_PP16_FAST_NOAES_NODC: // SoCAL: 0x0
    case ALT_FPGAMGR_STAT_MSEL_E_PP16_FAST_AES_NODC:   // SoCAL: 0x1
    case ALT_FPGAMGR_STAT_MSEL_E_PP16_FAST_AESOPT_DC:  // SoCAL: 0x2
    case ALT_FPGAMGR_STAT_MSEL_E_PP16_SLOW_NOAES_NODC: // SoCAL: 0x4
    case ALT_FPGAMGR_STAT_MSEL_E_PP16_SLOW_AES_NODC:   // SoCAL: 0x5
    case ALT_FPGAMGR_STAT_MSEL_E_PP16_SLOW_AESOPT_DC:  // SoCAL: 0x6
    case ALT_FPGAMGR_STAT_MSEL_E_PP32_FAST_NOAES_NODC: // SoCAL: 0x8
    case ALT_FPGAMGR_STAT_MSEL_E_PP32_FAST_AES_NODC:   // SoCAL: 0x9
    case ALT_FPGAMGR_STAT_MSEL_E_PP32_FAST_AESOPT_DC:  // SoCAL: 0xa
    case ALT_FPGAMGR_STAT_MSEL_E_PP32_SLOW_NOAES_NODC: // SoCAL: 0xc
    case ALT_FPGAMGR_STAT_MSEL_E_PP32_SLOW_AES_NODC:   // SoCAL: 0xd
    case ALT_FPGAMGR_STAT_MSEL_E_PP32_SLOW_AESOPT_DC:  // SoCAL: 0xe
        // The definitions for the various msel's match up with the hardware
        // definitions, so just cast it to the enum type.
        return (ALT_FPGA_CFG_MODE_t) msel;
    default:
        return ALT_FPGA_CFG_MODE_UNKNOWN;
    }
}

ALT_STATUS_CODE alt_fpga_cfg_mode_set(ALT_FPGA_CFG_MODE_t cfg_mode)
{
    // This function will always return ERROR. See header for reasons.
    return ALT_E_ERROR;
}

//
// This function handles writing data to the FPGA data register and ensuring
// the image was programmed correctly.
//
static ALT_STATUS_CODE alt_fpga_internal_configure_idata(FPGA_DATA_t * fpga_data)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Step 9:
    //  - Write configuration image to AXI DATA register in 4 byte chunks.

    dprintf("FPGA: === Step 9 ===\n");

    // This is the largest configuration image possible for the largest Arria 5
    // SoC device with some generous padding added. Given that the Arria 5 SoC
    // is larger than the Cyclone 5 SoC, this value will also be sufficient for
    // the Cyclone 5 SoC device.

    // From the A5 datasheet, it is 186 Mb => ~ 23 MiB. Thus cap the max
    // configuration data size to 32 MiB. Anything larger will cause an error
    // to be reported to the user. This will also terminate the IStream
    // interface should the stream never end.

    uint32_t data_limit = 32 * 1024 * 1024;

    if (fpga_data->type == FPGA_DATA_FULL)
    {
        if (fpga_data->mode.full.length > data_limit)
        {
            status = ALT_E_FPGA_CFG;
        }
        else
        {
            status = alt_fpga_internal_writeaxi(fpga_data->mode.full.buffer, fpga_data->mode.full.length
#if ALT_FPGA_ENABLE_DMA_SUPPORT
                                                ,
                                                fpga_data->use_dma, fpga_data->dma_channel
#endif
            );
        }
    }
    else
    {
        char buffer[ISTREAM_CHUNK_SIZE];
        int32_t cb_status = 0; // Callback status

        do
        {
            cb_status = fpga_data->mode.istream.stream(buffer, sizeof(buffer), fpga_data->mode.istream.data);

            if (cb_status > sizeof(buffer))
            {
                // Callback data overflows buffer space.
                status = ALT_E_FPGA_CFG_STM;
            }
            else if (cb_status < 0)
            {
                // A problem occurred when streaming data from the source.
                status = ALT_E_FPGA_CFG_STM;
            }
            else if (cb_status == 0)
            {
                // End of IStream data.
                break;
            }
            else if (cb_status > data_limit)
            {
                // Limit hit for the largest permissible data stream.
                status = ALT_E_FPGA_CFG_STM;
            }
            else
            {
                // Copy in configuration data.
                status = alt_fpga_internal_writeaxi(buffer, cb_status
#if ALT_FPGA_ENABLE_DMA_SUPPORT
                                                    ,
                                                    fpga_data->use_dma, fpga_data->dma_channel
#endif
                    );

                data_limit -= cb_status;
            }

            if (status != ALT_E_SUCCESS)
            {
                break;
            }

        } while (cb_status > 0);
    }

    if (status != ALT_E_SUCCESS)
    {
        dprintf("FPGA: Error in step 9: Problem streaming or writing out AXI data.\n");
        return status;
    }

    // Step 10:
    //  - Observe CONF_DONE and nSTATUS (active low)
    //  - if CONF_DONE = 1 and nSTATUS = 1, configuration was successful
    //  - if CONF_DONE = 0 and nSTATUS = 0, configuration failed

    dprintf("FPGA: === Step 10 ===\n");

    status = wait_for_config_done(_ALT_FPGA_TMO_CONFIG);

    if (status != ALT_E_SUCCESS)
    {
        if (status == ALT_E_FPGA_CRC)
        {
            dprintf("FPGA: Error in step 10: CRC error detected.\n");
            return ALT_E_FPGA_CRC;
        }
        else if (status == ALT_E_TMO)
        {
            dprintf("FPGA: Error in step 10: Timeout waiting for CONF_DONE + nSTATUS.\n");
            return ALT_E_FPGA_CFG;
        }
        else
        {
            dprintf("FPGA: Error in step 10: Configuration error CONF_DONE, nSTATUS = 0.\n");
            return ALT_E_FPGA_CFG;
        }
    }

    return ALT_E_SUCCESS;
}

//
// Helper function which does handles the common steps for Full Buffer or
// IStream FPGA configuration.
//
static ALT_STATUS_CODE alt_fpga_internal_configure(FPGA_DATA_t * fpga_data)
{
    // Verify preconditions.
    // This is a minor difference from the configure instructions given by the NPP.

    // Verify that HPS has control of the FPGA control block.
    if (alt_fpga_control_is_enabled() != true)
    {
        return ALT_E_FPGA_NO_SOC_CTRL;
    }

    // Detect FPGA power status.
    if (alt_fpga_state_get() == ALT_FPGA_STATE_POWER_OFF)
    {
        return ALT_E_FPGA_PWR_OFF;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    dprintf("FPGA: Configure() !!!\n");

    // The FPGA CTRL register cache
    uint32_t ctrl_reg;

    ctrl_reg = alt_read_word(ALT_FPGAMGR_CTL_ADDR);

    // Step 1:
    //  - Set CTRL.CFGWDTH, CTRL.CDRATIO to match cfg mode
    //  - Set CTRL.NCE to 0

    dprintf("FPGA: === Step 1 ===\n");

    int cfgwidth = 0;
    int cdratio  = 0;

    switch (alt_fpga_cfg_mode_get())
    {
    case ALT_FPGA_CFG_MODE_PP16_FAST_NOAES_NODC:
        cfgwidth = 16;
        cdratio  = 1;
        break;
    case ALT_FPGA_CFG_MODE_PP16_FAST_AES_NODC:
        cfgwidth = 16;
        cdratio  = 2;
        break;
    case ALT_FPGA_CFG_MODE_PP16_FAST_AESOPT_DC:
        cfgwidth = 16;
        cdratio  = 4;
        break;
    case ALT_FPGA_CFG_MODE_PP16_SLOW_NOAES_NODC:
        cfgwidth = 16;
        cdratio  = 1;
        break;
    case ALT_FPGA_CFG_MODE_PP16_SLOW_AES_NODC:
        cfgwidth = 16;
        cdratio  = 2;
        break;
    case ALT_FPGA_CFG_MODE_PP16_SLOW_AESOPT_DC:
        cfgwidth = 16;
        cdratio  = 4;
        break;
    case ALT_FPGA_CFG_MODE_PP32_FAST_NOAES_NODC:
        cfgwidth = 32;
        cdratio  = 1;
        break;
    case ALT_FPGA_CFG_MODE_PP32_FAST_AES_NODC:
        cfgwidth = 32;
        cdratio  = 4;
        break;
    case ALT_FPGA_CFG_MODE_PP32_FAST_AESOPT_DC:
        cfgwidth = 32;
        cdratio  = 8;
        break;
    case ALT_FPGA_CFG_MODE_PP32_SLOW_NOAES_NODC:
        cfgwidth = 32;
        cdratio  = 1;
        break;
    case ALT_FPGA_CFG_MODE_PP32_SLOW_AES_NODC:
        cfgwidth = 32;
        cdratio  = 4;
        break;
    case ALT_FPGA_CFG_MODE_PP32_SLOW_AESOPT_DC:
        cfgwidth = 32;
        cdratio  = 8;
        break;
    default:
        return ALT_E_ERROR;
    }

    dprintf("FPGA: CDRATIO  = %x\n", cdratio);
    dprintf("FPGA: CFGWIDTH = %s\n", cfgwidth == 16 ? "16" : "32");

    // Adjust CTRL for the CDRATIO
    ctrl_reg &= ALT_FPGAMGR_CTL_CDRATIO_CLR_MSK;
    switch (cdratio)
    {
    case 1:
        ctrl_reg |= ALT_FPGAMGR_CTL_CDRATIO_SET(ALT_FPGAMGR_CTL_CDRATIO_E_X1);
        break;
    case 2: // Unused; included for completeness.
        ctrl_reg |= ALT_FPGAMGR_CTL_CDRATIO_SET(ALT_FPGAMGR_CTL_CDRATIO_E_X2);
        break;
    case 4:
        ctrl_reg |= ALT_FPGAMGR_CTL_CDRATIO_SET(ALT_FPGAMGR_CTL_CDRATIO_E_X4);
        break;
    case 8:
        ctrl_reg |= ALT_FPGAMGR_CTL_CDRATIO_SET(ALT_FPGAMGR_CTL_CDRATIO_E_X8);
        break;
    default:
        return ALT_E_ERROR;
    }

    // Adjust CTRL for CFGWIDTH
    switch (cfgwidth)
    {
    case 16:
        ctrl_reg &= ALT_FPGAMGR_CTL_CFGWDTH_CLR_MSK;
        break;
    case 32:
        ctrl_reg |= ALT_FPGAMGR_CTL_CFGWDTH_SET_MSK;
        break;
    default:
        return ALT_E_ERROR;
    }

    // Set NCE to 0.
    ctrl_reg &= ALT_FPGAMGR_CTL_NCE_CLR_MSK;

    alt_write_word(ALT_FPGAMGR_CTL_ADDR, ctrl_reg);

    // Step 2:
    //  - Set CTRL.EN to 1

    dprintf("FPGA: === Step 2 (skipped due to precondition) ===\n");

    // Step 3:
    //  - Set CTRL.NCONFIGPULL to 1 to put FPGA in reset

    dprintf("FPGA: === Step 3 ===\n");

    ctrl_reg |= ALT_FPGAMGR_CTL_NCFGPULL_SET_MSK;
    alt_write_word(ALT_FPGAMGR_CTL_ADDR, ctrl_reg);

    // Step 4:
    //  - Wait for STATUS.MODE to report FPGA is in reset phase

    dprintf("FPGA: === Step 4 ===\n");

    status = wait_for_fpga_state(ALT_FPGA_STATE_RESET, _ALT_FPGA_TMO_STATE);
    // Handle any error conditions after reset has been unasserted.

    // Step 5:
    //  - Set CONTROL.NCONFIGPULL to 0 to release FPGA from reset

    dprintf("FPGA: === Step 5 ===\n");

    ctrl_reg &= ALT_FPGAMGR_CTL_NCFGPULL_CLR_MSK;
    alt_write_word(ALT_FPGAMGR_CTL_ADDR, ctrl_reg);

    if (status != ALT_E_SUCCESS)
    {
        // This is a failure from Step 4.
        dprintf("FPGA: Error in step 4: Wait for RESET timeout.\n");
        return ALT_E_FPGA_CFG;
    }

    // Step 6:
    //  - Wait for STATUS.MODE to report FPGA is in configuration phase

    dprintf("FPGA: === Step 6 ===\n");

    status = wait_for_fpga_state(ALT_FPGA_STATE_CFG, _ALT_FPGA_TMO_STATE);

    if (status != ALT_E_SUCCESS)
    {
        dprintf("FPGA: Error in step 6: Wait for CFG timeout.\n");
        return ALT_E_FPGA_CFG;
    }

    // Step 7:
    //  - Clear nSTATUS interrupt in CB Monitor

    dprintf("FPGA: === Step 7 ===\n");

    alt_write_word(ALT_FPGAMGR_MON_GPIO_PORTA_EOI_ADDR,
                   ALT_MON_GPIO_PORTA_EOI_NS_SET(ALT_MON_GPIO_PORTA_EOI_NS_E_CLR));

    // Step 8:
    //  - Set CTRL.AXICFGEN to 1 to enable config data on AXI slave bus

    dprintf("FPGA: === Step 8 ===\n");

    ctrl_reg |= ALT_FPGAMGR_CTL_AXICFGEN_SET_MSK;
    alt_write_word(ALT_FPGAMGR_CTL_ADDR, ctrl_reg);

    /////

    //
    // Helper function to handle steps 9 - 10.
    //

    ALT_STATUS_CODE data_status;
    data_status = alt_fpga_internal_configure_idata(fpga_data);

    /////

    // Step 11:
    //  - Set CTRL.AXICFGEN to 0 to disable config data on AXI slave bus

    dprintf("FPGA: === Step 11 ===\n");

    ctrl_reg &= ALT_FPGAMGR_CTL_AXICFGEN_CLR_MSK;
    alt_write_word(ALT_FPGAMGR_CTL_ADDR, ctrl_reg);

    // Step 12:
    //  - Write 4 to DCLKCNT
    //  - Wait for STATUS.DCNTDONE = 1
    //  - Clear W1C bit in STATUS.DCNTDONE

    dprintf("FPGA: === Step 12 ===\n");

    status = dclk_set_and_wait_clear(4, _ALT_FPGA_TMO_DCLK_CONST + 4 * _ALT_FPGA_TMO_DCLK_MUL);
    if (status != ALT_E_SUCCESS)
    {
        dprintf("FPGA: Error in step 12: Wait for dclk(4) timeout.\n");

        // The error here is probably a result of an error in the FPGA data.
        if (data_status != ALT_E_SUCCESS)
        {
            return data_status;
        }
        else
        {
            return ALT_E_FPGA_CFG;
        }
    }

#if _ALT_FPGA_USE_DCLK

    // Extra steps for Configuration with DCLK for Initialization Phase (4.2.1.2)

    // Step 14 (using 4.2.1.2 steps), 15 (using 4.2.1.2 steps)
    //  - Write 0x5000 to DCLKCNT
    //  - Poll until STATUS.DCNTDONE = 1, write 1 to clear

    dprintf("FPGA: === Step 14 (4.2.1.2) ===\n");
    dprintf("FPGA: === Step 15 (4.2.1.2) ===\n");
    
    status = dclk_set_and_wait_clear(0x5000, _ALT_FPGA_TMO_DCLK_CONST + 0x5000 * _ALT_FPGA_TMO_DCLK_MUL);
    if (status == ALT_E_TMO)
    {
        dprintf("FPGA: Error in step 15 (4.2.1.2): Wait for dclk(0x5000) timeout.\n");

        // The error here is probably a result of an error in the FPGA data.
        if (data_status != ALT_E_SUCCESS)
        {
            return data_status;
        }
        else
        {
            return ALT_E_FPGA_CFG;
        }
    }

#endif

    // Step 13:
    //  - Wait for STATUS.MODE to report USER MODE

    dprintf("FPGA: === Step 13 ===\n");

    status = wait_for_fpga_state(ALT_FPGA_STATE_USER_MODE, _ALT_FPGA_TMO_STATE);
    if (status == ALT_E_TMO)
    {
        dprintf("FPGA: Error in step 13: Wait for state = USER_MODE timeout.\n");

        // The error here is probably a result of an error in the FPGA data.
        if (data_status != ALT_E_SUCCESS)
        {
            return data_status;
        }
        else
        {
            return ALT_E_FPGA_CFG;
        }
    }

    // Step 14:
    //  - Set CTRL.EN to 0

    dprintf("FPGA: === Step 14 (skipped due to precondition) ===\n");

    // Return data_status. status is used for the setup of the FPGA parameters
    // and should be successful. Any errors in programming the FPGA is
    // returned in data_status.
    return data_status;
}

ALT_STATUS_CODE alt_fpga_configure(const void* cfg_buf, 
                                   size_t cfg_buf_len)
{
    FPGA_DATA_t fpga_data;
    fpga_data.type             = FPGA_DATA_FULL;
    fpga_data.mode.full.buffer = cfg_buf;
    fpga_data.mode.full.length = cfg_buf_len;
#if ALT_FPGA_ENABLE_DMA_SUPPORT
    fpga_data.use_dma          = false;
#endif

    return alt_fpga_internal_configure(&fpga_data);
}

#if ALT_FPGA_ENABLE_DMA_SUPPORT
ALT_STATUS_CODE alt_fpga_configure_dma(const void* cfg_buf, 
                                       size_t cfg_buf_len,
                                       ALT_DMA_CHANNEL_t dma_channel)
{
    FPGA_DATA_t fpga_data;
    fpga_data.type             = FPGA_DATA_FULL;
    fpga_data.mode.full.buffer = cfg_buf;
    fpga_data.mode.full.length = cfg_buf_len;
    fpga_data.use_dma          = true;
    fpga_data.dma_channel      = dma_channel;

    return alt_fpga_internal_configure(&fpga_data);
}
#endif

ALT_STATUS_CODE alt_fpga_istream_configure(alt_fpga_istream_t cfg_stream,
                                           void * user_data)
{
    FPGA_DATA_t fpga_data;
    fpga_data.type                = FPGA_DATA_ISTREAM;
    fpga_data.mode.istream.stream = cfg_stream;
    fpga_data.mode.istream.data   = user_data;
#if ALT_FPGA_ENABLE_DMA_SUPPORT
    fpga_data.use_dma             = false;
#endif

    return alt_fpga_internal_configure(&fpga_data);
}

#if ALT_FPGA_ENABLE_DMA_SUPPORT
ALT_STATUS_CODE alt_fpga_istream_configure_dma(alt_fpga_istream_t cfg_stream,
                                               void * user_data,
                                               ALT_DMA_CHANNEL_t dma_channel)
{
    FPGA_DATA_t fpga_data;
    fpga_data.type                = FPGA_DATA_ISTREAM;
    fpga_data.mode.istream.stream = cfg_stream;
    fpga_data.mode.istream.data   = user_data;
    fpga_data.use_dma             = true;
    fpga_data.dma_channel         = dma_channel;

    return alt_fpga_internal_configure(&fpga_data);
}
#endif

uint32_t alt_fpga_gpi_read(uint32_t mask)
{
    if (mask == 0)
    {
        return 0;
    }

    return alt_read_word(ALT_FPGAMGR_GPI_ADDR) & mask;
}

ALT_STATUS_CODE alt_fpga_gpo_write(uint32_t mask, uint32_t value)
{
    if (mask == 0)
    {
        return ALT_E_SUCCESS;
    }

    alt_write_word(ALT_FPGAMGR_GPO_ADDR, (alt_read_word(ALT_FPGAMGR_GPO_ADDR) & ~mask) | (value & mask));

    return ALT_E_SUCCESS;
}

/////

ALT_STATUS_CODE alt_fpga_man_irq_disable(ALT_FPGA_MON_STATUS_t mon_stat_mask)
{
    // Ensure only bits 11:0 are set.
    if (mon_stat_mask & ~((1 << 12) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t current = alt_read_word(ALT_FPGAMGR_MON_GPIO_INTEN_ADDR);
    current &= ~((uint32_t)mon_stat_mask) & ((1 << 12) - 1);
    alt_write_word(ALT_FPGAMGR_MON_GPIO_INTEN_ADDR, current);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_fpga_man_irq_enable(ALT_FPGA_MON_STATUS_t mon_stat_mask)
{
    // Ensure only bits 11:0 are set.
    if (mon_stat_mask & ~((1 << 12) - 1))
    {
        return ALT_E_BAD_ARG;
    }

    alt_setbits_word(ALT_FPGAMGR_MON_GPIO_INTEN_ADDR, mon_stat_mask);

    return ALT_E_SUCCESS;
}
