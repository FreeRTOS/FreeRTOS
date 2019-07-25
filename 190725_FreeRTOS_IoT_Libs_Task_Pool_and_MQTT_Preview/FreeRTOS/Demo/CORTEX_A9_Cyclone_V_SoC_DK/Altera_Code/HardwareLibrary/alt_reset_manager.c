
/******************************************************************************
*
* alt_reset_manager.c - API for the Altera SoC FPGA reset manager.
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

#include "alt_reset_manager.h"
#include "socal/socal.h"
#include "socal/hps.h"
#include "socal/alt_rstmgr.h"

/////


uint32_t alt_reset_event_get(void)
{
    return alt_read_word(ALT_RSTMGR_STAT_ADDR);
}

ALT_STATUS_CODE alt_reset_event_clear(uint32_t event_mask)
{
    alt_write_word(ALT_RSTMGR_STAT_ADDR, event_mask);
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_reset_cold_reset(void)
{
    alt_write_word(ALT_RSTMGR_CTL_ADDR, ALT_RSTMGR_CTL_SWCOLDRSTREQ_SET_MSK);
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_reset_warm_reset(uint32_t warm_reset_delay,
                                     uint32_t nRST_pin_clk_assertion,
                                     bool sdram_refresh_enable,
                                     bool fpga_mgr_handshake,
                                     bool scan_mgr_handshake,
                                     bool fpga_handshake,
                                     bool etr_stall)
{
    // Cached register values
    uint32_t ctrl_reg   = ALT_RSTMGR_CTL_SWWARMRSTREQ_SET_MSK;
    uint32_t counts_reg = 0;

    /////

    // Validate warm_reset_delay is above 16 and below the field width
    if ((warm_reset_delay < 16) || (warm_reset_delay >= (1 << ALT_RSTMGR_COUNTS_WARMRSTCYCLES_WIDTH)))
    {
        return ALT_E_BAD_ARG;
    }

    // Validate nRST_pin_clk_assertion delay is non-zero and below the field width
    if (!nRST_pin_clk_assertion)
    {
        return ALT_E_ERROR;
    }
    if (nRST_pin_clk_assertion >= (1 << ALT_RSTMGR_COUNTS_NRSTCNT_WIDTH))
    {
        return ALT_E_BAD_ARG;
    }

    // Update counts register with warm_reset_delay information
    counts_reg |= ALT_RSTMGR_COUNTS_WARMRSTCYCLES_SET(warm_reset_delay);

    // Update counts register with nRST_pin_clk_assertion information
    counts_reg |= ALT_RSTMGR_COUNTS_NRSTCNT_SET(nRST_pin_clk_assertion);

    /////

    // Update ctrl register with the specified option flags

    if (sdram_refresh_enable)
    {
        ctrl_reg |= ALT_RSTMGR_CTL_SDRSELFREFEN_SET_MSK;
    }

    if (fpga_mgr_handshake)
    {
        ctrl_reg |= ALT_RSTMGR_CTL_FPGAMGRHSEN_SET_MSK;
    }

    if (scan_mgr_handshake)
    {
        ctrl_reg |= ALT_RSTMGR_CTL_SCANMGRHSEN_SET_MSK;
    }

    if (fpga_handshake)
    {
        ctrl_reg |= ALT_RSTMGR_CTL_FPGAHSEN_SET_MSK;
    }

    if (etr_stall)
    {
        ctrl_reg |= ALT_RSTMGR_CTL_ETRSTALLEN_SET_MSK;
    }

    /////

    // Commit registers to hardware
    alt_write_word(ALT_RSTMGR_COUNTS_ADDR, counts_reg);
    alt_write_word(ALT_RSTMGR_CTL_ADDR,    ctrl_reg);

    return ALT_E_SUCCESS;
}
