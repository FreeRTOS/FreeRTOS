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
 * EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 ******************************************************************************/

#include "alt_spi.h"
#include "alt_reset_manager.h"
#include "socal/alt_rstmgr.h"

// Timeout for reset manager
#define  ALT_SPI_RESET_TMO_INIT      8192

// Maximum value of SPI Clock Divider
#define  ALT_SPI_MAX_CLK_DIV         65534
// Minimum value of SPI Clock Divider
#define  ALT_SPI_MIN_CLK_DIV         2
// Timeout for waiting interrupt
#define  ALT_SPI_TMO_WAITER          2500000

/////

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MAX(a, b) ((a) > (b) ? (a) : (b))

/////

//
// Check whether spi space is correct.
//
static ALT_STATUS_CODE alt_spi_checking(ALT_SPI_DEV_t * spi_dev)

{
    if (!spi_dev)
    {
        //Incorrect pointer
        return ALT_E_FALSE;
    }

    if (   spi_dev->location != (void *)ALT_SPI_SPIS0
        && spi_dev->location != (void *)ALT_SPI_SPIS1
        && spi_dev->location != (void *)ALT_SPI_SPIM0
        && spi_dev->location != (void *)ALT_SPI_SPIM1)
    {
        // Incorrect device
        return ALT_E_FALSE;
    }

    
    return ALT_E_TRUE;
}

//
// Initialize the specified SPI controller instance for use and return a device
// handle referencing it.
//
ALT_STATUS_CODE alt_spi_init(const ALT_SPI_CTLR_t spi,
                             ALT_SPI_DEV_t * spi_dev)

{
    if (!spi_dev || spi == 0)
    {
        return ALT_E_BAD_ARG;
    }

    //Save spi start address to the instance
    spi_dev->location = (void *)spi;
    
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_clk_is_enabled(ALT_CLK_SPI_M) != ALT_E_TRUE)
    {
        return ALT_E_BAD_CLK;
    }

    // Define operation mode
    if  (   spi_dev->location == (void *)ALT_SPI_SPIM0
         || spi_dev->location == (void *)ALT_SPI_SPIM1)
    {
        spi_dev->op_mode = ALT_SPI_OP_MODE_MASTER;
    }
    else if (   spi_dev->location == (void *)ALT_SPI_SPIS0
             || spi_dev->location == (void *)ALT_SPI_SPIS1)
    {
        spi_dev->op_mode = ALT_SPI_OP_MODE_SLAVE;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        // Get spi clock frequence
        status = alt_clk_freq_get(ALT_CLK_SPI_M, &spi_dev->clock_freq);
    }

    // Reset spi module
    if (status == ALT_E_SUCCESS)
    {
        status = alt_spi_reset(spi_dev);
    }

    return status;
}

//
// Reset spi module by reset manager
//
static ALT_STATUS_CODE alt_spi_rstmgr_set(ALT_SPI_DEV_t * spi_dev)
{
    uint32_t rst_mask = ALT_RSTMGR_PERMODRST_SPIM0_SET_MSK;

    // Assert the appropriate SPI module reset signal via the Reset Manager Peripheral Reset register.
    switch ((ALT_SPI_CTLR_t)spi_dev->location)
    {
    case ALT_SPI_SPIM0:
        rst_mask = ALT_RSTMGR_PERMODRST_SPIM0_SET_MSK;
        break;
    case ALT_SPI_SPIM1:
        rst_mask = ALT_RSTMGR_PERMODRST_SPIM1_SET_MSK;
        break;
    case ALT_SPI_SPIS0:
        rst_mask = ALT_RSTMGR_PERMODRST_SPIS0_SET_MSK;
        break;
    case ALT_SPI_SPIS1:
        rst_mask = ALT_RSTMGR_PERMODRST_SPIS1_SET_MSK;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, rst_mask);

    return ALT_E_SUCCESS;
}

//
// Reset spi module by reset manager
//
static ALT_STATUS_CODE alt_spi_rstmgr_strobe(ALT_SPI_DEV_t * spi_dev)
{
    uint32_t rst_mask = ALT_RSTMGR_PERMODRST_SPIM0_SET_MSK;

    // Assert the appropriate SPI module reset signal via the Reset Manager Peripheral Reset register.
    switch ((ALT_SPI_CTLR_t)spi_dev->location)
    {
    case ALT_SPI_SPIM0:
        rst_mask = ALT_RSTMGR_PERMODRST_SPIM0_SET_MSK;
        break;
    case ALT_SPI_SPIM1:
        rst_mask = ALT_RSTMGR_PERMODRST_SPIM1_SET_MSK;
        break;
    case ALT_SPI_SPIS0:
        rst_mask = ALT_RSTMGR_PERMODRST_SPIS0_SET_MSK;
        break;
    case ALT_SPI_SPIS1:
        rst_mask = ALT_RSTMGR_PERMODRST_SPIS1_SET_MSK;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, rst_mask);

    volatile uint32_t timeout = ALT_SPI_RESET_TMO_INIT;

    // Wait while spi modure is reseting
    while (timeout--)
        ;

    // Deassert the appropriate SPI module reset signal via the Reset Manager Peripheral Reset register.
    alt_clrbits_word(ALT_RSTMGR_PERMODRST_ADDR, rst_mask);

    return ALT_E_SUCCESS;
}

//
// Reset spi module
//
ALT_STATUS_CODE alt_spi_reset(ALT_SPI_DEV_t * spi_dev)
{

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    ALT_STATUS_CODE    status = ALT_E_SUCCESS;
    bool already_enabled = (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_spi_disable(spi_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }
    
    // Reset spi module by reset manager
    alt_spi_rstmgr_strobe(spi_dev);

    // Reset the last target address cache.
    spi_dev->last_slave_mask = 0xffffffff;
    spi_dev->last_transfer_mode = (uint32_t)(-1);

    if (already_enabled)
    {
        // Re-enable controller
        status = alt_spi_enable(spi_dev);
    }

    return status;
}


//
// Uninitialize the SPI controller referenced by the spi_dev handle.
//
ALT_STATUS_CODE alt_spi_uninit(ALT_SPI_DEV_t * spi_dev)
{
    ALT_STATUS_CODE    status = ALT_E_SUCCESS;
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    // Disable spi controller
    status = alt_spi_disable(spi_dev);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    // Reset spi module by reset manager
    alt_spi_rstmgr_set(spi_dev);

    return status;
}


//
// Enables the SPI controller.
//
ALT_STATUS_CODE alt_spi_enable(ALT_SPI_DEV_t * spi_dev)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_setbits_word(ALT_SPIM_SPIENR_ADDR(spi_dev->location),
                         ALT_SPIM_SPIENR_SPI_EN_SET_MSK);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        alt_setbits_word(ALT_SPIS_SPIENR_ADDR(spi_dev->location),
                         ALT_SPIS_SPIENR_SPI_EN_SET_MSK);
        break;
    }
    
    return ALT_E_SUCCESS;
}

//
// Disables the SPI controller
//
ALT_STATUS_CODE alt_spi_disable(ALT_SPI_DEV_t * spi_dev)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    // If spi controller is enabled, return with sucess
    if (alt_spi_is_enabled(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_SUCCESS;
    }
  
    // Else clear enable bit of spi_enable register
    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_clrbits_word(ALT_SPIM_SPIENR_ADDR(spi_dev->location),
                         ALT_SPIM_SPIENR_SPI_EN_SET_MSK);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        alt_clrbits_word(ALT_SPIS_SPIENR_ADDR(spi_dev->location),
                         ALT_SPIS_SPIENR_SPI_EN_SET_MSK);
        break;
    }

    // Clear interrapts mask and clear interrupt status
    alt_spi_int_disable(spi_dev, ALT_SPI_STATUS_ALL);
    alt_spi_int_clear(spi_dev, ALT_SPI_STATUS_ALL);

    return ALT_E_SUCCESS;
}

//
// Check whether spi controller is enable
//
ALT_STATUS_CODE alt_spi_is_enabled(ALT_SPI_DEV_t * spi_dev)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    ALT_STATUS_CODE en_status = ALT_E_FALSE;
    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        en_status = ALT_SPIM_SPIENR_SPI_EN_GET(alt_read_word(ALT_SPIM_SPIENR_ADDR(spi_dev->location)));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        en_status = ALT_SPIS_SPIENR_SPI_EN_GET(alt_read_word(ALT_SPIS_SPIENR_ADDR(spi_dev->location)));
        break;
    }
    return en_status;
}

ALT_STATUS_CODE alt_spi_is_busy(ALT_SPI_DEV_t *spi_dev)

{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }
   
    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        if (ALT_SPIM_SR_BUSY_GET(alt_read_word(ALT_SPIM_SR_ADDR(spi_dev->location))))
        {
            return ALT_E_TRUE;
        }
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        if (ALT_SPIS_SR_BUSY_GET(alt_read_word(ALT_SPIS_SR_ADDR(spi_dev->location))))
        {
            return ALT_E_TRUE;
        }
        break;
    }
   
    return ALT_E_FALSE;
}

//
// Get config parameters from appropriate registers.
//
ALT_STATUS_CODE alt_spi_config_get(ALT_SPI_DEV_t *spi_dev,
                                   ALT_SPI_CONFIG_t* cfg)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !cfg)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t cfg_register;
    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        cfg_register = alt_read_word(ALT_SPIM_CTLR0_ADDR(spi_dev->location));
      
        cfg->frame_size    = (ALT_SPI_DFS_t)ALT_SPIM_CTLR0_DFS_GET(cfg_register);
        cfg->frame_format  = (ALT_SPI_FRF_t)ALT_SPIM_CTLR0_FRF_GET(cfg_register);
        cfg->clk_phase     = (ALT_SPI_SCPH_t)ALT_SPIM_CTLR0_SCPH_GET(cfg_register);
        cfg->clk_polarity  = (ALT_SPI_SCPOL_t)ALT_SPIM_CTLR0_SCPOL_GET(cfg_register);
        cfg->transfer_mode = (ALT_SPI_TMOD_t)ALT_SPIM_CTLR0_TMOD_GET(cfg_register);
        cfg->loopback_mode = (bool)ALT_SPIM_CTLR0_SRL_GET(cfg_register);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        cfg_register       = alt_read_word(ALT_SPIS_CTLR0_ADDR(spi_dev->location));

        cfg->frame_size    = (ALT_SPI_DFS_t)ALT_SPIS_CTLR0_DFS_GET(cfg_register);
        cfg->frame_format  = (ALT_SPI_FRF_t)ALT_SPIS_CTLR0_FRF_GET(cfg_register);
        cfg->clk_phase     = (ALT_SPI_SCPH_t)ALT_SPIS_CTLR0_SCPH_GET(cfg_register);
        cfg->clk_polarity  = (ALT_SPI_SCPOL_t)ALT_SPIS_CTLR0_SCPOL_GET(cfg_register);
        cfg->transfer_mode = (ALT_SPI_TMOD_t)ALT_SPIS_CTLR0_TMOD_GET(cfg_register);
        cfg->slave_output_enable = (bool)ALT_SPIS_CTLR0_SLV_OE_GET(cfg_register);
        cfg->loopback_mode = (bool)ALT_SPIS_CTLR0_SRL_GET(cfg_register);
        break;
    }
    return ALT_E_SUCCESS;
}

//
// Set config parameters to appropriate registers.
//
ALT_STATUS_CODE alt_spi_config_set(ALT_SPI_DEV_t *spi_dev,
                                   const ALT_SPI_CONFIG_t* cfg)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !cfg)
    {
        return ALT_E_BAD_ARG;
    }

    if (cfg->frame_size < ALT_SPI_DFS_4BIT ||cfg->frame_size > ALT_SPI_DFS_16BIT
        || cfg->frame_format > ALT_SPI_FRF_MICROWIRE || cfg->clk_polarity > ALT_SPI_SCPOL_INACTIVE_HIGH
        || cfg->clk_phase > ALT_SPI_SCPH_TOGGLE_START)
    {
        return ALT_E_ARG_RANGE;
    }

    // Set config parameters to appropriate registers
    uint32_t cfg_register;
    uint32_t cfg_mask;
    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        cfg_register = ALT_SPIM_CTLR0_DFS_SET(cfg->frame_size)
                     | ALT_SPIM_CTLR0_FRF_SET(cfg->frame_format)
                     | ALT_SPIM_CTLR0_SCPH_SET(cfg->clk_phase)
                     | ALT_SPIM_CTLR0_SCPOL_SET(cfg->clk_polarity)
                     | ALT_SPIM_CTLR0_TMOD_SET(cfg->transfer_mode)
                     | ALT_SPIM_CTLR0_SRL_SET(cfg->loopback_mode);

        cfg_mask     = ALT_SPIM_CTLR0_DFS_SET_MSK
                     | ALT_SPIM_CTLR0_FRF_SET_MSK
                     | ALT_SPIM_CTLR0_SCPH_SET_MSK
                     | ALT_SPIM_CTLR0_SCPOL_SET_MSK
                     | ALT_SPIM_CTLR0_TMOD_SET_MSK
                     | ALT_SPIM_CTLR0_SRL_SET_MSK;
                       
        alt_replbits_word(ALT_SPIM_CTLR0_ADDR(spi_dev->location), cfg_mask, cfg_register);
        break;
    case ALT_SPI_OP_MODE_SLAVE:

    cfg_register     = ALT_SPIS_CTLR0_DFS_SET(cfg->frame_size)
                     | ALT_SPIS_CTLR0_FRF_SET(cfg->frame_format)
                     | ALT_SPIS_CTLR0_SCPH_SET(cfg->clk_phase)
                     | ALT_SPIS_CTLR0_SCPOL_SET(cfg->clk_polarity)
                     | ALT_SPIS_CTLR0_TMOD_SET(cfg->transfer_mode)
                     | ALT_SPIS_CTLR0_SLV_OE_SET(cfg->slave_output_enable)
                     | ALT_SPIS_CTLR0_SRL_SET(cfg->loopback_mode);

        cfg_mask     = ALT_SPIS_CTLR0_DFS_SET_MSK
                     | ALT_SPIS_CTLR0_FRF_SET_MSK
                     | ALT_SPIS_CTLR0_SCPH_SET_MSK
                     | ALT_SPIS_CTLR0_SCPOL_SET_MSK
                     | ALT_SPIS_CTLR0_TMOD_SET_MSK
                     | ALT_SPIS_CTLR0_SLV_OE_SET_MSK
                     | ALT_SPIS_CTLR0_SRL_SET_MSK;
                       
        alt_replbits_word(ALT_SPIS_CTLR0_ADDR(spi_dev->location), cfg_mask, cfg_register);
        break;
    }

    spi_dev->last_transfer_mode = cfg->transfer_mode;

    return status;

}

//
// Get config parameters from appropriate registers for microwire mode.
//
ALT_STATUS_CODE alt_spi_mw_config_get(ALT_SPI_DEV_t *spi_dev,
                                      ALT_SPI_MW_CONFIG_t* cfg)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !cfg)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t cfg_register, mwcr_register;
    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        cfg_register           = alt_read_word(ALT_SPIM_CTLR0_ADDR(spi_dev->location));
        mwcr_register          = alt_read_word(ALT_SPIM_MWCR_ADDR(spi_dev->location));
        
        cfg->ctl_frame_size    = ALT_SPIM_CTLR0_DFS_GET(cfg_register);
        cfg->mode              = (ALT_SPI_MW_MODE_t)ALT_SPIM_MWCR_MWMOD_GET(mwcr_register);
        cfg->dir               = (ALT_SPI_MW_DIR_t)ALT_SPIM_MWCR_MDD_GET(mwcr_register);
        cfg->handshake_enabled = ALT_SPIM_MWCR_MHS_GET(mwcr_register);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        cfg_register          = alt_read_word(ALT_SPIS_CTLR0_ADDR(spi_dev->location));
        mwcr_register         = alt_read_word(ALT_SPIS_MWCR_ADDR(spi_dev->location));
        
        cfg->ctl_frame_size = ALT_SPIS_CTLR0_DFS_GET(cfg_register);
        cfg->mode             = (ALT_SPI_MW_MODE_t)ALT_SPIS_MWCR_MWMOD_GET(mwcr_register);
        cfg->dir              = (ALT_SPI_MW_DIR_t)ALT_SPIS_MWCR_MDD_GET(mwcr_register);
        break;
    }
    return ALT_E_SUCCESS;
}

//
// Set config parameters to appropriate registers for microwire mode.
//
ALT_STATUS_CODE alt_spi_mw_config_set(ALT_SPI_DEV_t *spi_dev,
                                      const ALT_SPI_MW_CONFIG_t* cfg)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !cfg)
    {
        return ALT_E_BAD_ARG;
    }

    if (cfg->ctl_frame_size > ALT_SPI_MW_CTL_FRAME_SIZE_MAX
        || cfg->mode > ALT_SPI_MW_SEQUENTIAL || cfg->dir > ALT_SPI_MW_DIR_TX)
    {
        return ALT_E_ARG_RANGE;
    }

    // Set config parameters to appropriate registers
    uint32_t mwcr_register;
    uint32_t mwcr_mask;
    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        mwcr_register = ALT_SPIM_MWCR_MWMOD_SET(cfg->mode)
                      | ALT_SPIM_MWCR_MDD_SET(cfg->dir)
                      | ALT_SPIM_MWCR_MHS_SET(cfg->handshake_enabled);

        mwcr_mask     = ALT_SPIM_MWCR_MWMOD_SET_MSK
                      | ALT_SPIM_MWCR_MDD_SET_MSK
                      | ALT_SPIM_MWCR_MHS_SET_MSK;
                        
        alt_replbits_word(ALT_SPIM_MWCR_ADDR(spi_dev->location), mwcr_mask, mwcr_register);
        alt_replbits_word(ALT_SPIM_CTLR0_ADDR(spi_dev->location), 
                          ALT_SPIM_CTLR0_DFS_SET_MSK,
                          ALT_SPIM_CTLR0_DFS_SET(cfg->ctl_frame_size));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        mwcr_register = ALT_SPIS_MWCR_MWMOD_SET(cfg->mode)
                      | ALT_SPIS_MWCR_MDD_SET(cfg->dir);

        mwcr_mask     = ALT_SPIS_MWCR_MWMOD_SET_MSK
                      | ALT_SPIS_MWCR_MDD_SET_MSK;
                        
        alt_replbits_word(ALT_SPIS_MWCR_ADDR(spi_dev->location), mwcr_mask, mwcr_register);
        alt_replbits_word(ALT_SPIS_CTLR0_ADDR(spi_dev->location), 
                          ALT_SPIS_CTLR0_DFS_SET_MSK,
                          ALT_SPIS_CTLR0_DFS_SET(cfg->ctl_frame_size));
        break;
    }

    return status;

}

//
// Disable the specified SPI controller slave select output lines..
//
ALT_STATUS_CODE alt_spi_slave_select_disable(ALT_SPI_DEV_t *spi_dev,
                                             const uint32_t mask)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (mask > ALT_SPI_SLAVE_MASK_ALL)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_clrbits_word(ALT_SPIM_SER_ADDR(spi_dev->location), mask);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        status = ALT_E_ERROR;
        break;
    }

    return status;
}

//
// Enable the specified SPI controller slave select output lines.
//
ALT_STATUS_CODE alt_spi_slave_select_enable(ALT_SPI_DEV_t *spi_dev,
                                            const uint32_t mask)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (mask > ALT_SPI_SLAVE_MASK_ALL)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_setbits_word(ALT_SPIM_SER_ADDR(spi_dev->location), mask);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        status = ALT_E_ERROR;
        break;
    }

    return status;
}

//
// Get the configured baud rate divider value for the specified SPI controller
//
ALT_STATUS_CODE alt_spi_divider_get(ALT_SPI_DEV_t *spi_dev, uint32_t *div)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *div = ALT_SPIM_BAUDR_SCKDV_GET(alt_read_word(ALT_SPIM_BAUDR_ADDR(spi_dev->location)));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

//
// Set the baud rate divider to configure the generated sclk_out frequency
//
ALT_STATUS_CODE alt_spi_divider_set(ALT_SPI_DEV_t *spi_dev, const uint32_t div)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (spi_dev->op_mode != ALT_SPI_OP_MODE_MASTER)
    {
        return ALT_E_ERROR;
    }

    if (div < ALT_SPI_MIN_CLK_DIV || div > ALT_SPI_MAX_CLK_DIV)
    {
        return ALT_E_BAD_ARG;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    bool already_enabled = (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_spi_disable(spi_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }

    alt_replbits_word(ALT_SPIM_BAUDR_ADDR(spi_dev->location),
                      ALT_SPIM_BAUDR_SCKDV_SET_MSK,
                      ALT_SPIM_BAUDR_SCKDV_SET(div));

    if (already_enabled)
    {
        // Re-enable controller
        status = alt_spi_enable(spi_dev);
    }

    return status;
}

    
//
// Get the configured baud rate divider value for the specified SPI controller
//
ALT_STATUS_CODE alt_spi_baud_rate_get(ALT_SPI_DEV_t *spi_dev, uint32_t *div)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !div)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *div = ALT_SPIM_BAUDR_SCKDV_GET(alt_read_word(ALT_SPIM_BAUDR_ADDR(spi_dev->location)));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        status = ALT_E_ERROR;
        break;
    }

    return status;
}
    
//
// Set the baud rate divider to configure the generated sclk_out frequency
//
ALT_STATUS_CODE alt_spi_baud_rate_set(ALT_SPI_DEV_t *spi_dev, const uint32_t div)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE )
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        if(div < ALT_SPI_MIN_CLK_DIV || div > ALT_SPI_MAX_CLK_DIV)
        {
            status = ALT_E_BAD_ARG;
            break;
        }
        alt_replbits_word(ALT_SPIM_BAUDR_ADDR(spi_dev->location), 
                          ALT_SPIM_BAUDR_SCKDV_SET_MSK,
                          ALT_SPIM_BAUDR_SCKDV_SET(div));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        status = ALT_E_ERROR;
        break;
    }

    return status;

}

//
// Return bus speed by configuration of spi controller for master mode.
//
ALT_STATUS_CODE alt_spi_speed_get(ALT_SPI_DEV_t * spi_dev,
                                  uint32_t * speed_in_hz)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t div;

    status = alt_spi_divider_get(spi_dev, &div);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }
 
    if (div < ALT_SPI_MIN_CLK_DIV || div > ALT_SPI_MAX_CLK_DIV)
    {
        return ALT_E_BAD_ARG;
    }
        
    //<speed, Hz> = <internal clock> / <lcount>
    *speed_in_hz = spi_dev->clock_freq / div;

    return ALT_E_SUCCESS;
}

//
// Fill struct with configuration of spi controller for master mode by bus speed
//
ALT_STATUS_CODE alt_spi_speed_set(ALT_SPI_DEV_t * spi_dev,
                                  uint32_t speed_in_hz)

{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    // If speed is not standard or fast return range error
    if (speed_in_hz > spi_dev->clock_freq || speed_in_hz == 0)
    {
        return ALT_E_ARG_RANGE;
    }

    //<lcount> = <internal clock> / <speed, Hz>
    uint32_t div = spi_dev->clock_freq / speed_in_hz;

    return alt_spi_divider_set(spi_dev, div);
}

//
// Fill struct with configuration of spi controller for master mode by bus speed
//
ALT_STATUS_CODE alt_spi_speed_to_divider(ALT_SPI_DEV_t * spi_dev, 
                                         uint32_t speed_in_hz, 
                                         uint32_t * div)
    
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !div)
    {
        return ALT_E_BAD_ARG;
    }

    // If speed is not standard or fast return range error
    if (speed_in_hz > spi_dev->clock_freq || speed_in_hz == 0)
    {
        return ALT_E_ARG_RANGE;
    }
    
    // <lcount> = <internal clock> / <speed, Hz>
    *div = spi_dev->clock_freq / speed_in_hz;

    return ALT_E_SUCCESS;
}

//
// Return bus speed by configuration of spi controller for master mode.
//
ALT_STATUS_CODE alt_spi_divider_to_speed(ALT_SPI_DEV_t * spi_dev, 
                                         uint32_t * speed_in_hz, 
                                         const uint32_t * div)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !div)
    {
        return ALT_E_BAD_ARG;
    }

    if (*div < ALT_SPI_MIN_CLK_DIV || *div > ALT_SPI_MAX_CLK_DIV)
    {
        return ALT_E_BAD_ARG;
    }
    
    // <speed, Hz> = <internal clock> / <lcount>
    *speed_in_hz = spi_dev->clock_freq / *div;

    return ALT_E_SUCCESS;
}

//
// Get the current number of data frames configured for the SPI controller.
//
ALT_STATUS_CODE alt_spi_num_data_frames_get(ALT_SPI_DEV_t *spi_dev, uint32_t *num_data_frames)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !num_data_frames)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *num_data_frames = ALT_SPIM_CTLR1_NDF_GET(alt_read_word(ALT_SPIM_CTLR1_ADDR(spi_dev->location)));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        status = ALT_E_ERROR;
        break;
    }

    return status;
}
   
//
// Set the number of data frames configured for the SPI controller.
//
ALT_STATUS_CODE alt_spi_num_data_frames_set(ALT_SPI_DEV_t *spi_dev, const uint32_t num_data_frames)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE )
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        if(num_data_frames & ALT_SPIM_CTLR1_NDF_CLR_MSK)
        {
            status = ALT_E_BAD_ARG;
            break;
        }
        alt_replbits_word(ALT_SPIM_CTLR1_ADDR(spi_dev->location), 
                          ALT_SPIM_CTLR1_NDF_SET_MSK,
                          ALT_SPIM_CTLR1_NDF_SET(num_data_frames));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        status = ALT_E_ERROR;
        break;
    }

    return status;

}

//
// Returns the current SPI controller interrupt status conditions.
//
ALT_STATUS_CODE alt_spi_int_status_get(ALT_SPI_DEV_t *spi_dev,
                                       uint32_t *status)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !status)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *status = alt_read_word(ALT_SPIM_ISR_ADDR(spi_dev->location));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        *status = alt_read_word(ALT_SPIS_ISR_ADDR(spi_dev->location));
        break;
    }

    return ALT_E_SUCCESS;
}

//
// Returns the SPI controller raw interrupt status conditions irrespective of
// the interrupt status condition enablement state.
//
ALT_STATUS_CODE alt_spi_int_raw_status_get(ALT_SPI_DEV_t *spi_dev,
                                           uint32_t *status)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !status)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *status = alt_read_word(ALT_SPIM_RISR_ADDR(spi_dev->location));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        *status = alt_read_word(ALT_SPIS_RISR_ADDR(spi_dev->location));
        break;
    }

    return ALT_E_SUCCESS;
}

//
// Clears the specified SPI controller interrupt status conditions identified
// in the mask (for slave mode).
//
static ALT_STATUS_CODE alt_spi_slave_int_clear(ALT_SPI_DEV_t *spi_dev, const uint32_t mask)
{
    if (mask == ALT_SPI_STATUS_ALL)
    {
        alt_read_word(ALT_SPIS_ICR_ADDR(spi_dev->location));
        return ALT_E_SUCCESS;
    }
    
    // For different status clear different register
    if (mask & ALT_SPI_STATUS_TXOI)
    {
        alt_read_word(ALT_SPIS_TXOICR_ADDR(spi_dev->location));
    } 
    if (mask & ALT_SPI_STATUS_RXOI)
    {
        alt_read_word(ALT_SPIS_RXOICR_ADDR(spi_dev->location));
    }
    if (mask & ALT_SPI_STATUS_RXUI)
    {
        alt_read_word(ALT_SPIS_RXUICR_ADDR(spi_dev->location));
    }

    return ALT_E_SUCCESS;
}

//
// Clears the specified SPI controller interrupt status conditions identified
// in the mask (for master mode).
//
static ALT_STATUS_CODE alt_spi_master_int_clear(ALT_SPI_DEV_t *spi_dev, const uint32_t mask)
{
    if (mask == ALT_SPI_STATUS_ALL)
    {
        alt_read_word(ALT_SPIM_ICR_ADDR(spi_dev->location));
        return ALT_E_SUCCESS;
    }
    
    // For different status clear different register
    if (mask & ALT_SPI_STATUS_TXOI)
    {
        alt_read_word(ALT_SPIM_TXOICR_ADDR(spi_dev->location));
    }
    if (mask & ALT_SPI_STATUS_RXOI)
    {
        alt_read_word(ALT_SPIM_RXOICR_ADDR(spi_dev->location));
    }
    if (mask & ALT_SPI_STATUS_RXUI)
    {
        alt_read_word(ALT_SPIM_RXUICR_ADDR(spi_dev->location));
    }

    return ALT_E_SUCCESS;
}

//
// Clears the specified SPI controller interrupt status conditions identified
// in the mask.
//
ALT_STATUS_CODE alt_spi_int_clear(ALT_SPI_DEV_t *spi_dev, const uint32_t mask)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        status = alt_spi_master_int_clear(spi_dev, mask);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        status = alt_spi_slave_int_clear(spi_dev, mask);
        break;
    }
    return status;
}

//
// Disable the specified SPI controller interrupt status conditions identified in
// the mask.
//
ALT_STATUS_CODE alt_spi_int_disable(ALT_SPI_DEV_t *spi_dev, const uint32_t mask)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_clrbits_word(ALT_SPIM_IMR_ADDR(spi_dev->location), mask);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        alt_clrbits_word(ALT_SPIS_IMR_ADDR(spi_dev->location), mask);
        break;
    }

    return ALT_E_SUCCESS;
}

//
// Enable the specified SPI controller interrupt status conditions identified in
// the mask.
//
ALT_STATUS_CODE alt_spi_int_enable(ALT_SPI_DEV_t *spi_dev, const uint32_t mask)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_setbits_word(ALT_SPIM_IMR_ADDR(spi_dev->location), mask);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        alt_setbits_word(ALT_SPIS_IMR_ADDR(spi_dev->location), mask);
        break;
    }

    return ALT_E_SUCCESS;
}

//
// Returns ALT_E_TRUE when the receive FIFO is empty.
//
ALT_STATUS_CODE alt_spi_rx_fifo_is_empty(ALT_SPI_DEV_t *spi_dev)
{
    ALT_STATUS_CODE status = ALT_E_FALSE;
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        if (ALT_SPIM_SR_RFNE_GET(alt_read_word(ALT_SPIM_SR_ADDR(spi_dev->location))) == ALT_SPIM_SR_RFNE_E_EMPTY)
        {
            status = ALT_E_TRUE;
        }
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        if (ALT_SPIS_SR_RFNE_GET(alt_read_word(ALT_SPIS_SR_ADDR(spi_dev->location))) == ALT_SPIS_SR_RFNE_E_EMPTY)
        {
            status =  ALT_E_TRUE;
        }
        break;
    }
    return status;
}

//
// Returns ALT_E_TRUE when the receive FIFO is completely full.
//
ALT_STATUS_CODE alt_spi_rx_fifo_is_full(ALT_SPI_DEV_t *spi_dev)
{
    ALT_STATUS_CODE status = ALT_E_FALSE;
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        if (ALT_SPIM_SR_RFF_GET(alt_read_word(ALT_SPIM_SR_ADDR(spi_dev->location))) == ALT_SPIM_SR_RFF_E_FULL)
        {
            status = ALT_E_TRUE;
        }
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        if (ALT_SPIS_SR_RFF_GET(alt_read_word(ALT_SPIS_SR_ADDR(spi_dev->location))) == ALT_SPIS_SR_RFF_E_FULL)
        {
            status = ALT_E_TRUE;
        }
        break;
    }
    return status;
}

//
// Returns the number of valid entries in the receive FIFO.
//
ALT_STATUS_CODE alt_spi_rx_fifo_level_get(ALT_SPI_DEV_t *spi_dev,
                                          uint32_t *num_entries)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !num_entries)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *num_entries = ALT_SPIM_RXFLR_RXTFL_GET(alt_read_word(ALT_SPIM_RXFLR_ADDR(spi_dev->location)));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        *num_entries = ALT_SPIS_RXFLR_RXTFL_GET(alt_read_word(ALT_SPIS_RXFLR_ADDR(spi_dev->location)));
        break;
    }

    return ALT_E_SUCCESS;

}

//
// Gets the current receive FIFO threshold level value.
//
ALT_STATUS_CODE alt_spi_rx_fifo_threshold_get(ALT_SPI_DEV_t *spi_dev,
                                              uint8_t *threshold)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !threshold)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *threshold = ALT_SPIM_RXFTLR_RFT_GET(alt_read_word(ALT_SPIM_RXFTLR_ADDR(spi_dev->location)));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        *threshold = ALT_SPIS_RXFTLR_RFT_GET(alt_read_word(ALT_SPIS_RXFTLR_ADDR(spi_dev->location)));
        break;
    }

    return ALT_E_SUCCESS;

}

//
// Sets the current receive FIFO threshold level value.
//
ALT_STATUS_CODE alt_spi_rx_fifo_threshold_set(ALT_SPI_DEV_t *spi_dev,
                                              const uint8_t threshold)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_replbits_word(ALT_SPIM_RXFTLR_ADDR(spi_dev->location), 
                          ALT_SPIM_RXFTLR_RFT_SET_MSK,
                          ALT_SPIM_RXFTLR_RFT_SET(threshold));
        
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        alt_replbits_word(ALT_SPIS_RXFTLR_ADDR(spi_dev->location), 
                          ALT_SPIS_RXFTLR_RFT_SET_MSK,
                          ALT_SPIS_RXFTLR_RFT_SET(threshold));
        
        break;
    }

    return status;
}

//
// Returns ALT_E_TRUE when the transmit FIFO is empty.
//
ALT_STATUS_CODE alt_spi_tx_fifo_is_empty(ALT_SPI_DEV_t *spi_dev)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        if (ALT_SPIM_SR_TFE_GET(alt_read_word(ALT_SPIM_SR_ADDR(spi_dev->location))) == ALT_SPIM_SR_TFE_E_EMPTY)
        {
            return ALT_E_TRUE;
        }
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        if (ALT_SPIS_SR_TFE_GET(alt_read_word(ALT_SPIS_SR_ADDR(spi_dev->location))) == ALT_SPIS_SR_TFE_E_EMPTY)
        {
            return ALT_E_TRUE;
        }
        break;
    }

    return ALT_E_FALSE;
}

//
// Returns ALT_E_TRUE when the transmit FIFO is completely full.
//
ALT_STATUS_CODE alt_spi_tx_fifo_is_full(ALT_SPI_DEV_t *spi_dev)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        if (ALT_SPIM_SR_TFNF_GET(alt_read_word(ALT_SPIM_SR_ADDR(spi_dev->location))) == ALT_SPIM_SR_TFNF_E_FULL)
        {
            return ALT_E_TRUE;
        }
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        if (ALT_SPIS_SR_TFNF_GET(alt_read_word(ALT_SPIS_SR_ADDR(spi_dev->location))) == ALT_SPIS_SR_TFNF_E_FULL)
        {
            return ALT_E_TRUE;
        }
        break;
    }

    return ALT_E_FALSE;
}

//
// Returns the number of valid entries in the transmit FIFO.
//
ALT_STATUS_CODE alt_spi_tx_fifo_level_get(ALT_SPI_DEV_t *spi_dev,
                                          uint32_t *num_entries)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !num_entries)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *num_entries = ALT_SPIM_TXFLR_TXTFL_GET(alt_read_word(ALT_SPIM_TXFLR_ADDR(spi_dev->location)));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        *num_entries = ALT_SPIS_TXFLR_TXTFL_GET(alt_read_word(ALT_SPIS_TXFLR_ADDR(spi_dev->location)));
        break;
    }

    return ALT_E_SUCCESS;

}


//
// Sets the current transmit FIFO threshold level value.
//
ALT_STATUS_CODE alt_spi_tx_fifo_threshold_get(ALT_SPI_DEV_t *spi_dev,
                                              uint8_t *threshold)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !threshold)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *threshold = ALT_SPIM_TXFTLR_TFT_GET(alt_read_word(ALT_SPIM_TXFTLR_ADDR(spi_dev->location)));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        *threshold = ALT_SPIS_TXFTLR_TFT_GET(alt_read_word(ALT_SPIS_TXFTLR_ADDR(spi_dev->location)));
        break;
    }

    return ALT_E_SUCCESS;

}

//
// Sets the current transmit FIFO threshold level value.
//
ALT_STATUS_CODE alt_spi_tx_fifo_threshold_set(ALT_SPI_DEV_t *spi_dev,
                                              const uint8_t threshold)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_replbits_word(ALT_SPIM_TXFTLR_ADDR(spi_dev->location), 
                          ALT_SPIM_TXFTLR_TFT_SET_MSK,
                          ALT_SPIM_TXFTLR_TFT_SET(threshold));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        alt_replbits_word(ALT_SPIS_TXFTLR_ADDR(spi_dev->location), 
                          ALT_SPIS_TXFTLR_TFT_SET_MSK,
                          ALT_SPIS_TXFTLR_TFT_SET(threshold));
        break;
    }

    return status;
}

//
// Get the configured Rx sample delay value.
//
ALT_STATUS_CODE alt_spi_rx_sample_delay_get(ALT_SPI_DEV_t *spi_dev, uint32_t *delay)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !delay)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *delay = ALT_SPIM_RX_SMPL_DLY_RSD_GET(alt_read_word(ALT_SPIM_RX_SMPL_DLY_ADDR(spi_dev->location)));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        status = ALT_E_ERROR;
        break;
    }

    return status;
}

//
// Set the configured Rx sample delay value.
//
ALT_STATUS_CODE alt_spi_rx_sample_delay_set(ALT_SPI_DEV_t *spi_dev, const uint32_t delay)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_is_enabled(spi_dev) == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        if(delay & ALT_SPIM_RX_SMPL_DLY_RSD_CLR_MSK)
        {
            status = ALT_E_BAD_ARG;
            break;
        }
        alt_replbits_word(ALT_SPIM_RX_SMPL_DLY_ADDR(spi_dev->location), 
                          ALT_SPIM_RX_SMPL_DLY_RSD_SET_MSK,
                          ALT_SPIM_RX_SMPL_DLY_RSD_SET(delay));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        status = ALT_E_ERROR;
        break;
    }

    return status;
}

//
// Disable the transmit (Tx) FIFO DMA channel.
//
ALT_STATUS_CODE alt_spi_dma_tx_disable(ALT_SPI_DEV_t *spi_dev)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    // Else clear enable bit of spi_enable register
    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_clrbits_word(ALT_SPIM_DMACR_ADDR(spi_dev->location), 
                         ALT_SPIM_DMACR_TDMAE_SET_MSK);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        alt_clrbits_word(ALT_SPIS_DMACR_ADDR(spi_dev->location), 
                         ALT_SPIS_DMACR_TDMAE_SET_MSK);
        break;
    }

    return ALT_E_SUCCESS;
}

//
// Enable and set the transmit data level for the transmit (Tx) FIFO DMA channel.
//
ALT_STATUS_CODE alt_spi_dma_tx_enable(ALT_SPI_DEV_t *spi_dev, const uint32_t level)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_setbits_word(ALT_SPIM_DMACR_ADDR(spi_dev->location),
                         ALT_SPIM_DMACR_TDMAE_SET_MSK);
        if(level & ALT_SPIM_DMATDLR_DMATDL_CLR_MSK)
        {
            status = ALT_E_BAD_ARG;
            break;
        }
        alt_replbits_word(ALT_SPIM_DMATDLR_ADDR(spi_dev->location), 
                          ALT_SPIM_DMATDLR_DMATDL_SET_MSK,
                          ALT_SPIM_DMATDLR_DMATDL_SET(level));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        if(level & ALT_SPIS_DMATDLR_DMATDL_CLR_MSK)
        {
            status = ALT_E_BAD_ARG;
            break;
        }
        alt_setbits_word( ALT_SPIS_DMACR_ADDR(spi_dev->location),
                          ALT_SPIS_DMACR_TDMAE_SET_MSK);
        alt_replbits_word(ALT_SPIS_DMATDLR_ADDR(spi_dev->location), 
                          ALT_SPIS_DMATDLR_DMATDL_SET_MSK,
                          ALT_SPIS_DMATDLR_DMATDL_SET(level));
        break;
    }
    
    return status;
}

//
// Disable the receive (Rx) FIFO DMA channel.
//
ALT_STATUS_CODE alt_spi_dma_rx_disable(ALT_SPI_DEV_t *spi_dev)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    // Else clear enable bit of spi_enable register
    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_clrbits_word(ALT_SPIM_DMACR_ADDR(spi_dev->location), 
                         ALT_SPIM_DMACR_RDMAE_SET_MSK);
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        alt_clrbits_word(ALT_SPIS_DMACR_ADDR(spi_dev->location), 
                         ALT_SPIS_DMACR_RDMAE_SET_MSK);
        break;
    }

    return ALT_E_SUCCESS;
}

//
// Enable and set the receive data level for the receive (Rx) FIFO DMA channel.
//
ALT_STATUS_CODE alt_spi_dma_rx_enable(ALT_SPI_DEV_t *spi_dev, const uint32_t level)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_setbits_word( ALT_SPIM_DMACR_ADDR(spi_dev->location),
                          ALT_SPIM_DMACR_RDMAE_SET_MSK);
        if(level & ALT_SPIM_DMARDLR_DMARDL_CLR_MSK)
        {
            status = ALT_E_BAD_ARG;
            break;
        }
        alt_replbits_word(ALT_SPIM_DMARDLR_ADDR(spi_dev->location), 
                          ALT_SPIM_DMARDLR_DMARDL_SET_MSK,
                          ALT_SPIM_DMARDLR_DMARDL_SET(level));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        if(level & ALT_SPIS_DMARDLR_DMARDL_CLR_MSK)
        {
            status = ALT_E_BAD_ARG;
            break;
        }
        alt_setbits_word( ALT_SPIS_DMACR_ADDR(spi_dev->location),
                          ALT_SPIS_DMACR_RDMAE_SET_MSK);
        alt_replbits_word(ALT_SPIS_DMARDLR_ADDR(spi_dev->location), 
                          ALT_SPIS_DMARDLR_DMARDL_SET_MSK,
                          ALT_SPIS_DMARDLR_DMARDL_SET(level));
        break;
    }
    
    return status;
}

//
// Reads a data frame from the receive (Rx) FIFO.
//
ALT_STATUS_CODE alt_spi_rx_fifo_deq(ALT_SPI_DEV_t *spi_dev, uint16_t *data)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE || !data)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_spi_is_enabled(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        *data = (ALT_SPIM_DR_DR_GET(alt_read_word(ALT_SPIM_DR_ADDR(spi_dev->location))));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        *data = (ALT_SPIS_DR_DR_GET(alt_read_word(ALT_SPIS_DR_ADDR(spi_dev->location))));
        break;
    }

    return ALT_E_SUCCESS;
}

//
// Writes a data frame to the transmit (Tx) FIFO for transmittal.
//
ALT_STATUS_CODE alt_spi_tx_fifo_enq(ALT_SPI_DEV_t *spi_dev, const uint16_t data)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_spi_is_enabled(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    switch (spi_dev->op_mode)
    {
    case ALT_SPI_OP_MODE_MASTER:
        alt_write_word(ALT_SPIM_DR_ADDR(spi_dev->location), ALT_SPIM_DR_DR_SET(data));
        break;
    case ALT_SPI_OP_MODE_SLAVE:
        alt_write_word(ALT_SPIS_DR_ADDR(spi_dev->location), ALT_SPIS_DR_DR_SET(data));
        break;
    }

    return ALT_E_SUCCESS;
}

//
// This function writes a single data byte to the transmit FIFO. 
//
static ALT_STATUS_CODE alt_spi_transmit_error_handler(ALT_SPI_DEV_t *spi_dev, ALT_STATUS_CODE *err_status)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    uint32_t int_status = 0;

    status = alt_spi_int_raw_status_get(spi_dev, &int_status);

    if (status == ALT_E_TRUE && int_status != 0)
    {
        if(int_status 
            & (ALT_SPI_STATUS_TXOI
                | ALT_SPI_STATUS_RXOI
                | ALT_SPI_STATUS_RXUI))
        {
            *err_status = ALT_E_BUF_OVF;
        }
    }

    return status;
}

//
// Write or read bulk of data form master mode
//
static ALT_STATUS_CODE alt_spi_master_transfer_helper(ALT_SPI_DEV_t *spi_dev, 
                                                      size_t data_send,
                                                      size_t data_recv,
                                                      const uint16_t * tx_buf, 
                                                      uint16_t * rx_buf)
{
    ALT_STATUS_CODE    status  = ALT_E_SUCCESS;

    const uint16_t * buffer_tx = tx_buf;
    uint16_t * buffer_rx       = rx_buf;
    uint32_t timeout           = MAX(data_send, data_recv) * 10000;
    
    while (data_send > 0 || data_recv > 0)
    {
        // Error handling
        ALT_STATUS_CODE err_status = 0;
        status = alt_spi_transmit_error_handler(spi_dev, &err_status);
    
        if (status != ALT_E_SUCCESS)
        {
            break;
        }
    
        if (err_status != ALT_E_SUCCESS)
        {
            status = err_status;
            break;
        }
    
        // Top up the TX FIFO with sending data
    
        if (data_send > 0)
        {
            uint32_t level = 0;
            status = alt_spi_tx_fifo_level_get(spi_dev, &level);
            if (status != ALT_E_SUCCESS)
            {
                break;
            }
    
            uint32_t space = ALT_SPI_TX_FIFO_NUM_ENTRIES - level;
    
            space = MIN(data_send, space);
    
            for (uint32_t i = 0; i < space; ++i)
            {
                alt_write_word(ALT_SPIM_DR_ADDR(spi_dev->location), ALT_SPIM_DR_DR_SET(*buffer_tx));
                ++buffer_tx;
            }
    
            data_send -= space;
        }
    
        // Read out the resulting received data as they come in.
    
        if (data_recv > 0)
        {
            uint32_t level = 0;
            status = alt_spi_rx_fifo_level_get(spi_dev, &level);
            if (status != ALT_E_SUCCESS)
            {
                break;
            }
    
            if (level == 0)
            {
                timeout--;
                if (timeout == 0)
                {
                    status = ALT_E_TMO;
                    break;
                }
            }
    
            level = MIN(data_recv, level);
    
            for (uint32_t i = 0; i < level; ++i)
            {
                uint32_t data_read = alt_read_word(ALT_SPIM_DR_ADDR(spi_dev->location));
                *buffer_rx = (ALT_SPIM_DR_DR_GET(data_read));
                //printf("data %x\n", (unsigned int)data_read);
                ++buffer_rx;
            }
    
            data_recv -= level;
        }
    }

    return status;
}

//
// This function performs a master SPI/SSP serial master transfer operations (use by all transfer functions).
//
static ALT_STATUS_CODE alt_spi_master_transfer(ALT_SPI_DEV_t *spi_dev, 
                                               const uint32_t slave_select,
                                               const size_t num_frames,
                                               const uint16_t * tx_buf, 
                                               uint16_t * rx_buf,
                                               ALT_SPI_TMOD_t transfer_mode,
                                               const uint8_t opcode,
                                               const uint32_t eeprom_addr)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (spi_dev->op_mode == ALT_SPI_OP_MODE_SLAVE)
    {
        return ALT_E_ERROR;
    }
    
    if (num_frames == 0) 
    {
        return ALT_E_SUCCESS;
    }

    ALT_STATUS_CODE    status = ALT_E_SUCCESS;

    if(alt_spi_is_busy(spi_dev) == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    // Checking necessity to update slave mask
    if (slave_select != spi_dev->last_slave_mask)
    {
        status = alt_spi_disable(spi_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
        // Update slave select mask
        alt_spi_slave_select_disable(spi_dev, ALT_SPI_SLAVE_MASK_ALL);
        status = alt_spi_slave_select_enable(spi_dev, slave_select);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }

        spi_dev->last_slave_mask = slave_select;
    }

    // Checking necessity to update transfer mode
    if (transfer_mode != spi_dev->last_transfer_mode)
    {
        status = alt_spi_disable(spi_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
        // Update transfer mode
        alt_replbits_word(ALT_SPIM_CTLR0_ADDR(spi_dev->location),
                          ALT_SPIM_CTLR0_TMOD_SET_MSK,
                          ALT_SPIM_CTLR0_TMOD_SET(transfer_mode));
        spi_dev->last_transfer_mode = transfer_mode;
    }
    
    if (transfer_mode == ALT_SPI_TMOD_RX || transfer_mode == ALT_SPI_TMOD_EEPROM)
    {
        status = alt_spi_disable(spi_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
        // Set number of data frames for read
        status = alt_spi_num_data_frames_set(spi_dev, num_frames - 1);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }

    // Clear interrupt status and disable interrupt mask
    alt_spi_int_clear(spi_dev, ALT_SPI_STATUS_ALL);
    alt_spi_int_disable(spi_dev, ALT_SPI_STATUS_ALL);

    if (alt_spi_is_enabled(spi_dev) == ALT_E_FALSE)
    {
        status = alt_spi_enable(spi_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }
    
    //Enable abort and TXFIFO empty interrupt status
    alt_spi_int_enable(spi_dev, ALT_SPI_STATUS_RXOI | 
                                ALT_SPI_STATUS_RXUI | 
                                ALT_SPI_STATUS_TXOI);

    // This SPI controller requires that a read issue be performed for each byte requested.
    // Read issue takes space in the TX FIFO, which may asynchronously handling a previous request.
    
    uint32_t data_send = 0;
    uint32_t data_recv = 0;
    
    if (transfer_mode == ALT_SPI_TMOD_TX || transfer_mode == ALT_SPI_TMOD_TXRX)
    {
        data_send = num_frames;
    }
    
    if (transfer_mode == ALT_SPI_TMOD_RX   || 
        transfer_mode == ALT_SPI_TMOD_TXRX ||
        transfer_mode == ALT_SPI_TMOD_EEPROM)
    {
        data_recv = num_frames;
    }
    
    if (transfer_mode == ALT_SPI_TMOD_EEPROM)
    {
        //Send opcode and eeprom address
        alt_write_word(ALT_SPIM_DR_ADDR(spi_dev->location), ALT_SPIM_DR_DR_SET(opcode));
        alt_write_word(ALT_SPIM_DR_ADDR(spi_dev->location), ALT_SPIM_DR_DR_SET(((eeprom_addr & 0xFF00) >> 8)));
        alt_write_word(ALT_SPIM_DR_ADDR(spi_dev->location), ALT_SPIM_DR_DR_SET(eeprom_addr & 0xFF));
    }
    if (transfer_mode == ALT_SPI_TMOD_RX)
    {
        //Activate rx transfer
        alt_spi_tx_fifo_enq(spi_dev, 0);
    }
    
    // Write or read bulk of data
    status = alt_spi_master_transfer_helper(spi_dev,
                                            data_send, data_recv,
                                            tx_buf,  
                                            rx_buf);

    // Need reset for set spi bus in idle state
    if(status == ALT_E_TMO)
        alt_spi_reset(spi_dev);

    // Mask all interrupts
    alt_spi_int_disable(spi_dev, ALT_SPI_STATUS_ALL);

    return status;
}

//
// This function performs a master SPI/SSP serial transmit and receive transfer.
//
ALT_STATUS_CODE alt_spi_master_tx_rx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                              const uint32_t slave_select,
                                              const size_t num_frames,
                                              const uint16_t * tx_buf, 
                                              uint16_t * rx_buf)
{
    return alt_spi_master_transfer(spi_dev, 
                                   slave_select, 
                                   num_frames,
                                   tx_buf, 
                                   rx_buf, 
                                   ALT_SPI_TMOD_TXRX, 
                                   0, 0);
}

//
// This function performs a master SPI/SSP serial transmit only transfer.
//
ALT_STATUS_CODE alt_spi_master_tx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                           const uint32_t slave_select,
                                           const size_t num_frames,
                                           const uint16_t * tx_buf)
{
    return alt_spi_master_transfer(spi_dev, 
                                   slave_select, 
                                   num_frames,
                                   tx_buf, NULL, 
                                   ALT_SPI_TMOD_TX, 
                                   0, 0);
}

//
// This function performs a master SPI/SSP serial receive only transfer.
//
ALT_STATUS_CODE alt_spi_master_rx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                           const uint32_t slave_select,
                                           const size_t num_frames,
                                           uint16_t * rx_buf)
{
    return alt_spi_master_transfer(spi_dev, 
                                   slave_select, 
                                   num_frames,
                                   NULL, 
                                   rx_buf, 
                                   ALT_SPI_TMOD_RX, 
                                   0, 0);
}

//
// This function performs a master SPI EEPROM read transfer.
//
ALT_STATUS_CODE alt_spi_master_eeprom_transfer(ALT_SPI_DEV_t *spi_dev, 
                                               const uint32_t slave_select,
                                               const uint8_t opcode,
                                               const uint16_t eeprom_addr,
                                               const size_t num_frames,
                                               uint16_t * rx_buf)
{
    return alt_spi_master_transfer(spi_dev, 
                                   slave_select, 
                                   num_frames,
                                   NULL, 
                                   rx_buf, 
                                   ALT_SPI_TMOD_EEPROM, 
                                   opcode, 
                                   eeprom_addr);
}

//
// Write or read bulk of data form slave mode
//
static ALT_STATUS_CODE alt_spi_slave_transfer_helper(ALT_SPI_DEV_t *spi_dev, 
                                              size_t data_send,
                                              size_t data_recv,
                                              const uint16_t * tx_buf, 
                                              uint16_t * rx_buf)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    const uint16_t * buffer_tx = tx_buf;
    uint16_t * buffer_rx = rx_buf;
    uint32_t timeout = MAX(data_send, data_recv) * 10000;
    
    while (data_send > 0 || data_recv > 0)
    {
        // Error handling
        ALT_STATUS_CODE err_status = 0;
        status = alt_spi_transmit_error_handler(spi_dev, &err_status);
    
        if (status != ALT_E_SUCCESS)
        {
            break;
        }
    
        if (err_status != ALT_E_SUCCESS)
        {
            status = err_status;
            break;
        }
    
        // Read out the resulting received data as they come in.
        
        if (data_recv > 0)
        {
            uint32_t level = 0;
            status = alt_spi_rx_fifo_level_get(spi_dev, &level);
            if (status != ALT_E_SUCCESS)
            {
                break;
            }
        
            if (level == 0)
            {
                if (--timeout == 0)
                {
                    status = ALT_E_TMO;
                    break;
                }
            }
        
            level = MIN(data_recv, level);
        
            for (uint32_t i = 0; i < level; ++i)
            {
                *buffer_rx = (ALT_SPIS_DR_DR_GET(alt_read_word(ALT_SPIS_DR_ADDR(spi_dev->location))));
                ++buffer_rx;
            }
        
            data_recv -= level;
        }

        // Top up the TX FIFO with sending data
        
        if (data_send > 0)
        {
            uint32_t level = 0;
            status = alt_spi_tx_fifo_level_get(spi_dev, &level);
            if (status != ALT_E_SUCCESS)
            {
                break;
            }
    
            uint32_t space = ALT_SPI_TX_FIFO_NUM_ENTRIES - level;
    
            space = MIN(data_send, space);
    
            for (uint32_t i = 0; i < space; ++i)
            {
                alt_write_word(ALT_SPIS_DR_ADDR(spi_dev->location), ALT_SPIS_DR_DR_SET(*buffer_tx));
                ++buffer_tx;
            }
    
            data_send -= space;
        }
    
    }

    return status;
}
//
// This function performs a slave SPI/SSP serial slave transfer.
//
static ALT_STATUS_CODE alt_spi_slave_transfer(ALT_SPI_DEV_t *spi_dev, 
                                              const uint16_t * tx_buf, 
                                              uint16_t * rx_buf,
                                              const size_t buf_len,
                                              ALT_SPI_TMOD_t transfer_mode)
{
    if (alt_spi_checking(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (spi_dev->op_mode == ALT_SPI_OP_MODE_MASTER)
    {
        return ALT_E_ERROR;
    }
    
    if (buf_len == 0) 
    {
        return ALT_E_SUCCESS;
    }

    if (alt_spi_is_enabled(spi_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }
    
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Clear interrupt status and disable interrupt mask
    alt_spi_int_clear(  spi_dev,ALT_SPI_STATUS_ALL);
    alt_spi_int_disable(spi_dev,ALT_SPI_STATUS_ALL);
    // Enable abort and TXFIFO empty interrupt status
    alt_spi_int_enable( spi_dev,ALT_SPI_STATUS_RXOI | 
                                ALT_SPI_STATUS_RXUI | 
                                ALT_SPI_STATUS_TXOI);

    // This SPI controller requires that a read issue be performed for each byte requested.
    // Read issue takes space in the TX FIFO, which may asynchronously handling a previous request.
    
    uint32_t data_send = 0;
    uint32_t data_recv = 0;
    
    if (transfer_mode == ALT_SPI_TMOD_TX || transfer_mode == ALT_SPI_TMOD_TXRX)
    {
        data_send = buf_len;
    }
    
    if (transfer_mode == ALT_SPI_TMOD_RX || transfer_mode == ALT_SPI_TMOD_TXRX)
    {
        data_recv = buf_len;
    }
    
    // Write or read bulk of data
    status = alt_spi_slave_transfer_helper(spi_dev, 
                                           data_send, 
                                           data_recv,
                                           tx_buf, 
                                           rx_buf);

    // Need reset for set spi bus in idle state
    if(status == ALT_E_TMO)
        alt_spi_reset(spi_dev);

    // Mask all interrupts
    alt_spi_int_disable(spi_dev, ALT_SPI_STATUS_ALL);

    return status;

}

//
// This function performs a slave SPI/SSP serial transmit and receive transfer.
//
ALT_STATUS_CODE alt_spi_slave_tx_rx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                             const uint16_t * tx_buf, 
                                             uint16_t * rx_buf,
                                             const size_t buf_len)
{
    return alt_spi_slave_transfer(spi_dev, 
                                  tx_buf, 
                                  rx_buf, 
                                  buf_len, 
                                  ALT_SPI_TMOD_TXRX);
}

//
// This function performs a slave SPI/SSP serial transmit only transfer.
//
ALT_STATUS_CODE alt_spi_slave_tx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                          const uint16_t * tx_buf,
                                          const size_t buf_len)
{
    alt_spi_int_disable(spi_dev, ALT_SPI_STATUS_RXFI);
    return alt_spi_slave_transfer(spi_dev, 
                                  tx_buf, 
                                  NULL, 
                                  buf_len, 
                                  ALT_SPI_TMOD_TXRX);
}

//
// This function performs a slave SPI/SSP serial receive only transfer.
//
ALT_STATUS_CODE alt_spi_slave_rx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                          uint16_t * rx_buf,
                                          const size_t buf_len)
{
    alt_spi_int_disable(spi_dev, ALT_SPI_STATUS_TXEI);
    return alt_spi_slave_transfer(spi_dev, 
                                  NULL, 
                                  rx_buf, 
                                  buf_len, 
                                  ALT_SPI_TMOD_TXRX);
}

