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

#include "alt_i2c.h"
#include "alt_reset_manager.h"
#include <stdio.h>

/////

// NOTE: To enable debugging output, delete the next line and uncomment the
//   line after.
#define dprintf(...)
// #define dprintf(fmt, ...) printf(fmt, ##__VA_ARGS__)

/////

#define MIN(a, b) ((a) > (b) ? (b) : (a))

/////

// Timeout for reset manager
#define ALT_I2C_RESET_TMO_INIT      8192
// Timeout for disable device
#define ALT_I2C_MAX_T_POLL_COUNT    8192
// Timeout for waiting interrupt
#define ALT_I2C_TMO_WAITER          2500000

// Min frequency during standard speed
#define ALT_I2C_SS_MIN_SPEED        8000
// Max frequency during standard speed
#define ALT_I2C_SS_MAX_SPEED        100000
// Min frequency during fast speed
#define ALT_I2C_FS_MIN_SPEED        100000
// Max frequency during fast speed
#define ALT_I2C_FS_MAX_SPEED        400000
// Default spike suppression limit during standard speed
#define ALT_I2C_SS_DEFAULT_SPKLEN   11
// Default spike suppression limit during fast speed
#define ALT_I2C_FS_DEFAULT_SPKLEN   4

// Diff between SCL LCNT and SCL HCNT
#define ALT_I2C_DIFF_LCNT_HCNT      70

// Reserved address from 0x00 to 0x07
#define ALT_I2C_SLV_RESERVE_ADDR_S_1     0x00
#define ALT_I2C_SLV_RESERVE_ADDR_F_1     0x07
// Reserved address from 0x78 to 0x7F
#define ALT_I2C_SLV_RESERVE_ADDR_S_2     0x78
#define ALT_I2C_SLV_RESERVE_ADDR_F_2     0x7F

static ALT_STATUS_CODE alt_i2c_is_enabled_helper(ALT_I2C_DEV_t * i2c_dev);

//
// Check whether i2c space is correct.
//
static ALT_STATUS_CODE alt_i2c_checking(ALT_I2C_DEV_t * i2c_dev)
{
    if (   (i2c_dev->location != (void *)ALT_I2C_I2C0)
        && (i2c_dev->location != (void *)ALT_I2C_I2C1)
        && (i2c_dev->location != (void *)ALT_I2C_I2C2)
        && (i2c_dev->location != (void *)ALT_I2C_I2C3))
    {
        // Incorrect device
        return ALT_E_FALSE;
    }

    // Reset i2c module
    return ALT_E_TRUE;
}

static ALT_STATUS_CODE alt_i2c_rstmgr_set(ALT_I2C_DEV_t * i2c_dev)
{
    uint32_t rst_mask = ALT_RSTMGR_PERMODRST_I2C0_SET_MSK;

    // Assert the appropriate I2C module reset signal via the Reset Manager Peripheral Reset register.
    switch ((ALT_I2C_CTLR_t)i2c_dev->location)
    {
    case ALT_I2C_I2C0:
        rst_mask = ALT_RSTMGR_PERMODRST_I2C0_SET_MSK;
        break;
    case ALT_I2C_I2C1:
        rst_mask = ALT_RSTMGR_PERMODRST_I2C1_SET_MSK;
        break;
    case ALT_I2C_I2C2:
        rst_mask = ALT_RSTMGR_PERMODRST_I2C2_SET_MSK;
        break;
    case ALT_I2C_I2C3:
        rst_mask = ALT_RSTMGR_PERMODRST_I2C3_SET_MSK;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, rst_mask);

    return ALT_E_SUCCESS;
}

//
// Reset i2c module by reset manager
//
static ALT_STATUS_CODE alt_i2c_rstmgr_strobe(ALT_I2C_DEV_t * i2c_dev)
{
    uint32_t rst_mask = ALT_RSTMGR_PERMODRST_I2C0_SET_MSK;

    // Assert the appropriate I2C module reset signal via the Reset Manager Peripheral Reset register.
    switch ((ALT_I2C_CTLR_t)i2c_dev->location)
    {
    case ALT_I2C_I2C0:
        rst_mask = ALT_RSTMGR_PERMODRST_I2C0_SET_MSK;
        break;
    case ALT_I2C_I2C1:
        rst_mask = ALT_RSTMGR_PERMODRST_I2C1_SET_MSK;
        break;
    case ALT_I2C_I2C2:
        rst_mask = ALT_RSTMGR_PERMODRST_I2C2_SET_MSK;
        break;
    case ALT_I2C_I2C3:
        rst_mask = ALT_RSTMGR_PERMODRST_I2C3_SET_MSK;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, rst_mask);

    volatile uint32_t timeout = ALT_I2C_RESET_TMO_INIT;

    // Wait while i2c modure is reseting
    while (--timeout)
        ;

    // Deassert the appropriate I2C module reset signal via the Reset Manager Peripheral Reset register.
    alt_clrbits_word(ALT_RSTMGR_PERMODRST_ADDR, rst_mask);

    return ALT_E_SUCCESS;
}

//
// Initialize the specified I2C controller instance for use and return a device
// handle referencing it.
//
ALT_STATUS_CODE alt_i2c_init(const ALT_I2C_CTLR_t i2c,
                             ALT_I2C_DEV_t * i2c_dev)
{
    // Save i2c start address to the instance
    i2c_dev->location = (void *)i2c;
    
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_clk_is_enabled(ALT_CLK_L4_SP) != ALT_E_TRUE)
    {
        return ALT_E_BAD_CLK;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_clk_freq_get(ALT_CLK_L4_SP, &i2c_dev->clock_freq);
    }

    // Reset i2c module
    if (status == ALT_E_SUCCESS)
    {
        status = alt_i2c_reset(i2c_dev);
    }

    return status;
}

//
// Reset i2c module
//
ALT_STATUS_CODE alt_i2c_reset(ALT_I2C_DEV_t * i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    bool already_enabled = (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_i2c_disable(i2c_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }
    
    // Reset i2c module by reset manager
    alt_i2c_rstmgr_strobe(i2c_dev);

    // Set optimal parameters for all i2c devices on the bus
    ALT_I2C_MASTER_CONFIG_t cfg;
    cfg.addr_mode      = ALT_I2C_ADDR_MODE_7_BIT;
    cfg.speed_mode     = ALT_I2C_SPEED_STANDARD;
    cfg.fs_spklen      = ALT_I2C_SS_DEFAULT_SPKLEN;
    cfg.restart_enable = ALT_E_TRUE;
    cfg.ss_scl_lcnt    = cfg.fs_scl_lcnt = 0x2FB;
    cfg.ss_scl_hcnt    = cfg.fs_scl_hcnt = 0x341;

    alt_i2c_master_config_set(i2c_dev, &cfg);

    // Active master mode 
    alt_i2c_op_mode_set(i2c_dev, ALT_I2C_MODE_MASTER);

    // Reset the last target address cache.
    i2c_dev->last_target = 0xffffffff;

    // Clear interrupts mask and clear interrupt status.
    // Interrupts are unmasked by default.
    alt_i2c_int_disable(i2c_dev, ALT_I2C_STATUS_INT_ALL);
    alt_i2c_int_clear(i2c_dev, ALT_I2C_STATUS_INT_ALL);

    if (already_enabled)
    {
        // Re-enable controller
        status = alt_i2c_enable(i2c_dev);
    }

    return status;
}

//
// Uninitialize the I2C controller referenced by the i2c_dev handle.
//
ALT_STATUS_CODE alt_i2c_uninit(ALT_I2C_DEV_t * i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Disable i2c controller
    if (status == ALT_E_SUCCESS)
    {
        status = alt_i2c_disable(i2c_dev);
    }

    // Reset i2c module by reset manager
    if (status == ALT_E_SUCCESS)
    {
        status = alt_i2c_rstmgr_set(i2c_dev);
    }

    return status;
}

//
// Enables the I2C controller.
//
ALT_STATUS_CODE alt_i2c_enable(ALT_I2C_DEV_t * i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    // Enable DMA by default.
    alt_write_word(ALT_I2C_DMA_CR_ADDR(i2c_dev->location), 
                   ALT_I2C_DMA_CR_TDMAE_SET_MSK | ALT_I2C_DMA_CR_RDMAE_SET_MSK);

    alt_setbits_word(ALT_I2C_EN_ADDR(i2c_dev->location), ALT_I2C_EN_EN_SET_MSK);

    return ALT_E_SUCCESS;
}

//
// Disables the I2C controller
//
ALT_STATUS_CODE alt_i2c_disable(ALT_I2C_DEV_t * i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    // If i2c controller is enabled, return with sucess
    if (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_SUCCESS;
    }

    // Else clear enable bit of i2c_enable register
    alt_clrbits_word(ALT_I2C_EN_ADDR(i2c_dev->location), ALT_I2C_EN_EN_SET_MSK);
    
    uint32_t timeout = ALT_I2C_MAX_T_POLL_COUNT;

    // Wait to complete all transfer operations or timeout
    while (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_TRUE)
    {
        // If controller still are active, return timeout error
        if (--timeout == 0)
        {
            return ALT_E_TMO;
        }
    }

    // Clear interrupt status
    alt_i2c_int_clear(i2c_dev, ALT_I2C_STATUS_INT_ALL);

    return ALT_E_SUCCESS;
}

//
// Check whether i2c controller is enable
//
static ALT_STATUS_CODE alt_i2c_is_enabled_helper(ALT_I2C_DEV_t * i2c_dev)
{
    if (ALT_I2C_EN_STAT_IC_EN_GET(alt_read_word(ALT_I2C_EN_STAT_ADDR(i2c_dev->location))))
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

ALT_STATUS_CODE alt_i2c_is_enabled(ALT_I2C_DEV_t * i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    return alt_i2c_is_enabled_helper(i2c_dev);
}

//
// Get config parameters from appropriate registers for master mode.
//
ALT_STATUS_CODE alt_i2c_master_config_get(ALT_I2C_DEV_t *i2c_dev,
                                          ALT_I2C_MASTER_CONFIG_t* cfg)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t cfg_register  = alt_read_word(ALT_I2C_CON_ADDR(i2c_dev->location));
    uint32_t tar_register  = alt_read_word(ALT_I2C_TAR_ADDR(i2c_dev->location));
    uint32_t spkl_register = alt_read_word(ALT_I2C_FS_SPKLEN_ADDR(i2c_dev->location));

    cfg->speed_mode     = (ALT_I2C_SPEED_t)ALT_I2C_CON_SPEED_GET(cfg_register);
    cfg->fs_spklen      = ALT_I2C_FS_SPKLEN_SPKLEN_GET(spkl_register);
    cfg->restart_enable = ALT_I2C_CON_IC_RESTART_EN_GET(cfg_register);
    cfg->addr_mode      = (ALT_I2C_ADDR_MODE_t)ALT_I2C_TAR_IC_10BITADDR_MST_GET(tar_register);

    cfg->ss_scl_lcnt = alt_read_word(ALT_I2C_SS_SCL_LCNT_ADDR(i2c_dev->location));
    cfg->ss_scl_hcnt = alt_read_word(ALT_I2C_SS_SCL_HCNT_ADDR(i2c_dev->location));
    cfg->fs_scl_lcnt = alt_read_word(ALT_I2C_FS_SCL_LCNT_ADDR(i2c_dev->location));
    cfg->fs_scl_hcnt = alt_read_word(ALT_I2C_FS_SCL_HCNT_ADDR(i2c_dev->location));

    return ALT_E_SUCCESS;
}

//
// Set config parameters to appropriate registers for master mode.
//
ALT_STATUS_CODE alt_i2c_master_config_set(ALT_I2C_DEV_t *i2c_dev,
                                          const ALT_I2C_MASTER_CONFIG_t* cfg)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (   (cfg->speed_mode != ALT_I2C_SPEED_STANDARD)
        && (cfg->speed_mode != ALT_I2C_SPEED_FAST))
    {
        return ALT_E_BAD_ARG;
    }

    if (   (cfg->addr_mode != ALT_I2C_ADDR_MODE_7_BIT)
        && (cfg->addr_mode != ALT_I2C_ADDR_MODE_10_BIT))
    {
        return ALT_E_ARG_RANGE;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    bool already_enabled = (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_i2c_disable(i2c_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }

    // Set config parameters to appropriate registers

    alt_replbits_word(ALT_I2C_CON_ADDR(i2c_dev->location),
                      ALT_I2C_CON_SPEED_SET_MSK | ALT_I2C_CON_IC_RESTART_EN_SET_MSK,
                      ALT_I2C_CON_SPEED_SET(cfg->speed_mode) | ALT_I2C_CON_IC_RESTART_EN_SET(cfg->restart_enable));
    
    alt_replbits_word(ALT_I2C_TAR_ADDR(i2c_dev->location),
                      ALT_I2C_TAR_IC_10BITADDR_MST_SET_MSK, 
                      ALT_I2C_TAR_IC_10BITADDR_MST_SET(cfg->addr_mode));

    alt_replbits_word(ALT_I2C_FS_SPKLEN_ADDR(i2c_dev->location),
                      ALT_I2C_FS_SPKLEN_SPKLEN_SET_MSK,
                      ALT_I2C_FS_SPKLEN_SPKLEN_SET(cfg->fs_spklen));
    
    alt_replbits_word(ALT_I2C_SS_SCL_LCNT_ADDR(i2c_dev->location),
                      ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT_SET_MSK,
                      ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT_SET(cfg->ss_scl_lcnt));
    alt_replbits_word(ALT_I2C_SS_SCL_HCNT_ADDR(i2c_dev->location),
                      ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT_SET_MSK,
                      ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT_SET(cfg->ss_scl_hcnt));
    alt_replbits_word(ALT_I2C_FS_SCL_LCNT_ADDR(i2c_dev->location),
                      ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT_SET_MSK,
                      ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT_SET(cfg->fs_scl_lcnt));
    alt_replbits_word(ALT_I2C_FS_SCL_HCNT_ADDR(i2c_dev->location),
                      ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT_SET_MSK,
                      ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT_SET(cfg->fs_scl_hcnt));

    if (already_enabled)
    {
        // Re-enable controller
        status = alt_i2c_enable(i2c_dev);
    }

    return status;
}

//
// Return bus speed by configuration of i2c controller for master mode.
//
ALT_STATUS_CODE alt_i2c_master_config_speed_get(ALT_I2C_DEV_t *i2c_dev,
                                                const ALT_I2C_MASTER_CONFIG_t * cfg,
                                                uint32_t * speed_in_hz)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t scl_lcnt = (cfg->speed_mode == ALT_I2C_SPEED_STANDARD) ? cfg->ss_scl_lcnt : cfg->fs_scl_lcnt;

    if (scl_lcnt == 0)
    {
        return ALT_E_BAD_ARG;
    }
    
    *speed_in_hz = i2c_dev->clock_freq / (scl_lcnt << 1);

    return ALT_E_SUCCESS;
}

//
// Fill struct with configuration of i2c controller for master mode by bus speed
//
ALT_STATUS_CODE alt_i2c_master_config_speed_set(ALT_I2C_DEV_t *i2c_dev,
                                                ALT_I2C_MASTER_CONFIG_t * cfg,
                                                uint32_t speed_in_hz)    
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    // If speed is not standard or fast return range error
    if ((speed_in_hz > ALT_I2C_FS_MAX_SPEED) || (speed_in_hz < ALT_I2C_SS_MIN_SPEED))
    {
        return ALT_E_ARG_RANGE;
    }
    
    if (speed_in_hz > ALT_I2C_FS_MIN_SPEED)
    {
        cfg->speed_mode = ALT_I2C_SPEED_FAST;
        cfg->fs_spklen  = ALT_I2C_FS_DEFAULT_SPKLEN;
    }
    else
    {
        cfg->speed_mode = ALT_I2C_SPEED_STANDARD;
        cfg->fs_spklen  = ALT_I2C_SS_DEFAULT_SPKLEN;
    }

    // <lcount> = <internal clock> / 2 * <speed, Hz>
    uint32_t scl_lcnt = i2c_dev->clock_freq / (speed_in_hz << 1);

    cfg->ss_scl_lcnt = cfg->fs_scl_lcnt = scl_lcnt;
    // hcount = <lcount> + 70
    cfg->ss_scl_hcnt = cfg->fs_scl_hcnt = scl_lcnt - ALT_I2C_DIFF_LCNT_HCNT;

    // lcount = <internal clock> / 2 * <speed, Hz>

    return ALT_E_SUCCESS;
}

//
// Get config parameters from appropriate registers for slave mode.
//
ALT_STATUS_CODE alt_i2c_slave_config_get(ALT_I2C_DEV_t *i2c_dev,
                                         ALT_I2C_SLAVE_CONFIG_t* cfg)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t cfg_register  = alt_read_word(ALT_I2C_CON_ADDR(i2c_dev->location));
    uint32_t sar_register  = alt_read_word(ALT_I2C_SAR_ADDR(i2c_dev->location));
    uint32_t nack_register = alt_read_word(ALT_I2C_SLV_DATA_NACK_ONLY_ADDR(i2c_dev->location));

    cfg->addr_mode   = (ALT_I2C_ADDR_MODE_t)ALT_I2C_CON_IC_10BITADDR_SLV_GET(cfg_register);
    cfg->addr        = ALT_I2C_SAR_IC_SAR_GET(sar_register);
    cfg->nack_enable = ALT_I2C_SLV_DATA_NACK_ONLY_NACK_GET(nack_register);

    return ALT_E_SUCCESS;
}

//
// Set config parameters to appropriate registers for slave mode.
//
ALT_STATUS_CODE alt_i2c_slave_config_set(ALT_I2C_DEV_t *i2c_dev,
                                         const ALT_I2C_SLAVE_CONFIG_t* cfg)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (   (cfg->addr_mode != ALT_I2C_ADDR_MODE_7_BIT)
        && (cfg->addr_mode != ALT_I2C_ADDR_MODE_10_BIT))
    {
        return ALT_E_BAD_ARG;
    }

    if (   (cfg->addr > ALT_I2C_SAR_IC_SAR_SET_MSK)
        || (cfg->addr < ALT_I2C_SLV_RESERVE_ADDR_F_1)
        || ((cfg->addr > ALT_I2C_SLV_RESERVE_ADDR_S_2) && (cfg->addr < ALT_I2C_SLV_RESERVE_ADDR_F_2))
       )
    {
        return ALT_E_ARG_RANGE;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    bool already_enabled = (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_i2c_disable(i2c_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }

    alt_replbits_word(ALT_I2C_CON_ADDR(i2c_dev->location),
                      ALT_I2C_CON_IC_10BITADDR_SLV_SET_MSK,
                      ALT_I2C_CON_IC_10BITADDR_SLV_SET(cfg->addr_mode));

    alt_replbits_word(ALT_I2C_SAR_ADDR(i2c_dev->location),
                      ALT_I2C_SAR_IC_SAR_SET_MSK,
                      ALT_I2C_SAR_IC_SAR_SET(cfg->addr));
    alt_replbits_word(ALT_I2C_SLV_DATA_NACK_ONLY_ADDR(i2c_dev->location),
                      ALT_I2C_SLV_DATA_NACK_ONLY_NACK_SET_MSK,
                      ALT_I2C_SLV_DATA_NACK_ONLY_NACK_SET(cfg->nack_enable));

    if (already_enabled)
    {
        // Re-enable controller
        status = alt_i2c_enable(i2c_dev);
    }

    return status;
}

//
// Get hold time (use during slave mode)
//
ALT_STATUS_CODE alt_i2c_sda_hold_time_get(ALT_I2C_DEV_t *i2c_dev, 
                                          uint16_t *hold_time)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t sda_register = alt_read_word(ALT_I2C_SDA_HOLD_ADDR(i2c_dev->location));
    *hold_time = ALT_I2C_SDA_HOLD_IC_SDA_HOLD_GET(sda_register);

    return ALT_E_SUCCESS;
}
    
//
// Set hold time (use during slave mode)
//
ALT_STATUS_CODE alt_i2c_sda_hold_time_set(ALT_I2C_DEV_t *i2c_dev, 
                                          const uint16_t hold_time)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    bool already_enabled = (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_i2c_disable(i2c_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }

    alt_replbits_word(ALT_I2C_SDA_HOLD_ADDR(i2c_dev->location),
                      ALT_I2C_SDA_HOLD_IC_SDA_HOLD_SET_MSK,
                      ALT_I2C_SDA_HOLD_IC_SDA_HOLD_SET(hold_time));

    if (already_enabled)
    {
        // Re-enable controller
        status = alt_i2c_enable(i2c_dev);
    }

    return status;
}
    
//
// Gets the current operational mode of the I2C controller.
//
ALT_STATUS_CODE alt_i2c_op_mode_get(ALT_I2C_DEV_t *i2c_dev,
                                    ALT_I2C_MODE_t* mode)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }
    
    uint32_t cfg_register = alt_read_word(ALT_I2C_CON_ADDR(i2c_dev->location));
    uint32_t mst_mod_stat = ALT_I2C_CON_MST_MOD_GET(cfg_register);
    uint32_t slv_mod_stat = ALT_I2C_CON_IC_SLV_DIS_GET(cfg_register);

    // Return error if master and slave modes enable or disable at the same time
    if (   (mst_mod_stat == ALT_I2C_CON_MST_MOD_E_EN  && slv_mod_stat == ALT_I2C_CON_IC_SLV_DIS_E_EN) 
        || (mst_mod_stat == ALT_I2C_CON_MST_MOD_E_DIS && slv_mod_stat == ALT_I2C_CON_IC_SLV_DIS_E_DIS))
    {
        return ALT_E_ERROR;
    }

    *mode = (ALT_I2C_MODE_t)mst_mod_stat;

    return ALT_E_SUCCESS;
}
    
//
// Sets the operational mode of the I2C controller.
//
ALT_STATUS_CODE alt_i2c_op_mode_set(ALT_I2C_DEV_t *i2c_dev,
                                    const ALT_I2C_MODE_t mode)    
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (   (mode != ALT_I2C_MODE_MASTER)
        && (mode != ALT_I2C_MODE_SLAVE))
    {
        return ALT_E_ARG_RANGE;
    }
    
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    bool already_enabled = (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_i2c_disable(i2c_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }

    if (mode == ALT_I2C_MODE_MASTER)
    {
        // Enable master, disable slave
        alt_replbits_word(ALT_I2C_CON_ADDR(i2c_dev->location),
                          ALT_I2C_CON_IC_SLV_DIS_SET_MSK | ALT_I2C_CON_MST_MOD_SET_MSK,
                          ALT_I2C_CON_IC_SLV_DIS_SET(ALT_I2C_CON_IC_SLV_DIS_E_DIS) | ALT_I2C_CON_MST_MOD_SET(ALT_I2C_CON_MST_MOD_E_EN));
    }
    else if (mode == ALT_I2C_MODE_SLAVE)
    {
        // Enable slave, disable master
        alt_replbits_word(ALT_I2C_CON_ADDR(i2c_dev->location),
                          ALT_I2C_CON_IC_SLV_DIS_SET_MSK | ALT_I2C_CON_MST_MOD_SET_MSK,
                          ALT_I2C_CON_IC_SLV_DIS_SET(ALT_I2C_CON_IC_SLV_DIS_E_EN) | ALT_I2C_CON_MST_MOD_SET(ALT_I2C_CON_MST_MOD_E_DIS));
    }
        
    if (already_enabled)
    {
        // Re-enable controller
        status = alt_i2c_enable(i2c_dev);
    }
    
    return status;
}
    
//
// Returns ALT_E_TRUE if the I2C controller is busy
//
ALT_STATUS_CODE alt_i2c_is_busy(ALT_I2C_DEV_t *i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }
    
    if ( ALT_I2C_STAT_ACTIVITY_GET(alt_read_word(ALT_I2C_STAT_ADDR(i2c_dev->location))))
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

//
// This function reads a single data byte from the receive FIFO.
//
ALT_STATUS_CODE alt_i2c_read(ALT_I2C_DEV_t *i2c_dev, uint8_t *value)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    *value = (uint8_t)(ALT_I2C_DATA_CMD_DAT_GET(alt_read_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location))));

    return ALT_E_SUCCESS;
}

//
// This function writes a single data byte to the transmit FIFO.
//
ALT_STATUS_CODE alt_i2c_write(ALT_I2C_DEV_t *i2c_dev, const uint8_t value)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    alt_write_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location),
                   ALT_I2C_DATA_CMD_DAT_SET(value));

    return ALT_E_SUCCESS;
}

//
// This function acts in the role of a slave-receiver by receiving a single data
// byte from the I2C bus in response to a write command from the master.
//
ALT_STATUS_CODE alt_i2c_slave_receive(ALT_I2C_DEV_t * i2c_dev,
                                      uint8_t * data)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    // alt_i2c_read().
    *data = (uint8_t)(ALT_I2C_DATA_CMD_DAT_GET(alt_read_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location))));

    return ALT_E_SUCCESS;
}

//
// This function acts in the role of a slave-transmitter by transmitting a single
// data byte to the I2C bus in response to a read request from the master.
//
ALT_STATUS_CODE alt_i2c_slave_transmit(ALT_I2C_DEV_t *i2c_dev,
                                       const uint8_t data)
{
    // Send bulk of data with one value
    return alt_i2c_slave_bulk_transmit(i2c_dev, &data, 1);
}

//
// This function acts in the role of a slave-transmitter by transmitting data in
// bulk to the I2C bus in response to a series of read requests from a master.
//
ALT_STATUS_CODE alt_i2c_slave_bulk_transmit(ALT_I2C_DEV_t *i2c_dev,
                                            const void * data,
                                            const size_t size)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    const char * buffer = data;
    for (size_t i = 0; i < size; ++i)
    {
        alt_write_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location),
                         ALT_I2C_DATA_CMD_DAT_SET(*buffer)
                       | ALT_I2C_DATA_CMD_STOP_SET(false)
                       | ALT_I2C_DATA_CMD_RESTART_SET(false));

        ++buffer;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_i2c_master_target_get(ALT_I2C_DEV_t * i2c_dev, uint32_t * target_addr)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    *target_addr = i2c_dev->last_target;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_i2c_master_target_set(ALT_I2C_DEV_t * i2c_dev, uint32_t target_addr)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Wait until the TX FIFO flushes. This is needed because TAR can only be
    // updated under specific conditions.

    if (target_addr != i2c_dev->last_target)
    {
        uint32_t timeout = 10000;

        while (alt_i2c_tx_fifo_is_empty(i2c_dev) == ALT_E_FALSE)
        {
            if (--timeout == 0)
            {
                status = ALT_E_TMO;
                break;
            }
        }

        // Update target address
        if (status == ALT_E_SUCCESS)
        {
            alt_replbits_word(ALT_I2C_TAR_ADDR(i2c_dev->location),
                              ALT_I2C_TAR_IC_TAR_SET_MSK,
                              ALT_I2C_TAR_IC_TAR_SET(target_addr));

            i2c_dev->last_target = target_addr;
        }
    }

    return status;
}

//
// Write bulk of data or read requests to tx fifo
//
static ALT_STATUS_CODE alt_i2c_master_transmit_helper(ALT_I2C_DEV_t * i2c_dev,
                                                      const uint8_t * buffer,
                                                      size_t size,
                                                      bool issue_restart,
                                                      bool issue_stop)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // If the rested size is 1, the restart and stop may need to be sent in the
    // same frame.
    if (size == 1)
    {
        if (status == ALT_E_SUCCESS)
        {
            status = alt_i2c_issue_write(i2c_dev,
                                         *buffer,
                                         issue_restart,
                                         issue_stop);

            ++buffer;
            --size;
        }
    }
    else
    {
        // First byte

        if (status == ALT_E_SUCCESS)
        {
            status = alt_i2c_issue_write(i2c_dev,
                                         *buffer,
                                         issue_restart,
                                         false);

            ++buffer;
            --size;
        }

        /////
            
        // Middle byte(s)

        if (status == ALT_E_SUCCESS)
        {
            uint32_t timeout = size * 10000;

            while (size > 1)
            {
                uint32_t level = 0;
                status = alt_i2c_tx_fifo_level_get(i2c_dev, &level);
                if (status != ALT_E_SUCCESS)
                {
                    break;
                }

                uint32_t space = ALT_I2C_TX_FIFO_NUM_ENTRIES - level;
                if (space == 0)
                {
                    if (--timeout == 0)
                    {
                        status = ALT_E_TMO;
                        break;
                    }

                    continue;
                }
                
                // Subtract 1 because the last byte may need to issue_stop
                space = MIN(space, size - 1);

                for (uint32_t i = 0; i < space; ++i)
                {
                    alt_write_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location),
                                     ALT_I2C_DATA_CMD_DAT_SET(*buffer)
                                   | ALT_I2C_DATA_CMD_STOP_SET(false)
                                   | ALT_I2C_DATA_CMD_RESTART_SET(false));

                    ++buffer;
                }

                size -= space;
            }
        }

        /////

        // Last byte

        if (status == ALT_E_SUCCESS)
        {
            status = alt_i2c_issue_write(i2c_dev,
                                         *buffer,
                                         false,
                                         issue_stop);

            ++buffer;
            --size;
        }
    }

    return status;
}

//
// This function acts in the role of a master-transmitter by issuing a write
// command and transmitting data to the I2C bus.
//
ALT_STATUS_CODE alt_i2c_master_transmit(ALT_I2C_DEV_t *i2c_dev,
                                        const void * data,
                                        const size_t size,
                                        const bool issue_restart,
                                        const bool issue_stop)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    if (size == 0)
    {
        return ALT_E_SUCCESS;
    }
    
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_i2c_master_transmit_helper(i2c_dev,
                                                data,
                                                size,
                                                issue_restart,
                                                issue_stop);
    }

    // Need reset for set i2c bus in idle state
    if (status == ALT_E_TMO)
    {
        alt_i2c_reset(i2c_dev);
    }

    return status;
}

ALT_STATUS_CODE alt_i2c_master_receive_helper(ALT_I2C_DEV_t *i2c_dev,
                                              uint8_t * buffer,
                                              size_t size,
                                              bool issue_restart,
                                              bool issue_stop)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t issue_left = size;
    uint32_t data_left  = size;

    uint32_t timeout = size * 10000;

    // Wait for space in the TX FIFO to send the first read request.
    // This is needed because the issue restart need to be set.

    if (issue_restart == true)
    {
        if (status == ALT_E_SUCCESS)
        {
            while (alt_i2c_tx_fifo_is_full(i2c_dev) == ALT_E_TRUE)
            {
                if (--timeout == 0)
                {
                    status = ALT_E_TMO;
                    break;
                }
            }
        }

        // Now send the first request.

        if (status == ALT_E_SUCCESS)
        {
            alt_write_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location),
                             ALT_I2C_DATA_CMD_CMD_SET(ALT_I2C_DATA_CMD_CMD_E_RD)
                           | ALT_I2C_DATA_CMD_STOP_SET(false)
                           | ALT_I2C_DATA_CMD_RESTART_SET(issue_restart));

            --issue_left;
        }
    }

    // For the rest of the data ...

    while (data_left > 0)
    {
        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        // Top up the TX FIFO with read issues
        // Special consideration must be made for the last read issue, as it may be necessary to "issue_stop".

        if (issue_left > 0)
        {
            uint32_t level = 0;
            status = alt_i2c_tx_fifo_level_get(i2c_dev, &level);
            if (status != ALT_E_SUCCESS)
            {
                break;
            }

            uint32_t space = ALT_I2C_TX_FIFO_NUM_ENTRIES - level;

            if (issue_left == 1)
            {
                if (space > 0)
                {
                    space = 1;

                    alt_write_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location),
                                   ALT_I2C_DATA_CMD_CMD_SET(ALT_I2C_DATA_CMD_CMD_E_RD)
                                   | ALT_I2C_DATA_CMD_STOP_SET(issue_stop)
                                   | ALT_I2C_DATA_CMD_RESTART_SET(false));
                }
            }
            else
            {
                // Send up to issue_left - 1, as the last issue has special considerations.
                space = MIN(issue_left - 1, space);

                for (uint32_t i = 0; i < space; ++i)
                {
                    alt_write_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location),
                                   ALT_I2C_DATA_CMD_CMD_SET(ALT_I2C_DATA_CMD_CMD_E_RD)
                                   | ALT_I2C_DATA_CMD_STOP_SET(false)
                                   | ALT_I2C_DATA_CMD_RESTART_SET(false));
                }
            }

            issue_left -= space;
        }

        // Read out the resulting received data as they come in.

        if (data_left > 0)
        {
            uint32_t level = 0;
            status = alt_i2c_rx_fifo_level_get(i2c_dev, &level);
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

            level = MIN(data_left, level);

            for (uint32_t i = 0; i < level; ++i)
            {
                // alt_i2c_read(i2c_dev, &value);
                *buffer = (uint8_t)(ALT_I2C_DATA_CMD_DAT_GET(alt_read_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location))));
                ++buffer;
            }

            data_left -= level;
        }
    }


    return status;
}

//
// This function acts in the role of a master-receiver by receiving one or more
// data bytes transmitted from a slave in response to read requests issued from
// this master.
//
ALT_STATUS_CODE alt_i2c_master_receive(ALT_I2C_DEV_t *i2c_dev, 
                                       void * data,
                                       const size_t size,
                                       const bool issue_restart,
                                       const bool issue_stop)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    if (size == 0)
    {
        return ALT_E_SUCCESS;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // This I2C controller requires that a read issue be performed for each byte requested.
    // Read issue takes space in the TX FIFO, which may asynchronously handling a previous request.

    if (size == 1)
    {
        uint32_t timeout = 10000;

        // Wait for space in the TX FIFO to send the read request.

        if (status == ALT_E_SUCCESS)
        {
            while (alt_i2c_tx_fifo_is_full(i2c_dev) == ALT_E_TRUE)
            {
                if (--timeout == 0)
                {
                    status = ALT_E_TMO;
                    break;
                }
            }
        }

        // Issue the read request in the TX FIFO.

        if (status == ALT_E_SUCCESS)
        {
            alt_write_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location),
                             ALT_I2C_DATA_CMD_CMD_SET(ALT_I2C_DATA_CMD_CMD_E_RD)
                           | ALT_I2C_DATA_CMD_STOP_SET(issue_stop)
                           | ALT_I2C_DATA_CMD_RESTART_SET(issue_restart));

        }

        // Wait for data to become available in the RX FIFO.

        if (status == ALT_E_SUCCESS)
        {
            while (alt_i2c_rx_fifo_is_empty(i2c_dev) == ALT_E_TRUE)
            {
                if (--timeout == 0)
                {
                    status = ALT_E_TMO;
                    break;
                }
            }
        }

        // Read the RX FIFO.

        if (status == ALT_E_SUCCESS)
        {
            uint8_t * buffer = data;
            *buffer = (uint8_t)(ALT_I2C_DATA_CMD_DAT_GET(alt_read_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location))));
        }
    }
    else if (size <= 64)
    {
        if (status == ALT_E_SUCCESS)
        {
            status = alt_i2c_master_receive_helper(i2c_dev,
                                                   data,
                                                   size,
                                                   issue_restart,
                                                   issue_stop);
        }
    }
    else
    {
        uint8_t * buffer = data;
        size_t size_left = size;

        // Send the first ALT_I2C_RX_FIFO_NUM_ENTRIES items

        if (status == ALT_E_SUCCESS)
        {
            status = alt_i2c_master_receive_helper(i2c_dev,
                                                   buffer,
                                                   ALT_I2C_RX_FIFO_NUM_ENTRIES,
                                                   issue_restart,
                                                   false);
        }

        buffer    += ALT_I2C_RX_FIFO_NUM_ENTRIES;
        size_left -= ALT_I2C_RX_FIFO_NUM_ENTRIES;

        while (size_left > 0)
        {
            if (size_left > ALT_I2C_RX_FIFO_NUM_ENTRIES)
            {
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_i2c_master_receive_helper(i2c_dev,
                                                           buffer,
                                                           ALT_I2C_RX_FIFO_NUM_ENTRIES,
                                                           false,
                                                           false);
                }

                buffer    += ALT_I2C_RX_FIFO_NUM_ENTRIES;
                size_left -= ALT_I2C_RX_FIFO_NUM_ENTRIES;
            }
            else
            {
                if (status == ALT_E_SUCCESS)
                {
                    status = alt_i2c_master_receive_helper(i2c_dev,
                                                           buffer,
                                                           size_left,
                                                           false,
                                                           issue_stop);
                }

                size_left = 0;
            }

            if (status != ALT_E_SUCCESS)
            {
                break;
            }
        }
    }

    // Need reset for set i2c bus in idle state
    if (status == ALT_E_TMO)
    {
        alt_i2c_reset(i2c_dev);
    }

    return status;
}

//
// This function causes the I2C controller master to send data to the bus.
//
ALT_STATUS_CODE alt_i2c_issue_write(ALT_I2C_DEV_t *i2c_dev,
                                    const uint8_t value,
                                    const bool issue_restart,
                                    const bool issue_stop)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    // Wait until there is a FIFO spot
    uint32_t timeout = 10000;

    while (alt_i2c_tx_fifo_is_full(i2c_dev) == ALT_E_TRUE)
    {
        if (--timeout == 0)
        {
            return ALT_E_TMO;
        }
    }

    alt_write_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location),
                     ALT_I2C_DATA_CMD_DAT_SET(value)
                   | ALT_I2C_DATA_CMD_STOP_SET(issue_stop)
                   | ALT_I2C_DATA_CMD_RESTART_SET(issue_restart));

    return ALT_E_SUCCESS;
}

//
// This function causes the I2C controller master to issue a READ request on the bus.
//
ALT_STATUS_CODE alt_i2c_issue_read(ALT_I2C_DEV_t *i2c_dev,
                                   const bool issue_restart,
                                   const bool issue_stop)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    // Wait until there is a FIFO spot
    uint32_t timeout = 10000;

    while (alt_i2c_tx_fifo_is_full(i2c_dev) == ALT_E_TRUE)
    {
        if (--timeout == 0)
        {
            return ALT_E_TMO;
        }
    }

    alt_write_word(ALT_I2C_DATA_CMD_ADDR(i2c_dev->location),
                     ALT_I2C_DATA_CMD_CMD_SET(ALT_I2C_DATA_CMD_CMD_E_RD)
                   | ALT_I2C_DATA_CMD_STOP_SET(issue_stop)
                   | ALT_I2C_DATA_CMD_RESTART_SET(issue_restart));

    return ALT_E_SUCCESS;
}

//
// This function acts in the role of a master-transmitter by issuing a general
// call command to all devices connected to the I2C bus.
//
ALT_STATUS_CODE alt_i2c_master_general_call(ALT_I2C_DEV_t *i2c_dev,
                                            const void * data,
                                            const size_t size,
                                            const bool issue_restart,
                                            const bool issue_stop)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_ERROR;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_i2c_master_target_set(i2c_dev, 0);
    }

    // General call is a transmit in master mode (target address are not used during it)
    if (status == ALT_E_SUCCESS)
    {
        status = alt_i2c_master_transmit(i2c_dev, data, size, issue_restart, issue_stop);
    }

    return status;
}

/////

ALT_STATUS_CODE alt_i2c_general_call_ack_disable(ALT_I2C_DEV_t *i2c_dev)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    bool already_enabled = (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_i2c_disable(i2c_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }

    alt_replbits_word(ALT_I2C_TAR_ADDR(i2c_dev->location),
                      ALT_I2C_TAR_SPECIAL_SET_MSK | ALT_I2C_TAR_GC_OR_START_SET_MSK,
                      ALT_I2C_TAR_SPECIAL_SET(ALT_I2C_TAR_SPECIAL_E_STARTBYTE) | ALT_I2C_TAR_GC_OR_START_SET(ALT_I2C_TAR_GC_OR_START_E_STARTBYTE));

    if (already_enabled)
    {
        // Re-enable controller
        status = alt_i2c_enable(i2c_dev);
    }

    return status;
}

//
// Enables the I2C controller to respond with an ACK when it receives a General
// Call address.
//
ALT_STATUS_CODE alt_i2c_general_call_ack_enable(ALT_I2C_DEV_t *i2c_dev)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    bool already_enabled = (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_i2c_disable(i2c_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }

    alt_replbits_word(ALT_I2C_TAR_ADDR(i2c_dev->location),
                      ALT_I2C_TAR_SPECIAL_SET_MSK | ALT_I2C_TAR_GC_OR_START_SET_MSK,
                      ALT_I2C_TAR_SPECIAL_SET(ALT_I2C_TAR_SPECIAL_E_GENCALL) | ALT_I2C_TAR_GC_OR_START_SET(ALT_I2C_TAR_GC_OR_START_E_GENCALL));

    if (already_enabled)
    {
        // Re-enable controller
        status = alt_i2c_enable(i2c_dev);
    }

    return status;
}

//
// Returns ALT_E_TRUE if the I2C controller is enabled to respond to General Call
// addresses.
//
ALT_STATUS_CODE alt_i2c_general_call_ack_is_enabled(ALT_I2C_DEV_t *i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t tar_register = alt_read_word(ALT_I2C_TAR_ADDR(i2c_dev->location));
    
    if (   (ALT_I2C_TAR_SPECIAL_GET(tar_register)     == ALT_I2C_TAR_SPECIAL_E_GENCALL)
        && (ALT_I2C_TAR_GC_OR_START_GET(tar_register) == ALT_I2C_TAR_GC_OR_START_E_GENCALL)
       )
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

//
// Returns the current I2C controller interrupt status conditions.
//
ALT_STATUS_CODE alt_i2c_int_status_get(ALT_I2C_DEV_t *i2c_dev,
                                       uint32_t *status)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    *status = alt_read_word(ALT_I2C_INTR_STAT_ADDR(i2c_dev->location));

    return ALT_E_SUCCESS;
}

//
// Returns the I2C controller raw interrupt status conditions irrespective of
// the interrupt status condition enablement state.
//
ALT_STATUS_CODE alt_i2c_int_raw_status_get(ALT_I2C_DEV_t *i2c_dev,
                                           uint32_t *status)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    *status = alt_read_word(ALT_I2C_RAW_INTR_STAT_ADDR(i2c_dev->location));

    return ALT_E_SUCCESS;
}

//
// Clears the specified I2C controller interrupt status conditions identified
// in the mask.
//
ALT_STATUS_CODE alt_i2c_int_clear(ALT_I2C_DEV_t *i2c_dev, const uint32_t mask)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (mask == ALT_I2C_STATUS_INT_ALL)
    {
        alt_read_word(ALT_I2C_CLR_INTR_ADDR(i2c_dev->location));
        return ALT_E_SUCCESS;
    }
    
    // For different status clear different register

    if (mask & ALT_I2C_STATUS_RX_UNDER)
    {
        alt_read_word(ALT_I2C_CLR_RX_UNDER_ADDR(i2c_dev->location));
    }
    if (mask & ALT_I2C_STATUS_RX_OVER)
    {
        alt_read_word(ALT_I2C_CLR_RX_OVER_ADDR(i2c_dev->location));
    }
    if (mask & ALT_I2C_STATUS_TX_OVER)
    {
        alt_read_word(ALT_I2C_CLR_TX_OVER_ADDR(i2c_dev->location));
    }
    if (mask & ALT_I2C_STATUS_RD_REQ)
    {
        alt_read_word(ALT_I2C_CLR_RD_REQ_ADDR(i2c_dev->location));
    }
    if (mask & ALT_I2C_STATUS_TX_ABORT)
    {
        alt_read_word(ALT_I2C_CLR_TX_ABRT_ADDR(i2c_dev->location));
    }
    if (mask & ALT_I2C_STATUS_RX_DONE)
    {
        alt_read_word(ALT_I2C_CLR_RX_DONE_ADDR(i2c_dev->location));
    }
    if (mask & ALT_I2C_STATUS_ACTIVITY)
    {
        alt_read_word(ALT_I2C_CLR_ACTIVITY_ADDR(i2c_dev->location));
    }
    if (mask & ALT_I2C_STATUS_STOP_DET)
    {
        alt_read_word(ALT_I2C_CLR_STOP_DET_ADDR(i2c_dev->location));
    }
    if (mask & ALT_I2C_STATUS_START_DET)
    {
        alt_read_word(ALT_I2C_CLR_START_DET_ADDR(i2c_dev->location));
    }
    if (mask & ALT_I2C_STATUS_INT_CALL)
    {
        alt_read_word(ALT_I2C_CLR_GEN_CALL_ADDR(i2c_dev->location));
    }

    return ALT_E_SUCCESS;
}

//
// Disable the specified I2C controller interrupt status conditions identified in
// the mask.
//
ALT_STATUS_CODE alt_i2c_int_disable(ALT_I2C_DEV_t *i2c_dev, const uint32_t mask)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    alt_clrbits_word(ALT_I2C_INTR_MSK_ADDR(i2c_dev->location), mask);    

    return ALT_E_SUCCESS;
}

//
// Enable the specified I2C controller interrupt status conditions identified in
// the mask.
//
ALT_STATUS_CODE alt_i2c_int_enable(ALT_I2C_DEV_t *i2c_dev, const uint32_t mask)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    alt_setbits_word(ALT_I2C_INTR_MSK_ADDR(i2c_dev->location), mask);

    return ALT_E_SUCCESS;
}

/////

//
// Gets the cause of I2C transmission abort.
//
ALT_STATUS_CODE alt_i2c_tx_abort_cause_get(ALT_I2C_DEV_t *i2c_dev,
                                           ALT_I2C_TX_ABORT_CAUSE_t *cause)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    *cause = (ALT_I2C_TX_ABORT_CAUSE_t)alt_read_word(ALT_I2C_TX_ABRT_SRC_ADDR(i2c_dev->location));

    return ALT_E_SUCCESS;
}

/////

//
// Returns ALT_E_TRUE when the receive FIFO is empty.
//
ALT_STATUS_CODE alt_i2c_rx_fifo_is_empty(ALT_I2C_DEV_t *i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (ALT_I2C_STAT_RFNE_GET(alt_read_word(ALT_I2C_STAT_ADDR(i2c_dev->location))) == ALT_I2C_STAT_RFNE_E_EMPTY)
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

//
// Returns ALT_E_TRUE when the receive FIFO is completely full.
//
ALT_STATUS_CODE alt_i2c_rx_fifo_is_full(ALT_I2C_DEV_t *i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (ALT_I2C_STAT_RFF_GET(alt_read_word(ALT_I2C_STAT_ADDR(i2c_dev->location))) == ALT_I2C_STAT_RFF_E_FULL)
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

//
// Returns the number of valid entries in the receive FIFO.
//
ALT_STATUS_CODE alt_i2c_rx_fifo_level_get(ALT_I2C_DEV_t *i2c_dev,
                                          uint32_t *num_entries)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    *num_entries = ALT_I2C_RXFLR_RXFLR_GET(alt_read_word(ALT_I2C_RXFLR_ADDR(i2c_dev->location)));

    return ALT_E_SUCCESS;
}

//
// Gets the current receive FIFO threshold level value.
//
ALT_STATUS_CODE alt_i2c_rx_fifo_threshold_get(ALT_I2C_DEV_t *i2c_dev,
                                              uint8_t *threshold)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    *threshold = ALT_I2C_RX_TL_RX_TL_GET(alt_read_word(ALT_I2C_RX_TL_ADDR(i2c_dev->location)));

    return ALT_E_SUCCESS;
}

//
// Sets the current receive FIFO threshold level value.
//
ALT_STATUS_CODE alt_i2c_rx_fifo_threshold_set(ALT_I2C_DEV_t *i2c_dev,
                                              const uint8_t threshold)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    bool already_enabled = (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_i2c_disable(i2c_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }

    alt_replbits_word(ALT_I2C_RX_TL_ADDR(i2c_dev->location),
                      ALT_I2C_RX_TL_RX_TL_SET_MSK,
                      ALT_I2C_RX_TL_RX_TL_SET(threshold));

    if (already_enabled)
    {
        // Re-enable controller
        status = alt_i2c_enable(i2c_dev);
    }

    return status;
}

//
// Returns ALT_E_TRUE when the transmit FIFO is empty.
//
ALT_STATUS_CODE alt_i2c_tx_fifo_is_empty(ALT_I2C_DEV_t *i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (ALT_I2C_STAT_TFE_GET(alt_read_word(ALT_I2C_STAT_ADDR(i2c_dev->location))) == ALT_I2C_STAT_TFE_E_EMPTY)
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

//
// Returns ALT_E_TRUE when the transmit FIFO is completely full.
//
ALT_STATUS_CODE alt_i2c_tx_fifo_is_full(ALT_I2C_DEV_t *i2c_dev)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (ALT_I2C_STAT_TFNF_GET(alt_read_word(ALT_I2C_STAT_ADDR(i2c_dev->location))) == ALT_I2C_STAT_TFNF_E_FULL)
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

//
// Returns the number of valid entries in the transmit FIFO.
//
ALT_STATUS_CODE alt_i2c_tx_fifo_level_get(ALT_I2C_DEV_t *i2c_dev,
                                          uint32_t *num_entries)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    *num_entries = ALT_I2C_TXFLR_TXFLR_GET(alt_read_word(ALT_I2C_TXFLR_ADDR(i2c_dev->location)));

    return ALT_E_SUCCESS;
}

//
// Sets the current transmit FIFO threshold level value.
//
ALT_STATUS_CODE alt_i2c_tx_fifo_threshold_get(ALT_I2C_DEV_t *i2c_dev,
                                              uint8_t *threshold)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    *threshold = ALT_I2C_TX_TL_TX_TL_GET(alt_read_word(ALT_I2C_TX_TL_ADDR(i2c_dev->location)));

    return ALT_E_SUCCESS;
}

//
// Sets the current transmit FIFO threshold level value.
//
ALT_STATUS_CODE alt_i2c_tx_fifo_threshold_set(ALT_I2C_DEV_t *i2c_dev,
                                              const uint8_t threshold)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    bool already_enabled = (alt_i2c_is_enabled_helper(i2c_dev) == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily disable controller
        status = alt_i2c_disable(i2c_dev);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }

    alt_replbits_word(ALT_I2C_TX_TL_ADDR(i2c_dev->location),
                      ALT_I2C_TX_TL_TX_TL_SET_MSK,
                      ALT_I2C_TX_TL_TX_TL_SET(threshold));

    if (already_enabled)
    {
        // Re-enable controller
        status = alt_i2c_enable(i2c_dev);
    }

    return status;
}

/////

ALT_STATUS_CODE alt_i2c_rx_dma_threshold_get(ALT_I2C_DEV_t * i2c_dev, uint8_t * threshold)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    *threshold = ALT_I2C_DMA_RDLR_DMARDL_GET(alt_read_word(ALT_I2C_DMA_RDLR_ADDR(i2c_dev->location)));
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_i2c_rx_dma_threshold_set(ALT_I2C_DEV_t * i2c_dev, uint8_t threshold)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (threshold > ALT_I2C_DMA_RDLR_DMARDL_SET_MSK)
    {
        return ALT_E_ARG_RANGE;
    }

    alt_write_word(ALT_I2C_DMA_RDLR_ADDR(i2c_dev->location), threshold);
    return ALT_E_SUCCESS;

}

ALT_STATUS_CODE alt_i2c_tx_dma_threshold_get(ALT_I2C_DEV_t * i2c_dev, uint8_t * threshold)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    *threshold = ALT_I2C_DMA_TDLR_DMATDL_GET(alt_read_word(ALT_I2C_DMA_TDLR_ADDR(i2c_dev->location)));
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_i2c_tx_dma_threshold_set(ALT_I2C_DEV_t * i2c_dev, uint8_t threshold)
{
    if (alt_i2c_checking(i2c_dev) == ALT_E_FALSE)
    {
        return ALT_E_BAD_ARG;
    }

    if (threshold > ALT_I2C_DMA_TDLR_DMATDL_SET_MSK)
    {
        return ALT_E_ARG_RANGE;
    }

    alt_write_word(ALT_I2C_DMA_TDLR_ADDR(i2c_dev->location), threshold);
    return ALT_E_SUCCESS;
}
