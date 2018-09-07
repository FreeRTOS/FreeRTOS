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

#include "alt_sdmmc.h"
#include "alt_clock_manager.h"
#include "alt_reset_manager.h"
#include "socal/alt_sdmmc.h"
#include "socal/alt_rstmgr.h"
#include "socal/hps.h"
#include "socal/socal.h"
#include <stdio.h>

/////

//#define LOGGER
// NOTE: To enable debugging output, delete the next line and uncomment the
//   line after.
//#define dprintf(...)
#define dprintf(fmt, ...) printf(fmt, ##__VA_ARGS__)
#ifdef LOGGER
#endif

/////

#define MIN(a, b) ((a) > (b) ? (b) : (a))
#define ARRAY_COUNT(array) (sizeof(array) / sizeof(array[0]))

/////

// Timeout for reset manager
#define  ALT_SDMMC_RESET_TMO_INIT      8192
// Timeout for disable device
#define  ALT_SDMMC_MAX_T_POLL_COUNT    8192
// Timeout for waiting event
#define  ALT_SDMMC_TMO_WAITER          1000000

#define ALT_SDMMC_DMA_SEGMENT_SIZE      512
#define ALT_SDMMC_DMA_DESC_COUNT        128

#define ALT_SDMMC_FSM_IDLE              0
#define ALT_SDMMC_DMA_FSM_IDLE          0

#define ALT_SDMMC_CSD_MAX_R_BLK_MSK             0x000F0000
#define ALT_SDMMC_CSD_MAX_W_BLK_MSK             0x03C00000
#define ALT_SDMMC_CSD_PART_R_ALLOW_MSK          0x00008000
#define ALT_SDMMC_CSD_PART_W_ALLOW_MSK          0x00200000
#define ALT_SDMMC_CSD_SPEED_RATE_MSK            0x00000007
#define ALT_SDMMC_CSD_SPEED_TIME_MSK            0x00000078
#define ALT_SDMMC_CSD_MAX_R_BLK_GET(val)        ((val & ALT_SDMMC_CSD_MAX_R_BLK_MSK) >> 16)
#define ALT_SDMMC_CSD_MAX_W_BLK_GET(val)        ((val & ALT_SDMMC_CSD_MAX_W_BLK_MSK) >> 22)
#define ALT_SDMMC_CSD_PART_R_ALLOW_GET(val)     ((val & ALT_SDMMC_CSD_PART_R_ALLOW_MSK) >> 15)
#define ALT_SDMMC_CSD_PART_W_ALLOW_GET(val)     ((val & ALT_SDMMC_CSD_PART_W_ALLOW_MSK) >> 21)
#define ALT_SDMMC_CSD_SPEED_RATE_GET(val)       ((val & ALT_SDMMC_CSD_SPEED_RATE_MSK) >> 0)
#define ALT_SDMMC_CSD_SPEED_TIME_GET(val)       ((val & ALT_SDMMC_CSD_SPEED_TIME_MSK) >> 3)
typedef enum ALT_SDMMC_TMOD_e
{
    ALT_SDMMC_TMOD_READ          = 0,
    ALT_SDMMC_TMOD_WRITE         = 1,
} ALT_SDMMC_TMOD_t;

#ifdef LOGGER
uint32_t log_buffer[1000] = { 0 };
uint32_t log_index = 0;

#define D_ADD_VALUE(value)({if (log_index < 1000) log_buffer[log_index++] = value;})
#endif

static alt_freq_t clock_freq;

// Default configurations of used commands
static ALT_SDMMC_CMD_CONFIG_t cmd_default_cfg[20] = 
{
    {
        .cmd_index = ALT_SDMMC_WRITE_MULTIPLE_BLOCK,
        .send_auto_stop = true,
        .response_expect = true,
        .data_expected = 1,
        .write_active = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_READ_MULTIPLE_BLOCK,
        .send_auto_stop = true,
        .response_expect = true,
        .data_expected = 1,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SD_SEND_SCR,
        .response_expect = true,
        .data_expected = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_WRITE_BLOCK,
        .response_expect = true,
        .data_expected = true,
        .write_active = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_READ_SINGLE_BLOCK,
        .response_expect = true,
        .data_expected = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_SET_BLOCKLEN,
        .response_expect = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_SEL_DES_CARD,
        .response_expect = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_APP_CMD,
        .response_expect = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SD_SET_BUS_WIDTH,
        .response_expect = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SD_SEND_OP_COND,
        .response_expect = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_SEND_OP_COND,
        .response_expect = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_IF_COND,
        .response_expect = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_SET_RELATIVE_ADDR,
        .response_expect = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_SEND_STATUS,
        .response_expect = true,
        .card_number = 0,
        .use_hold_reg = true
    },
    {
        .cmd_index = ALT_SDMMC_ALL_SEND_CID,
        .response_expect = true,
        .response_length_long = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_SEND_CID,
        .response_expect = true,
        .response_length_long = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_SEND_CSD,
        .response_expect = true,
        .response_length_long = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_STOP_TRANSMISSION,
        .stop_abort_cmd = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    },
    {
        .cmd_index = ALT_SDMMC_GO_IDLE_STATE,
        .send_initialization = true,
        .card_number = 0,
        .use_hold_reg = true,
        .wait_prvdata_complete = true
    }
};

static ALT_SDMMC_CMD_CONFIG_t cmd_clock_cfg = 
{
    .update_clock_registers_only = true,
    .wait_prvdata_complete = true
};

static uint32_t                    rca_number; /*!< Relative card address.  */
static ALT_SDMMC_DMA_BUF_DESC_t    dma_descriptors[ALT_SDMMC_DMA_DESC_COUNT];
                                        /*!< Array of dma descriptors.  */
static ALT_SDMMC_DMA_BUF_DESC_t    *dma_cur_descr; 
                                        /*!< Current decriptor.  */

//
// Reset sdmmc module by reset manager without deassert
//
static ALT_STATUS_CODE alt_sdmmc_rstmgr_set(void)
{
    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_SDMMC_SET_MSK);

    return ALT_E_SUCCESS;
}

//
// Assert reset sdmmc module by reset manager, wait, deasert
//
static ALT_STATUS_CODE alt_sdmmc_rstmgr_strobe(void)
{
    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_SDMMC_SET_MSK);

    volatile uint32_t timeout = ALT_SDMMC_RESET_TMO_INIT;

    // Wait while sdmmc module is reseting
    while (timeout--)
        ;

    // Deassert the appropriate sdmmc module reset signal via the Reset Manager Peripheral Reset register.
    alt_clrbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_SDMMC_SET_MSK);

    return ALT_E_SUCCESS;
}

//
// Initialize descriptor chain for dma
//
static ALT_STATUS_CODE alt_sdmmc_desc_chain_init()
{
    ALT_SDMMC_DMA_BUF_DESC_t * dma_desc = dma_descriptors;

    // Initialising descriptor chain
    for (uint32_t count = 0; count < ALT_SDMMC_DMA_DESC_COUNT; count++)
    {
        dma_desc[count].des0.fld.own  = 0;
        dma_desc[count].des0.fld.ch   = 1;
        dma_desc[count].des0.fld.er   = 0;
        dma_desc[count].des1.fld.bs1  = 0;
        dma_desc[count].des2.fld.bap1 = 0;

        // Create chain description list
        if (count == (ALT_SDMMC_DMA_DESC_COUNT - 1))
        {
            // If it is latest element set pointer to the ring head.
            dma_desc[count].des3.fld.bap2_or_next = (uint32_t) dma_desc;
        }
        else
        {
            // Set pointer to the next element in the ring
            dma_desc[count].des3.fld.bap2_or_next = (uint32_t) (&dma_desc[count + 1]);
        }
    }
    
    dma_cur_descr = dma_desc;

    return ALT_E_SUCCESS;
}

//
// Clear descriptors of chain for dma operations
//
static ALT_STATUS_CODE alt_sdmmc_desc_chain_clear()
{
    ALT_SDMMC_DMA_BUF_DESC_t * dma_desc = dma_descriptors;

    // Clean descriptions
    for (uint32_t count = 0; count < ALT_SDMMC_DMA_DESC_COUNT; count++)
    {
        dma_desc[count].des0.fld.own  = 0;
        dma_desc[count].des0.fld.dic  = 0;
        dma_desc[count].des0.fld.ld   = 0;
        dma_desc[count].des0.fld.fs   = 0;
        dma_desc[count].des1.fld.bs1  = 0;
        dma_desc[count].des2.fld.bap1 = 0;
    }

    dma_cur_descr = dma_desc;

    return ALT_E_SUCCESS;
}

//
// Initialize the specified sdmmc controller instance for use and return a device
// handle referencing it.
//
ALT_STATUS_CODE alt_sdmmc_init()
{
    if (alt_clk_is_enabled(ALT_CLK_SDMMC) != ALT_E_TRUE)
    {
        return ALT_E_BAD_CLK;
    }

    /////

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Query the SDMMC clock.
    if (status == ALT_E_SUCCESS)
    {
        status = alt_clk_freq_get(ALT_CLK_SDMMC, &clock_freq);
    }

    // Reset sdmmc module
    if (status == ALT_E_SUCCESS)
    {
        status = alt_sdmmc_reset();
    }

    return status;
}

//
//Reset the SD/MMC controller by stopping any data transfers in progress and
//putting the controller into reset and reinit it after reset complete.
//
ALT_STATUS_CODE alt_sdmmc_reset()
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    bool already_enabled = (alt_sdmmc_card_pwr_is_on() == ALT_E_TRUE);

    if (already_enabled)
    {
        // Temporarily power off the card
        status = alt_sdmmc_card_pwr_off();
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }
    }
    
    // Reset sdmmc module by reset manager
    alt_sdmmc_rstmgr_strobe();
    
    if (already_enabled)
    {
        // Re-enable card power
        status = alt_sdmmc_card_pwr_on();
    }

    // Relative card address have not readed yet
    rca_number = 0;
    // Init description chain
    alt_sdmmc_desc_chain_init();

    if (status == ALT_E_SUCCESS)
    {
        //Enable default clock for working alt_sdmmc_command_send
        alt_write_word(ALT_SDMMC_CLKENA_ADDR, ALT_SDMMC_CLKENA_CCLK_EN_SET(true));
        status = alt_sdmmc_command_send(ALT_SDMMC_CLK_INDEX, 0x0, NULL);
    }

    return status;
}

//
// Uninitialize the sdmmc controller referenced by the sdmmc_dev handle.
//
ALT_STATUS_CODE alt_sdmmc_uninit(void)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    // Clean descriptor chain
    alt_sdmmc_desc_chain_clear();

    // Card power off
    if (status == ALT_E_SUCCESS)
    {
        status = alt_sdmmc_card_pwr_off();
    }

    // Reset sdmmc module by reset manager
    if (status == ALT_E_SUCCESS)
    {
        status = alt_sdmmc_rstmgr_set();
    }

    return status;
}

//
// Power on of the card.
//
ALT_STATUS_CODE alt_sdmmc_card_pwr_on(void)
{
    alt_setbits_word(ALT_SDMMC_PWREN_ADDR, 
                     ALT_SDMMC_PWREN_POWER_EN_SET_MSK);

    return ALT_E_SUCCESS;
}

//
//Power off of the card.
//
ALT_STATUS_CODE alt_sdmmc_card_pwr_off(void)
{
    //If sdmmc controller is enabled, return with sucess
    if (alt_sdmmc_card_pwr_is_on() == ALT_E_FALSE)
    {
        return ALT_E_SUCCESS;
    }

    //Else clear enable bit of sdmmc_enable register
    alt_clrbits_word(ALT_SDMMC_PWREN_ADDR,
                     ALT_SDMMC_PWREN_POWER_EN_SET_MSK);
    
    // Clear interrupt status
    alt_sdmmc_int_clear(ALT_SDMMC_INT_STATUS_ALL);

    // Relative card address have not readed yet
    rca_number = 0;
    // Reset state of card stack
    return ALT_E_SUCCESS;
}

//
// Check whether sdmmc controller is enable
//
bool alt_sdmmc_card_pwr_is_on(void)
{
    if (ALT_SDMMC_PWREN_POWER_EN_GET(alt_read_word(ALT_SDMMC_PWREN_ADDR)) == 
        ALT_SDMMC_PWREN_POWER_EN_E_ON)
    {
        return true;
    }
    else
    {
        return false;
    }
}

//
// Returns ALT_E_TRUE if the sdmmc controller is busy
//
static ALT_STATUS_CODE alt_sdmmc_is_busy(void)
{
    if (ALT_SDMMC_STAT_DATA_BUSY_GET(alt_read_word(ALT_SDMMC_STAT_ADDR)) ==
        ALT_SDMMC_STAT_DATA_BUSY_E_CARDBUSY)
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

//
// Returns ALT_E_TRUE if the sdmmc and iddmac controller is in idle state
//
static ALT_STATUS_CODE alt_sdmmc_is_idle(void)
{
    uint32_t mmc_state = ALT_SDMMC_STAT_CMD_FSM_STATES_GET(alt_read_word(ALT_SDMMC_STAT_ADDR));
    
    uint32_t dma_state = ALT_SDMMC_IDSTS_FSM_GET(alt_read_word(ALT_SDMMC_IDSTS_ADDR));
    
    if ((mmc_state != ALT_SDMMC_FSM_IDLE) || (dma_state != ALT_SDMMC_DMA_FSM_IDLE))
    {
#ifdef LOGGER
        dprintf("\nstate %x dma_state %x\n", (int)mmc_state, (int)dma_state);
#endif
        return ALT_E_FALSE;
    }
    else
    {
        return ALT_E_TRUE;
    }
}

//
// Get config clock parameters
//
uint32_t alt_sdmmc_card_clk_div_get(void)
{
    return ALT_SDMMC_CLKDIV_CLK_DIVR0_GET(alt_read_word(ALT_SDMMC_CLKDIV_ADDR));
}

//
// Set config clock parameters (7.2.3 Clock Programming)
//
ALT_STATUS_CODE alt_sdmmc_card_clk_div_set(const uint32_t clk_div)
{
    if (alt_sdmmc_is_busy() == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    alt_write_word(ALT_SDMMC_CLKDIV_ADDR, ALT_SDMMC_CLKDIV_CLK_DIVR0_SET(clk_div));

    return alt_sdmmc_command_send(ALT_SDMMC_CLK_INDEX, 0x0, NULL);
}

uint32_t alt_sdmmc_card_speed_get(void)
{
    uint32_t clk_div = alt_sdmmc_card_clk_div_get();

    uint32_t speed_bps = clock_freq / (2 * clk_div);

    return speed_bps;
}

ALT_STATUS_CODE alt_sdmmc_card_speed_set(uint32_t xfer_speed)
{
    uint32_t clk_div = clock_freq / (2 * xfer_speed);

    return alt_sdmmc_card_clk_div_set(clk_div);
}

ALT_STATUS_CODE alt_sdmmc_card_clk_disable(void)
{
    if (alt_sdmmc_is_busy() == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    alt_write_word(ALT_SDMMC_CLKENA_ADDR, ALT_SDMMC_CLKENA_CCLK_EN_SET(false));

    return alt_sdmmc_command_send(ALT_SDMMC_CLK_INDEX, 0x0, NULL);
}

//
// Enables the card clock (sdmmc_cclk_out).
//
ALT_STATUS_CODE alt_sdmmc_card_clk_enable(const bool use_low_pwr_mode)
{
    if (alt_sdmmc_is_busy() == ALT_E_TRUE)
    {
        return ALT_E_ERROR;
    }

    // Enable clock
    alt_write_word(ALT_SDMMC_CLKENA_ADDR, ALT_SDMMC_CLKENA_CCLK_EN_SET(true)
                                        | ALT_SDMMC_CLKENA_CCLK_LOW_POWER_SET(use_low_pwr_mode));

    return alt_sdmmc_command_send(ALT_SDMMC_CLK_INDEX, 0x0, NULL);
}

//
// Returns true if the card clock (sdmmc_cclk_out) is enabled otherwise returns
//
bool alt_sdmmc_card_clk_is_enabled(void)
{
    return ALT_SDMMC_CLKENA_CCLK_EN_GET(alt_read_word(ALT_SDMMC_CLKENA_ADDR));
}

//
// Get sdmmc bus width
//
static ALT_SDMMC_BUS_WIDTH_t alt_sdmmc_bus_width_get(void)
{
    uint32_t ctype_register = alt_read_word(ALT_SDMMC_CTYPE_ADDR);

    uint16_t card_width1 = ALT_SDMMC_CTYPE_CARD_WIDTH1_GET(ctype_register);
    uint16_t card_width2 = ALT_SDMMC_CTYPE_CARD_WIDTH2_GET(ctype_register);

    if (card_width1 == ALT_SDMMC_CTYPE_CARD_WIDTH1_E_MOD8BIT)
    {
        return ALT_SDMMC_BUS_WIDTH_8;
    }
    else if (card_width2 == ALT_SDMMC_CTYPE_CARD_WIDTH2_E_MOD4BIT)
    {
        return ALT_SDMMC_BUS_WIDTH_4;
    }
    else
    {
        return ALT_SDMMC_BUS_WIDTH_1;
    }
}

//
// Set sdmmc bus width
//
static ALT_STATUS_CODE alt_sdmmc_bus_width_set(const ALT_SDMMC_BUS_WIDTH_t width)
{
    // Set config parameters to appropriate registers
    switch (width)
    {
    case ALT_SDMMC_BUS_WIDTH_8:
        alt_replbits_word(ALT_SDMMC_CTYPE_ADDR,
                          ALT_SDMMC_CTYPE_CARD_WIDTH1_SET_MSK,
                          ALT_SDMMC_CTYPE_CARD_WIDTH1_SET(ALT_SDMMC_CTYPE_CARD_WIDTH1_E_MOD8BIT));
        break;

    case ALT_SDMMC_BUS_WIDTH_4:
        alt_replbits_word(ALT_SDMMC_CTYPE_ADDR,
                          ALT_SDMMC_CTYPE_CARD_WIDTH1_SET_MSK,
                          ALT_SDMMC_CTYPE_CARD_WIDTH1_SET(ALT_SDMMC_CTYPE_CARD_WIDTH1_E_NON8BIT));
        alt_replbits_word(ALT_SDMMC_CTYPE_ADDR,
                          ALT_SDMMC_CTYPE_CARD_WIDTH2_SET_MSK, 
                          ALT_SDMMC_CTYPE_CARD_WIDTH2_SET(ALT_SDMMC_CTYPE_CARD_WIDTH2_E_MOD4BIT));
        break;

    case ALT_SDMMC_BUS_WIDTH_1:
        alt_replbits_word(ALT_SDMMC_CTYPE_ADDR,
                          ALT_SDMMC_CTYPE_CARD_WIDTH1_SET_MSK, 
                          ALT_SDMMC_CTYPE_CARD_WIDTH1_SET(ALT_SDMMC_CTYPE_CARD_WIDTH1_E_NON8BIT));
        alt_replbits_word(ALT_SDMMC_CTYPE_ADDR,
                          ALT_SDMMC_CTYPE_CARD_WIDTH2_SET_MSK, 
                          ALT_SDMMC_CTYPE_CARD_WIDTH2_SET(ALT_SDMMC_CTYPE_CARD_WIDTH2_E_MOD1BIT));
        break;

    default:
        return ALT_E_BAD_ARG;
    }

    return ALT_E_SUCCESS;
}

//
// Get block size
//
inline static uint16_t alt_sdmmc_block_size_get(void)
{
    uint32_t blksiz_register = alt_read_word(ALT_SDMMC_BLKSIZ_ADDR);
    return ALT_SDMMC_BLKSIZ_BLOCK_SIZE_GET(blksiz_register);
}

//
// Set block size
//
inline static ALT_STATUS_CODE alt_sdmmc_block_size_set(uint16_t block_size)
{
    alt_replbits_word(ALT_SDMMC_BLKSIZ_ADDR,
                      ALT_SDMMC_BLKSIZ_BLOCK_SIZE_SET_MSK,
                      ALT_SDMMC_BLKSIZ_BLOCK_SIZE_SET(block_size));

    return ALT_E_SUCCESS;
}

//
// Set byte count
//
inline static ALT_STATUS_CODE alt_sdmmc_byte_count_set(uint32_t count)
{
    alt_replbits_word(ALT_SDMMC_BYTCNT_ADDR,
                      ALT_SDMMC_BYTCNT_BYTE_COUNT_SET_MSK,
                      ALT_SDMMC_BYTCNT_BYTE_COUNT_SET(count));

    return ALT_E_SUCCESS;
}

//
// Get sdmmc timeouts for command response and data sending
//
ALT_STATUS_CODE alt_sdmmc_card_misc_get(ALT_SDMMC_CARD_MISC_t *card_misc_cfg)
{
    uint32_t tmout_register = alt_read_word(ALT_SDMMC_TMOUT_ADDR);

    card_misc_cfg->response_timeout = ALT_SDMMC_TMOUT_RESPONSE_TMO_GET(tmout_register);
    card_misc_cfg->data_timeout     = ALT_SDMMC_TMOUT_DATA_TMO_GET(tmout_register);

    card_misc_cfg->card_width = alt_sdmmc_bus_width_get();
    card_misc_cfg->block_size = alt_sdmmc_block_size_get();

    card_misc_cfg->debounce_count = ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_GET(alt_read_word(ALT_SDMMC_DEBNCE_ADDR));

    return ALT_E_SUCCESS;
}

//
//Set sdmmc timeouts for command response and data sending
//
ALT_STATUS_CODE alt_sdmmc_card_misc_set(const ALT_SDMMC_CARD_MISC_t *card_misc_cfg)
{
    uint32_t tmout_value = ALT_SDMMC_TMOUT_RESPONSE_TMO_SET(card_misc_cfg->response_timeout)
                         | ALT_SDMMC_TMOUT_DATA_TMO_SET(card_misc_cfg->data_timeout);

    alt_write_word(ALT_SDMMC_TMOUT_ADDR, tmout_value);

    alt_replbits_word(ALT_SDMMC_DEBNCE_ADDR,
                      ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_SET_MSK,
                      ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_SET(card_misc_cfg->debounce_count));

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    if (status == ALT_E_SUCCESS)
    {
        status = alt_sdmmc_bus_width_set(card_misc_cfg->card_width);
    }

    if (status == ALT_E_SUCCESS)
    {
        status = alt_sdmmc_block_size_set(card_misc_cfg->block_size);
    }

    return status;
}

//
// Starts the SD/MMC internal DMA transfer with the specified
// descriptor an bus mode transfer configuration.
//
ALT_STATUS_CODE alt_sdmmc_dma_start(ALT_SDMMC_DMA_BUF_DESC_t *buf_desc_list, 
                                    const uint32_t desc_skip_len,
                                    const ALT_SDMMC_DMA_PBL_t burst_len,
                                    const bool use_fixed_burst)
{
    uint32_t bmod_set_value = ALT_SDMMC_BMOD_PBL_SET(burst_len)
                            | ALT_SDMMC_BMOD_FB_SET(use_fixed_burst)
                            | ALT_SDMMC_BMOD_DSL_SET(desc_skip_len);

    uint32_t bmod_set_mask = ALT_SDMMC_BMOD_PBL_SET_MSK
                           | ALT_SDMMC_BMOD_FB_SET_MSK
                           | ALT_SDMMC_BMOD_DSL_SET_MSK;

    alt_replbits_word(ALT_SDMMC_BMOD_ADDR, bmod_set_mask, bmod_set_value);

    // Set start address of descriptor chain
    alt_write_word(ALT_SDMMC_DBADDR_ADDR, (uint32_t)buf_desc_list);

    return ALT_E_SUCCESS;
}

//
// Enables the sdmmc write protect.
//
bool alt_sdmmc_card_is_write_protected(void)
{
    alt_setbits_word(ALT_SDMMC_WRTPRT_ADDR, 
                     ALT_SDMMC_WRTPRT_WR_PROTECT_SET_MSK);

    return ALT_E_SUCCESS;
}

//
// FIFO reset
//
ALT_STATUS_CODE alt_sdmmc_fifo_reset(void)
{
    uint32_t timeout = ALT_SDMMC_MAX_T_POLL_COUNT;

    // Activate fifo reset
    alt_setbits_word(ALT_SDMMC_CTL_ADDR, ALT_SDMMC_CTL_FIFO_RST_SET_MSK);
    
    // Wait to complete reset or timeout
    while (ALT_SDMMC_CTL_FIFO_RST_GET(alt_read_word(ALT_SDMMC_CTL_ADDR))
                                                && --timeout)
        ;

    // If fifo reset still are active, return timeout error
    if (timeout == 0)
    {
        return ALT_E_TMO;
    }

    return ALT_E_SUCCESS;
}
    
//
// DMA reset
//
ALT_STATUS_CODE alt_sdmmc_dma_reset(void)
{
    uint32_t timeout = ALT_SDMMC_MAX_T_POLL_COUNT;

    //Activate dma reset
    alt_setbits_word(ALT_SDMMC_CTL_ADDR, ALT_SDMMC_CTL_DMA_RST_SET_MSK);
    
    // Wait to complete reset or timeout
    while (ALT_SDMMC_CTL_DMA_RST_GET(alt_read_word(ALT_SDMMC_CTL_ADDR))
                                                && --timeout)
        ;

    // If dma reset still are active, return timeout error
    if (timeout == 0)
    {
        return ALT_E_TMO;
    }

    return ALT_E_SUCCESS;
}
        

//
// Returns ALT_E_TRUE if the sdmmc controller is present depend on cdata_in.
//
bool alt_sdmmc_card_is_detected(void)
{
    if (ALT_SDMMC_STAT_DATA_3_STAT_GET(alt_read_word(ALT_SDMMC_STAT_ADDR)) ==
        ALT_SDMMC_STAT_DATA_3_STAT_E_CARDPRESENT)
//    if (ALT_SDMMC_CDETECT_CARD_DETECT_N_GET(alt_read_word(ALT_SDMMC_CDETECT_ADDR))
//                                        == ALT_SDMMC_CDETECT_CARD_DETECT_N_E_DETECTED)
    {
        return true;
    }
    else
    {
        return false;
    }
}

//
//Set command configuration
//
static ALT_STATUS_CODE alt_sdmmc_cmd_set(const ALT_SDMMC_CMD_INDEX_t cmd_index,
                                         const ALT_SDMMC_CMD_CONFIG_t *cmd_cfg,
                                         bool start_cmd)
{
     uint32_t cmd_register = ALT_SDMMC_CMD_CMD_INDEX_SET(cmd_index)
                           | ALT_SDMMC_CMD_RESPONSE_EXPECT_SET(cmd_cfg->response_expect) 
                           | ALT_SDMMC_CMD_RESPONSE_LEN_SET(cmd_cfg->response_length_long)
                           | ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_SET(cmd_cfg->check_response_crc)
                           | ALT_SDMMC_CMD_DATA_EXPECTED_SET(cmd_cfg->data_expected)
                           | ALT_SDMMC_CMD_RD_WR_SET(cmd_cfg->write_active)
                           | ALT_SDMMC_CMD_TFR_MOD_SET(cmd_cfg->stream_mode_active)
                           | ALT_SDMMC_CMD_SEND_AUTO_STOP_SET(cmd_cfg->send_auto_stop)
                           | ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_SET(cmd_cfg->wait_prvdata_complete)
                           | ALT_SDMMC_CMD_STOP_ABT_CMD_SET(cmd_cfg->stop_abort_cmd)
                           | ALT_SDMMC_CMD_SEND_INITIALIZATION_SET(cmd_cfg->send_initialization)
                           | ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_SET(cmd_cfg->update_clock_registers_only)
                           | ALT_SDMMC_CMD_RD_CEATA_DEVICE_SET(cmd_cfg->read_ceata_device)
                           | ALT_SDMMC_CMD_CCS_EXPECTED_SET(cmd_cfg->ccs_expected)
                           | ALT_SDMMC_CMD_EN_BOOT_SET(cmd_cfg->enable_boot)
                           | ALT_SDMMC_CMD_EXPECT_BOOT_ACK_SET(cmd_cfg->expect_boot_ack)
                           | ALT_SDMMC_CMD_DIS_BOOT_SET(cmd_cfg->disable_boot)
                           | ALT_SDMMC_CMD_BOOT_MOD_SET(cmd_cfg->boot_mode)
                           | ALT_SDMMC_CMD_VOLT_SWITCH_SET(cmd_cfg->volt_switch)
                           | ALT_SDMMC_CMD_USE_HOLD_REG_SET(cmd_cfg->use_hold_reg)
                           | ALT_SDMMC_CMD_START_CMD_SET(start_cmd);

    alt_write_word(ALT_SDMMC_CMD_ADDR, cmd_register);

#ifdef LOGGER
    dprintf("\ncommand = %X\n", (int)cmd_register);
#endif

    return ALT_E_SUCCESS;
}

//
// Set command argument
//
inline static ALT_STATUS_CODE alt_sdmmc_cmd_arg_set(uint32_t cmdarg)
{
    alt_write_word(ALT_SDMMC_CMDARG_ADDR, cmdarg);

    return ALT_E_SUCCESS;
}

//
// Get response previous command.
//
inline static ALT_STATUS_CODE alt_sdmmc_read_short_response(uint32_t *response)
{
    uint32_t resp0 = alt_read_word(ALT_SDMMC_RESP0_ADDR);
    *response = (uint32_t)(ALT_SDMMC_RESP0_RESPONSE0_GET(resp0));

    return ALT_E_SUCCESS;
}

//
// Get long response of previous command.
//
ALT_STATUS_CODE alt_sdmmc_read_long_response(ALT_SDMMC_RESPONSE_t *response)
{
    uint32_t resp0 = alt_read_word(ALT_SDMMC_RESP0_ADDR);
    uint32_t resp1 = alt_read_word(ALT_SDMMC_RESP1_ADDR);
    uint32_t resp2 = alt_read_word(ALT_SDMMC_RESP2_ADDR);
    uint32_t resp3 = alt_read_word(ALT_SDMMC_RESP3_ADDR);

    response->resp0 = (uint32_t)(ALT_SDMMC_RESP0_RESPONSE0_GET(resp0));
    response->resp1 = (uint32_t)(ALT_SDMMC_RESP1_RESPONSE1_GET(resp1));
    response->resp2 = (uint32_t)(ALT_SDMMC_RESP2_RESPONSE2_GET(resp2));
    response->resp3 = (uint32_t)(ALT_SDMMC_RESP3_RESPONSE3_GET(resp3));

    return ALT_E_SUCCESS;
}

//
//This function reads a single data byte from the receive FIFO.
//
ALT_STATUS_CODE alt_sdmmc_fifo_read(void *dest, const size_t size)
{
    uint32_t * dest_ptr = dest;
    for (int counter = 0; counter < size / 4; counter++)
    {
        dest_ptr[counter] = (uint32_t)(ALT_SDMMC_DATA_VALUE_GET(alt_read_word(ALT_SDMMC_DATA_ADDR)));
    }
    
    if (size & 0x3)
    {
        uint8_t * add_dest_ptr = (uint8_t*)dest + (size / 4);
        uint32_t word_notfull = (uint32_t)(ALT_SDMMC_DATA_VALUE_GET(alt_read_word(ALT_SDMMC_DATA_ADDR)));
    
        for (int counter = 0; counter < (size & 0x3); counter++)
        {
            add_dest_ptr[counter] = (uint8_t)word_notfull;
            word_notfull = word_notfull >> 8;
        }
    }

    return ALT_E_SUCCESS;
}

//
// This function writes a single data byte to the transmit FIFO.
//
ALT_STATUS_CODE alt_sdmmc_fifo_write(const void *src, const size_t size)
{
    const uint32_t * src_ptr = src;
    for (int counter = 0; counter < size / 4; counter++)
    {
        alt_write_word(ALT_SDMMC_DATA_ADDR, ALT_SDMMC_DATA_VALUE_SET(src_ptr[counter]));
    }

    if (size & 0x3)
    {
        const uint8_t *add_src_ptr = (uint8_t*)src + (size / 4);
        uint32_t word_notfull = 0;

        for (int counter = 0; counter < (size & 0x3); counter++)
        {
            word_notfull |= (uint32_t)add_src_ptr[counter] << (8 * counter);
        }

        alt_write_word(ALT_SDMMC_DATA_ADDR, ALT_SDMMC_DATA_VALUE_SET(word_notfull));
    }
    
    return ALT_E_SUCCESS;
}

//
// Returns the current sdmmc controller interrupt status conditions.
//
uint32_t alt_sdmmc_int_status_get(void)
{
    return alt_read_word(ALT_SDMMC_MINTSTS_ADDR);
}

//
// Returns the sdmmc controller raw interrupt status conditions irrespective of
// the interrupt status condition enablement state.
//
uint32_t alt_sdmmc_int_mask_get(void)
{
    return alt_read_word(ALT_SDMMC_INTMSK_ADDR);
}

//
// Clears the specified sdmmc controller interrupt status conditions identified
// in the mask.
//
ALT_STATUS_CODE alt_sdmmc_int_clear(const uint32_t mask)
{
    alt_write_word(ALT_SDMMC_RINTSTS_ADDR, mask);

    return ALT_E_SUCCESS;
}

//
// Disable the specified sdmmc controller interrupt status conditions identified in
// the mask.
//
ALT_STATUS_CODE alt_sdmmc_int_disable(const uint32_t mask)
{
    alt_clrbits_word(ALT_SDMMC_INTMSK_ADDR, mask);

    return ALT_E_SUCCESS;
}

//
// Enable the specified sdmmc controller interrupt status conditions identified in
// the mask.
//
ALT_STATUS_CODE alt_sdmmc_int_enable(const uint32_t mask)
{
    if (mask & 0x0001ffff)
    {
        alt_setbits_word(ALT_SDMMC_CTL_ADDR, 
                     ALT_SDMMC_CTL_INT_EN_SET_MSK);

        alt_setbits_word(ALT_SDMMC_INTMSK_ADDR, mask);
    }
    return ALT_E_SUCCESS;
}

//
//Returns true if SD/MMC controller FIFO has reached the receive watermark level
//otherwise returns false.
//
bool alt_sdmmc_fifo_is_rx_wtrmk_reached(void)
{
    if (ALT_SDMMC_STAT_FIFO_RX_WATERMARK_GET(alt_read_word(ALT_SDMMC_STAT_ADDR)) == 
                    ALT_SDMMC_STAT_FIFO_RX_WATERMARK_E_RXWATERMARK)
    {
        return true;
    }
    else
    {
        return false;
    }
}

//
//Returns true if SD/MMC controller FIFO has reached the transmit watermark level
//otherwise returns false.
//
bool alt_sdmmc_fifo_is_tx_wtrmk_reached(void)
{
    if (ALT_SDMMC_STAT_FIFO_TX_WATERMARK_GET(alt_read_word(ALT_SDMMC_STAT_ADDR)) == 
                     ALT_SDMMC_STAT_FIFO_TX_WATERMARK_E_TXWATERMARK)
    {
        return true;
    }
    else
    {
        return false;
    }
}

//
// Returns ALT_E_TRUE when the receive FIFO is empty.
//
bool alt_sdmmc_fifo_is_empty(void)
{
    if (ALT_SDMMC_STAT_FIFO_EMPTY_GET(alt_read_word(ALT_SDMMC_STAT_ADDR)) ==
        ALT_SDMMC_STAT_FIFO_EMPTY_E_FIFOEMPTY)
    {
        return true;
    }
    else
    {
        return false;
    }
}

//
// Returns ALT_E_TRUE when the receive FIFO is completely full.
//
bool alt_sdmmc_fifo_is_full(void)
{
    if (ALT_SDMMC_STAT_FIFO_FULL_GET(alt_read_word(ALT_SDMMC_STAT_ADDR)) ==
        ALT_SDMMC_STAT_FIFO_FULL_E_FIFOFULL)
    {
        return true;
    }
    else
    {
        return false;
    }
}

//
// Returns the number of valid entries in the receive FIFO.
//
int32_t alt_sdmmc_fifo_count(void)
{
    return (int32_t)ALT_SDMMC_STAT_FIFO_COUNT_GET(alt_read_word(ALT_SDMMC_STAT_ADDR));
}

//
// Gets the configured FIFO operational parameter values.
//
ALT_STATUS_CODE alt_sdmmc_fifo_param_get(uint32_t *rx_wtrmk, uint32_t *tx_wtrmk, ALT_SDMMC_MULT_TRANS_t *mult_trans_size)
{
    uint32_t fifoth = alt_read_word(ALT_SDMMC_FIFOTH_ADDR);

    *rx_wtrmk        = ALT_SDMMC_FIFOTH_RX_WMARK_GET(fifoth);
    *tx_wtrmk        = ALT_SDMMC_FIFOTH_TX_WMARK_GET(fifoth);
    *mult_trans_size = (ALT_SDMMC_MULT_TRANS_t)ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_GET(fifoth);

    return ALT_E_SUCCESS;
}

//
// Sets the configured FIFO operational parameter values.
//
ALT_STATUS_CODE alt_sdmmc_fifo_param_set(uint32_t rx_wtrmk, uint32_t tx_wtrmk, ALT_SDMMC_MULT_TRANS_t mult_trans_size)
{
    uint32_t fifoth_set_mask = ALT_SDMMC_FIFOTH_RX_WMARK_SET_MSK
                             | ALT_SDMMC_FIFOTH_TX_WMARK_SET_MSK
                             | ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_SET_MSK;
    
    uint32_t fifoth_set_value = ALT_SDMMC_FIFOTH_RX_WMARK_SET(rx_wtrmk)
                              | ALT_SDMMC_FIFOTH_TX_WMARK_SET(tx_wtrmk)
                              | ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_SET(mult_trans_size);
                            
    alt_replbits_word(ALT_SDMMC_FIFOTH_ADDR,
                      fifoth_set_mask,
                      fifoth_set_value);

    return ALT_E_SUCCESS;
}

//
// Card reset
//
ALT_STATUS_CODE alt_sdmmc_card_reset(void)
{
    // Assert card reset 
    alt_setbits_word(ALT_SDMMC_RST_N_ADDR, 
                     ALT_SDMMC_RST_N_CARD_RST_SET_MSK);

    volatile uint32_t timeout = ALT_SDMMC_RESET_TMO_INIT;

    // Wait while card reset
    while (timeout--)
        ;

    // Deassert the appropriate card reset.
    alt_clrbits_word(ALT_SDMMC_RST_N_ADDR, 
                     ALT_SDMMC_RST_N_CARD_RST_SET_MSK);

    return ALT_E_SUCCESS;
}

//
// Enables the sdmmc Internal DMA Controller.
//
ALT_STATUS_CODE alt_sdmmc_dma_enable(void)
{
    alt_setbits_word(ALT_SDMMC_CTL_ADDR, 
                     ALT_SDMMC_CTL_USE_INTERNAL_DMAC_SET_MSK);
    alt_setbits_word(ALT_SDMMC_BMOD_ADDR, 
                     ALT_SDMMC_BMOD_DE_SET_MSK);

    return ALT_E_SUCCESS;
}

//
// Disables the sdmmc Internal DMA Controller
//
ALT_STATUS_CODE alt_sdmmc_dma_disable(void)
{
    alt_clrbits_word(ALT_SDMMC_CTL_ADDR, 
                     ALT_SDMMC_CTL_USE_INTERNAL_DMAC_SET_MSK);
    alt_clrbits_word(ALT_SDMMC_BMOD_ADDR, 
                     ALT_SDMMC_BMOD_DE_SET_MSK);

    return ALT_E_SUCCESS;
}

//
// Enables the sdmmc Internal DMA Controller.
//
ALT_STATUS_CODE alt_sdmmc_is_dma_enabled(void)
{
    if (   ALT_SDMMC_CTL_USE_INTERNAL_DMAC_GET(alt_read_word(ALT_SDMMC_CTL_ADDR))
        && ALT_SDMMC_BMOD_DE_GET(alt_read_word(ALT_SDMMC_BMOD_ADDR)))
    {
        return ALT_E_TRUE;
    }
    else
    {
        return ALT_E_FALSE;
    }
}

//
// Returns the current sdmmc controller interrupt IDMAC status conditions.
//
uint32_t alt_sdmmc_dma_int_status_get(void)
{
    return alt_read_word(ALT_SDMMC_IDSTS_ADDR);
}

//
// Returns the SD/MMC internal DMA controller interrupt mask value which
// reflects the enabled internal DMA controller interrupt status conditions.
//
uint32_t alt_sdmmc_dma_int_mask_get(void)
{
    return alt_read_word(ALT_SDMMC_IDINTEN_ADDR);
}

//
// Clears the specified sdmmc controller interrupt status IDMAC conditions identified
// in the mask.
//
ALT_STATUS_CODE alt_sdmmc_dma_int_clear(const uint32_t mask)
{
    alt_write_word(ALT_SDMMC_IDSTS_ADDR, mask);

    return ALT_E_SUCCESS;
}

//
// Disable the specified sdmmc controller interrupt IDMAC status conditions identified in
// the mask.
//
ALT_STATUS_CODE alt_sdmmc_dma_int_disable(const uint32_t mask)
{
    alt_clrbits_word(ALT_SDMMC_IDINTEN_ADDR, mask);

    return ALT_E_SUCCESS;
}

//
// Enable the specified sdmmc controller interrupt status conditions identified in
// the mask.
//
ALT_STATUS_CODE alt_sdmmc_dma_int_enable(const uint32_t mask)
{
    alt_setbits_word(ALT_SDMMC_IDINTEN_ADDR, mask);

    return ALT_E_SUCCESS;
}

//
// Sets value into this register for the IDMAC FSM to resume normal descriptor fetch operation.
//
ALT_STATUS_CODE alt_sdmmc_poll_demand_set(const uint32_t value)
{
    alt_replbits_word(ALT_SDMMC_PLDMND_ADDR,
                      ALT_SDMMC_PLDMND_PD_SET_MSK,
                      ALT_SDMMC_PLDMND_PD_SET(value));

    return ALT_E_SUCCESS;
}

//
// Disable Card Read Threshold .
//
ALT_STATUS_CODE alt_sdmmc_card_rd_threshold_disable(void)
{
    alt_clrbits_word(ALT_SDMMC_CARDTHRCTL_ADDR,
                     ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_SET_MSK);

    return ALT_E_SUCCESS;
}


//
// Enable Card Read Threshold .
//
ALT_STATUS_CODE alt_sdmmc_card_rd_threshold_enable(const uint32_t threshold)
{
    alt_replbits_word(ALT_SDMMC_CARDTHRCTL_ADDR,
                        ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD_SET_MSK 
                      | ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_SET_MSK,
                        ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD_SET(threshold) 
                      | ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_SET(ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_E_END));

    return ALT_E_SUCCESS;
}

//
// This function return ALT_E_ERROR if interrupt error was detected
//
static ALT_STATUS_CODE alt_sdmmc_error_status_detect(void)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    uint32_t int_status = 0;

    // All sdmmc interrupt status caused by an error 
    uint32_t err = (  ALT_SDMMC_INT_STATUS_RE
                    | ALT_SDMMC_INT_STATUS_RCRC
                    | ALT_SDMMC_INT_STATUS_DCRC
                    | ALT_SDMMC_INT_STATUS_RTO
                    | ALT_SDMMC_INT_STATUS_DRTO
                    | ALT_SDMMC_INT_STATUS_FRUN
                    | ALT_SDMMC_INT_STATUS_HLE
                    | ALT_SDMMC_INT_STATUS_SBE
                    | ALT_SDMMC_INT_STATUS_EBE);

    int_status = alt_sdmmc_int_status_get();
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }
    
    // Checking on errors
    if (int_status & err)
    {
        status = ALT_E_ERROR;
    }

    return status;
}

//
// Read/write all data from/to buffer
//
static ALT_STATUS_CODE alt_sdmmc_transfer_helper(uint32_t * buffer,
                                                 const size_t size,
                                                 ALT_SDMMC_TMOD_t transfer_mode)
{
#ifdef LOGGER
    dprintf("\nalt_sdmmc_transfer_helper\n");
#endif

    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t data_size = size;
    bool read_freeze  = false;
    bool write_freeze = false;
    
    while (data_size > 0)
    {
#ifdef LOGGER
        dprintf("\ndata_size = %x\n", (int)data_size);
        // Error handling
#endif
        // Error checking
        status = alt_sdmmc_error_status_detect();

        if (status != ALT_E_SUCCESS)
        {
            break;
        }

        uint32_t timeout = ALT_SDMMC_TMO_WAITER;

        do
        {
            read_freeze =(transfer_mode == ALT_SDMMC_TMOD_READ)
                                            && alt_sdmmc_fifo_is_empty() == true;
            write_freeze = transfer_mode == ALT_SDMMC_TMOD_WRITE
                                            && alt_sdmmc_fifo_is_full() == true;
#ifdef LOGGER
            dprintf("\nread_freeze = %x write_freeze = %x\n", (int)read_freeze, (int)write_freeze);
#endif
            if (--timeout == 0)
            {
                status = ALT_E_TMO;
                return status;
            }
        }
        while (read_freeze || write_freeze);
        
        uint32_t level = alt_sdmmc_fifo_count();

#ifdef LOGGER
        dprintf("\nfifo level = %x\n", (int)level);
#endif

        // Top up the TX FIFO with read issues

        if (transfer_mode == ALT_SDMMC_TMOD_WRITE)
        {
            uint32_t free_space = ALT_SDMMC_FIFO_NUM_ENTRIES - level;
            free_space = MIN(data_size / 4, free_space);

            for (uint32_t i = 0; i < free_space; i++)
            {
                alt_write_word(ALT_SDMMC_DATA_ADDR, *buffer);
                ++buffer;
            }
            data_size -= free_space * 4;
        }

        // Read out the resulting received data as they come in.

        if (transfer_mode == ALT_SDMMC_TMOD_READ)
        {
            level = MIN(data_size / 4, level);

            for (uint32_t i = 0; i < level; i++)
            {
                *buffer = ALT_SDMMC_DATA_VALUE_GET(alt_read_word(ALT_SDMMC_DATA_ADDR));
                ++buffer;
            }

            data_size -= level * 4;
        }
    }

    return status;
}

//
// Fill descriptors
//
static ALT_STATUS_CODE alt_sdmmc_dma_trans_helper(uint32_t * buffer,
                                                  size_t buf_len)
{
#ifdef LOGGER
    dprintf("\nalt_sdmmc_dma_trans_helper: buf_len = %d\n",
                                                (int)buf_len);
#endif
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    //Pointer to current descriptor
    ALT_SDMMC_DMA_BUF_DESC_t *cur_dma_desc = dma_cur_descr;

    uint32_t cur_buffer = (uint32_t)buffer;
    uint32_t len_left = buf_len;

    while (len_left > 0)
    {
        //Error checking
        status = alt_sdmmc_error_status_detect();
        if (status != ALT_E_SUCCESS)
        {
            status = ALT_E_ERROR;
            break;
        }
        //If current descriptor is free then fill it
        if (cur_dma_desc->des0.fld.own == 0)
        {
            int set_len = len_left > ALT_SDMMC_DMA_SEGMENT_SIZE ? ALT_SDMMC_DMA_SEGMENT_SIZE : len_left;
            //Disable interrupt after it will be free
            cur_dma_desc->des0.fld.dic = 1;//socfpga->dma_cur_pos % 4;
            //Set If it is first part of buffer for transfer
            cur_dma_desc->des0.fld.fs = (buf_len == len_left) ? 1 : 0;
            //Set size of des2
            cur_dma_desc->des1.fld.bs1 = set_len;
            //Set address of buffer in memory
            cur_dma_desc->des2.fld.bap1 = cur_buffer;

#ifdef LOGGER
            dprintf("socfpga_setup_dma_add: des_adrdr %08X des2_paddr %08X des1_len %08X len_left %08X\n", 
                        (int)cur_dma_desc, (int)cur_buffer, (int)set_len, (int)len_left);
#endif

            //Update address buffer and buffer len
            cur_buffer += set_len;
            len_left -= set_len;
            //Set if it is last part of buffer
            cur_dma_desc->des0.fld.ld = (len_left == 0) ? 1 : 0;
            //Descriptor could be used
            cur_dma_desc->des0.fld.own = 1;
            //Currernt descriptor set sa next element 
            cur_dma_desc = (ALT_SDMMC_DMA_BUF_DESC_t *)cur_dma_desc->des3.fld.bap2_or_next;
        }

        uint32_t idmac_status = alt_sdmmc_dma_int_status_get();

        // If DMA status is as descriptor unavailable then resume transfer and clean interrupt status
        if (idmac_status & ALT_SDMMC_DMA_INT_STATUS_DU)
        {
            alt_sdmmc_poll_demand_set(0xFFFF);
            alt_sdmmc_dma_int_clear(ALT_SDMMC_DMA_INT_STATUS_ALL);
        }
        // If DMA status is another abnormal then break with error
        else if (idmac_status & ALT_SDMMC_DMA_INT_STATUS_AI)
        {
            status = ALT_E_ERROR;
            break;
        }

    }

    return status;

}

//
// Waiter of data transfer complete
//
static ALT_STATUS_CODE alt_sdmmc_data_done_waiter(void)
{
    ALT_STATUS_CODE status = ALT_E_TMO;
    uint32_t timeout = ALT_SDMMC_TMO_WAITER;

    while (--timeout)
    {
        uint32_t int_status;
        int_status = alt_sdmmc_int_status_get();

        // Error checking
        if (alt_sdmmc_error_status_detect() != ALT_E_SUCCESS)
        {
            status = ALT_E_ERROR;
            break;
        }

        uint32_t idmac_status = alt_sdmmc_dma_int_status_get();

        // If DMA status is abnormal then transfer complete with error
        if (idmac_status & ALT_SDMMC_DMA_INT_STATUS_AI)
        {
            status = ALT_E_ERROR;
            break;
        }
        // Data transfer over caused by complete transfer operation
        if (int_status & ALT_SDMMC_INT_STATUS_DTO)
        {
            alt_sdmmc_int_clear(ALT_SDMMC_INT_STATUS_DTO);
            status = ALT_E_SUCCESS;
            break;
        }
    }

    timeout = ALT_SDMMC_TMO_WAITER;
    while (!alt_sdmmc_is_idle() && timeout--)
        ;
    if (timeout == 0)
    {
        status = ALT_E_TMO;
    }

    return status;
}


//
// Waiter of clock command complete
//
static ALT_STATUS_CODE alt_sdmmc_clock_waiter(void)
{
    ALT_STATUS_CODE status = ALT_E_TMO;
    uint32_t timeout = ALT_SDMMC_TMO_WAITER;
    
    while (--timeout)
    {
        uint32_t cmd_register = alt_read_word(ALT_SDMMC_CMD_ADDR);
        
        // Error checking
        if (alt_sdmmc_error_status_detect() != ALT_E_SUCCESS)
        {
            status = ALT_E_ERROR;
            break;
        }

        // Only for clock command detect complete operation by 0 in start_cmd bit of cmd register
        if (ALT_SDMMC_CMD_START_CMD_GET(cmd_register) == ALT_SDMMC_CMD_START_CMD_E_NOSTART)
        {
            status = ALT_E_SUCCESS;
            break;
        }
    }
    return status;
}

//
// Waiter of command complete
//
static ALT_STATUS_CODE alt_sdmmc_cmd_waiter(void)
{
    ALT_STATUS_CODE status = ALT_E_TMO;
    uint32_t timeout = ALT_SDMMC_TMO_WAITER;
    
    while (--timeout)
    {
        uint32_t int_status;
        int_status = alt_sdmmc_int_status_get();

        // Error checking
        if (alt_sdmmc_error_status_detect() != ALT_E_SUCCESS)
        {
            status = ALT_E_ERROR;
            break;
        }
        
        //Check command done
        if (int_status & ALT_SDMMC_INT_STATUS_CMD)
        {
            alt_sdmmc_int_clear(ALT_SDMMC_INT_STATUS_CMD);
            status = ALT_E_SUCCESS;
            break;
        }
    }
    return status;
}

//
// Read SRC register from card and read supported bus width
//
static ALT_STATUS_CODE alt_sdmmc_card_scr_get(uint64_t *scr_reg)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
#ifdef LOGGER
    uint32_t response = 0;
#endif
    
    uint16_t prev_blk_size = 0;
    // Save current block size and change it
    prev_blk_size = alt_sdmmc_block_size_get();
    alt_sdmmc_block_size_set(8);
    alt_sdmmc_byte_count_set(8);

    // Activate ACMD commands
    status = alt_sdmmc_command_send(ALT_SDMMC_APP_CMD, rca_number, NULL);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_APP_CMD response = %x\n", (int)response);
#endif
    
    // Send request for read SRC register
    status = alt_sdmmc_command_send(ALT_SD_SEND_SCR, 0x0, NULL);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }
    
#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SD_SEND_SCR responce = %x\n", (int)response);
#endif

    // Read SRC register
    status = alt_sdmmc_transfer_helper((uint32_t*)scr_reg, 8, ALT_SDMMC_TMOD_READ);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    // Transfer complete
    status = alt_sdmmc_data_done_waiter();
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    dprintf("\nALT_SD_SEND_SCR data = ");
    uint8_t* scr_buf_8 = (uint8_t*)scr_reg;
    for (int count = 0; count < 8; count++)
    {
        dprintf("%02x", scr_buf_8[count]);
    }
    dprintf("\n");
#endif

    // Re-change block size
    alt_sdmmc_block_size_set(prev_blk_size);

    return status;
}

//
// Set sdmmc card width
//
ALT_STATUS_CODE alt_sdmmc_card_bus_width_set(const ALT_SDMMC_BUS_WIDTH_t width)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint64_t scr_reg;
    
    // Read SRC register
    status = alt_sdmmc_card_scr_get(&scr_reg);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    uint8_t * scr_buf_8 = (uint8_t*)&scr_reg;
    // Get supported bus width
    uint32_t supported_bus_width = scr_buf_8[1] & 0xF;

#ifdef LOGGER
    dprintf("\nbus_width_supported = %02x\n", (int)supported_bus_width);
#endif

    if ((supported_bus_width & width) == 0)
    {
        return ALT_E_BAD_ARG;
    }

    uint32_t set_width_arg;
    switch (width)
    {
    case ALT_SDMMC_BUS_WIDTH_8:
        set_width_arg = 0x3;
        break;
    case ALT_SDMMC_BUS_WIDTH_4:
        set_width_arg = 0x2;
        break;
    case ALT_SDMMC_BUS_WIDTH_1:
        set_width_arg = 0x0;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

#ifdef LOGGER
    uint32_t response = 0;
#endif

    // Activate ACMD commands
    status = alt_sdmmc_command_send(ALT_SDMMC_APP_CMD, rca_number, NULL);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_APP_CMD response = %x\n", (int)response);
#endif
    
    // Send new card bus width
    status = alt_sdmmc_command_send(ALT_SD_SET_BUS_WIDTH, set_width_arg, NULL);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SD_SET_BUS_WIDTH responce = %x\n", (int)response);
#endif
    
    // Set new bus width in controller register
    alt_sdmmc_bus_width_set(width);
    
    return status;
}

//
// Set block size
//
ALT_STATUS_CODE alt_sdmmc_card_block_size_set(const uint16_t block_size)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    
    // Send new block size to card
    status = alt_sdmmc_command_send(ALT_SDMMC_SET_BLOCKLEN, block_size, NULL);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    uint32_t response;

    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_SET_BLOCKLEN response = %x\n", (int)response);
#endif

    // Set new block size in controller register
    alt_sdmmc_block_size_set(block_size);

    return status;
}

//
// Enumerated Card Stack ident sdio io only
//
static ALT_STATUS_CODE alt_sdmmc_card_ident_io_only(ALT_SDMMC_CARD_INFO_t *card_info)
{
#ifdef LOGGER
    dprintf("\nalt_sdmmc_card_ident_io_only\n");
#endif
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t int_status = 0;
    uint32_t response = 0;
    // Enumerated Card Stack p.2a - 2b
    // Activates the card's initialization process.
    status = alt_sdmmc_command_send(ALT_SDMMC_SEND_OP_COND, 0x0, &response);
    if (status != ALT_E_SUCCESS)
    {
        int_status = alt_sdmmc_int_status_get();
        if (int_status & ALT_SDMMC_INT_STATUS_RTO)
        {
            return ALT_E_SUCCESS;
        }
        else
        {
            return status;
        }
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_SEND_OP_COND_1 = %x\n", (int)response);
#endif

    // Enumerated Card Stack p.2c
    status = alt_sdmmc_command_send(ALT_SDMMC_SEND_OP_COND, 0x100000, &response);
    if (status != ALT_E_SUCCESS)
    {
        int_status = alt_sdmmc_int_status_get();
        if (int_status & ALT_SDMMC_INT_STATUS_RTO)
        {
            return ALT_E_SUCCESS;
        }
        else
        {
            return status;
        }
    }
    
#ifdef LOGGER
    dprintf("\nALT_SDMMC_SEND_OP_COND_2 response = %x\n", (int)response);
#endif
    // Enumerated Card Stack p.2d
    bool is_sdio_combo = response & (1 << 27);
    card_info->card_type = (is_sdio_combo) 
                           ? ALT_SDMMC_CARD_TYPE_NOTDETECT
                           : ALT_SDMMC_CARD_TYPE_SDIOIO;

    return ALT_E_SUCCESS;
}

//
// Enumerated Card Stack ident sdhc type
//
static ALT_STATUS_CODE alt_sdmmc_card_ident_sdhc(ALT_SDMMC_CARD_INFO_t *card_info)
{
#ifdef LOGGER
    dprintf("\nalt_sdmmc_card_ident_sdhc\n");
#endif
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t int_status = 0;
    uint32_t response = 0;
    // Resets all cards to Idle State
    status = alt_sdmmc_command_send(ALT_SDMMC_GO_IDLE_STATE, 0x0, &response);
    if (status != ALT_E_SUCCESS)
    {
        int_status = alt_sdmmc_int_status_get();
        if (int_status & ALT_SDMMC_INT_STATUS_RTO)
        {
            return ALT_E_SUCCESS;
        }
        else
        {
            return status;
        }
    }
    
#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_GO_IDLE_STATE response = %x\n", (int)response);
#endif
    
    // Enumerated Card Stack p.3a
    // For only SDC V2. Check voltage range.
    status = alt_sdmmc_command_send(ALT_SDMMC_IF_COND, 0x1AA, &response);
    if (status != ALT_E_SUCCESS)
    {
        int_status = alt_sdmmc_int_status_get();
        if (int_status & ALT_SDMMC_INT_STATUS_RTO)
        {
            return ALT_E_SUCCESS;
        }
        else
        {
            return status;
        }
    }
    
    alt_sdmmc_read_short_response(&response);
#ifdef LOGGER
    dprintf("\nALT_SDMMC_IF_COND response = %x\n", (int)response);
#endif
    
    if (response != 0x1AA)
    {
        return ALT_E_ERROR;
    }

    // Indicates to the card that the next command is an 
    // application specific command rather than a 
    // standard command
    status = alt_sdmmc_command_send(ALT_SDMMC_APP_CMD, 0x0, &response);
    if (status != ALT_E_SUCCESS)
    {
        int_status = alt_sdmmc_int_status_get();
        if (int_status & ALT_SDMMC_INT_STATUS_RTO)
        {
            return ALT_E_SUCCESS;
        }
        else
        {
            return status;
        }
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_APP_CMD response = %x\n", (int)response);
#endif
    
    // Enumerated Card Stack p.3c
    // Asks the accessed card to send its operating condition 
    // register (OCR) con tent in the response on the CMD 
    // line. 
    status = alt_sdmmc_command_send(ALT_SD_SEND_OP_COND, 0x40FF8000, &response);
    if (status != ALT_E_SUCCESS)
    {
        int_status = alt_sdmmc_int_status_get();
        if (int_status & ALT_SDMMC_INT_STATUS_RTO)
        {
            return ALT_E_SUCCESS;
        }
        else
        {
            return status;
        }
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SD_SEND_OP_COND responce = %x\n", (int)response);
#endif
    
    //Enumerated Card Stack p.3d
    card_info->card_type = ALT_SDMMC_CARD_TYPE_SDHC;

    return status;
}

//
//Enumerated Card Stack ident sd type
//
static ALT_STATUS_CODE alt_sdmmc_card_ident_sd(ALT_SDMMC_CARD_INFO_t *card_info)
{
#ifdef LOGGER
    dprintf("\nalt_sdmmc_card_ident_sd\n");
#endif
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t int_status = 0;
#ifdef LOGGER
    uint32_t response = 0;
#endif
    // Enumerated Card Stack p.3e
    // Indicates to the card that the next command is an 
    // application specific command rather than a 
    // standard command 
    status = alt_sdmmc_command_send(ALT_SDMMC_APP_CMD, 0x0, NULL);
    if (status != ALT_E_SUCCESS)
    {
        int_status = alt_sdmmc_int_status_get();
        if (int_status & ALT_SDMMC_INT_STATUS_RTO)
        {
            return ALT_E_SUCCESS;
        }
        else
        {
            return status;
        }
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_APP_CMD response = %x\n", (int)response);
#endif
    
    // Asks the accessed card to send its operating condition 
    // register (OCR) con tent in the response on the CMD 
    // line. 
    status = alt_sdmmc_command_send(ALT_SD_SEND_OP_COND, 0x00FF8000, NULL);
    if (status != ALT_E_SUCCESS)
    {
        int_status = alt_sdmmc_int_status_get();
        if (int_status & ALT_SDMMC_INT_STATUS_RTO)
        {
            return ALT_E_SUCCESS;
        }
        else
        {
            return status;
        }
    }
    
#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SD_SEND_OP_COND responce = %x\n", (int)response);
#endif
    
    // Enumerated Card Stack p.3f
    card_info->card_type = ALT_SDMMC_CARD_TYPE_SD;

    return status;
}

//
// Enumerated Card Stack enumarete sd cart type
//
static ALT_STATUS_CODE alt_sdmmc_card_enum_sd(ALT_SDMMC_CARD_INFO_t *card_info)
{
#ifdef LOGGER
    dprintf("\nalt_sdmmc_card_enum_sd\n");
#endif
    ALT_STATUS_CODE status = ALT_E_SUCCESS;

    uint32_t clk_div = clock_freq / (2 * 400000);

    status = alt_sdmmc_card_clk_div_set(clk_div);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }
    status = alt_sdmmc_card_clk_enable(false);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }
    
    uint32_t response = 0;
    // Resets all cards to Idle State
    status = alt_sdmmc_command_send(ALT_SDMMC_GO_IDLE_STATE, 0x0, &response);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }
    
#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_GO_IDLE_STATE response = %x\n", (int)response);
#endif
    // For only SDC V2. Check voltage range.
    status = alt_sdmmc_command_send(ALT_SDMMC_IF_COND, 0x1AA, &response);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_IF_COND response = %x\n", (int)response);
#endif

/*    OCR Bit VDD Voltage Window 
           0-3          Reserved 
            4             1.6-1.7 
            5             1.7-1.8 
            6             1.8-1.9 
            7             1.9-2.0 
            8             2.0-2.1 
            9             2.1-2.2 
            10           2.2-2.3 
            11           2.3-2.4 
            12           2.4-2.5 
            13           2.5-2.6 
            14           2.6-2.7 
            15           2.7-2.8 
            16           2.8-2.9 
            17           2.9-3.0 
            18           3.0-3.1 
            19           3.1-3.2 
            20           3.2-3.3 
            21           3.3-3.4 
            22           3.4-3.5 
            23           3.5-3.6 
          24-29       Reserved 
            30          High capacity card
            31          Card power up status bit (busy)
*/
    uint32_t ocr_reg = 0xFF8000;

    if (card_info->card_type == ALT_SDMMC_CARD_TYPE_SDHC)
    {
        ocr_reg |= (1 << 30);
    }

    do
    {
        status = alt_sdmmc_command_send(ALT_SDMMC_APP_CMD, 0x0, &response);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }

#ifdef LOGGER
        alt_sdmmc_read_short_response(&response);
        dprintf("\nALT_SDMMC_APP_CMD response = %x\n", (int)response);
#endif
        
        volatile uint32_t timeout = 1000000;

        // Wait while sdmmc module is reseting
        while (timeout--)
            ;
        status = alt_sdmmc_command_send(ALT_SD_SEND_OP_COND, 0x40FF8000, &response);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }

        alt_sdmmc_read_short_response(&response);
#ifdef LOGGER
        dprintf("\nALT_SD_SEND_OP_COND response = %x\n", (int)response);
#endif
    }
    while ((response & (1UL << 31)) == 0);
    
    //Asks any card to send their CID numbers on the CMD line.
    //(Any card that is connected to the host will respond.)
    status = alt_sdmmc_command_send(ALT_SDMMC_ALL_SEND_CID, 0x0, &response);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_ALL_SEND_CID response = %x\n", (int)response);
#endif
    // Asks the card to publish a new relative address (RCA).
    status = alt_sdmmc_command_send(ALT_SDMMC_SET_RELATIVE_ADDR, 0x0, &response);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    alt_sdmmc_read_short_response(&response);
#ifdef LOGGER
    dprintf("\nALT_SDMMC_SET_RELATIVE_ADDR responce = %x\n", (int)response);
#endif
    
    uint32_t RCA_number = response & 0xFFFF0000;
    rca_number = RCA_number;

    // Addressed card sends its card identification (CID) on the CMD line.
    status = alt_sdmmc_command_send(ALT_SDMMC_SEND_CID, rca_number, &response);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_SEND_CID responce = %x\n", (int)response);
#endif

    // Addressed card sends its card-specific data (CSD) 
    // on the CMD line.
    status = alt_sdmmc_command_send(ALT_SDMMC_SEND_CSD, rca_number, &response);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_SEND_CSD responce = %x\n", (int)response);
#endif

    ALT_SDMMC_RESPONSE_t response_long;
    alt_sdmmc_read_long_response(&response_long);
    static const uint32_t tran_speed_mul_x10[] = { 0, 10, 12, 13, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 70, 80 };
    static const uint32_t freq_unit[] = { 100000, 1000000, 10000000, 100000000 };
//    card_info->max_r_blkln = pow(2, ALT_SDMMC_CSD_MAX_R_BLK_GET(response_long.resp2));
//    card_info->max_w_blkln = pow(2, ALT_SDMMC_CSD_MAX_W_BLK_GET(response_long.resp0));
    card_info->max_r_blkln = 1 << ALT_SDMMC_CSD_MAX_R_BLK_GET(response_long.resp2);
    card_info->max_w_blkln = 1 << ALT_SDMMC_CSD_MAX_W_BLK_GET(response_long.resp0);
    card_info->partial_r_allowed = ALT_SDMMC_CSD_PART_R_ALLOW_GET(response_long.resp2);
    card_info->partial_w_allowed = ALT_SDMMC_CSD_PART_W_ALLOW_GET(response_long.resp0);
    uint32_t rate_unit = ALT_SDMMC_CSD_SPEED_RATE_GET(response_long.resp3);
    uint32_t time_val = ALT_SDMMC_CSD_SPEED_TIME_GET(response_long.resp3);
    if ((time_val != 0) && (rate_unit <= 3))
    {
        // uint32_t speed_rate = (rate_unit == 0) ? 100 : pow(10, rate_unit - 1) * 1000;
        uint32_t speed_rate = freq_unit[rate_unit];
        card_info->xfer_speed = speed_rate * tran_speed_mul_x10[time_val] / 10;
    }
    else
    {
        return ALT_E_ERROR;
    }

    // Command toggles a card between the Stand-by 
    // and Transfer states or between the Programming 
    // and Disconnect state
    status = alt_sdmmc_command_send(ALT_SDMMC_SEL_DES_CARD, rca_number, &response);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_SEL_DES_CARD responce = %x\n", (int)response);
#endif

    // Addressed card sends its status register
    status = alt_sdmmc_command_send(ALT_SDMMC_SEND_STATUS, rca_number, &response);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    alt_sdmmc_read_short_response(&response);
    dprintf("\nALT_SDMMC_SEND_STATUS responce = %x\n", (int)response);
#endif

    return status;
}

//
// Enumerated Card Stack
//
ALT_STATUS_CODE alt_sdmmc_card_identify(ALT_SDMMC_CARD_INFO_t *card_info)
{
#ifdef LOGGER
    dprintf("\nalt_sdmmc_card_identify\n");
#endif
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    card_info->card_type = ALT_SDMMC_CARD_TYPE_NOTDETECT;

    //Enumerated Card Stack p.1
    alt_sdmmc_bus_width_set(ALT_SDMMC_BUS_WIDTH_1);

    if (status == ALT_E_SUCCESS)
    {
        status = alt_sdmmc_card_ident_io_only(card_info);
        // If card is identified as SDIO IO only or SDIO COMBO then prepare it
        if (card_info->card_type != ALT_SDMMC_CARD_TYPE_NOTDETECT && status == ALT_E_SUCCESS)
        {
            return status;
        }
    }
    if (status == ALT_E_SUCCESS)
    {
        status =  alt_sdmmc_card_ident_sdhc(card_info);
        if (card_info->card_type != ALT_SDMMC_CARD_TYPE_NOTDETECT && status == ALT_E_SUCCESS)
        {
            // If card is identified as SDHC then prepare it
            status = alt_sdmmc_card_enum_sd(card_info);
            return status;
        }
    }
    if (status != ALT_E_SUCCESS)
    {
        status =  alt_sdmmc_card_ident_sd(card_info);
        if (card_info->card_type != ALT_SDMMC_CARD_TYPE_NOTDETECT && status == ALT_E_SUCCESS)
        {
            // If card is identified as SD card then prepare it
            status = alt_sdmmc_card_enum_sd(card_info);
            return status;
        }
    }

    return status;
}

//
// Send the a command and command argument to the card and optionally return the
// command response.
//
ALT_STATUS_CODE alt_sdmmc_command_send(ALT_SDMMC_CMD_INDEX_t command, 
                                       uint32_t command_arg, uint32_t *response)
{
    const ALT_SDMMC_CMD_CONFIG_t * cmd_cfg = NULL;

    bool found = false;

    if (command == ALT_SDMMC_CLK_INDEX)
    {
        cmd_cfg = &cmd_clock_cfg;
        found = true;
    }

    for (uint32_t counter = 0; counter < ARRAY_COUNT(cmd_default_cfg); counter++)
    {
        if (found == true)
        {
            break;
        }
        if (cmd_default_cfg[counter].cmd_index == command)
        {
            cmd_cfg = &cmd_default_cfg[counter];
            found = true;
        }
    }

    if (found == false)
    {
        return ALT_E_BAD_ARG;
    }

    if (cmd_cfg->wait_prvdata_complete)
    {
        uint32_t timeout = ALT_SDMMC_TMO_WAITER;
        while (alt_sdmmc_is_busy() && timeout--)
            ;
    }

    // Create interrupt mask by command configurations
    uint32_t int_mask = ALT_SDMMC_INT_STATUS_RE             // Response error
                      | ALT_SDMMC_INT_STATUS_RTO            // Response timeout
                      | ALT_SDMMC_INT_STATUS_CD             // Card detect (CD) interrupt
                      | ALT_SDMMC_INT_STATUS_HLE            // Hardware Locked Write Error
                      | ALT_SDMMC_INT_STATUS_CMD;           // Command done (CD) interrupt

    if (cmd_cfg->data_expected == true)
    {
        int_mask |= ALT_SDMMC_INT_STATUS_DTO                // Data transfer over
                  | ALT_SDMMC_INT_STATUS_RCRC               // Response CRC error
                  | ALT_SDMMC_INT_STATUS_DCRC               // Data CRC error
                  | ALT_SDMMC_INT_STATUS_HTO                // Data starvation by host timeout
                  | ALT_SDMMC_INT_STATUS_FRUN               // FIFO underrun/overrun error
                  | ALT_SDMMC_INT_STATUS_EBE;               // End-bit error
        
        if (cmd_cfg->write_active == ALT_SDMMC_TMOD_WRITE)
        {
            int_mask |= ALT_SDMMC_INT_STATUS_TXDR           // Transmit FIFO data request (TXDR)
                      | ALT_SDMMC_INT_STATUS_HLE;           // Hardware locked write error (HLE)
        }
        else
        {
            int_mask |= ALT_SDMMC_INT_STATUS_RXDR           // Receive FIFO data request (RXDR)
                       |ALT_SDMMC_INT_STATUS_SBE;           // Start-bit error (SBE)
        }
        
    }
    
    alt_sdmmc_int_disable(ALT_SDMMC_INT_STATUS_ALL);
    // Reset all possible interrupts
    alt_sdmmc_int_clear(ALT_SDMMC_INT_STATUS_ALL);
    // Interrupts enable
    alt_sdmmc_int_enable(int_mask);
    // Setup the Argument Register and send CMD
    alt_sdmmc_cmd_arg_set(command_arg);

    // Set command configuraions
    alt_sdmmc_cmd_set(command, cmd_cfg, false);
    // Send commnd
    alt_sdmmc_cmd_set(command, cmd_cfg, true);

#ifdef LOGGER
    uint32_t state = (uint32_t)ALT_SDMMC_STAT_CMD_FSM_STATES_GET(alt_read_word(ALT_SDMMC_STAT_ADDR));
    
    uint32_t dma_state = (uint32_t)ALT_SDMMC_IDSTS_FSM_GET(alt_read_word(ALT_SDMMC_IDSTS_ADDR));

    dprintf("\nstate %x dma_state %x\n", (int)state, (int)dma_state);
    dprintf("\nCMD = %d ARG = %x\n", (int)command, (int)command_arg);
#endif

    ALT_STATUS_CODE status = 0;
    if (cmd_cfg->update_clock_registers_only == true)
    {
        //Wait for complete clock update command
        status = alt_sdmmc_clock_waiter();
#ifdef LOGGER
        if (status == ALT_E_TMO)
        {
            dprintf("\nTIMEOUT\n");
        }
#endif
        return status;
    }

    //Wait for complete
    if (   alt_sdmmc_is_dma_enabled() == ALT_E_FALSE
        || cmd_cfg->data_expected == false)
    {
        status = alt_sdmmc_cmd_waiter();
    }
#ifdef LOGGER
    if (status == ALT_E_TMO)
    {
        dprintf("\nTIMEOUT\n");
    }
#endif
    if (status == ALT_E_SUCCESS)
    {
        alt_sdmmc_read_short_response(response);
    }
    
    return status;
}

static ALT_STATUS_CODE alt_sdmmc_transfer(uint32_t start_addr,
                                          uint32_t buffer[],
                                          const size_t buf_len,
                                          ALT_SDMMC_TMOD_t transfer_mode)
{
    if (buf_len == 0)
    {
        return ALT_E_SUCCESS;
    }

    if (!alt_sdmmc_is_idle())
    {
        return ALT_E_ERROR;
    }

    uint16_t block_size = alt_sdmmc_block_size_get();

    if (   (start_addr % block_size != 0) 
        || (buf_len    % block_size != 0))
    {
        return ALT_E_BAD_ARG;
    }

    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    // Number of block to transfer
    uint32_t block_count = buf_len / block_size;
    // New count of reading byte
    uint32_t byte_count = block_count * block_size;

    // reset FIFO
    status = alt_sdmmc_fifo_reset();
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }
    
    // reset DMA
    status = alt_sdmmc_dma_reset();
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    alt_sdmmc_byte_count_set(byte_count);
    alt_sdmmc_card_rd_threshold_enable(0x80);

    uint32_t cmd_index = 0;
    if (buf_len == block_size)
    {
        cmd_index = (transfer_mode == ALT_SDMMC_TMOD_READ) 
                                        ? ALT_SDMMC_READ_SINGLE_BLOCK 
                                        : ALT_SDMMC_WRITE_BLOCK;
    }
    else
    {
        cmd_index = (transfer_mode == ALT_SDMMC_TMOD_READ) 
                                        ? ALT_SDMMC_READ_MULTIPLE_BLOCK 
                                        : ALT_SDMMC_WRITE_MULTIPLE_BLOCK;
    }

    if (alt_sdmmc_is_dma_enabled())
    {
        // Clean descriptor chain
        alt_sdmmc_desc_chain_clear();
        
        alt_sdmmc_dma_start(dma_cur_descr, 0x0,
                            ALT_SDMMC_DMA_PBL_1, false);
        //Enable all dma interrupt status
        alt_sdmmc_dma_int_enable(ALT_SDMMC_DMA_INT_STATUS_ALL);
    }
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

#ifdef LOGGER
    dprintf("\nstart_addr = %d\n", (int)start_addr);
#endif

    //Send transfer command
    status = alt_sdmmc_command_send((ALT_SDMMC_CMD_INDEX_t)cmd_index, start_addr / block_size, NULL);
    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    //Send or read data
    if (alt_sdmmc_is_dma_enabled())
    {
        //Fill descriptors
        status = alt_sdmmc_dma_trans_helper(buffer, byte_count);
    }
    else
    {
        status = alt_sdmmc_transfer_helper(buffer, byte_count, transfer_mode);
    }

    if (status != ALT_E_SUCCESS)
    {
        return status;
    }

    //Wait for data transfer complete
    status = alt_sdmmc_data_done_waiter();

    return status;
}

//
// This function performs SDMMC write.
//
ALT_STATUS_CODE alt_sdmmc_write(void *dest, void *src, const size_t size)
{
    return alt_sdmmc_transfer((uint32_t)dest, src, size, ALT_SDMMC_TMOD_WRITE);
}

//
// This function performs SDMMC read.
//
ALT_STATUS_CODE alt_sdmmc_read(void *dest, void *src, const size_t size)
{
    return alt_sdmmc_transfer((uint32_t)src, dest, size, ALT_SDMMC_TMOD_READ);
}
