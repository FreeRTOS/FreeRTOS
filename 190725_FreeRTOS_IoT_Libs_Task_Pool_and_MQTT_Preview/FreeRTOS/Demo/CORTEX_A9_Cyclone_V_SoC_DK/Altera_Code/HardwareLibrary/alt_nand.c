/******************************************************************************
*
* alt_nand.c - API for the Altera SoC FPGA NAND device.
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

#include "hwlib.h"
#include "alt_clock_manager.h"
#include "alt_nand_flash.h"
#include "socal/alt_nand.h"
#include "socal/alt_rstmgr.h"
#include "socal/alt_sysmgr.h"
#include "socal/hps.h"
#include "socal/socal.h"
#include "alt_nand_private.h"
//#include "denali_flash_regs.h"
#include <stdbool.h>
#include <string.h>
#include <stdio.h>

static int s_nand_is_interrupt_enabled = false;
static uint32_t g_nand_interrup_status_register_poll_counter_limit;
static nand_interrupt_handler_t    s_nand_interrupt_handler = NULL;
uint32_t alt_nand_number_blocks_of_plane_get(void);

static __inline uint32_t alt_nand_compose_map01_cmd_addr(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr);
static __inline uint32_t alt_nand_get_interrupt_status_register_addr(const uint32_t bank);
static __inline uint32_t alt_nand_get_interrupt_enable_register_addr(const uint32_t bank);
static __inline uint32_t alt_nand_get_device_reset_register_bank(const uint32_t bank);

uint32_t  nand_read_register(const uint32_t offset);

static uint32_t real_table[ALT_HHP_NAND_NUM_OF_BLOCK_TOTAL/32];
alt_nand_bad_block_table_t  nand_bad_block_table = real_table;

ALT_NAND_MGR_t nand_io = 
{    
        (ALT_NAND_CFG_raw_t*)ALT_NAND_CFG_ADDR, 
        (ALT_NAND_PARAM_raw_t*)ALT_NAND_PARAM_ADDR,
        (ALT_NAND_STAT_raw_t*)ALT_NAND_STAT_ADDR,
        (ALT_NAND_ECC_raw_t*)ALT_NAND_ECC_ADDR,
        (ALT_NAND_DMA_raw_t*)ALT_NAND_DMA_ADDR,
        (uint32_t *)ALT_NANDDATA_ADDR,              /*control_address */   
        ALT_CAST(uint32_t *, (ALT_CAST(char *, (ALT_NANDDATA_ADDR)) + 0x10))
};

ALT_NAND_MGR_t * nand = &nand_io; 

FLASH_CHARACTERIZATION_t memory =
{
    /*manufacturer id             */  ALT_HHP_NAND_MANUFACTURER_ID,
    /*device_id                   */  ALT_HHP_NAND_DEVICE_ID,
    /*device_param_0              */  0,
    /*device_param_1              */  0,
    /*device_param_2              */  0,
    /*page_size                   */  ALT_HHP_NAND_PAGE_SIZE,
    /*spare_size                  */  ALT_HHP_NAND_SPARE_SIZE,
    /*revision                    */  ALT_HHP_NAND_REVISION,
    /*onfi_device_feature         */  0,
    /*onfi_optional_commands      */  0,
    /*onfi_timing_mode            */  0,
    /*onfi_pgm_cache_timing_mode  */  0,
    /*onfi_compliant              */  1,
    /*onfi_device_no_of_luns      */  0,
    /*onfi_device_no_of_blocks_per_lun  */  0,
    /*features                    */  0,

    /*number_of_planes            */  ALT_HHP_NAND_NUMBER_OF_PLANES,
    /*pages_per_block             */  ALT_HHP_NAND_PAGES_PER_BLOCK,
    /*device_width                */  ALT_HHP_NAND_DEVICE_WIDTH,
    /*block_size                  */  ALT_HHP_NAND_PAGES_PER_BLOCK * ALT_HHP_NAND_PAGE_SIZE,
    /*spare_area_skip_bytes       */  ALT_HHP_NAND_SPARE_SKIP,
    /*first block of next plane   */  ALT_HHP_NAND_FIRST_BLOCK_OF_NEXT_PLANE,
    /*page_size_in_32             */  ALT_HHP_NAND_PAGE_SIZE / sizeof(uint32_t),
    /*block_shift                 */  ALT_HHP_NAND_BLOCK_SHIFT,
    /*dma_burst_length            */  0,
    /*ecc_correct                 */  ALT_HHP_NAND_ECC_CORRECT,
};

FLASH_CHARACTERIZATION_t * flash = &memory;

ALT_STATUS_CODE alt_nand_flash_init(const bool load_block0_page0,
                                    const bool page_size_512,
                                    alt_nand_flash_custom_init_t custom_init,
                                    void *user_arg)
{
    ALT_NAND_CFG_raw_t * cfg = (ALT_NAND_CFG_raw_t *)(nand->cfg);
    ALT_NAND_PARAM_raw_t * param = (ALT_NAND_PARAM_raw_t *)(nand->param);
    ALT_STATUS_CODE ret = ALT_E_SUCCESS;
    uint32_t x;

    alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_NAND_SET_MSK);
    alt_nand_set_sysmgr_bootstrap_value( ALT_NAND_BOOTSTRAP_INHIBIT_INIT_DISABLE,
                                         load_block0_page0,  
                                         page_size_512,
                                         ALT_NAND_BOOTSTRAP_TWO_ROW_ADDR_CYCLES_DISABLE
                                       );
    alt_clrbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_NAND_SET_MSK);
                             
    g_nand_interrup_status_register_poll_counter_limit = (uint32_t)(-1);

    ret = (*custom_init)(user_arg);
    if (ret == ALT_E_RESERVED)    // no custom initialization being done
    {
        alt_nand_reset_bank(0);
    }

    // Read flash device characterization 
    flash->manufacturer_id = alt_read_word(&param->manufacturer_id);
    flash->device_id = alt_read_word(&param->device_id);
    flash->device_param_0 = alt_read_word(&param->device_param_0);
    flash->device_param_1 = alt_read_word(&param->device_param_1);
    flash->device_param_2 = alt_read_word(&param->device_param_2);
    flash->page_size = alt_read_word(&cfg->device_main_area_size);
    flash->spare_size = alt_read_word(&cfg->device_spare_area_size);
    flash->revision = alt_read_word(&param->revision);
    flash->onfi_device_features = alt_read_word(&param->onfi_device_features);
    flash->onfi_optional_commands = alt_read_word(&param->onfi_optional_commands);
    flash->onfi_timing_mode = alt_read_word(&param->onfi_timing_mode);
    flash->onfi_pgm_cache_timing_mode = alt_read_word(&param->onfi_pgm_cache_timing_mode);
    flash->onfi_compliant = alt_read_word(&param->onfi_device_no_of_luns) >> 8;
    flash->onfi_device_no_of_luns = alt_read_word(&param->onfi_device_no_of_luns) & 0xff;
    x = alt_read_word(&param->onfi_device_no_of_blocks_per_lun_l);
    flash->onfi_device_no_of_blocks_per_lun = (alt_read_word(&param->onfi_device_no_of_blocks_per_lun_u) << 16) + x;
    flash->features = alt_read_word(&param->features);
    x = alt_read_word(&cfg->number_of_planes);
    switch (x)
    {
        case 0:
             flash->number_of_planes = 1;
             break;
        case 1: 
             flash->number_of_planes = 2;
             break;
        case 3: 
             flash->number_of_planes = 4;
             break;
        case 7: 
             flash->number_of_planes = 4;
             break;
        default: 
             flash->number_of_planes = 1;
             break;
    }
    flash->pages_per_block = alt_read_word(&cfg->pages_per_block);

    // Device Width register content should automatically update SystemManager:NandGrp:BootStrap:page512 or page512x16 bit
    flash->device_width = alt_read_word(&cfg->device_width);

    // Set the skip bytes and then read back the result.
    alt_write_word(&cfg->spare_area_skip_bytes, flash->spare_area_skip_bytes);
    flash->spare_area_skip_bytes = alt_read_word(&cfg->spare_area_skip_bytes);
    flash->block_size = flash->pages_per_block * flash->page_size;

    flash->first_block_of_next_plane = alt_read_word(&cfg->first_block_of_next_plane);
    // Set flash config based on read config
    flash->page_size_32 = flash->page_size / sizeof(uint32_t);

    flash->page_shift = ffs32(flash->page_size);
    flash->block_shift = ffs32(flash->pages_per_block);
  
    alt_nand_rb_pin_mode_clear(ALT_NAND_CFG_RB_PIN_END_BANK0_SET_MSK);
    alt_nand_flash_ecc_disable();
    alt_write_word(&cfg->first_block_of_next_plane,alt_nand_number_blocks_of_plane_get());
    flash->first_block_of_next_plane  = alt_read_word(&cfg->first_block_of_next_plane);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_nand_flash_uninit(void)
{
    alt_nand_flash_ecc_disable();
    alt_nand_dma_set_enabled( false );
    return ALT_E_SUCCESS;
}

#define ALT_NAND_INVALID_FLASH_ADDR     0xffffffff

uint32_t alt_nand_block_address_get(const uint32_t addr)
{
    return addr >> (flash->block_shift + flash->page_shift); 
}

uint32_t alt_nand_page_address_get(const uint32_t addr)
{
    return addr >> flash->page_shift & ((1 << flash->block_shift) - 1); 
}

uint32_t alt_nand_flash_addr_compose(const uint32_t block_num, 
                                     const uint32_t page_num)
{
    return (block_num << (flash->block_shift + flash->page_shift)) + (page_num << flash->page_shift);
}

ALT_STATUS_CODE alt_nand_flash_block_erase(const uint32_t block_addr,
                                           alt_nand_callback_t completion_callback,
                                           void *completion_arg)
{
    int32_t            ret = ALT_E_SUCCESS;
    int32_t            res = -1;
    uint32_t        bank = alt_nand_bank_get();
    const uint32_t    interrup_status_register = alt_nand_get_interrupt_status_register_addr( bank );
    const uint32_t    addr = alt_nand_compose_map10_cmd_addr( bank, block_addr, 0 );
    
    alt_write_word(interrup_status_register, ALT_HHP_UINT32_MASK );

    alt_nand_write_indirect( addr, ALT_HHP_NAND_10_OP_ERASE_BLOCK );
    
    res = alt_nand_poll_for_interrupt_status_register(interrup_status_register,  
                                                  ALT_NAND_INT_STATUS_TIME_OUT  | 
                                                  ALT_NAND_INT_STATUS_ERASE_COMP | 
                                                  ALT_NAND_INT_STATUS_ERASE_FAIL);

    if (!(res & ALT_NAND_STAT_INTR_STAT0_ERASE_COMP_SET_MSK)) 
    {
        //printf("FAIL: erasing not complete. (%08lX, %ld)\n", res, block_addr);
        ret = ALT_E_ERROR;
    }

    return ret;
}

ALT_STATUS_CODE alt_nand_flash_page_read(const uint32_t page_addr, 
                                         const uint32_t num_pages,
                                         void *dest,
                                         const uint32_t dest_size)
{
    // currently only one page
    uint32_t bank  = alt_nand_bank_get();     
    uint32_t page  = alt_nand_page_address_get(page_addr);
    uint32_t block = alt_nand_block_address_get(page_addr);

    return alt_nand_full_page_read_with_map10( bank, block, page, (uint32_t *)dest);
}

ALT_STATUS_CODE alt_nand_flash_page_write(const uint32_t page_addr, 
                                          const uint32_t num_pages,
                                          const void *src,
                                          const uint32_t src_size)
{
    // currently only one page
    uint32_t bank  = alt_nand_bank_get();     
    uint32_t page  = alt_nand_page_address_get(page_addr);
    uint32_t block = alt_nand_block_address_get(page_addr);
   
    return alt_nand_full_page_write_with_map10( bank, block, page, (uint32_t *)src);
}

ALT_STATUS_CODE alt_nand_flash_page_dma_read(const uint32_t page_addr, 
                                             const uint32_t num_pages,
                                             void *dest,
                                             const uint32_t dest_size,
                                             alt_nand_callback_t completion_callback,
                                             void *completion_arg)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    uint32_t mem_addr = page_addr;
    uint32_t dest_addr = (uint32_t)dest;
    uint32_t buff_size = dest_size;

    uint32_t bank  = alt_nand_bank_get();     
    uint32_t page;
    uint32_t block;

    for (int i = 0; (i < num_pages) && (buff_size >= flash->page_size); i++) {

        page  = alt_nand_page_address_get(mem_addr);
        block = alt_nand_block_address_get(mem_addr);
        
        status = alt_nand_dma_page_read(bank, block, page, dest_addr);
        if (status == ALT_E_SUCCESS)
        {    
            mem_addr   += flash->page_size;
            dest_addr  += flash->page_size;
            buff_size  -= flash->page_size;
        }
        else
            break;
    }

    if (status == ALT_E_SUCCESS)
    {
        (*completion_callback)(status, completion_arg);
    }

    return status;
}

ALT_STATUS_CODE alt_nand_flash_page_dma_write(const uint32_t page_addr, 
                                              const uint32_t num_pages,
                                              const void *src,
                                              const uint32_t src_size,
                                              alt_nand_callback_t completion_callback,
                                              void *completion_arg)
{
    ALT_STATUS_CODE status = ALT_E_SUCCESS;
    uint32_t mem_addr = page_addr;
    uint32_t src_addr = (uint32_t)src;
    uint32_t buff_size = src_size;

    uint32_t bank  = alt_nand_bank_get();     
    uint32_t page;
    uint32_t block;

    for (int i = 0; (i < num_pages) && (buff_size >= flash->page_size); i++) {

        page  = alt_nand_page_address_get(mem_addr);
        block = alt_nand_block_address_get(mem_addr);

        status = alt_nand_dma_page_write(bank, block, page, src_addr);
        if (status == ALT_E_SUCCESS)
        {    
            mem_addr   += flash->page_size;
            src_addr   += flash->page_size;
            buff_size  -= flash->page_size;
        }
        else
            break;
    }

    if (status == ALT_E_SUCCESS)
    {
        (*completion_callback)(status, completion_arg);
    }

    return status;
}

ALT_STATUS_CODE alt_nand_flash_ecc_enable(const ALT_NAND_ECC_CORRECTION_t ecc_correction)
{
    ALT_NAND_CFG_raw_t * cfg = (ALT_NAND_CFG_raw_t *)(nand->cfg);
    alt_setbits_word(&cfg->ecc_enable, ALT_NAND_CFG_ECC_EN_FLAG_SET_MSK); 
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_nand_flash_ecc_disable(void)
{
    ALT_NAND_CFG_raw_t * cfg = (ALT_NAND_CFG_raw_t *)(nand->cfg);
    alt_clrbits_word(&cfg->ecc_enable, ALT_NAND_CFG_ECC_EN_FLAG_SET_MSK); 
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_nand_flash_ecc_status_get(ALT_NAND_FLASH_ECC_STATUS_t *ecc_status)
{
    ALT_NAND_ECC_raw_t * ecc = (ALT_NAND_ECC_raw_t *)(nand->ecc);
    uint32_t status;
 
    status = alt_read_word(&ecc->ECCCorInfo_b01); 
    ecc_status->corrected_errors[0] = (status & ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0_SET_MSK) >> ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0_LSB;   
    ecc_status->corrected_errors[1] = (status & ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1_SET_MSK) >> ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1_LSB;   
    ecc_status->uncorrected_error[0] = (status & ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0_SET_MSK) >> ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0_LSB;   
    ecc_status->uncorrected_error[1] = (status & ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1_SET_MSK) >> ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1_LSB;   
    status = alt_read_word(&ecc->ECCCorInfo_b23); 
    ecc_status->corrected_errors[2] = (status & ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2_SET_MSK) >> ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2_LSB;   
    ecc_status->corrected_errors[3] = (status & ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3_SET_MSK) >> ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3_LSB;   
    ecc_status->uncorrected_error[2] = (status & ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2_SET_MSK) >> ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2_LSB;   
    ecc_status->uncorrected_error[3] = (status & ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3_SET_MSK) >> ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3_LSB;   
    return ALT_E_SUCCESS;
}

uint32_t alt_nand_int_status_get(void)
{
    uint32_t bank = alt_nand_bank_get();
    uint32_t reg = alt_nand_get_interrupt_status_register_addr(bank);
    return alt_read_word(reg);
}

ALT_STATUS_CODE alt_nand_int_clear(const uint32_t mask)
{
    uint32_t bank = alt_nand_bank_get();
    uint32_t reg = alt_nand_get_interrupt_status_register_addr(bank);
    alt_setbits_word(reg, mask);
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_nand_int_disable(const uint32_t mask)
{
    uint32_t bank = alt_nand_bank_get();
    uint32_t reg = alt_nand_get_interrupt_enable_register_addr(bank);
    alt_clrbits_word(reg, mask);
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_nand_int_enable(const uint32_t mask)
{
    uint32_t bank = alt_nand_bank_get();
    uint32_t reg  = alt_nand_get_interrupt_enable_register_addr(bank);
    alt_setbits_word(reg, mask);
    return ALT_E_SUCCESS;
}

uint32_t alt_nand_num_planes_get(void)
{
    return flash->number_of_planes; 
}

uint32_t alt_nand_number_blocks_of_plane_get(void)
{
    return (flash->onfi_device_no_of_blocks_per_lun / flash->number_of_planes);
}

uint32_t alt_nand_first_block_of_next_plane(void)
{
    return flash->first_block_of_next_plane;
}

uint32_t alt_nand_num_blocks_get(void)
{
    return (alt_nand_num_planes_get() * alt_nand_number_blocks_of_plane_get()) ;
}

uint32_t alt_nand_num_pages_per_block_get(void)
{
    return flash->pages_per_block;
}

uint32_t alt_nand_sector_size_get(void)
{
    return ALT_HHP_NAND_SECTOR_SIZE;
}

uint32_t alt_nand_spare_size_get(void)
{
    return flash->spare_size;
}

bool alt_nand_block_is_bad(const uint32_t block_addr)
{
    return false;
}

ALT_STATUS_CODE alt_nand_bad_block_table_get(alt_nand_bad_block_table_t bad_block_table,
                                             const uint32_t bad_block_table_len)
{
    alt_nand_callback_t dma_callback = &alt_nand_dma_page_callback;
    uint32_t completion_arg = 0;
    uint32_t total_blocks = (flash->onfi_device_no_of_luns * flash->onfi_device_no_of_blocks_per_lun);
    uint32_t addr = (total_blocks - 1) << (flash->block_shift + flash->page_shift);  // highest block is reseved for bad block table 
    uint32_t buff[ALT_HHP_NAND_PAGE_SIZE];

    alt_nand_flash_page_dma_read( addr, 1, buff, sizeof(buff), dma_callback, &completion_arg);
    for (int i = 0; i <ALT_HHP_NAND_NUM_OF_BLOCK_TOTAL/32; i++) 
    {
        bad_block_table[i] = buff[i];
    }
    return ALT_E_SUCCESS;
}

void alt_nand_rb_pin_mode_set(uint32_t mask)
{
    ALT_NAND_CFG_raw_t * cfg = (ALT_NAND_CFG_raw_t *)(nand->cfg);
    alt_setbits_word(&cfg->rb_pin_enabled, mask);
}

void alt_nand_rb_pin_mode_clear(uint32_t mask)
{
    ALT_NAND_CFG_raw_t * cfg = (ALT_NAND_CFG_raw_t *)(nand->cfg);
    alt_clrbits_word(&cfg->rb_pin_enabled, mask);
}

void alt_nand_reset_bank(uint32_t bank)
{
    ALT_NAND_CFG_raw_t * cfg = (ALT_NAND_CFG_raw_t *)(nand->cfg);

    uint32_t  interrup_status_register = alt_nand_get_interrupt_status_register_addr(bank);
    uint32_t  device_reset_bank        = alt_nand_get_device_reset_register_bank(bank);


    // Write on clear of all interrupt status
    alt_write_word(interrup_status_register, ALT_HHP_UINT32_MASK);

    // Controller sends a RESET command to device
    alt_setbits_word(&cfg->device_reset, device_reset_bank);

    alt_nand_poll_for_interrupt_status_register(interrup_status_register, ALT_NAND_STAT_INTR_STAT0_RST_COMP_SET_MSK);

    // Write on clear of all interrupt status
    alt_write_word(interrup_status_register, ALT_HHP_UINT32_MASK);
}



/* 
 * Count the consecutive zero bits (trailing) on the right in parallel
 *
 * Some bit fiddleing stuff.
 * From... http://graphics.stanford.edu/~seander/bithacks.html
 */
uint32_t ffs32(uint32_t v)
{
    uint32_t r = 0;
    do
    {
        if(v == 0)
            break;

        if(v & 0xFFFF0000){v >>= 16;r |= 16;}
        if(v & 0x0000FF00){v >>=  8;r |=  8;}
        if(v & 0x000000F0){v >>=  4;r |=  4;}
        if(v & 0x0000000C){v >>=  2;r |=  2;}
        if(v & 0x00000002){        ;r |=  1;}
    } while(0);

    return(r);
}

uint32_t alt_nand_poll_for_interrupt_status_register(uint32_t interrup_status_register, uint32_t interrup_status_mask )
{
    uint32_t ret;
    uint32_t i = 0;

    if ( !s_nand_is_interrupt_enabled )
    {
        ret = alt_read_word( interrup_status_register );
        while( !( ret & (interrup_status_mask | ALT_NAND_INT_STATUS_UNSUP_CMD ) ) )
        {
            ret = alt_read_word( interrup_status_register );
            //printf("<alt_nand_poll for interrupt status register>->interrupt status reg = %08lX\n", ret);
            if ( ++i == g_nand_interrup_status_register_poll_counter_limit )
            {
                break;
            }
        }

        if ( ret & ALT_NAND_STAT_INTR_EN0_UNSUP_CMD_SET_MSK )
        {
            //printf( "Warning: Unsupported CMD interrupt INTR_STATUS_UNSUP_CMD is raised!!!!\n" );
        }
    }
    else
    {
        ret = s_nand_interrupt_handler( interrup_status_register, interrup_status_mask );
    }

    return ret;
}


int32_t alt_nand_full_page_read_with_map10(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, uint32_t *buffer )
{
    int32_t            ret = ALT_E_SUCCESS;
    int32_t            res = -1;
    const uint32_t    PAGES_TO_READ = 1;  // NOTE: Only 2 bits wide
    const uint32_t    interrup_status_register = alt_nand_get_interrupt_status_register_addr( bank );
    const uint32_t    addr = alt_nand_compose_map10_cmd_addr( bank, block_addr, page_addr );

    alt_write_word( interrup_status_register, ALT_HHP_UINT32_MASK );

    // Sets up a pipeline read-ahead of for a read (0x2001)
    alt_nand_write_indirect( addr, ALT_HHP_NAND_10_OP_READ_PIPE | PAGES_TO_READ );
    res = alt_nand_poll_for_interrupt_status_register( interrup_status_register, 
                                                       ALT_NAND_INT_STATUS_TIME_OUT | 
                                                       ALT_NAND_INT_STATUS_LOAD_COMP );

    if((res &  ALT_NAND_INT_STATUS_LOAD_COMP) != 0)
    {
        alt_nand_full_page_read_with_map10_post_read_with_map01( bank, block_addr, page_addr, buffer);
    }
    else
    {
        //printf("FAIL: Timeout loading NAND page. (%08lX,%ld,%ld)\n", res, bank, page_addr);
        ret = ALT_E_ERROR;
    }

    return ret;
}

uint32_t alt_nand_get_device_reset_register_bank(const uint32_t bank)
{
    uint32_t    ret=0;

    switch( bank )
    {
    case 0:
        ret = ALT_NAND_CFG_DEVICE_RST_BANK0_SET_MSK;
        break;
    
    case 1:
        ret = ALT_NAND_CFG_DEVICE_RST_BANK1_SET_MSK;
        break;
    
    case 2:
        ret = ALT_NAND_CFG_DEVICE_RST_BANK2_SET_MSK;
        break;
    
    case 3:
        ret = ALT_NAND_CFG_DEVICE_RST_BANK3_SET_MSK;
        break;
    
    default:
        // info_assert(0, "Do not support more than 4 banks");
        break;
    }

    return ret;
}

uint32_t alt_nand_get_interrupt_status_register_addr(const uint32_t bank)
{
    ALT_NAND_STAT_raw_t * stat = (ALT_NAND_STAT_raw_t *)(nand->stat);
    uint32_t ret=0;

    switch( bank )
    {
    case 0:
        ret = (uint32_t)(&stat->intr_status0);
        break;
    
    case 1:
        ret = (uint32_t)(&stat->intr_status1);
        break;
    
    case 2:
        ret = (uint32_t)(&stat->intr_status2);
        break;
    
    case 3:
        ret = (uint32_t)(&stat->intr_status3);
        break;
    
    default:
        // info_assert(0, "Do not support more than 4 banks");
        break;
    }

    return ret;
}

uint32_t alt_nand_get_interrupt_enable_register_addr(uint32_t bank)
{
    uint32_t  interrup_enable_register=0;

    ALT_NAND_STAT_raw_t * stat = (ALT_NAND_STAT_raw_t *)(nand->stat);

    switch( bank )
    {
    case 0:
        interrup_enable_register = (uint32_t)(&stat->intr_en0);
        //printf("interrupt status register: %08lX \n", interrup_enable_register);
        break;
    
    case 1:
        interrup_enable_register = (uint32_t)(&stat->intr_en1);
        break;
    
    case 2:
        interrup_enable_register = (uint32_t)(&stat->intr_en2);
        break;
    
    case 3:
        interrup_enable_register = (uint32_t)(&stat->intr_en3);
        break;
    
    default:
        // info_assert(0, "Do not support more than 4 banks");
        break;
    }

   return interrup_enable_register;
}

uint32_t alt_nand_compose_map01_cmd_addr(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr)
{
    const uint32_t BANK_MASK = 0x3;
    const uint32_t BLOCK_ADDR_MASK = (1 << (23 - flash->block_shift + 1)) - 1;
    const uint32_t PAGE_ADDR_MASK = (1 << flash->block_shift) - 1;

    const uint32_t ret = ALT_HHP_NAND_MODE_01 |
                         ((bank & BANK_MASK) << ALT_HHP_NAND_ADDR_MAP_BANK_SEL_LSB_INDEX) | 
                         ((block_addr & BLOCK_ADDR_MASK) << flash->block_shift) | 
                         (page_addr & PAGE_ADDR_MASK);

    return ret;
}

uint32_t alt_nand_compose_map10_cmd_addr(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr)
{
    const uint32_t BANK_MASK = 0x3;
    const uint32_t BLOCK_ADDR_MASK = (1 << (23 - flash->block_shift + 1)) - 1;
    const uint32_t PAGE_ADDR_MASK =  (1 << flash->block_shift) - 1;

    const uint32_t ret = ALT_HHP_NAND_MODE_10 |
                         ((bank & BANK_MASK) << ALT_HHP_NAND_ADDR_MAP_BANK_SEL_LSB_INDEX) | 
                         ((block_addr & BLOCK_ADDR_MASK) << flash->block_shift) | 
                         (page_addr & PAGE_ADDR_MASK);

    return ret;
}

void alt_nand_write_indirect(const uint32_t address, const uint32_t value)
{
    alt_write_word(nand->ctrl_addr, address);
    alt_write_word(nand->data_addr,   value);
}

uint32_t alt_nand_read_indirect(const uint32_t address)
{
    alt_write_word(nand->ctrl_addr, address);
    return alt_read_word(nand->data_addr);
}

void alt_nand_full_page_read_with_map10_post_read_with_map01(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, uint32_t *buffer)
{
    const uint32_t    addr = alt_nand_compose_map01_cmd_addr( bank, block_addr, page_addr );
    uint32_t        *cur = buffer;
    uint32_t        i;

    for( i = 0; i < flash->page_size_32; ++i )
    {
        *cur++ = alt_nand_read_indirect( addr );
    }
}

int32_t alt_nand_full_page_write_with_map10(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, const uint32_t *buffer)
{
    int32_t            ret = 0;
    int32_t            res = -1;
    const uint32_t    PAGES_TO_READ = 1;  // NOTE: Only 2 bits wide
    const uint32_t    interrup_status_register = alt_nand_get_interrupt_status_register_addr( bank );
    const uint32_t    addr = alt_nand_compose_map10_cmd_addr( bank, block_addr, page_addr );

    alt_write_word( interrup_status_register, ALT_HHP_UINT32_MASK );

    // Sets up a pipeline read-ahead of “01” pages.“W” = 0 for a read (0x2001)
    alt_nand_write_indirect( addr, ALT_HHP_NAND_10_OP_WRITE_PIPE | PAGES_TO_READ );

//
// don't forget this one, it is a hardware bug
//    
    for (int i = 0; i < 10000; i++) ; 

    // Temporarily disable status check as RTL doesn't seem to raise any flag.
    // But, it works.
    //res = alt_nand_poll_for_interrupt_status_register( interrup_status_register, INTR_STATUS0__TIME_OUT | INTR_STATUS0__PIPE_CPYBCK_CMD_COMP );
    res = ALT_NAND_INT_STATUS_PIPE_CPYBCK_CMD_COMP;
    if((res & ALT_NAND_INT_STATUS_PIPE_CPYBCK_CMD_COMP) != 0)
    {
        alt_nand_full_page_write_with_map10_post_write_with_map01( bank, block_addr, page_addr, buffer );
    }
    else
    {
        //printf("FAIL: Timeout loading NAND page. (%08lX,%ld,%ld)\n", res, bank, page_addr);
        ret = 1;
    }

    return ret;
}

void alt_nand_full_page_write_with_map10_post_write_with_map01(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, const uint32_t *buffer)
{
    const uint32_t    addr = alt_nand_compose_map01_cmd_addr( bank, block_addr, page_addr );
    const uint32_t    *cur = buffer;
    uint32_t        i;

    for( i = 0; i < flash->page_size_32; ++i )
    {
        alt_nand_write_indirect( addr, *cur++ );
    }
}


void alt_nand_set_sysmgr_bootstrap_value( uint32_t  bootstrp_inhibit_init,
                                          uint32_t  bootstrp_inhibit_b0p0_load,
                                          uint32_t  bootstrp_512b_device,
                                          uint32_t  bootstrp_two_row_addr_cycles)
{
    uint32_t settings = ALT_SYSMGR_NAND_BOOTSTRAP_NOINIT_SET(bootstrp_inhibit_init) |
                        ALT_SYSMGR_NAND_BOOTSTRAP_PAGE512_SET(bootstrp_512b_device) |  
                        ALT_SYSMGR_NAND_BOOTSTRAP_NOLDB0P0_SET(bootstrp_inhibit_b0p0_load) |  
                        ALT_SYSMGR_NAND_BOOTSTRAP_TWOROWADDR_SET(bootstrp_two_row_addr_cycles);

    alt_write_word(ALT_SYSMGR_NAND_BOOTSTRAP_ADDR, settings); 
}


uint32_t  alt_nand_bank_get(void)
{
    // on SOC, only bank 0 of physical memory is connected
    return ALT_NAND_FLASH_MEM_BANK_0;
}


int32_t alt_nand_dma_page_write(  const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, uint32_t mem_addr )
{
    int32_t     ret = 0;
    uint32_t res;
    const uint32_t    interrup_status_register = alt_nand_get_interrupt_status_register_addr( bank );

    alt_write_word( interrup_status_register, ALT_HHP_UINT32_MASK );

    alt_nand_dma_set_enabled( true );

    alt_nand_dma_write_cmd_structure( bank, block_addr, page_addr, 1, mem_addr, false, 64);

    res = alt_nand_poll_for_interrupt_status_register( interrup_status_register,  
                                                   ALT_NAND_INT_STATUS_DMA_CMD_COMP | 
                                                   ALT_NAND_INT_STATUS_PROGRAM_FAIL | 
                                                   ALT_NAND_INT_STATUS_LOCKED_BLK );  
                                                   // 10.8. Order of interrupt status bits assertion  8.

    if ( !(res & ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP_SET_MSK) )
    {
        //printf( "Error: DMA command is incomplete: 0x%lx\n", res );
        ret = res;
    }

    alt_nand_dma_set_enabled( false );

    return ret;
}

int32_t alt_nand_dma_page_read(  const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, uint32_t mem_addr )
{
    int32_t        ret = 0;
    uint32_t    res;
    const uint32_t    interrup_status_register = alt_nand_get_interrupt_status_register_addr( bank );

    alt_write_word( interrup_status_register, ALT_HHP_UINT32_MASK );

    alt_nand_dma_set_enabled( true );

    alt_nand_dma_write_cmd_structure( bank, block_addr, page_addr, 1, mem_addr, true, 64 );

    res = alt_nand_poll_for_interrupt_status_register( interrup_status_register,  
                                                   ALT_NAND_INT_STATUS_DMA_CMD_COMP | 
                                                   ALT_NAND_INT_STATUS_ECC_UNCOR_ERR);  
                                                   // 10.8. Order of interrupt status bits assertion  9.

    if ( !(res & ALT_NAND_INT_STATUS_DMA_CMD_COMP) )
    {
        //printf( "Error: DMA command is incomplete: 0x%lx\n", res );
        ret = res;
    }

    alt_nand_dma_set_enabled( false );

    return ret;
}

void alt_nand_dma_set_enabled( int32_t is_enabled )
{
    ALT_NAND_DMA_raw_t * dma = (ALT_NAND_DMA_raw_t *)(nand->dma);
    alt_write_word(&dma->dma_enable, ( is_enabled ? ALT_NAND_DMA_DMA_EN_FLAG_SET_MSK : 0 ) );
    alt_read_word( &dma->dma_enable);
}

void alt_nand_dma_write_cmd_structure( const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, const uint32_t page_count, uint64_t mem_addr, int32_t is_read_op, const uint32_t burst_len )
{
    const uint32_t  MODE_BANK_MASK = 0xFF000000;
    uint32_t        addr = alt_nand_compose_map10_cmd_addr( bank, block_addr, page_addr );

    // Transaction 1
    // Table 7.2. Address Encoding
    // Table 7.3. Data
    alt_nand_write_indirect( addr, 0x2000 | (is_read_op ? 0x0 : 0x100) | page_count);

    // Transaction 2
    // Table 7.4. Address Encoding
    // Table 7.5. Data
    addr &= MODE_BANK_MASK;
    addr |= ((uint16_t)(mem_addr >> 16) << 8);
    alt_nand_write_indirect( addr, 0x2200 );

    // Transaction 3
    // Table 7.6. Address Encoding
    // Table 7.7. Data
    addr &= MODE_BANK_MASK;
    addr |= ((uint16_t)mem_addr << 8);
    alt_nand_write_indirect( addr, 0x2300 );

    // Transaction 4
    // Table 7.8. Address Encoding
    // Table 7.9. Data
    addr &= MODE_BANK_MASK;
    addr |= 0x10000 | burst_len << 8;  // Enable INTR_STATUS__DMA_CMD_COMP always.
    alt_nand_write_indirect( addr, 0x2400);
}


ALT_STATUS_CODE alt_nand_flash_init_manual(void *user_arg)
{
    //printf("Entered Custom Init Routine for NAND.\n");
    return ALT_E_RESERVED;
}

void alt_nand_erase_block_callback(ALT_STATUS_CODE status, void *callback_arg)
{
    //printf("NAND Block Erase Callback is successful.\n");
    return;
}

void alt_nand_dma_page_callback(ALT_STATUS_CODE status, void *callback_arg)
{
    //printf("NAND DMA read Callback is successful.\n");
    return;
}

uint32_t  nand_read_register(const uint32_t offset)
{
    return alt_read_word(&nand->cfg + offset);
}

