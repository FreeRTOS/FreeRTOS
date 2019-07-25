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
 *  Altera - NAND Flash Controller Module
 */

#ifndef __ALT_NAND_PRIVATE_H__
#define __ALT_NAND_PRIVATE_H__


/*
 * *****************************************
 * Struct for NAND Manager IO block
 * which consists of cfg, param, status, ecc and dma register blocks
 * located at address: ALT_NAND_CFG_ADDR
 * *****************************************
 */
typedef struct  {
	ALT_NAND_CFG_raw_t*		cfg;            // nand configuration block
	ALT_NAND_PARAM_raw_t*   param;          // nand parameter block
	ALT_NAND_STAT_raw_t*    stat;           // nand status block
	ALT_NAND_ECC_raw_t*		ecc;            // nand ecc block
	ALT_NAND_DMA_raw_t*		dma;            // nand dma block
    volatile uint32_t * const   ctrl_addr;  // indirect access address control
    volatile uint32_t * const   data_addr;  // fifo access address control
} ALT_NAND_MGR_t;

//
// flash memory characterization
//
typedef struct 
{
  uint32_t                    manufacturer_id;
  uint32_t                    device_id;
  uint32_t                    device_param_0;
  uint32_t                    device_param_1;
  uint32_t                    device_param_2;
  uint32_t                    page_size;
  uint32_t                    spare_size;
  uint32_t                    revision;
  uint32_t                    onfi_device_features;
  uint32_t                    onfi_optional_commands;
  uint32_t                    onfi_timing_mode;
  uint32_t                    onfi_pgm_cache_timing_mode;
  uint32_t                    onfi_compliant;
  uint32_t                    onfi_device_no_of_luns;
  uint32_t                    onfi_device_no_of_blocks_per_lun;
  uint32_t                    features;

  uint32_t                    number_of_planes;
  uint32_t                    pages_per_block;
  uint32_t                    device_width;
  uint32_t                    device_main_area_size;
  uint32_t                    device_spare_area_size;
  uint32_t                    block_size;
  uint32_t                    spare_area_skip_bytes;
  uint32_t                    first_block_of_next_plane;
  uint32_t                    page_size_32;
  uint32_t                    page_shift;
  uint32_t                    block_shift;
  uint32_t			          dma_burst_length;
  uint32_t                    ecc_correct;
} FLASH_CHARACTERIZATION_t;


typedef uint32_t (*nand_interrupt_handler_t)(uint32_t interrup_status_register, uint32_t interrup_status_mask );


/*
 *  Some default values.
 */
#define ALT_HHP_NAND_SECTOR_SIZE      (512)
#define ALT_HHP_NAND_PAGE_SIZE        (2048)
#define ALT_HHP_NAND_PAGE_SHIFT       (11)
#define ALT_HHP_NAND_SPARE_SIZE       (128)         /* Spare bytes per page. */
#define ALT_HHP_NAND_PAGES_PER_BLOCK  (64)         /* 128 pages per block (512KB) */
#define ALT_HHP_NAND_BLOCK_SIZE       (ALT_HHP_NAND_PAGE_SIZE *ALT_HHP_NAND_PAGES_PER_BLOCK)
#define ALT_HHP_NAND_ECC_CORRECT      (8)           /* 8 bit ECC. */
#define ALT_HHP_NAND_SPARE_SKIP       (2)           /* Skip the first 2 bytes of the spare space. */
#define ALT_HHP_NAND_BLOCK_SHIFT      (6)           /* from page boundary */
#define ALT_HHP_NAND_MANUFACTURER_ID  (0x1)
#define ALT_HHP_NAND_DEVICE_ID        (0xd3)
#define ALT_HHP_NAND_REVISION         (5)

#define ALT_HHP_NAND_NUMBER_OF_PLANES (2)
#define ALT_HHP_NAND_DEVICE_WIDTH     (0)
#define ALT_HHP_NAND_FIRST_BLOCK_OF_NEXT_PLANE  (2048)

#define ALT_HHP_NAND_NUM_OF_LUNS	        (2)
#define ALT_HHP_NAND_NUM_OF_BLOCK_PER_LUNS	(4096)
#define ALT_HHP_NAND_NUM_OF_BLOCK_TOTAL		(ALT_HHP_NAND_NUM_OF_LUNS * ALT_HHP_NAND_NUM_OF_BLOCK_PER_LUNS)	   	  

//
// Constants from 8.1. Address Mapping
//
// Table 8.2
#define ALT_HHP_NAND_MODE_00            (0x00000000)
#define ALT_HHP_NAND_MODE_01            (0x04000000)
#define ALT_HHP_NAND_MODE_10            (0x08000000)
#define ALT_HHP_NAND_MODE_11            (0x0C000000)

#define ALT_HHP_NAND_ADDR_MAP_CMD_MAP_LSB_INDEX		(26)
#define ALT_HHP_NAND_ADDR_MAP_BANK_SEL_LSB_INDEX	(24)
#define ALT_HHP_NAND_ADDR_MAP_MEM_ADDR_LSB_INDEX	(0)

#define ALT_HHP_NAND_10_OP_DEFAULT_AREA (0x0042)
#define ALT_HHP_NAND_10_OP_ERASE_BLOCK  (0x0001)
#define ALT_HHP_NAND_10_OP_LOAD_PAGE    (0x0060)
#define ALT_HHP_NAND_10_OP_DEST_ADDR    (0x0061)
#define ALT_HHP_NAND_10_OP_WRITE_PAGE   (0x0062)

#define ALT_HHP_NAND_10_OP_READ_PIPE    (0x2000)
#define ALT_HHP_NAND_10_OP_WRITE_PIPE   (0x2100)

#define ALT_HHP_UINT32_MASK				((uint32_t) -1)


#define ALT_NAND_BOOTSTRAP_INHIBIT_INIT_ENABLE          (1)
#define ALT_NAND_BOOTSTRAP_INHIBIT_INIT_DISABLE         (0)
#define ALT_NAND_BOOTSTRAP_INHIBIT_B0P0_LOAD_ENABLE     (1)
#define ALT_NAND_BOOTSTRAP_INHIBIT_B0P0_LOAD_DISABLE    (0)
#define ALT_NAND_BOOTSTRAP_512B_DEVICE_ENABLE           (1)
#define ALT_NAND_BOOTSTRAP_512B_DEVICE_DISABLE          (0)
#define ALT_NAND_BOOTSTRAP_TWO_ROW_ADDR_CYCLES_EABLE    (1)
#define ALT_NAND_BOOTSTRAP_TWO_ROW_ADDR_CYCLES_DISABLE  (0)

#define ALT_NAND_FLASH_MEM_BANK_0                       (0)
#define ALT_NAND_FLASH_MEM_BANK_1                       (1)
#define ALT_NAND_FLASH_MEM_BANK_2                       (2)
#define ALT_NAND_FLASH_MEM_BANK_3                       (3)

uint32_t alt_nand_poll_for_interrupt_status_register(uint32_t , uint32_t );
uint32_t ffs32(uint32_t);
uint32_t alt_nand_compose_map10_cmd_addr(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr);
int32_t alt_nand_full_page_read_with_map10(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, uint32_t *buffer);
void alt_nand_write_indirect(const uint32_t address, const uint32_t value);
uint32_t alt_nand_read_indirect(const uint32_t address);
int32_t alt_nand_full_page_write_with_map10(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, const uint32_t *buffer);
void alt_nand_full_page_read_with_map10_post_read_with_map01(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, uint32_t *buffer);
void alt_nand_full_page_write_with_map10_post_write_with_map01(const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, const uint32_t *buffer);

void alt_nand_set_sysmgr_bootstrap_value( uint32_t  bootstrp_inhibit_init,
                                     uint32_t  bootstrp_inhibit_b0p0_load,
                                     uint32_t  bootstrp_512b_device,
                                     uint32_t  bootstrp_two_row_addr_cycles);
void alt_nand_reset_bank(uint32_t bank);
uint32_t  alt_nand_bank_get(void);

void alt_nand_dma_write_cmd_structure( const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, const uint32_t page_count, uint64_t mem_addr, int32_t is_read_op, const uint32_t burst_len );

void alt_nand_dma_set_enabled( int32_t is_enabled );
int32_t alt_nand_dma_page_read(  const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, uint32_t mem_addr );
int32_t alt_nand_dma_page_write(  const uint32_t bank, const uint32_t block_addr, const uint32_t page_addr, uint32_t mem_addr );
ALT_STATUS_CODE alt_nand_flash_init_manual(void *);
void alt_nand_erase_block_callback(ALT_STATUS_CODE, void *);
void alt_nand_dma_page_callback(ALT_STATUS_CODE, void *);
void nand_print_device(void);
uint32_t nand_read_register(uint32_t offset);
void alt_nand_rb_pin_mode_set(uint32_t);
void alt_nand_rb_pin_mode_clear(uint32_t);

#endif  /* __ALT_NAND_PRIVATE_H__ */
