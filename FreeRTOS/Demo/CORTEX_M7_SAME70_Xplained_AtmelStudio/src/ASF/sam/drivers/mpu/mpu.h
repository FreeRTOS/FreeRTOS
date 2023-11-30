/**
 * \file
 *
 * \brief SAMV70/SAMV71/SAME70/SAMS70-XULTRA board mpu config.
 *
 * Copyright (c) 2015 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */


#ifndef _MPU_H_
#define _MPU_H_

#include "compiler.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/
#define ARM_MODE_USR            0x10

#define PRIVILEGE_MODE 0
#define USER_MODE      1

#define MPU_DEFAULT_ITCM_REGION                 ( 1 )
#define MPU_DEFAULT_IFLASH_REGION               ( 2 )
#define MPU_DEFAULT_DTCM_REGION                 ( 3 )
#define MPU_DEFAULT_SRAM_REGION_1               ( 4 )
#define MPU_DEFAULT_SRAM_REGION_2               ( 5 )
#define MPU_PERIPHERALS_REGION                  ( 6 )
#define MPU_EXT_EBI_REGION                      ( 7 )
#define MPU_DEFAULT_SDRAM_REGION                ( 8 )
#define MPU_QSPIMEM_REGION                      ( 9 )
#define MPU_USBHSRAM_REGION                     ( 10 )
#if defined MPU_HAS_NOCACHE_REGION
#define MPU_NOCACHE_SRAM_REGION                 ( 11 )
#endif

#define MPU_REGION_VALID                        ( 0x10 )
#define MPU_REGION_ENABLE                       ( 0x01 )
#define MPU_REGION_DISABLE                      ( 0x0 )

#define MPU_ENABLE                              ( 0x1 << MPU_CTRL_ENABLE_Pos)
#define MPU_HFNMIENA                            ( 0x1 << MPU_CTRL_HFNMIENA_Pos )
#define MPU_PRIVDEFENA                          ( 0x1 << MPU_CTRL_PRIVDEFENA_Pos )


#define MPU_REGION_BUFFERABLE                   ( 0x01 << MPU_RASR_B_Pos )
#define MPU_REGION_CACHEABLE                    ( 0x01 << MPU_RASR_C_Pos )
#define MPU_REGION_SHAREABLE                    ( 0x01 << MPU_RASR_S_Pos )

#define MPU_REGION_EXECUTE_NEVER                ( 0x01 << MPU_RASR_XN_Pos )

#define MPU_AP_NO_ACCESS                        ( 0x00 << MPU_RASR_AP_Pos )
#define MPU_AP_PRIVILEGED_READ_WRITE            ( 0x01 << MPU_RASR_AP_Pos )
#define MPU_AP_UNPRIVILEGED_READONLY            ( 0x02 << MPU_RASR_AP_Pos )
#define MPU_AP_FULL_ACCESS                      ( 0x03 << MPU_RASR_AP_Pos )
#define MPU_AP_RES                              ( 0x04 << MPU_RASR_AP_Pos )
#define MPU_AP_PRIVILEGED_READONLY              ( 0x05 << MPU_RASR_AP_Pos )
#define MPU_AP_READONLY                         ( 0x06 << MPU_RASR_AP_Pos )
#define MPU_AP_READONLY2                        ( 0x07 << MPU_RASR_AP_Pos )

#define MPU_TEX_B000                            ( 0x01 << MPU_RASR_TEX_Pos )
#define MPU_TEX_B001                            ( 0x01 << MPU_RASR_TEX_Pos )
#define MPU_TEX_B010                            ( 0x01 << MPU_RASR_TEX_Pos )
#define MPU_TEX_B011                            ( 0x01 << MPU_RASR_TEX_Pos )
#define MPU_TEX_B100                            ( 0x01 << MPU_RASR_TEX_Pos )
#define MPU_TEX_B101                            ( 0x01 << MPU_RASR_TEX_Pos )
#define MPU_TEX_B110                            ( 0x01 << MPU_RASR_TEX_Pos )
#define MPU_TEX_B111                            ( 0x01 << MPU_RASR_TEX_Pos )

#define SHAREABLE       1
#define NON_SHAREABLE   0

#define INNER_NORMAL_WB_RWA_TYPE(x)   (( 0x04 << MPU_RASR_TEX_Pos ) | ( DISABLE  << MPU_RASR_C_Pos ) | ( ENABLE  << MPU_RASR_B_Pos )  | ( x << MPU_RASR_S_Pos ))
#define INNER_NORMAL_WB_NWA_TYPE(x)   (( 0x04 << MPU_RASR_TEX_Pos ) | ( ENABLE  << MPU_RASR_C_Pos )  | ( ENABLE  << MPU_RASR_B_Pos )  | ( x << MPU_RASR_S_Pos ))
#define STRONGLY_ORDERED_SHAREABLE_TYPE      (( 0x00 << MPU_RASR_TEX_Pos ) | ( DISABLE << MPU_RASR_C_Pos ) | ( DISABLE << MPU_RASR_B_Pos ))     // DO not care //
#define SHAREABLE_DEVICE_TYPE                (( 0x00 << MPU_RASR_TEX_Pos ) | ( DISABLE << MPU_RASR_C_Pos ) | ( ENABLE  << MPU_RASR_B_Pos ))     // DO not care //


/* Default memory map
   Address range          Memory region          Memory type      Shareability   Cache policy
   0x00000000- 0x1FFFFFFF Code                   Normal           Non-shareable  WT
   0x20000000- 0x3FFFFFFF SRAM                   Normal           Non-shareable  WBWA
   0x40000000- 0x5FFFFFFF Peripheral             Device           Non-shareable  -
   0x60000000- 0x7FFFFFFF RAM                    Normal           Non-shareable  WBWA
   0x80000000- 0x9FFFFFFF RAM                    Normal           Non-shareable  WT
   0xA0000000- 0xBFFFFFFF Device                 Device           Shareable
   0xC0000000- 0xDFFFFFFF Device                 Device           Non Shareable
   0xE0000000- 0xFFFFFFFF System                  -                     -
   */

/********* IFLASH memory macros *********************/
#define ITCM_START_ADDRESS                  0x00000000UL
#define ITCM_END_ADDRESS                    0x003FFFFFUL
#define IFLASH_START_ADDRESS                0x00400000UL
#define IFLASH_END_ADDRESS                  0x005FFFFFUL


#define IFLASH_PRIVILEGE_START_ADDRESS      (IFLASH_START_ADDRESS)
#define IFLASH_PRIVILEGE_END_ADDRESS        (IFLASH_START_ADDRESS + 0xFFF)

#define IFLASH_UNPRIVILEGE_START_ADDRESS    (IFLASH_PRIVILEGE_END_ADDRESS + 1)
#define IFLASH_UNPRIVILEGE_END_ADDRESS      (IFLASH_END_ADDRESS)

/**************** DTCM  *******************************/
#define DTCM_START_ADDRESS                  0x20000000UL
#define DTCM_END_ADDRESS                    0x203FFFFFUL


/******* SRAM memory macros ***************************/

#define SRAM_START_ADDRESS                  0x20400000UL
#define SRAM_END_ADDRESS                    0x2045FFFFUL

#if defined MPU_HAS_NOCACHE_REGION
#define NOCACHE_SRAM_REGION_SIZE            0x1000
#endif

/* Regions should be a 2^(N+1)  where 4 < N < 31 */
#define SRAM_FIRST_START_ADDRESS            (SRAM_START_ADDRESS)
#define SRAM_FIRST_END_ADDRESS              (SRAM_FIRST_START_ADDRESS + 0x3FFFF)        // (2^18) 256 KB

#if defined MPU_HAS_NOCACHE_REGION
#define SRAM_SECOND_START_ADDRESS           (SRAM_FIRST_END_ADDRESS+1)
#define SRAM_SECOND_END_ADDRESS             (SRAM_END_ADDRESS - NOCACHE_SRAM_REGION_SIZE )              // (2^17) 128 - 0x1000 KB
#define SRAM_NOCACHE_START_ADDRESS          (SRAM_SECOND_END_ADDRESS + 1)
#define SRAM_NOCACHE_END_ADDRESS            (SRAM_END_ADDRESS )
#else
#define SRAM_SECOND_START_ADDRESS           (SRAM_FIRST_END_ADDRESS + 1)
#define SRAM_SECOND_END_ADDRESS             (SRAM_END_ADDRESS)                          // (2^17) 128 KB
#endif
/************** Peripherals memory region macros ********/
#define PERIPHERALS_START_ADDRESS            0x40000000UL
#define PERIPHERALS_END_ADDRESS              0x5FFFFFFFUL

/******* Ext EBI memory macros ***************************/
#define EXT_EBI_START_ADDRESS                0x60000000UL
#define EXT_EBI_END_ADDRESS                  0x6FFFFFFFUL

/******* Ext-SRAM memory macros ***************************/
#define SDRAM_START_ADDRESS                  0x70000000UL
#define SDRAM_END_ADDRESS                    0x7FFFFFFFUL

/******* QSPI macros ***************************/
#define QSPI_START_ADDRESS                   0x80000000UL
#define QSPI_END_ADDRESS                     0x9FFFFFFFUL

/************** USBHS_RAM region macros ******************/
#define USBHSRAM_START_ADDRESS               0xA0100000UL
#define USBHSRAM_END_ADDRESS                 0xA01FFFFFUL

/*----------------------------------------------------------------------------
 *        Export functions
 *----------------------------------------------------------------------------*/
void mpu_enable(uint32_t dw_mpu_enable);
void mpu_set_region(uint32_t dw_region_base_addr, uint32_t dw_region_attr);
void mpu_set_region_num(uint32_t dw_region_num);
void mpu_disable_region(void);
uint32_t mpu_cal_mpu_region_size(uint32_t dw_actual_size_in_bytes);
void mpu_update_regions(uint32_t dw_region_num, uint32_t dw_region_base_addr, uint32_t dw_region_attr);

#endif /* #ifndef _MPU_H_ */