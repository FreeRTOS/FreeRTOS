/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _MPU_H_
#define _MPU_H_

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/
#define ARM_MODE_USR            0x10

#define PRIVILEGE_MODE 0
#define USER_MODE      1

//#define ITCM_SIZE
//#define DTCM_SIZE
//#define FLASH_SIZE
//#define ISRAM_SIZE

#define MPU_UNPRIVILEGED_RAM_REGION       ( 0 )
#define MPU_PRIVILEGE_RAM_REGION          ( 1 )
#define MPU_UNPRIVILEGED_FLASH_REGION     ( 2 )
#define MPU_PRIVILEGED_FLASH_REGION       ( 3 )
#define MPU_PRIVILEGED_PERIPHERALS_REGION ( 4 )
#define MPU_UART_REGION_REGION            ( 5 )
#define MPU_SDRAM_REGION                  ( 6 )

#if 1
#define MPU_DEFAULT_ITCM_REGION           ( 1 )
#define MPU_DEFAULT_IFLASH_REGION         ( 2 )
#define MPU_DEFAULT_DTCM_REGION           ( 3 )
#define MPU_DEFAULT_PRAM_REGION           ( 4 )
#define MPU_DEFAULT_UPRAM_REGION          ( 5 )
#define MPU_PERIPHERALS_REGION            ( 6 )
#define MPU_USBHSRAM_REGION               ( 7 )
#define MPU_QSPIMEM_REGION                ( 8 )
#endif

#if 0
#define MPU_QSPIMEM_REGION                ( 0 )
#define MPU_USBHSRAM_REGION               ( 1 )
#define MPU_PERIPHERALS_REGION            ( 2 )
#define MPU_DEFAULT_DTCM_REGION           ( 3 )
#define MPU_DEFAULT_ITCM_REGION           ( 4 )
#define MPU_DEFAULT_UPRAM_REGION          ( 5 )
#define MPU_DEFAULT_IFLASH_REGION         ( 6 )
#define MPU_DEFAULT_PRAM_REGION           ( 7 )
#endif






#define MPU_REGION_VALID                    ( 0x10 )
#define MPU_REGION_ENABLE                   ( 0x01 )
#define MPU_REGION_DISABLE                  ( 0x0 )

#define MPU_ENABLE                      ( 0x1 )
#define MPU_BGENABLE                    ( 0x1 << 2 )

#define PROTECT_PIO_SUBREGION           ( 0x1 << 4 ) 

#define MPU_REGION_BUFFERABLE               ( 0x01 << MPU_RASR_B_Pos )
#define MPU_REGION_CACHEABLE                ( 0x01 << MPU_RASR_C_Pos )
#define MPU_REGION_SHAREABLE                ( 0x01 << MPU_RASR_S_Pos )

#define MPU_REGION_EXECUTE_NEVER            ( 0x01 << MPU_RASR_XN_Pos )

#define MPU_AP_NO_ACCESS                    ( 0x00 << MPU_RASR_AP_Pos )
#define MPU_AP_PRIVILEGED_READ_WRITE        ( 0x01 << MPU_RASR_AP_Pos )
#define MPU_AP_UNPRIVILEGED_READONLY        ( 0x02 << MPU_RASR_AP_Pos )
#define MPU_AP_FULL_ACCESS                  ( 0x03 << MPU_RASR_AP_Pos )
#define MPU_AP_RES                          ( 0x04 << MPU_RASR_AP_Pos )
#define MPU_AP_PRIVILEGED_READONLY          ( 0x05 << MPU_RASR_AP_Pos )
#define MPU_AP_READONLY                     ( 0x06 << MPU_RASR_AP_Pos )
#define MPU_AP_READONLY2                    ( 0x07 << MPU_RASR_AP_Pos )

#define MPU_TEX_NON_CACHE                   ( 0x04 << MPU_RASR_TEX_Pos )
#define MPU_TEX_WRITE_BACK_ALLOCATE         ( 0x05 << MPU_RASR_TEX_Pos )
#define MPU_TEX_WRITE_THROUGH               ( 0x06 << MPU_RASR_TEX_Pos )
#define MPU_TEX_WRITE_BACK_NOALLOCATE       ( 0x07 << MPU_RASR_TEX_Pos )

/* Default memory map 
Address range          Memory region          Memory type      Shareability   Cache policy
0x00000000- 0x1FFFFFFF Code                   Normal           Non-shareablea WTb
0x20000000- 0x3FFFFFFF SRAM                   Normal           Non-shareablea WBWAb
0x40000000- 0x5FFFFFFF Peripheral             Device           Non-shareablea -
0x60000000- 0x7FFFFFFF External RAM           Normal           Non-shareablea WBWAb
0x80000000- 0x9FFFFFFF WTb
0xA0000000- 0xBFFFFFFF External device Devicea Shareable
0xC0000000- 0xDFFFFFFF Non-shareablea
0xE0000000- 0xE00FFFFF Private Peripheral Bus Strongly ordered Shareablea -
0xE0100000- 0xFFFFFFFF Vendor-specific device Device           Non-shareablea -
*/

/********* IFLASH memory macros *********************/
#define ITCM_START_ADDRESS                  0x00000000UL
#define ITCM_END_ADDRESS                    0x00400000UL
#define IFLASH_START_ADDRESS                0x00400000UL
#define IFLASH_END_ADDRESS                  0x00600000UL
#define IFLASH_HALF                         ((IFLASH_END_ADDRESS - IFLASH_START_ADDRESS) >> 1)

#define IFLASH_PRIVILEGE_START_ADDRESS      (IFLASH_START_ADDRESS)
#define IFLASH_PRIVILEGE_END_ADDRESS        (IFLASH_START_ADDRESS + IFLASH_HALF)

#define IFLASH_UNPRIVILEGE_START_ADDRESS    (IFLASH_START_ADDRESS + IFLASH_HALF + 1)
#define IFLASH_UNPRIVILEGE_END_ADDRESS      (IFLASH_END_ADDRESS)

/**************** DTCM  *******************************/
#define DTCM_START_ADDRESS                  0x20000000UL
#define DTCM_END_ADDRESS                    0x20400000UL


/******* SRAM memory macros ***************************/

#define SRAM_START_ADDRESS                  0x20400000UL
#define SRAM_END_ADDRESS                    0x2045FFFFUL
#define SRAM_HALF                           ((SRAM_END_ADDRESS - SRAM_START_ADDRESS) >>1)


#define SRAM_PRIVILEGE_START_ADDRESS        (SRAM_START_ADDRESS)
#define SRAM_PRIVILEGE_END_ADDRESS          (SRAM_START_ADDRESS + 0x3FFFF)

#define SRAM_UNPRIVILEGE_START_ADDRESS      (SRAM_PRIVILEGE_END_ADDRESS + 1)
#define SRAM_UNPRIVILEGE_END_ADDRESS        (SRAM_END_ADDRESS)

/************** Peripherials memory region macros ********/

#define PERIPHERALS_START_ADDRESS               0x40000000UL
#define PERIPHERALS_END_ADDRESS                 0x400E2000UL

#define UART_REGION_START_ADDRESS               0x400E1C00UL
#define UART_REGION_END_ADDRESS                 0x400E2000UL

/************** Peripherials memory region macros ********/

#define PERIPHERALS_START_ADDRESS               0x40000000UL
#define PERIPHERALS_END_ADDRESS                 0x400E2000UL

/************** QSPI region macros ******************/

#define QSPI_START_ADDRESS                      0x80000000UL
#define QSPI_END_ADDRESS                        0x9FFFFFFFUL

/************** USBHS_RAM region macros ******************/

#define USBHSRAM_START_ADDRESS                  0xA0100000UL
#define USBHSRAM_END_ADDRESS                    0xA0200000UL

/******* Ext-SRAM memory macros ***************************/

#define SDRAM_START_ADDRESS                     0x70000000UL
#define SDRAM_END_ADDRESS                       0x7FFFFFFFUL

   /** Flag to indicate whether the svc is done */
extern volatile uint32_t dwRaisePriDone;
/*----------------------------------------------------------------------------
 *        Export functions
 *----------------------------------------------------------------------------*/
void MPU_Enable( uint32_t dwMPUEnable );
void MPU_SetRegion( uint32_t dwRegionBaseAddr, uint32_t dwRegionAttr );
void MPU_SetRegionNum( uint32_t dwRegionNum );
void MPU_DisableRegion( void );
uint32_t MPU_CalMPURegionSize( uint32_t dwActualSizeInBytes );
void MPU_UpdateRegions( uint32_t dwRegionNum, uint32_t dwRegionBaseAddr,
                                uint32_t dwRegionAttr);

#endif /* #ifndef _MMU_ */

