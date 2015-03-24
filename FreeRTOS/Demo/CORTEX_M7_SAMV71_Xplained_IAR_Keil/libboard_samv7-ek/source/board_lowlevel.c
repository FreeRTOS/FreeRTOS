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

/**
 * \file
 *
 * Provides the low-level initialization function that called on chip startup.
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"


/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/* Default memory map
   Address range          Memory region          Memory type      Shareability   Cache policy
   0x00000000- 0x1FFFFFFF Code                   Normal           Non-shareable  WT
   0x20000000- 0x3FFFFFFF SRAM                   Normal           Non-shareable  WBWA
   0x40000000- 0x5FFFFFFF Peripheral             Device           Non-shareable  -
   0x60000000- 0x7FFFFFFF External RAM           Normal           Non-shareable  WBWA
   0x80000000- 0x9FFFFFFF WTb
   0xA0000000- 0xBFFFFFFF External device Devicea Shareable
   0xC0000000- 0xDFFFFFFF Non-shareablea
   0xE0000000- 0xE00FFFFF Private Peripheral Bus Strongly ordered Shareablea -
   0xE0100000- 0xFFFFFFFF Vendor-specific device Device           Non-shareablea -
   */

/**
 * \brief Setup a memory region.
 */
void _SetupMemoryRegion( void )
{

	return;

#ifdef BELOW_CODE_REMOVED_FOR_REASON_STATED_IN_WARNING_MESSAGE_ABOVE
    uint32_t dwRegionBaseAddr;
    uint32_t dwRegionAttr;


/* ITCM memory region --- Normal */
/* #define ITCM_START_ADDRESS                  0x00000000UL
   #define ITCM_END_ADDRESS                    0x00400000UL
*/
    dwRegionBaseAddr =
        ITCM_START_ADDRESS |
        MPU_REGION_VALID |
        MPU_DEFAULT_ITCM_REGION;

    dwRegionAttr =
        MPU_AP_PRIVILEGED_READ_WRITE |
        MPU_TEX_WRITE_THROUGH |
        MPU_REGION_CACHEABLE |
        MPU_RASR_SRD_Msk |
        MPU_CalMPURegionSize(ITCM_END_ADDRESS - ITCM_START_ADDRESS) |
        MPU_REGION_ENABLE;

    MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

/* Internal flash privilege memory region --- Normal */
/* #define IFLASH_START_ADDRESS                0x00400000UL
   #define IFLASH_END_ADDRESS                  0x00600000UL
*/
    dwRegionBaseAddr =
        IFLASH_START_ADDRESS |
        MPU_REGION_VALID |
        MPU_DEFAULT_IFLASH_REGION;  //2

    dwRegionAttr =
        MPU_AP_FULL_ACCESS |
        MPU_REGION_CACHEABLE |
        MPU_TEX_WRITE_THROUGH |
        MPU_RASR_SRD_Msk |
        MPU_CalMPURegionSize(IFLASH_END_ADDRESS - IFLASH_START_ADDRESS) |
        MPU_REGION_ENABLE;

    MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);


    /* DTCM memory region */
    dwRegionBaseAddr =
        DTCM_START_ADDRESS |
        MPU_REGION_VALID |
        MPU_DEFAULT_DTCM_REGION; //3

    dwRegionAttr =
        MPU_AP_PRIVILEGED_READ_WRITE |
        MPU_REGION_CACHEABLE |
        MPU_REGION_BUFFERABLE |
        MPU_TEX_WRITE_BACK_ALLOCATE |
        MPU_RASR_SRD_Msk |
        MPU_CalMPURegionSize(DTCM_END_ADDRESS - DTCM_START_ADDRESS) |
        MPU_REGION_ENABLE;

    MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);


    /* SRAM memory privilege region */
    dwRegionBaseAddr =
        SRAM_PRIVILEGE_START_ADDRESS |
        MPU_REGION_VALID |
        MPU_DEFAULT_PRAM_REGION; //4

    dwRegionAttr =
        MPU_AP_FULL_ACCESS |
        MPU_REGION_CACHEABLE |
        MPU_REGION_BUFFERABLE |
        MPU_REGION_SHAREABLE |
        MPU_TEX_WRITE_BACK_ALLOCATE|
        MPU_RASR_SRD_Msk |
        MPU_CalMPURegionSize(SRAM_PRIVILEGE_END_ADDRESS - SRAM_PRIVILEGE_START_ADDRESS) |
        MPU_REGION_ENABLE;

    MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

    /* SRAM memory un-privilege region */
    dwRegionBaseAddr =
        SRAM_UNPRIVILEGE_START_ADDRESS |
        MPU_REGION_VALID |
        MPU_DEFAULT_UPRAM_REGION; //5

    dwRegionAttr =
        MPU_AP_PRIVILEGED_READ_WRITE |
        MPU_REGION_CACHEABLE |
        MPU_REGION_BUFFERABLE |
        MPU_TEX_WRITE_BACK_ALLOCATE|
        MPU_RASR_SRD_Msk |
        MPU_CalMPURegionSize(SRAM_UNPRIVILEGE_END_ADDRESS - SRAM_UNPRIVILEGE_START_ADDRESS) |
        MPU_REGION_ENABLE;

    MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);


/* Peripheral memory region ---- Device */
/* #define PERIPHERALS_START_ADDRESS               0x40000000UL
   #define PERIPHERALS_END_ADDRESS                 0x400E2000UL
*/
    dwRegionBaseAddr =
        PERIPHERALS_START_ADDRESS |
        MPU_REGION_VALID |
        MPU_PERIPHERALS_REGION;  //6

    dwRegionAttr = MPU_AP_FULL_ACCESS |
        MPU_REGION_EXECUTE_NEVER |
        MPU_RASR_SRD_Msk |
        MPU_CalMPURegionSize(PERIPHERALS_END_ADDRESS - PERIPHERALS_START_ADDRESS) |
        MPU_REGION_ENABLE;

    MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

/* USBHS_ram memory region -External device */
/*  #define USBHSRAM_START_ADDRESS                  0xA0100000UL
    #define USBHSRAM_END_ADDRESS                    0xA0200000UL
*/
    dwRegionBaseAddr =
        USBHSRAM_START_ADDRESS |
        MPU_REGION_VALID |
        MPU_USBHSRAM_REGION;  //7

    dwRegionAttr =
        MPU_AP_FULL_ACCESS |
        MPU_REGION_EXECUTE_NEVER |
        MPU_REGION_SHAREABLE |
        MPU_RASR_SRD_Msk |
        MPU_CalMPURegionSize(USBHSRAM_END_ADDRESS - USBHSRAM_START_ADDRESS) |
        MPU_REGION_ENABLE;

    MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

/* QSPI memory region -External RAM -- normal */
/* #define QSPI_START_ADDRESS                      0x80000000UL
   #define QSPI_END_ADDRESS                        0x9FFFFFFFUL
*/
    dwRegionBaseAddr =
        QSPI_START_ADDRESS |
        MPU_REGION_VALID |
        MPU_QSPIMEM_REGION;

    dwRegionAttr =
        MPU_AP_FULL_ACCESS |
        MPU_REGION_EXECUTE_NEVER |
        MPU_REGION_CACHEABLE |
        MPU_REGION_BUFFERABLE |
        MPU_TEX_WRITE_BACK_ALLOCATE|
        MPU_RASR_SRD_Msk |
        MPU_CalMPURegionSize(QSPI_END_ADDRESS - QSPI_START_ADDRESS) |
        MPU_REGION_ENABLE;

    MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

#ifdef SDRAM_VALID
    /* SDRAM memory region */
    dwRegionBaseAddr =
        SDRAM_START_ADDRESS |
        MPU_REGION_VALID |
        MPU_SDRAM_REGION;

    dwRegionAttr =
        MPU_REGION_READ_WRITE |
        MPU_REGION_CACHEABLE |
        MPU_REGION_BUFFERABLE |
        MPU_RASR_SRD_Msk |
        MPU_CalMPURegionSize(SDRAM_END_ADDRESS - SDRAM_START_ADDRESS) |
        MPU_REGION_ENABLE;

    MPU_SetRegion( dwRegionBaseAddr, dwRegionAttr);

#endif

    /* Enable the memory management fault , Bus Fault, Usage Fault exception */
    SCB->SHCSR |= (SCB_SHCSR_MEMFAULTENA_Msk | SCB_SHCSR_BUSFAULTENA_Msk | SCB_SHCSR_USGFAULTENA_Msk);

    /* Enable the MPU region */
    MPU_Enable( MPU_ENABLE | MPU_BGENABLE );
#endif /* BELOW_CODE_REMOVED_FOR_REASON_STATED_IN_WARNING_MESSAGE_ABOVE */
}



/**
 * \brief Performs the low-level initialization of the chip.
 * This includes EFC and master clock configuration.
 * It also enable a low level on the pin NRST triggers a user reset.
 */
extern WEAK void LowLevelInit( void )
{
    /* Set 6 FWS for Embedded Flash Access */
    EFC->EEFC_FMR = EEFC_FMR_FWS(6);
    if (!(PMC->CKGR_MOR & CKGR_MOR_MOSCSEL) )  /* Main Oscillator Selection */
    {
        SUPC_SelectExtCrystal32K();
        PMC_DisableAllClocks();
        PMC_SetMckSelection(PMC_MCKR_CSS_SLOW_CLK, PMC_MCKR_PRES_CLK_1);
        /* Then, enable Main XTAL oscillator */
        PMC_EnableExtOsc();
        PMC_SelectExtOsc();
        PMC_SetMckSelection(PMC_MCKR_CSS_MAIN_CLK, PMC_MCKR_PRES_CLK_1);
        /* wait Main CLK Ready */
        while(!(PMC->CKGR_MCFR & CKGR_MCFR_MAINFRDY));
        /* Then, cofigure PLLA and switch clock */
        PMC_ConfigureMckWithPlla(0x16, 0x1, PMC_MCKR_PRES_CLK_1);
        PMC->PMC_MCKR |= 1 << 8;
        while( !(PMC->PMC_SR & PMC_SR_MCKRDY) );
    }

    _SetupMemoryRegion();

}
