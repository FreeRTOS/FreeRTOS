/** @file nmpu.c
 *   @brief NMPU Driver Source File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - API Functions
 *   - Interrupt Handlers
 *   .
 *   which are relevant for the NMPU driver.
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#include "nmpu.h"

/** @fn void nmpuEnable(nmpuBASE_t * nmpu)
 *   @brief Enable memory protection
 *
 *   @param[in] nmpu  NMPU module instance
 *                      - nmpu_emacREG     : EMAC-NMPU (2 regions)
 *                      - nmpu_dmaREG      : DMA-NMPU (8 regions)
 *                      - nmpu_ps_scr_sREG : Peripheral Interconnect Subsystem-NMPU (8
 * regions)
 *
 *   This function enables memory protection
 */
/* SourceId : NMPU_SourceId_001 */
/* DesignId : NMPU_DesignId_001 */
/* Requirements : CONQ_NMPU_SR1 */
void nmpuEnable( nmpuBASE_t * nmpu )
{
    /* USER CODE BEGIN (0) */
    /* USER CODE END */

    nmpu->MPULOCK = 0xAU;  /* Allow MPU register writes  */
    nmpu->MPUCTRL1 = 0xAU; /* Enable Memory Protection   */
    nmpu->MPULOCK = 0x5U;  /* Block MPU register writes  */

    /* USER CODE BEGIN (1) */
    /* USER CODE END */
}

/** @fn void nmpuDisable(nmpuBASE_t * nmpu)
 *   @brief Disable memory protection
 *
 *   @param[in] nmpu  NMPU module instance
 *                      - nmpu_emacREG     : EMAC-NMPU (2 regions)
 *                      - nmpu_dmaREG      : DMA-NMPU (8 regions)
 *                      - nmpu_ps_scr_sREG : Peripheral Interconnect Subsystem-NMPU (8
 * regions)
 *
 *   This function disables memory protection
 */
/* SourceId : NMPU_SourceId_002 */
/* DesignId : NMPU_DesignId_002 */
/* Requirements : CONQ_NMPU_SR2 */
void nmpuDisable( nmpuBASE_t * nmpu )
{
    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    nmpu->MPULOCK = 0xAU;  /* Allow MPU register writes  */
    nmpu->MPUCTRL1 = 0x5U; /* Disable Memory Protection  */
    nmpu->MPULOCK = 0x5U;  /* Block MPU register writes  */

    /* USER CODE BEGIN (3) */
    /* USER CODE END */
}

/** @fn void nmpuEnableErrorGen(nmpuBASE_t * nmpu)
 *   @brief Enable error pulse output to ESM
 *
 *   @param[in] nmpu  NMPU module instance
 *                      - nmpu_emacREG     : EMAC-NMPU (2 regions)
 *                      - nmpu_dmaREG      : DMA-NMPU (8 regions)
 *                      - nmpu_ps_scr_sREG : Peripheral Interconnect Subsystem-NMPU (8
 * regions)
 *
 *   This function enables error pulse output to ESM
 */
/* SourceId : NMPU_SourceId_003 */
/* DesignId : NMPU_DesignId_003 */
/* Requirements : CONQ_NMPU_SR3 */
void nmpuEnableErrorGen( nmpuBASE_t * nmpu )
{
    /* USER CODE BEGIN (4) */
    /* USER CODE END */

    nmpu->MPULOCK = 0xAU;  /* Allow MPU register writes          */
    nmpu->MPUCTRL2 = 0xAU; /* Enable Error pulse output to ESM   */
    nmpu->MPULOCK = 0x5U;  /* Block MPU register writes          */

    /* USER CODE BEGIN (5) */
    /* USER CODE END */
}

/** @fn void nmpuDisableErrorGen(nmpuBASE_t * nmpu)
 *   @brief Disable error pulse output to ESM
 *
 *   @param[in] nmpu  NMPU module instance
 *                      - nmpu_emacREG     : EMAC-NMPU (2 regions)
 *                      - nmpu_dmaREG      : DMA-NMPU (8 regions)
 *                      - nmpu_ps_scr_sREG : Peripheral Interconnect Subsystem-NMPU (8
 * regions)
 *
 *   This function disables error pulse output to ESM
 */
/* SourceId : NMPU_SourceId_004 */
/* DesignId : NMPU_DesignId_004 */
/* Requirements : CONQ_NMPU_SR4 */
void nmpuDisableErrorGen( nmpuBASE_t * nmpu )
{
    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    nmpu->MPULOCK = 0xAU;  /* Allow MPU register writes          */
    nmpu->MPUCTRL2 = 0x5U; /* Disable Error pulse output to ESM  */
    nmpu->MPULOCK = 0x5U;  /* Block MPU register writes          */

    /* USER CODE BEGIN (7) */
    /* USER CODE END */
}

/** @fn boolean nmpuEnableRegion(nmpuBASE_t * nmpu, uint32 region, nmpuRegionAttributes_t
config)
*   @brief Enable NMPU region
*
*   @param[in] nmpu    NMPU module instance
*                        - nmpu_emacREG     : EMAC-NMPU (2 regions)
*                        - nmpu_dmaREG      : DMA-NMPU (8 regions)
*                        - nmpu_ps_scr_sREG : Peripheral Interconnect Subsystem-NMPU (8
regions)
*   @param[in] region  region number (NMPU_REGION0..NMPU_REGION7)
*   @param[in] config  struct containing the following elements:
                         - baseaddr         : 32-bit vase address (must be multiple of
region size)
                         - regionsize       : Region size (Refer enum nmpuRegionSize)
                         - accesspermission : Access Permission (Refer enum
nmpuAccessPermission)
*   @return    Returns TRUE if the input parameters are valid.
*
*   This function enables an NMPU region. This function will not enable the NMPU module.
Application must call the routine nmpuEnable to so the same.
*/
/* SourceId : NMPU_SourceId_005 */
/* DesignId : NMPU_DesignId_005 */
/* Requirements : CONQ_NMPU_SR5 */
boolean nmpuEnableRegion( nmpuBASE_t * nmpu,
                          nmpuReg_t region,
                          nmpuRegionAttributes_t config )
{
    boolean status = TRUE;
    uint32 addrMask;

    /* USER CODE BEGIN (8) */
    /* USER CODE END */

    if( ( uint32 ) region >= ( nmpu->MPUTYPE >> 8U ) )
    {
        /* Invalid region */
        status = FALSE;
    }

    addrMask = ( uint32 ) 2U << ( config.regionsize );
    addrMask = addrMask - 1U;
    if( ( config.baseaddr & addrMask ) != 0U )
    {
        /* Invalid Baseaddress - Not a multiple of region size */
        status = FALSE;
    }

    if( status == TRUE )
    {
        /* Set the region attributes */
        nmpu->MPULOCK = 0xAU;
        nmpu->MPUREGNUM = region;
        nmpu->MPUREGBASE = ( ( uint32 ) ( config.baseaddr ) );
        nmpu->MPUREGSENA = ( ( uint32 ) ( config.regionsize ) << 1U ) | 1U;
        nmpu->MPUREGACR = ( ( uint32 ) ( config.accesspermission ) << 8U );
        nmpu->MPULOCK = 0x5U;
    }

    /* USER CODE BEGIN (9) */
    /* USER CODE END */

    return status;
}

/** @fn nmpuDisableRegion(nmpuBASE_t * nmpu, uint32 region)
 *   @brief Disable error pulse output to ESM
 *
 *   @param[in] nmpu    NMPU module instance
 *                        - nmpu_emacREG     : EMAC-NMPU (2 regions)
 *                        - nmpu_dmaREG      : DMA-NMPU (8 regions)
 *                        - nmpu_ps_scr_sREG : Peripheral Interconnect Subsystem-NMPU (8
 * regions)
 *   @param[in] region  region number (NMPU_REGION0..NMPU_REGION7)
 *   @return    Returns TRUE if the input parameters are valid.
 *
 *   This function disables an NMPU region.
 */
/* SourceId : NMPU_SourceId_006 */
/* DesignId : NMPU_DesignId_006 */
/* Requirements : CONQ_NMPU_SR6 */
boolean nmpuDisableRegion( nmpuBASE_t * nmpu, nmpuReg_t region )
{
    boolean status;

    /* USER CODE BEGIN (10) */
    /* USER CODE END */

    if( ( uint32 ) region >= ( nmpu->MPUTYPE >> 8U ) )
    {
        /* Invalid region */
        status = FALSE;
    }
    else
    {
        nmpu->MPULOCK = 0xAU;
        nmpu->MPUREGNUM = region;
        nmpu->MPUREGSENA = 0U;
        nmpu->MPULOCK = 0x5U;
        status = TRUE;
    }

    /* USER CODE BEGIN (11) */
    /* USER CODE END */

    return status;
}

/** @fn nmpuErr_t nmpuGetErrorStatus(nmpuBASE_t * nmpu)
 *   @brief Get the error status
 *
 *   @param[in] nmpu    NMPU module instance
 *                        - nmpu_emacREG     : EMAC-NMPU (2 regions)
 *                        - nmpu_dmaREG      : DMA-NMPU (8 regions)
 *                        - nmpu_ps_scr_sREG : Peripheral Interconnect Subsystem-NMPU (8
 * regions)
 *   @return  Returns any of the following:
 *              - NMPU_ERROR_NONE     : No error
 *              - NMPU_ERROR_AP_READ  : Access permission Read Error
 *              - NMPU_ERROR_AP_WRITE : Access permission Write Error
 *              - NMPU_ERROR_BG_READ  : Backgroung Read Error
 *              - NMPU_ERROR_BG_WRITE : Backgroung Write Error
 *
 *   This function returns the status of NMPU error
 */
/* SourceId : NMPU_SourceId_007 */
/* DesignId : NMPU_DesignId_007 */
/* Requirements : CONQ_NMPU_SR7 */
nmpuErr_t nmpuGetErrorStatus( nmpuBASE_t * nmpu )
{
    nmpuErr_t status;

    /* USER CODE BEGIN (12) */
    /* USER CODE END */

    if( ( nmpu->MPUERRSTAT & 0x1U ) == 0x1U )
    {
        if( ( nmpu->MPUERRSTAT & 0x02000000U ) == 0x02000000U )
        {
            if( ( nmpu->MPUERRSTAT & 0x10000000U ) == 0x10000000U )
            {
                status = NMPU_ERROR_AP_READ;
            }
            else
            {
                status = NMPU_ERROR_AP_WRITE;
            }
        }
        else
        {
            if( ( nmpu->MPUERRSTAT & 0x10000000U ) == 0x10000000U )
            {
                status = NMPU_ERROR_BG_READ;
            }
            else
            {
                status = NMPU_ERROR_BG_WRITE;
            }
        }
    }
    else
    {
        status = NMPU_ERROR_NONE;
    }

    /* USER CODE BEGIN (13) */
    /* USER CODE END */

    return status;
}

/** @fn nmpuReg_t nmpuGetErrorRegion(nmpuBASE_t * nmpu)
 *   @brief Get the region for which an access permission error was detected
 *
 *   @param[in] nmpu    NMPU module instance
 *                        - nmpu_emacREG     : EMAC-NMPU (2 regions)
 *                        - nmpu_dmaREG      : DMA-NMPU (8 regions)
 *                        - nmpu_ps_scr_sREG : Peripheral Interconnect Subsystem-NMPU (8
 * regions)
 *   @return    Region where access permission error was detected
 *
 *   This function returns the region for which an access permission error was detected
 */
/* SourceId : NMPU_SourceId_008 */
/* DesignId : NMPU_DesignId_008 */
/* Requirements : CONQ_NMPU_SR9 */
nmpuReg_t nmpuGetErrorRegion( nmpuBASE_t * nmpu )
{
    /* USER CODE BEGIN (14) */
    /* USER CODE END */

    return ( nmpuReg_t ) ( ( nmpu->MPUERRSTAT & 0x70000U ) >> 16U );

    /* USER CODE BEGIN (15) */
    /* USER CODE END */
}

/** @fn uint32 nmpuGetErrorAddress(nmpuBASE_t * nmpu)
 *   @brief Get the address for MPU compare fail
 *
 *   @param[in] nmpu    NMPU module instance
 *                        - nmpu_emacREG     : EMAC-NMPU (2 regions)
 *                        - nmpu_dmaREG      : DMA-NMPU (8 regions)
 *                        - nmpu_ps_scr_sREG : Peripheral Interconnect Subsystem-NMPU (8
 * regions)
 *   @return    Address for MPU compare fail
 *
 *   This function returns the address for MPU compare fail
 */
/* SourceId : NMPU_SourceId_009 */
/* DesignId : NMPU_DesignId_009 */
/* Requirements : CONQ_NMPU_SR8 */
uint32 nmpuGetErrorAddress( nmpuBASE_t * nmpu )
{
    /* USER CODE BEGIN (16) */
    /* USER CODE END */

    return ( nmpu->MPUERRADDR );

    /* USER CODE BEGIN (17) */
    /* USER CODE END */
}

/** @fn void nmpuClearErrorStatus(nmpuBASE_t * nmpu)
 *   @brief Clear error status
 *
 *   @param[in] nmpu    NMPU module instance
 *                        - nmpu_emacREG     : EMAC-NMPU (2 regions)
 *                        - nmpu_dmaREG      : DMA-NMPU (8 regions)
 *                        - nmpu_ps_scr_sREG : Peripheral Interconnect Subsystem-NMPU (8
 * regions)
 *
 *   This function clears the error status flags
 */
/* SourceId : NMPU_SourceId_010 */
/* DesignId : NMPU_DesignId_010 */
/* Requirements : CONQ_NMPU_SR10 */
void nmpuClearErrorStatus( nmpuBASE_t * nmpu )
{
    /* USER CODE BEGIN (18) */
    /* USER CODE END */

    nmpu->MPUERRSTAT = 1U;

    /* USER CODE BEGIN (19) */
    /* USER CODE END */
}
