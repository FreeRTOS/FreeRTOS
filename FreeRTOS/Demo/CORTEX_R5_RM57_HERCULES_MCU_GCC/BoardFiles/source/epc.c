/** @file epc.c
 *   @brief EPC Driver Implementation File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *   This file contains APIs for the Error Profiling Controller Module.
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

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "epc.h"
#include "system.h"
#include "reg_esm.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @fn void epcEnableIP1ErrorGen(void)
 *   @brief Enable ECC error generation for ECC errors on DMA Port A
 *
 *   Enable ECC error generation for ECC errors detected on DMA Port A master by the
 *   CPU Interconnect Subsystem
 */
/* SourceId : EPC_SourceId_001 */
/* DesignId : EPC_DesignId_001 */
/* Requirements : CONQ_EPC_SR1 */
void epcEnableIP1ErrorGen( void )
{
    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    systemREG2->IP1ECCERREN = ( systemREG2->IP1ECCERREN & 0xFFFFFFF0U ) | 0xAU;

    /* USER CODE BEGIN (3) */
    /* USER CODE END */
}

/** @fn void epcDisableIP1ErrorGen(void)
 *   @brief Disable ECC error generation for ECC errors on DMA Port A
 *
 *   Disable ECC error generation for ECC errors detected on DMA Port A master by the
 *   CPU Interconnect Subsystem
 */
/* SourceId : EPC_SourceId_002 */
/* DesignId : EPC_DesignId_002 */
/* Requirements : CONQ_EPC_SR2 */
void epcDisableIP1ErrorGen( void )
{
    /* USER CODE BEGIN (4) */
    /* USER CODE END */

    systemREG2->IP1ECCERREN = ( systemREG2->IP1ECCERREN & 0xFFFFFFF0U ) | 0x5U;

    /* USER CODE BEGIN (5) */
    /* USER CODE END */
}

/** @fn void epcEnableIP2ErrorGen(void)
 *   @brief Enable ECC error generation for ECC errors on PS_SCR_M
 *
 *   Enable ECC error generation for ECC errors detected on PS_SCR_M master by the
 *   CPU Interconnect Subsystem
 */
/* SourceId : EPC_SourceId_003 */
/* DesignId : EPC_DesignId_003 */
/* Requirements : CONQ_EPC_SR3 */
void epcEnableIP2ErrorGen( void )
{
    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    systemREG2->IP1ECCERREN = ( systemREG2->IP1ECCERREN & 0xFFFFF0FFU ) | 0xA00U;

    /* USER CODE BEGIN (7) */
    /* USER CODE END */
}

/** @fn void epcDisableIP2ErrorGen(void)
 *   @brief Disable ECC error generation for ECC errors on PS_SCR_M
 *
 *   Disable ECC error generation for ECC errors detected on PS_SCR_M master by the
 *   CPU Interconnect Subsystem
 */
/* SourceId : EPC_SourceId_004 */
/* DesignId : EPC_DesignId_004 */
/* Requirements : CONQ_EPC_SR4 */
void epcDisableIP2ErrorGen( void )
{
    /* USER CODE BEGIN (8) */
    /* USER CODE END */

    systemREG2->IP1ECCERREN = ( systemREG2->IP1ECCERREN & 0xFFFFF0FFU ) | 0x500U;

    /* USER CODE BEGIN (9) */
    /* USER CODE END */
}

/** @fn void epcEnableSERREvent(void)
 *   @brief Single (correctable) bit error event enable.
 *
 *   These bits (when enabled) cause EPC to
 *   generate the serr_event if there is a correctable ECC fault address arrives from one
 * of the EPC-IP interface and the CAM has an empty entry.
 */
/* SourceId : EPC_SourceId_005 */
/* DesignId : EPC_DesignId_005 */
/* Requirements : CONQ_EPC_SR5 */
void epcEnableSERREvent( void )
{
    /* USER CODE BEGIN (10) */
    /* USER CODE END */

    epcREG1->EPCCNTRL = ( epcREG1->EPCCNTRL & 0xFFFFFFF0U ) | 0xAU;

    /* USER CODE BEGIN (11) */
    /* USER CODE END */
}

/** @fn void epcDisableSERREvent(void)
 *   @brief Single (correctable) bit error event disable.
 *
 *   These bits (when enabled) cause EPC to
 *   disable the serr_event generation.
 */
/* SourceId : EPC_SourceId_006 */
/* DesignId : EPC_DesignId_006 */
/* Requirements : CONQ_EPC_SR6 */
void epcDisableSERREvent( void )
{
    /* USER CODE BEGIN (12) */
    /* USER CODE END */

    epcREG1->EPCCNTRL = ( epcREG1->EPCCNTRL & 0xFFFFFFF0U ) | 0x5U;

    /* USER CODE BEGIN (13) */
    /* USER CODE END */
}

/** @fn void epcEnableInterrupt(void)
 *   @brief CAM or FIFO full interrupt enable.
 *
 *   If this bit is set and CAM is full, CAM Full Interrupt
 *   is generated.
 */
/* SourceId : EPC_SourceId_007 */
/* DesignId : EPC_DesignId_007 */
/* Requirements : CONQ_EPC_SR7 */
void epcEnableInterrupt( void )
{
    /* USER CODE BEGIN (14) */
    /* USER CODE END */

    epcREG1->EPCCNTRL |= ( uint32 ) ( ( uint32 ) 1U << 24U );

    /* USER CODE BEGIN (15) */
    /* USER CODE END */
}

/** @fn void epcDisableInterrupt(void)
 *   @brief CAM or FIFO full interrupt disable.
 *
 *   Disables interrupt generation in case CAM is full.
 */
/* SourceId : EPC_SourceId_008 */
/* DesignId : EPC_DesignId_008 */
/* Requirements : CONQ_EPC_SR8 */
void epcDisableInterrupt( void )
{
    /* USER CODE BEGIN (16) */
    /* USER CODE END */

    epcREG1->EPCCNTRL &= ~( uint32 ) ( ( uint32 ) 1U << 24U );

    /* USER CODE BEGIN (17) */
    /* USER CODE END */
}

/** @fn void epcCAMInit(void)
 *   @brief Initializes CAM.
 *
 *   CAM entries are cleared and available for future CAM usage.
 */
/* SourceId : EPC_SourceId_009 */
/* DesignId : EPC_DesignId_009 */
/* Requirements : CONQ_EPC_SR9 */
void epcCAMInit( void )
{
    uint8 i;
    /* USER CODE BEGIN (18) */
    /* USER CODE END */

    for( i = 0U; i < 8U; i++ )
    {
        epcREG1->CAM_INDEX[ i ] = 0x05050505U;
    }
    /* USER CODE BEGIN (19) */
    /* USER CODE END */
}

/** @fn void epcDiagnosticTest(void)
 *   @brief CAM diagnostic test.
 *   @return TRUE if diagnostic test passed, FALSE otherwise
 *
 *   This function executes a diagnostic test on EPC and returns the result
 */
/* SourceId : EPC_SourceId_010 */
/* DesignId : EPC_DesignId_010 */
/* Requirements : CONQ_EPC_SR14 */
boolean epcDiagnosticTest( void )
{
    uint32 epccntrl_bk, camCont_bk, camIndex_bk;
    uint32 camAvailable;
    boolean status = true;

    /* USER CODE BEGIN (20) */
    /* USER CODE END */

    /* Back up EPCCNTRL register */
    epccntrl_bk = epcREG1->EPCCNTRL;

    /* Back up CAM_CONTENT[0] and CAM_INDEX[0] registers */
    camCont_bk = epcREG1->CAM_CONTENT[ 0U ];
    camIndex_bk = epcREG1->CAM_INDEX[ 0U ];

    /* Enter CAM diagnostic mode and and enable Single (correctable) bit error event
     * generation */
    epcREG1->EPCCNTRL = ( epcREG1->EPCCNTRL & 0xFFFFF0F0U ) | 0x0A0AU;

    /* Clear first CAM entry */
    epcREG1->CAM_INDEX[ 0U ] = ( epcREG1->CAM_INDEX[ 0U ] & 0xFFFFFFF0U ) | 0x5U;

    /* Identify the number of CAM entries available */
    camAvailable = epcREG1->CAMAVAILSTAT;

    /* New CAM Entry */
    epcREG1->CAM_CONTENT[ 0U ] = 0x1000U;

    /* The number of CAM entries must reduce by 1 */
    if( ( ( esmREG->SR1[ 0U ] & 0x10U ) != 0x10U )
        || ( epcREG1->CAMAVAILSTAT != ( camAvailable - 1U ) )
        || ( epcCheckCAMEntry( 0U ) == true ) )
    {
        status = false;
    }

    /* Restore CAM_CONTENT and CAM_INDEX[0] registers */
    epcREG1->CAM_CONTENT[ 0U ] = camCont_bk;
    epcREG1->CAM_INDEX[ 0U ] = camIndex_bk;

    /* Disable CAM diagnostic mode and restore EPCCNTRL register */
    epcREG1->EPCCNTRL = epccntrl_bk;

    /* USER CODE BEGIN (21) */
    /* USER CODE END */

    return status;
}

/** @fn void epcAddCAMEEntry(uint32 address)
 *   @brief Add a new CAM Entry
 *
 *   Allows you to write a new CAM entry, after checking if there are any available
 * entries.
 */
/* SourceId : EPC_SourceId_011 */
/* DesignId : EPC_DesignId_011 */
/* Requirements : CONQ_EPC_SR10 */
boolean epcAddCAMEEntry( uint32 address )
{
    uint8 i = 0U;
    boolean status = false;

    /* USER CODE BEGIN (22) */
    /* USER CODE END */

    if( epcREG1->CAMAVAILSTAT != 0U )
    {
        for( i = 0U; i < 32U; i++ )
        {
            if( epcCheckCAMEntry( i ) == true )
            {
                epcREG1->CAM_CONTENT[ i ] = address;
                status = true;
                break;
            }
        }
    }
    else
    {
        status = false;
    }

    /* USER CODE BEGIN (23) */
    /* USER CODE END */

    return status;
}

/** @fn void epcCheckCAMEntry(uint32 CAMIndex)
 *   @brief Checks if CAM entry is available.
 *
 *   Checks if the CAM Entry is available and ready for future usage.
 */
/* SourceId : EPC_SourceId_012 */
/* DesignId : EPC_DesignId_012 */
/* Requirements : CONQ_EPC_SR11 */
boolean epcCheckCAMEntry( uint32 index )
{
    uint32 i, j;
    boolean status = false;

    /* USER CODE BEGIN (24) */
    /* USER CODE END */

    i = index / 4U;
    j = ( index % 4U ) * 8U;

    /* Check for availability of CAM Entry for future CAM usage. */
    if( ( epcREG1->CAM_INDEX[ i ] & ( uint32 ) ( ( uint32 ) 0xFU << j ) )
        == ( uint32 ) ( ( uint32 ) 0x5U << j ) )
    {
        status = true;
    }
    else
    {
        status = false;
    }

    /* USER CODE BEGIN (25) */
    /* USER CODE END */
    return status;
}

/* USER CODE BEGIN (28) */
/* USER CODE END */
