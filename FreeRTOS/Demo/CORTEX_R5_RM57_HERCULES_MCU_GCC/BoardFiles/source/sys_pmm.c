/** @file sys_pmm.c
 *   @brief PCR Driver Implementation File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
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

#include "sys_pmm.h"

#define PMM_LODICPWRSTAT   0x3U
#define PMM_DOMAINON       0x100U
#define PMM_AUTOCLKWAKEENA 0x1U

/** @fn void pmmTurnONLogicPowerDomain(pmm_LogicPD_t logicPD)
 *   @brief Turns on Logic Power Domain
 *   @param[in] logicPD - Power Domain to be turned on
 *              - PMM_LOGICPD2: Power domain PD2 will be turned on
 *              - PMM_LOGICPD3: Power domain PD3 will be turned on
 *              - PMM_LOGICPD4: Power domain PD4 will be turned on
 *              - PMM_LOGICPD5: Power domain PD5 will be turned on
 *              - PMM_LOGICPD6: Power domain PD6 will be turned on
 *
 *   This function turns on the selected Logic Power Domain
 *
 */
/* SourceId : PMM_SourceId_001 */
/* DesignId : PMM_DesignId_001 */
/* Requirements : CONQ_PMM_SR3 */
boolean pmmTurnONLogicPowerDomain( pmm_LogicPD_t logicPD )
{
    boolean status = TRUE;

    /* USER CODE BEGIN (0) */
    /* USER CODE END */

    /* Power On the domain */
    if( logicPD == PMM_LOGICPD2 )
    {
        pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xF0FFFFFFU ) | 0x05000000U;
    }
    else if( logicPD == PMM_LOGICPD3 )
    {
        pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFF0FFFFU ) | 0x00050000U;
    }
    else if( logicPD == PMM_LOGICPD4 )
    {
        pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFFFF0FFU ) | 0x00000500U;
    }
    else if( logicPD == PMM_LOGICPD5 )
    {
        pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFFFFFF0U ) | 0x00000005U;
    }
    else if( logicPD == PMM_LOGICPD6 )
    {
        pmmREG->LOGICPDPWRCTRL1 = 0x05000000U;
    }
    else
    {
        /* Invalid input */
        status = FALSE;
    }

    if( status == TRUE )
    {
        if( ( pmmREG->GLOBALCTRL1 & PMM_AUTOCLKWAKEENA ) == 0U )
        {
            /* Enable clocks to the power domain */
            pmmREG->PDCLKDISCLR = ( uint32 ) 1U << logicPD;
        }

        /* Wait until the domain is powered on */
        while( ( pmmREG->LOGICPDPWRSTAT[ logicPD ] & PMM_DOMAINON ) == 0U )
        {
            /* Add timeout code here */
        }
    }

    /* USER CODE BEGIN (1) */
    /* USER CODE END */

    return status;
}

/** @fn void pmmTurnOFFLogicPowerDomain(pmm_LogicPD_t logicPD)
 *   @brief Turns off Logic Power Domain
 *    @param[in] logicPD - Power Domain to be tured off
 *              - PMM_LOGICPD2: Power domain PD2 will be turned off
 *              - PMM_LOGICPD3: Power domain PD3 will be turned off
 *              - PMM_LOGICPD4: Power domain PD4 will be turned off
 *              - PMM_LOGICPD5: Power doamin PD5 will be turned off
 *              - PMM_LOGICPD6: Power doamin PD5 will be turned off
 *
 *   This function turns off the selected Logic Power Domain
 *
 */
/* SourceId : PMM_SourceId_002 */
/* DesignId : PMM_DesignId_002 */
/* Requirements : CONQ_PMM_SR4 */
boolean pmmTurnOFFLogicPowerDomain( pmm_LogicPD_t logicPD )
{
    boolean status = TRUE;

    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    /* Disable clocks to the power domain */
    pmmREG->PDCLKDISSET = ( uint32 ) 1U << logicPD;

    /* Power Down the domain */
    if( logicPD == PMM_LOGICPD2 )
    {
        pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xF0FFFFFFU ) | 0x0A000000U;
    }
    else if( logicPD == PMM_LOGICPD3 )
    {
        pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFF0FFFFU ) | 0x000A0000U;
    }
    else if( logicPD == PMM_LOGICPD4 )
    {
        pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFFFF0FFU ) | 0x00000A00U;
    }
    else if( logicPD == PMM_LOGICPD5 )
    {
        pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFFFFFF0U ) | 0x0000000AU;
    }
    else if( logicPD == PMM_LOGICPD6 )
    {
        pmmREG->LOGICPDPWRCTRL1 = 0x0A000000U;
    }
    else
    {
        /* Invalid input */
        status = FALSE;
    }

    if( status == TRUE )
    {
        /* Wait until the domain is powered down */
        while( ( pmmREG->LOGICPDPWRSTAT[ logicPD ] & PMM_LODICPWRSTAT ) != 0U )
        {
            /* Add timeout code here */
        }
    }

    /* USER CODE BEGIN (3) */
    /* USER CODE END */

    return status;
}

/** @fn boolean pmmIsLogicPowerDomainActive(pmm_LogicPD_t logicPD)
 *   @brief Check if the power domain is active or not
 *    @param[in] logicPD - Power Domain to be be checked
 *              - PMM_LOGICPD2: Checks whether Power domain PD2 is active or not
 *              - PMM_LOGICPD3: Checks whether Power domain PD3 is active or not
 *              - PMM_LOGICPD4: Checks whether Power domain PD4 is active or not
 *              - PMM_LOGICPD5: Checks whether Power domain PD5 is active or not
 *              - PMM_LOGICPD6: Checks whether Power domain PD6 is active or not
 *    @return The function will return:
 *              - TRUE : When the selected power domain is in Active state.
 *              - FALSE: When the selected power domain is in OFF state.
 *
 *   This function checks whether the selected power domain is active or not.
 *
 */
/* SourceId : PMM_SourceId_003 */
/* DesignId : PMM_DesignId_003 */
/* Requirements : CONQ_PMM_SR5 */
boolean pmmIsLogicPowerDomainActive( pmm_LogicPD_t logicPD )
{
    boolean status;

    /* USER CODE BEGIN (4) */
    /* USER CODE END */

    if( logicPD == PMM_LOGICPD1 )
    {
        status = TRUE;
    }
    else
    {
        if( ( pmmREG->LOGICPDPWRSTAT[ logicPD ] & PMM_LODICPWRSTAT ) == 0U )
        {
            status = FALSE;
        }
        else
        {
            status = TRUE;
        }
    }

    /* USER CODE BEGIN (5) */
    /* USER CODE END */

    return status;
}
