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

/* USER CODE BEGIN (0) */
/* USER CODE END */

/** @fn void pmmInit(void)
 *   @brief Initializes the PMM Driver
 *
 *   This function initializes the PMM module.
 */
/* SourceId : PMM_SourceId_001 */
/* DesignId : PMM_DesignId_001 */
/* Requirements : HL_SR63 */
void pmmInit( void )
{
    /*Disable clocks to all logic domains*/
    pmmREG->PDCLKDISREG = 0xFU;
    /*Enable or disable clock to pmctrl_wakeup block and automatic clock wake up*/
    pmmREG->GLOBALCTRL1 = ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) 0U; /*from GUI*/
    /*Power on the logic power domains*/
    pmmREG->LOGICPDPWRCTRL0 = PMM_LOGICPDPWRCTRL0_CONFIGVALUE;
    /*Power on the memory-only power domains*/
    pmmREG->MEMPDPWRCTRL0 = PMM_MEMPDPWRCTRL0_CONFIGVALUE;

    /*wait till Logic Power Domain PD2 turns ON*/
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Wait for hardware status bit" */
    while( ( pmmREG->LOGICPDPWRSTAT[ PMM_LOGICPD2 ] & PMM_LOGICPDPWRSTAT_DOMAINON )
           == 0U )
    {
    } /* Wait */

    /*wait till Logic Power Domain PD3 turns ON*/
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Wait for hardware status bit" */
    while( ( pmmREG->LOGICPDPWRSTAT[ PMM_LOGICPD3 ] & PMM_LOGICPDPWRSTAT_DOMAINON )
           == 0U )
    {
    } /* Wait */

    /*wait till Logic Power Domain PD5 turns ON*/
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Wait for hardware status bit" */
    while( ( pmmREG->LOGICPDPWRSTAT[ PMM_LOGICPD5 ] & PMM_LOGICPDPWRSTAT_DOMAINON )
           == 0U )
    {
    } /* Wait */

    /*wait till Memory Only Power Domain RAM_PD1 turns ON*/
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Wait for hardware status bit" */
    while( ( pmmREG->MEMPDPWRSTAT[ PMM_MEMPD1 ] & PMM_MEMPDPWRSTAT_DOMAINON ) == 0U )
    {
    } /* Wait */

    /*wait till Memory Only Power Domain RAM_PD2 turns ON*/
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Wait for hardware status bit" */
    while( ( pmmREG->MEMPDPWRSTAT[ PMM_MEMPD2 ] & PMM_MEMPDPWRSTAT_DOMAINON ) == 0U )
    {
    } /* Wait */

    if( ( pmmREG->GLOBALCTRL1 & PMM_GLOBALCTRL1_AUTOCLKWAKEENA ) == 0U )
    {
        /* Enable clocks for the selected logic domain */
        pmmREG->PDCLKDISREG = PMM_PDCLKDISREG_CONFIGVALUE;
    }
}

/** @fn void pmmTurnONLogicPowerDomain(pmm_LogicPD_t logicPD)
 *   @brief Turns on Logic Power Domain
 *   @param[in] logicPD - Power Domain to be turned on
 *              - PMM_LOGICPD2: Power domain PD2 will be turned on
 *              - PMM_LOGICPD3: Power domain PD3 will be turned on
 *              - PMM_LOGICPD4: Power domain PD4 will be turned on
 *              - PMM_LOGICPD5: Power domain PD5 will be turned on
 *
 *   This function turns on the selected Logic Power Domain
 *
 */
/* SourceId : PMM_SourceId_002 */
/* DesignId : PMM_DesignId_002 */
/* Requirements : HL_SR67 */
void pmmTurnONLogicPowerDomain( pmm_LogicPD_t logicPD )
{
    if( logicPD != PMM_LOGICPD1 )
    {
        /* Power on the domain */
        if( logicPD == PMM_LOGICPD2 )
        {
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xF0FFFFFFU )
                                    | 0x05000000U;
        }
        else if( logicPD == PMM_LOGICPD3 )
        {
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFF0FFFFU )
                                    | 0x00050000U;
        }
        else if( logicPD == PMM_LOGICPD4 )
        {
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFFFF0FFU )
                                    | 0x00000500U;
        }
        else
        {
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFFFFFF0U )
                                    | 0x00000005U;
        }

        /* Wait until the power domain turns on */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Wait for hardware status bit" */
        while( ( pmmREG->LOGICPDPWRSTAT[ logicPD ] & PMM_LOGICPDPWRSTAT_DOMAINON ) == 0U )
        {
        } /* Wait */

        if( ( pmmREG->GLOBALCTRL1 & PMM_GLOBALCTRL1_AUTOCLKWAKEENA ) == 0U )
        {
            /* Enable clocks to the power domain */
            pmmREG->PDCLKDISCLRREG = ( uint32 ) 1U << ( uint32 ) logicPD;
        }
    }
}

/** @fn void pmmTurnONMemPowerDomain(pmm_MemPD_t memPD)
 *   @brief Turns on Memory Power Domain
 *   @param[in] memPD - Power Domain to be tured on
 *              - PMM_MEMPD1: Power domain RAM_PD1 will be turned on
 *              - PMM_MEMPD2: Power domain RAM_PD2 will be turned on
 *              - PMM_MEMPD3: Power domain RAM_PD3 will be turned on
 *
 *   This function turns on the selected Memory Power Domain
 *
 */
/* SourceId : PMM_SourceId_003 */
/* DesignId : PMM_DesignId_003 */
/* Requirements : HL_SR66 */
void pmmTurnONMemPowerDomain( pmm_MemPD_t memPD )
{
    /* Power on the domain */
    if( memPD == PMM_MEMPD1 )
    {
        pmmREG->MEMPDPWRCTRL0 = ( pmmREG->MEMPDPWRCTRL0 & 0xF0FFFFFFU ) | 0x05000000U;
    }
    else if( memPD == PMM_MEMPD2 )
    {
        pmmREG->MEMPDPWRCTRL0 = ( pmmREG->MEMPDPWRCTRL0 & 0xFFF0FFFFU ) | 0x00050000U;
    }
    else
    {
        pmmREG->MEMPDPWRCTRL0 = ( pmmREG->MEMPDPWRCTRL0 & 0xFFFFF0FFU ) | 0x00000500U;
    }

    /*Wait until the power domain turns on*/
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Wait for hardware status bit" */
    while( ( pmmREG->MEMPDPWRSTAT[ memPD ] & PMM_MEMPDPWRSTAT_DOMAINON ) == 0U )
    {
    } /* Wait */
}

/** @fn void pmmTurnOFFLogicPowerDomain(pmm_LogicPD_t logicPD)
 *   @brief Turns off Logic Power Domain
 *    @param[in] logicPD - Power Domain to be tured off
 *              - PMM_LOGICPD2: Power domain PD2 will be turned off
 *              - PMM_LOGICPD3: Power domain PD3 will be turned off
 *              - PMM_LOGICPD4: Power domain PD4 will be turned off
 *              - PMM_LOGICPD5: Power doamin PD5 will be turned off
 *
 *   This function turns off the selected Logic Power Domain
 *
 */
/* SourceId : PMM_SourceId_004 */
/* DesignId : PMM_DesignId_004 */
/* Requirements : HL_SR67 */
void pmmTurnOFFLogicPowerDomain( pmm_LogicPD_t logicPD )
{
    if( logicPD != PMM_LOGICPD1 )
    {
        /* Disable all clocks to the power domain */
        pmmREG->PDCLKDISSETREG = ( uint32 ) 1U << ( uint32 ) logicPD;

        /* Power down the domain */
        if( logicPD == PMM_LOGICPD2 )
        {
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue*/
            pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xF0FFFFFFU )
                                    | 0x0A000000U;
        }
        else if( logicPD == PMM_LOGICPD3 )
        {
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFF0FFFFU )
                                    | 0x000A0000U;
        }
        else if( logicPD == PMM_LOGICPD4 )
        {
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFFFF0FFU )
                                    | 0x00000A00U;
        }
        else
        {
            /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
            pmmREG->LOGICPDPWRCTRL0 = ( pmmREG->LOGICPDPWRCTRL0 & 0xFFFFFFF0U )
                                    | 0x0000000AU;
        }

        /* Wait until the power domain turns off */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Wait for hardware status bit" */
        while( ( pmmREG->LOGICPDPWRSTAT[ logicPD ] & PMM_LOGICPDPWRSTAT_LOGICPDPWRSTAT )
               != 0U )
        {
        } /* Wait */
    }
}

/** @fn void pmmTurnOFFMemPowerDomain(pmm_MemPD_t memPD)
 *   @brief Turns off Memory Power Domain
 *   @param[in] memPD - Power Domain to be tured off
 *              - PMM_MEMPD1: Power domain RAM_PD1 will be turned off
 *              - PMM_MEMPD2: Power domain RAM_PD2 will be turned off
 *              - PMM_MEMPD3: Power domain RAM_PD3 will be turned off
 *
 *   This function turns off the selected Memory Power Domain
 *
 */
/* SourceId : PMM_SourceId_005 */
/* DesignId : PMM_DesignId_005 */
/* Requirements : HL_SR66 */
void pmmTurnOFFMemPowerDomain( pmm_MemPD_t memPD )
{
    /* Power down the domain */
    if( memPD == PMM_MEMPD1 )
    {
        pmmREG->MEMPDPWRCTRL0 = ( pmmREG->MEMPDPWRCTRL0 & 0xF0FFFFFFU ) | 0x0A000000U;
    }
    else if( memPD == PMM_MEMPD2 )
    {
        pmmREG->MEMPDPWRCTRL0 = ( pmmREG->MEMPDPWRCTRL0 & 0xFFF0FFFFU ) | 0x000A0000U;
    }
    else
    {
        pmmREG->MEMPDPWRCTRL0 = ( pmmREG->MEMPDPWRCTRL0 & 0xFFFFF0FFU ) | 0x00000A00U;
    }

    /*Wait until the power domain turns off*/
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Wait for hardware status bit" */
    while( ( pmmREG->MEMPDPWRSTAT[ memPD ] & PMM_MEMPDPWRSTAT_MEMPDPWRSTAT ) != 0U )
    {
    } /* Wait */
}

/** @fn boolean pmmIsLogicPowerDomainActive(pmm_LogicPD_t logicPD)
 *   @brief Check if the power domain is active or not
 *    @param[in] logicPD - Power Domain to be be checked
 *              - PMM_LOGICPD2: Checks whether Power domain PD2 is active or not
 *              - PMM_LOGICPD3: Checks whether Power domain PD3 is active or not
 *              - PMM_LOGICPD4: Checks whether Power domain PD4 is active or not
 *              - PMM_LOGICPD5: Checks whether Power domain PD5 is active or not
 *    @return The function will return:
 *              - TRUE : When the selected power domain is in Active state.
 *              - FALSE: When the selected power domain is in OFF state.
 *
 *   This function checks whether the selected power domain is active or not.
 *
 */
/* SourceId : PMM_SourceId_006 */
/* DesignId : PMM_DesignId_006 */
/* Requirements : HL_SR62 */
boolean pmmIsLogicPowerDomainActive( pmm_LogicPD_t logicPD )
{
    boolean status;

    if( ( pmmREG->LOGICPDPWRSTAT[ logicPD ] & PMM_LOGICPDPWRSTAT_DOMAINON ) == 0U )
    {
        status = FALSE;
    }
    else
    {
        status = TRUE;
    }

    return status;
}

/** @fn boolean pmmIsMemPowerDomainActive(pmm_MemPD_t memPD)
 *   @brief Check if the power domain is active or not
 *    @param[in] memPD - Power Domain to be tured off
 *              - PMM_MEMPD1: Checks whether Power domain RAM_PD1 is active or not
 *              - PMM_MEMPD2: Checks whether Power domain RAM_PD2 is active or not
 *              - PMM_MEMPD3: Checks whether Power domain RAM_PD3 is active or not
 *    @return The function will return:
 *              - TRUE : When the selected power domain is in Active state.
 *              - FALSE: When the selected power domain is in OFF state.
 *
 *   This function checks whether the selected power domain is active or not.
 *
 */
/* SourceId : PMM_SourceId_007 */
/* DesignId : PMM_DesignId_007 */
/* Requirements : HL_SR65 */
boolean pmmIsMemPowerDomainActive( pmm_MemPD_t memPD )
{
    boolean status;

    if( ( pmmREG->MEMPDPWRSTAT[ memPD ] & PMM_MEMPDPWRSTAT_DOMAINON ) == 0U )
    {
        status = FALSE;
    }
    else
    {
        status = TRUE;
    }

    return status;
}

/** @fn void pmmGetConfigValue(pmm_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration register
 *    @param[in] *config_reg - pointer to the struct to which the initial or current value
 * of the configuration registers need to be stored
 *    @param[in] type  -     whether initial or current value of the configuration
 * registers need to be stored
 *                        - InitialValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *                        - CurrentValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg This function will copy the initial
 * or current value (depending on the parameter 'type') of the configuration registers to
 * the struct pointed by config_reg
 */
/* SourceId : PMM_SourceId_008 */
/* DesignId : PMM_DesignId_008 */
/* Requirements : HL_SR64 */
void pmmGetConfigValue( pmm_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_LOGICPDPWRCTRL0 = PMM_LOGICPDPWRCTRL0_CONFIGVALUE;
        config_reg->CONFIG_MEMPDPWRCTRL0 = PMM_MEMPDPWRCTRL0_CONFIGVALUE;
        config_reg->CONFIG_PDCLKDISREG = PMM_PDCLKDISREG_CONFIGVALUE;
        config_reg->CONFIG_GLOBALCTRL1 = PMM_GLOBALCTRL1_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_LOGICPDPWRCTRL0 = pmmREG->LOGICPDPWRCTRL0;
        config_reg->CONFIG_MEMPDPWRCTRL0 = pmmREG->MEMPDPWRCTRL0;
        config_reg->CONFIG_PDCLKDISREG = pmmREG->PDCLKDISREG;
        config_reg->CONFIG_GLOBALCTRL1 = pmmREG->GLOBALCTRL1;
    }
}

/** @fn void pmmSetMode(pmm_Mode_t mode)
 *   @brief Set PSCON Compare Block Mode
 *    @param[in] mode - PSCON Compare Block mode
 *                - LockStep                : PSCON compare block is set to Lock-Step mode
 *                - SelfTest                : PSCON compare block is set to Self-Test mode
 *                - ErrorForcing            : PSCON compare block is set to Error-Forcing
 * mode
 *                - SelfTestErrorForcing    : PSCON compare block is set to
 * Self-Test-Error-Forcing mode
 *
 *   This function sets the PSCON Compare block to the selected mode
 *
 */
/* SourceId : PMM_SourceId_009 */
/* DesignId : PMM_DesignId_009 */
/* Requirements : HL_SR68 */
void pmmSetMode( pmm_Mode_t mode )
{
    /* Set PSCON Compare Block Mode */
    pmmREG->PRCKEYREG = mode;
}

/** @fn boolean pmmPerformSelfTest(void)
 *   @brief Perform self test and return the result
 *
 *    @return The function will return
 *            - TRUE if PSCON compare block passed self-test
 *            - FALSE if PSCON compare block failed in self-test
 *
 *   This function checks whether PSCON compare block passed the self-test or not.
 *
 */
/* SourceId : PMM_SourceId_010 */
/* DesignId : PMM_DesignId_010 */
/* Requirements : HL_SR72 */
boolean pmmPerformSelfTest( void )
{
    boolean status = TRUE;

    /*Enter self-test mode*/
    pmmREG->PRCKEYREG = ( uint32 ) SelfTest;

    /*Wait till self test is completed*/
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( pmmREG->LPDDCSTAT1 & 0xFU ) != 0xFU )
    {
    } /* Wait */

    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( pmmREG->MPDDCSTAT1 & 0x3U ) != 0x3U )
    {
    } /* Wait */

    /*Check whether self-test passed or not*/
    if( ( pmmREG->LPDDCSTAT2 & 0xFU ) != 0U )
    {
        status = FALSE;
    }

    if( ( pmmREG->MPDDCSTAT2 & 0x7U ) != 0U )
    {
        status = FALSE;
    }

    /*Enter lock-step mode*/
    pmmREG->PRCKEYREG = ( uint32 ) LockStep;

    return status;
}

/* USER CODE BEGIN (1) */
/* USER CODE END */
