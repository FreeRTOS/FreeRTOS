/** @file dcc.c
 *   @brief DCC Driver Implementation File
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

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "dcc.h"
#include "sys_vim.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/* SourceId : DCC_SourceId_001 */
/* DesignId : DCC_DesignId_001 */
/* Requirements : CONQ_DCC_SR4 */
/** @fn void dccInit(void)
 *   @brief Initializes the DCC Driver
 *
 *   This function initializes the DCC module.
 */
void dccInit( void )
{
    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    /** @b initialize @b DCC1 */

    /** DCC1 Clock0 Counter Seed value configuration */
    dccREG1->CNT0SEED = 39204U;

    /** DCC1 Clock0 Valid Counter Seed value configuration */
    dccREG1->VALID0SEED = 792U;

    /** DCC1 Clock1 Counter Seed value configuration */
    dccREG1->CNT1SEED = 742500U;

    /** DCC1 Clock1 Source 1 Select */
    dccREG1->CNT1CLKSRC = ( uint32 ) ( ( uint32 ) 10U << 12U ) | /** DCC Enable / Disable
                                                                    Key */
                          ( uint32 ) DCC1_CNT1_PLL1; /** DCC1 Clock Source 1 */

    dccREG1->CNT0CLKSRC = ( uint32 ) DCC1_CNT0_OSCIN; /** DCC1 Clock Source 0 */

    /** DCC1 Global Control register configuration */
    dccREG1->GCTRL = ( uint32 ) 0xAU |                      /** Enable / Disable DCC1 */
                     ( uint32 ) ( ( uint32 ) 0xAU << 4U ) | /** Error Interrupt */
                     ( uint32 ) ( ( uint32 ) 0x5U << 8U ) | /** Single Shot mode */
                     ( uint32 ) ( ( uint32 ) 0xAU << 12U ); /** Done Interrupt */

    /** @b initialize @b DCC2 */

    /** DCC2 Clock0 Counter Seed value configuration */
    dccREG2->CNT0SEED = 0U;

    /** DCC2 Clock0 Valid Counter Seed value configuration */
    dccREG2->VALID0SEED = 0U;

    /** DCC2 Clock1 Counter Seed value configuration */
    dccREG2->CNT1SEED = 0U;

    /** DCC2 Clock1 Source 1 Select */
    dccREG2->CNT1CLKSRC = ( uint32 ) ( ( uint32 ) 0xAU << 12U ) | /** DCC Enable Key */
                          ( uint32 ) DCC2_CNT1_VCLK; /** DCC2 Clock Source 1 */

    dccREG2->CNT0CLKSRC = ( uint32 ) DCC2_CNT0_OSCIN; /** DCC2 Clock Source 0 */

    /** DCC2 Global Control register configuration */
    dccREG2->GCTRL = ( uint32 ) 0xAU |                      /** Enable DCC2 */
                     ( uint32 ) ( ( uint32 ) 0xAU << 4U ) | /** Error Interrupt */
                     ( uint32 ) ( ( uint32 ) 0x5U << 8U ) | /** Single Shot mode */
                     ( uint32 ) ( ( uint32 ) 0xAU << 12U ); /** Done Interrupt */

    /* USER CODE BEGIN (3) */
    /* USER CODE END */
}

/* SourceId : DCC_SourceId_002 */
/* DesignId : DCC_DesignId_002 */
/* Requirements : CONQ_DCC_SR5 */
/** @fn void dccSetCounter0Seed(dccBASE_t  *dcc, uint32 cnt0seed)
 *   @brief Set dcc Clock source 0 counter seed value
 *   @param[in] dcc Pointer to DCC module:
 *              - dccREG1: DCC1 module pointer
 *              - dccREG2: DCC2 module pointer
 *   @param[in] cnt0seed - Clock Source 0 Counter seed value
 *
 *   This function sets the seed value for Clock source 0 counter.
 *
 */
void dccSetCounter0Seed( dccBASE_t * dcc, uint32 cnt0seed )
{
    /* USER CODE BEGIN (4) */
    /* USER CODE END */

    dcc->CNT0SEED = cnt0seed;

    /* USER CODE BEGIN (5) */
    /* USER CODE END */
}

/* SourceId : DCC_SourceId_003 */
/* DesignId : DCC_DesignId_003 */
/* Requirements : CONQ_DCC_SR6 */
/** @fn void dccSetTolerance(dccBASE_t  *dcc, uint32 valid0seed)
 *   @brief Set dcc Clock source 0 counter seed value
 *   @param[in] dcc Pointer to DCC module:
 *              - dccREG1: DCC1 module pointer
 *              - dccREG2: DCC2 module pointer
 *   @param[in] valid0seed - Clock Source 0 Counter tolerance value
 *
 *   This function sets the seed value for Clock source 0 tolerance or
 *    valid counter.
 *
 */
void dccSetTolerance( dccBASE_t * dcc, uint32 valid0seed )
{
    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    dcc->VALID0SEED = valid0seed;

    /* USER CODE BEGIN (7) */
    /* USER CODE END */
}

/* SourceId : DCC_SourceId_004 */
/* DesignId : DCC_DesignId_004 */
/* Requirements : CONQ_DCC_SR7 */
/** @fn void dccSetCounter1Seed(dccBASE_t  *dcc, uint32 cnt1seed)
 *   @brief Set dcc Clock source 1 counter seed value
 *   @param[in] dcc Pointer to DCC module:
 *              - dccREG1: DCC1 module pointer
 *              - dccREG2: DCC2 module pointer
 *   @param[in] cnt1seed - Clock Source 1 Counter seed value
 *
 *   This function sets the seed value for Clock source 1 counter.
 *
 */
void dccSetCounter1Seed( dccBASE_t * dcc, uint32 cnt1seed )
{
    /* USER CODE BEGIN (8) */
    /* USER CODE END */

    dcc->CNT1SEED = cnt1seed;

    /* USER CODE BEGIN (9) */
    /* USER CODE END */
}

/* SourceId : DCC_SourceId_005 */
/* DesignId : DCC_DesignId_005 */
/* Requirements : CONQ_DCC_SR8 */
/** @fn void dccSetSeed(dccBASE_t  *dcc, uint32 cnt0seed, uint32 valid0seed, uint32
 * cnt1seed)
 *   @brief Set dcc Clock source 0 counter seed value
 *   @param[in] dcc Pointer to DCC module:
 *              - dccREG1: DCC1 module pointer
 *              - dccREG2: DCC2 module pointer
 *   @param[in] cnt0seed        - Clock Source 0 Counter seed value.
 *   @param[in] valid0seed    - Clock Source 0 Counter tolerance value.
 *   @param[in] cnt1seed        - Clock Source 1 Counter seed value.
 *
 *   This function sets the seed value for clock source 0, clock source 1
 *    and tolerance counter.
 *
 */
void dccSetSeed( dccBASE_t * dcc, uint32 cnt0seed, uint32 valid0seed, uint32 cnt1seed )
{
    /* USER CODE BEGIN (10) */
    /* USER CODE END */

    dcc->CNT0SEED = cnt0seed;
    dcc->VALID0SEED = valid0seed;
    dcc->CNT1SEED = cnt1seed;

    /* USER CODE BEGIN (11) */
    /* USER CODE END */
}

/* SourceId : DCC_SourceId_006 */
/* DesignId : DCC_DesignId_006 */
/* Requirements : CONQ_DCC_SR9 */
/** @fn void dccSelectClockSource(dccBASE_t  *dcc, uint32 cnt0_Clock_Source, uint32
 * cnt1_Clock_Source)
 *   @brief Set dcc counter Clock sources
 *   @param[in] dcc Pointer to DCC module:
 *              - dccREG1: DCC1 module pointer
 *              - dccREG2: DCC2 module pointer
 *   @param[in] cnt0_Clock_Source - Clock source for counter 0.
 *   @param[in] cnt1_Clock_Source - Clock source for counter 1.
 *
 *   This function sets the dcc counter 0 and counter 1 clock sources.
 *   DCC must be disabled using dccDisable API before calling this
 *   function.
 */
void dccSelectClockSource( dccBASE_t * dcc,
                           uint32 cnt0_Clock_Source,
                           uint32 cnt1_Clock_Source )
{
    /* USER CODE BEGIN (12) */
    /* USER CODE END */

    dcc->CNT1CLKSRC = ( ( uint32 ) ( ( uint32 ) 0xAU << 12U ) | /** DCC Enable Key */
                        ( uint32 ) ( cnt1_Clock_Source
                                     & 0x0000000FU ) ); /* Configure Clock source 1 */
    dcc->CNT0CLKSRC = cnt0_Clock_Source;                /* Configure Clock source 0 */

    /* USER CODE BEGIN (13) */
    /* USER CODE END */
}

/* SourceId : DCC_SourceId_007 */
/* DesignId : DCC_DesignId_007 */
/* Requirements : CONQ_DCC_SR10 */
/** @fn void dccEnable(dccBASE_t  *dcc)
 *   @brief Enable dcc module to begin counting
 *   @param[in] dcc Pointer to DCC module:
 *              - dccREG1: DCC1 module pointer
 *              - dccREG2: DCC2 module pointer
 *
 *   This function enables the dcc counters to begin counting.
 *
 */
void dccEnable( dccBASE_t * dcc )
{
    /* USER CODE BEGIN (14) */
    /* USER CODE END */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Hardware status bit read check" */
    dcc->GCTRL = ( dcc->GCTRL & 0xFFFFFFF0U ) | 0xAU;

    /* USER CODE BEGIN (15) */
    /* USER CODE END */
}

/* SourceId : DCC_SourceId_008 */
/* DesignId : DCC_DesignId_008 */
/* Requirements : CONQ_DCC_SR21 */
/** @fn void dccDisable(dccBASE_t  *dcc)
 *   @brief Make selected dcc module to stop counting
 *   @param[in] dcc Pointer to DCC module:
 *              - dccREG1: DCC1 module pointer
 *              - dccREG2: DCC2 module pointer
 *
 *   This function stops the dcc counters from counting.
 *
 */
void dccDisable( dccBASE_t * dcc )
{
    /* USER CODE BEGIN (16) */
    /* USER CODE END */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Hardware status bit read check" */
    dcc->GCTRL = ( dcc->GCTRL & 0xFFFFFFF0U ) | 0x5U;

    /* USER CODE BEGIN (17) */
    /* USER CODE END */
}

/* SourceId : DCC_SourceId_009 */
/* DesignId : DCC_DesignId_009 */
/* Requirements : CONQ_DCC_SR12 */
/** @fn uint32 dccGetErrStatus(dccBASE_t  *dcc)
 *   @brief Get error status from selected dcc module
 *   @param[in] dcc Pointer to DCC module:
 *              - dccREG1: DCC1 module pointer
 *              - dccREG2: DCC2 module pointer
 *
 *   @return The Error status of selected dcc module
 *
 *   Returns the error status of selected dcc module.
 *
 */
uint32 dccGetErrStatus( dccBASE_t * dcc )
{
    /* USER CODE BEGIN (18) */
    /* USER CODE END */

    return ( dcc->STAT & 0x00000001U );
}

/* SourceId : DCC_SourceId_010 */
/* DesignId : DCC_DesignId_010 */
/* Requirements : CONQ_DCC_SR13 */
/** @fn void dccEnableNotification(dccBASE_t  *dcc, uint32 notification)
 *   @brief Enable notification of selected DCC module
 *   @param[in] dcc Pointer to DCC module:
 *              - dccREG1: DCC1 module pointer
 *              - dccREG2: DCC2 module pointer
 *   @param[in] notification Select notification of DCC module:
 *              - dccNOTIFICATION_DONE:    DCC DONE notification
 *              - dccNOTIFICATION_ERROR: DCC ERROR notification
 *
 *   This function will enable the selected notification of a DCC module.
 *   It is possible to enable multiple notifications masked.
 */

void dccEnableNotification( dccBASE_t * dcc, uint32 notification )
{
    /* USER CODE BEGIN (19) */
    /* USER CODE END */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Hardware status bit read check" */
    dcc->GCTRL = ( ( dcc->GCTRL & 0xFFFF0F0FU ) | notification );

    /* USER CODE BEGIN (20) */
    /* USER CODE END */
}

/* SourceId : DCC_SourceId_011 */
/* DesignId : DCC_DesignId_011 */
/* Requirements : CONQ_DCC_SR14 */
/** @fn void dccDisableNotification(dccBASE_t  *dcc, uint32 notification)
 *   @brief Disable notification of selected DCC module
 *   @param[in] dcc Pointer to DCC module:
 *              - dccREG1: DCC1 module pointer
 *              - dccREG2: DCC2 module pointer
 *   @param[in] notification Select notification of DCC module:
 *              - dccNOTIFICATION_DONE:    DCC DONE notification
 *              - dccNOTIFICATION_ERROR: DCC ERROR notification
 *
 *   This function will enable the selected notification of a DCC module.
 *   It is possible to enable multiple notifications masked.
 */

void dccDisableNotification( dccBASE_t * dcc, uint32 notification )
{
    /* USER CODE BEGIN (21) */
    /* USER CODE END */
    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Hardware status bit read check" */
    dcc->GCTRL = ( ( dcc->GCTRL & 0xFFFF0F0FU ) | ( ( ~notification ) & 0x0000F0F0U ) );

    /* USER CODE BEGIN (22) */
    /* USER CODE END */
}

/* SourceId : DCC_SourceId_012 */
/* DesignId : DCC_DesignId_012 */
/* Requirements : CONQ_DCC_SR18 */
/** @fn void dcc1GetConfigValue(dcc_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *    @param[in] *config_reg: pointer to the struct to which the initial or current value
 * of the configuration registers need to be stored
 *    @param[in] type:     whether initial or current value of the configuration registers
 * need to be stored
 *                        - InitialValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *                        - CurrentValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */

void dcc1GetConfigValue( dcc_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_GCTRL = DCC1_GCTRL_CONFIGVALUE;
        config_reg->CONFIG_CNT0SEED = DCC1_CNT0SEED_CONFIGVALUE;
        config_reg->CONFIG_VALID0SEED = DCC1_VALID0SEED_CONFIGVALUE;
        config_reg->CONFIG_CNT1SEED = DCC1_CNT1SEED_CONFIGVALUE;
        config_reg->CONFIG_CNT1CLKSRC = DCC1_CNT1CLKSRC_CONFIGVALUE;
        config_reg->CONFIG_CNT0CLKSRC = DCC1_CNT0CLKSRC_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Hardware status bit read check" */
        config_reg->CONFIG_GCTRL = dccREG1->GCTRL;
        config_reg->CONFIG_CNT0SEED = dccREG1->CNT0SEED;
        config_reg->CONFIG_VALID0SEED = dccREG1->VALID0SEED;
        config_reg->CONFIG_CNT1SEED = dccREG1->CNT1SEED;
        config_reg->CONFIG_CNT1CLKSRC = dccREG1->CNT1CLKSRC;
        config_reg->CONFIG_CNT0CLKSRC = dccREG1->CNT0CLKSRC;
    }
}

/* SourceId : DCC_SourceId_013 */
/* DesignId : DCC_DesignId_012 */
/* Requirements : CONQ_DCC_SR19 */
/** @fn void dcc2GetConfigValue(rti_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *    @param[in] *config_reg: pointer to the struct to which the initial or current value
 * of the configuration registers need to be stored
 *    @param[in] type:     whether initial or current value of the configuration registers
 * need to be stored
 *                        - InitialValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *                        - CurrentValue: initial value of the configuration registers
 * will be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
void dcc2GetConfigValue( dcc_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_GCTRL = DCC2_GCTRL_CONFIGVALUE;
        config_reg->CONFIG_CNT0SEED = DCC2_CNT0SEED_CONFIGVALUE;
        config_reg->CONFIG_VALID0SEED = DCC2_VALID0SEED_CONFIGVALUE;
        config_reg->CONFIG_CNT1SEED = DCC2_CNT1SEED_CONFIGVALUE;
        config_reg->CONFIG_CNT1CLKSRC = DCC2_CNT1CLKSRC_CONFIGVALUE;
        config_reg->CONFIG_CNT0CLKSRC = DCC2_CNT0CLKSRC_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Hardware status bit read check" */
        config_reg->CONFIG_GCTRL = dccREG2->GCTRL;
        config_reg->CONFIG_CNT0SEED = dccREG2->CNT0SEED;
        config_reg->CONFIG_VALID0SEED = dccREG2->VALID0SEED;
        config_reg->CONFIG_CNT1SEED = dccREG2->CNT1SEED;
        config_reg->CONFIG_CNT1CLKSRC = dccREG2->CNT1CLKSRC;
        config_reg->CONFIG_CNT0CLKSRC = dccREG2->CNT0CLKSRC;
    }
}
