/** @file crc.c
 *   @brief CRC Driver Source File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - API Functions
 *   - Interrupt Handlers
 *   .
 *   which are relevant for the CRC driver.
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

#include "crc.h"
#include "sys_vim.h"
/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @fn void crcInit(void)
 *   @brief Initializes the crc Driver
 *
 *   This function initializes the crc module.
 */
/* SourceId : CRC_SourceId_001 */
/* DesignId : CRC_DesignId_001 */
/* Requirements : CONQ_CRC_SR2 */
void crcInit( void )
{
    /* USER CODE BEGIN (2) */
    /* USER CODE END */
    /** @b initialize @b CRC1 */
    /** - Reset  PSA*/
    crcREG1->CTRL0 = ( uint32 ) ( ( uint32 ) 1U << 0U )
                   | ( uint32 ) ( ( uint32 ) 1U << 8U );

    /** - Pulling PSA out of reset */
    crcREG1->CTRL0 = 0x00000000U;

    /** - Setup the Data trace for channel1 */
    crcREG1->CTRL2 |= ( uint32 ) 0U << 4U;

    /** - Set interrupt enable
     *     - Enable/Disable timeout
     *     - Enable/Disable underrun interrupt
     *     - Enable/Disable overrun interrupt
     *     - Enable/Disable CRC fail interrupt
     *     - Enable/Disable compression interrupt
     */
    crcREG1->INTS = 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
                  | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U;

    /** - Setup pattern count preload register for channel 1 and channel 2*/
    crcREG1->PCOUNT_REG1 = 0x00000000U;
    crcREG1->PCOUNT_REG2 = 0x00000000U;

    /** - Setup sector count preload register for channel 1 and channel 2*/
    crcREG1->SCOUNT_REG1 = 0x00000000U;
    crcREG1->SCOUNT_REG2 = 0x00000000U;

    /** - Setup watchdog timeout for channel 1 and channel 2*/
    crcREG1->WDTOPLD1 = 0x00000000U;
    crcREG1->WDTOPLD2 = 0x00000000U;

    /** - Setup block complete timeout for channel 1 and channel 2*/
    crcREG1->BCTOPLD1 = 0x00000000U;
    crcREG1->BCTOPLD2 = 0x00000000U;

    /** - Setup CRC value low for channel 1 and channel 2*/
    crcREG1->REGL1 = 0x00000000U;
    crcREG1->REGL2 = 0x00000000U;

    /** - Setup CRC value high for channel 1 and channel 2*/
    crcREG1->REGH1 = 0x00000000U;
    crcREG1->REGH2 = 0x00000000U;

    /** - Setup the Channel mode */
    crcREG1->CTRL2 |= ( uint32 ) ( CRC_FULL_CPU )
                    | ( uint32 ) ( ( uint32 ) CRC_FULL_CPU << 8U );

    /* USER CODE BEGIN (3) */
    /* USER CODE END */

    /** @b initialize @b CRC2 */

    /** - Reset  PSA*/
    crcREG2->CTRL0 = ( uint32 ) ( ( uint32 ) 1U << 0U )
                   | ( uint32 ) ( ( uint32 ) 1U << 8U );

    /** - Pulling PSA out of reset */
    crcREG2->CTRL0 = 0x00000000U;

    /** - Setup the Data trace for channel1 */
    crcREG2->CTRL2 |= ( uint32 ) 0U << 4U;

    /** - Set interrupt enable
     *     - Enable/Disable timeout
     *     - Enable/Disable underrun interrupt
     *     - Enable/Disable overrun interrupt
     *     - Enable/Disable CRC fail interrupt
     *     - Enable/Disable compression interrupt
     */
    crcREG2->INTS = 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
                  | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U;

    /** - Setup pattern count preload register for channel 1 and channel 2*/
    crcREG2->PCOUNT_REG1 = 0U;
    crcREG2->PCOUNT_REG2 = 0U;

    /** - Setup sector count preload register for channel 1 and channel 2*/
    crcREG2->SCOUNT_REG1 = 0U;
    crcREG2->SCOUNT_REG2 = 0U;

    /** - Setup watchdog timeout for channel 1 and channel 2*/
    crcREG2->WDTOPLD1 = 0U;
    crcREG2->WDTOPLD2 = 0U;

    /** - Setup block complete timeout for channel 1 and channel 2*/
    crcREG2->BCTOPLD1 = 0U;
    crcREG2->BCTOPLD2 = 0U;

    /** - Setup CRC value low for channel 1 and channel 2*/
    crcREG2->REGL1 = 0U;
    crcREG2->REGL2 = 0U;

    /** - Setup CRC value high for channel 1 and channel 2*/
    crcREG2->REGH1 = 0U;
    crcREG2->REGH2 = 0U;

    /** - Setup the Channel mode */
    crcREG2->CTRL2 |= ( uint32 ) ( CRC_FULL_CPU )
                    | ( uint32 ) ( ( uint32 ) CRC_FULL_CPU << 8U );

    /* USER CODE BEGIN (4) */
    /* USER CODE END */
}

/** @fn void crcSendPowerDown(crcBASE_t *crc)
 *   @brief Send crc power down
 *   @param[in] crc - crc module base address
 *
 *   Send crc power down signal to enter into sleep mode
 */
/* SourceId : CRC_SourceId_002 */
/* DesignId : CRC_DesignId_002 */
/* Requirements : CONQ_CRC_SR3 */
void crcSendPowerDown( crcBASE_t * crc )
{
    /* USER CODE BEGIN (5) */
    /* USER CODE END */

    crc->CTRL1 |= 0x00000001U;

    /* USER CODE BEGIN (6) */
    /* USER CODE END */
}

/** @fn void crcSignGen(crcBASE_t *crc,crcModConfig_t *param)
 *   @brief set the mode specific parameters for signature generation
 *   @param[in] crc - crc module base address
 *   @param[in] param - structure holding mode specific parameters
 *   Generate CRC signature
 */
/* SourceId : CRC_SourceId_003 */
/* DesignId : CRC_DesignId_003 */
/* Requirements : CONQ_CRC_SR4 */
void crcSignGen( crcBASE_t * crc, crcModConfig_t * param )
{
    /* USER CODE BEGIN (7) */
    /* USER CODE END */
    uint32 i = 0U, psaSigx;
    volatile uint64 *ptr64, *psaSigx_ptr64;
    ptr64 = param->src_data_pat;

    /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are only
     * allowed in this driver" */
    /*SAFETYMCUSW 439 S MR:11.3 <APPROVED> "Pointer Manupulation required to find offset"
     */
    psaSigx = ( uint32 ) ( &crc->PSA_SIGREGL1 )
            + ( ( uint32 ) ( param->crc_channel ) * 0x40U );
    psaSigx_ptr64 = ( uint64 * ) ( psaSigx );

    if( param->mode == CRC_AUTO )
    {
        /**      -do a channel reset
         *        -clear all interrupts by reading offset register
         *        -set CRC FAIL interrupt
         *        -set the pattern count and sector count
         *        -HW trigger in AUTO mode for CRC register update
         *        -copy from memory location to CRC register using DMA
         *        -copy from memory to PSA signature register using DMA
         *        -frame or block transfer,auto init
         *        -compare with crc reference
         *        -do a channel reset
         */
    }
    else if( param->mode == CRC_SEMI_CPU )
    {
        /* after DMA does the transfer,CPU is invoked by CC interrupt to do signature
         * verification */
    }
    else if( param->mode == CRC_FULL_CPU )
    {
        for( i = 0U; i < param->data_length; i++ )
        {
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            *psaSigx_ptr64 = *ptr64;
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            ptr64++;
        }
        /* USER CODE BEGIN (8) */
        /* USER CODE END */
    }
    else
    {
        /* Empty */
    }
}

/** @fn void crcSetConfig(crcBASE_t *crc,crcConfig_t *param)
 *   @brief Set crc configurations
 *   @param[in] crc - crc module base address
 *   @param[in] param - structure for channel configuration
 *   Set Channel parameters
 */
/* SourceId : CRC_SourceId_004 */
/* DesignId : CRC_DesignId_004 */
/* Requirements : CONQ_CRC_SR5 */
void crcSetConfig( crcBASE_t * crc, crcConfig_t * param )
{
    /* USER CODE BEGIN (9) */
    /* USER CODE END */

    switch( param->crc_channel )
    {
        case 0U:
            crc->CTRL2 &= 0xFFFFFFFCU;
            crc->CTRL0 |= 0x00000001U;
            crc->CTRL0 &= 0xFFFFFFFEU;
            crc->PCOUNT_REG1 = param->pcount;
            crc->SCOUNT_REG1 = param->scount;
            crc->WDTOPLD1 = param->wdg_preload;
            crc->BCTOPLD1 = param->block_preload;
            crc->CTRL2 |= param->mode;
            break;
        case 1U:
            crc->CTRL2 &= 0xFFFFFCFFU;
            crc->CTRL0 |= 0x00000100U;
            crc->CTRL0 &= 0xFFFFFEFFU;
            crc->PCOUNT_REG2 = param->pcount;
            crc->SCOUNT_REG2 = param->scount;
            crc->WDTOPLD2 = param->wdg_preload;
            crc->BCTOPLD2 = param->block_preload;
            crc->CTRL2 |= ( uint32 ) ( ( uint32 ) param->mode << 8U );
            break;
        default:
            break;
    }

    /* USER CODE BEGIN (10) */
    /* USER CODE END */
}

/** @fn uint64 crcGetSectorSig(crcBASE_t *crc,uint32 channel)
 *   @brief get genearted sector signature
 *   @param[in] crc - crc module base address
 *   @param[in] channel - crc channel
 *                      CRC_CH1 - channel1
 *                      CRC_CH2 - channel2
 *                      CRC_CH3 - channel3
 *                      CRC_CH4 - channel4
 *
 *   Get Sector signature value of selected channel
 */
/* SourceId : CRC_SourceId_005 */
/* DesignId : CRC_DesignId_006 */
/* Requirements : CONQ_CRC_SR7 */
uint64 crcGetSectorSig( crcBASE_t * crc, uint32 channel )
{
    uint64 status = 0U;
    uint32 CRC_PSA_SECSIGREGH1 = crc->PSA_SECSIGREGH1;
    uint32 CRC_PSA_SECSIGREGL1 = crc->PSA_SECSIGREGL1;
    uint32 CRC_PSA_SECSIGREGH2 = crc->PSA_SECSIGREGH2;
    uint32 CRC_PSA_SECSIGREGL2 = crc->PSA_SECSIGREGL2;

    /* USER CODE BEGIN (11) */
    /* USER CODE END */
    switch( channel )
    {
        case 0U:
            /*SAFETYMCUSW 51 S MR:12.3 <APPROVED> "Needs shifting for 64-bit value" */
            status = ( ( ( uint64 ) ( CRC_PSA_SECSIGREGL1 ) << 32U )
                       | ( uint64 ) ( CRC_PSA_SECSIGREGH1 ) );
            break;
        case 1U:
            /*SAFETYMCUSW 51 S MR:12.3 <APPROVED> "Needs shifting for 64-bit value" */
            status = ( ( ( uint64 ) ( CRC_PSA_SECSIGREGL2 ) << 32U )
                       | ( uint64 ) ( CRC_PSA_SECSIGREGH2 ) );
            break;
        default:
            break;
    }
    return status;

    /* USER CODE BEGIN (12) */
    /* USER CODE END */
}

/** @fn uint32 crcGetFailedSector(crcBASE_t *crc,uint32 channel)
 *   @brief get failed sector details
 *   @param[in] crc - crc module base address
 *   @param[in] channel - crc channel
 *                      CRC_CH1 - channel1
 *                      CRC_CH2 - channel2
 *                      CRC_CH3 - channel3
 *                      CRC_CH4 - channel4
 *
 *   Get Failed Sector value of selected channel
 */
/* SourceId : CRC_SourceId_006 */
/* DesignId : CRC_DesignId_007 */
/* Requirements : CONQ_CRC_SR8 */
uint32 crcGetFailedSector( crcBASE_t * crc, uint32 channel )
{
    uint32 sector = 0U;

    /* USER CODE BEGIN (13) */
    /* USER CODE END */

    switch( channel )
    {
        case 0U:
            sector = crc->CURSEC_REG1;
            break;
        case 1U:
            sector = crc->CURSEC_REG2;
            break;
        default:
            break;
    }
    return sector;
    /* USER CODE BEGIN (14) */
    /* USER CODE END */
}

/** @fn uint32 crcGetIntrPend(crcBASE_t *crc,uint32 channel)
 *   @brief get highest priority interrupt pending
 *   @param[in] crc - crc module base address
 *   @param[in] channel - crc channel
 *
 *   Get pending Interrupts of selected channel
 */
/* SourceId : CRC_SourceId_007 */
/* DesignId : CRC_DesignId_008 */
/* Requirements : CONQ_CRC_SR9 */
uint32 crcGetIntrPend( crcBASE_t * crc, uint32 channel )
{
    /* USER CODE BEGIN (15) */
    /* USER CODE END */
    return crc->INT_OFFSET_REG;
    /* USER CODE BEGIN (16) */
    /* USER CODE END */
}

/** @fn void crcChannelReset(crcBASE_t *crc,uint32 channel)
 *   @brief Reset the channel configurations
 *   @param[in] crc - crc module base address
 *   @param[in] channel-crc channel
 *                      CRC_CH1 - channel1
 *                      CRC_CH2 - channel2
 *                      CRC_CH3 - channel3
 *                      CRC_CH4 - channel4
 *
 *   Reset configurations of the selected channels.
 */
/* SourceId : CRC_SourceId_008 */
/* DesignId : CRC_DesignId_009 */
/* Requirements : CONQ_CRC_SR10 */
void crcChannelReset( crcBASE_t * crc, uint32 channel )
{
    /* USER CODE BEGIN (17) */
    /* USER CODE END */

    if( channel == 0U )
    {
        crc->CTRL0 |= ( uint32 ) ( ( uint32 ) 1U << 0U );  /** Reset the CRC channel  */
        crc->CTRL0 &= ~( uint32 ) ( ( uint32 ) 1U << 0U ); /** Exit the reset  */
    }
    else if( channel == 1U )
    {
        crc->CTRL0 |= ( uint32 ) ( ( uint32 ) 1U << 8U );  /** Reset the CRC channel  */
        crc->CTRL0 &= ~( uint32 ) ( ( uint32 ) 1U << 8U ); /** Exit the reset  */
    }
    else
    {
        /** Empty  */
    }
    /* USER CODE BEGIN (18) */
    /* USER CODE END */
}

/** @fn crcEnableNotification(crcBASE_t *crc, uint32 flags)
 *   @brief Enable interrupts
 *   @param[in] crc   - crc module base address
 *   @param[in] flags - Interrupts to be enabled, can be ored value of:
 *                      CRC_CH2_TO      - channel3 timeout error,
 *                      CRC_CH2_UR      - channel3 underrun error,
 *                      CRC_CH2_OR      - channel3 overrun error,
 *                      CRC_CH2_FAIL    - channel3 crc error,
 *                      CRC_CH2_CC      - channel3 compression complete interrupt ,
 *                      CRC_CH1_TO      - channel4 timeout error,
 *                      CRC_CH1_UR      - channel4 underrun error,
 *                      CRC_CH1_OR      - channel4 overrun error,
 *                      CRC_CH1_FAIL    - channel4 crc error,
 *                      CRC_CH1_CC      - channel4 compression complete interrupt
 *
 *   Enable Notifications / Interrupts
 */
/* SourceId : CRC_SourceId_009 */
/* DesignId : CRC_DesignId_010 */
/* Requirements : CONQ_CRC_SR11 */
void crcEnableNotification( crcBASE_t * crc, uint32 flags )
{
    /* USER CODE BEGIN (19) */
    /* USER CODE END */

    crc->INTS = flags;

    /* USER CODE BEGIN (20) */
    /* USER CODE END */
}

/** @fn crcDisableNotification(crcBASE_t *crc, uint32 flags)
 *   @brief Disable interrupts
 *   @param[in] crc   - crc module base address
 *   @param[in] flags - Interrupts to be disabled, can be ored value of:
 *                      CRC_CH2_TO      - channel3 timeout error,
 *                      CRC_CH2_UR      - channel3 underrun error,
 *                      CRC_CH2_OR      - channel3 overrun error,
 *                      CRC_CH2_FAIL    - channel3 crc error,
 *                      CRC_CH2_CC      - channel3 compression complete interrupt ,
 *                      CRC_CH1_TO      - channel4 timeout error,
 *                      CRC_CH1_UR      - channel4 underrun error,
 *                      CRC_CH1_OR      - channel4 overrun error,
 *                      CRC_CH1_FAIL    - channel4 crc error,
 *                      CRC_CH1_CC      - channel4 compression complete interrupt
 *
 *   Disable Notifications / Interrupts
 */
/* SourceId : CRC_SourceId_010 */
/* DesignId : CRC_DesignId_011 */
/* Requirements : CONQ_CRC_SR12 */
void crcDisableNotification( crcBASE_t * crc, uint32 flags )
{
    /* USER CODE BEGIN (21) */
    /* USER CODE END */

    crc->INTR = flags;

    /* USER CODE BEGIN (22) */
    /* USER CODE END */
}

/** @fn uint32 crcGetPSASig(crcBASE_t *crc,uint32 channel)
 *   @brief get genearted PSA signature used for FULL CPU mode
 *   @param[in] crc - crc module base address
 *   @param[in] channel - crc channel
 *                      CRC_CH1 - channel1
 *                      CRC_CH2 - channel2
 *                      CRC_CH3 - channel3
 *                      CRC_CH4 - channel4
 *
 *   Get PSA signature used for FULL CPU mode of selected channel
 */
/* SourceId : CRC_SourceId_011 */
/* DesignId : CRC_DesignId_005 */
/* Requirements : CONQ_CRC_SR6 */
uint64 crcGetPSASig( crcBASE_t * crc, uint32 channel )
{
    uint64 status = 0U;
    uint32 CRC_PSA_SIGREGH1 = crc->PSA_SIGREGH1;
    uint32 CRC_PSA_SIGREGL1 = crc->PSA_SIGREGL1;
    uint32 CRC_PSA_SIGREGH2 = crc->PSA_SIGREGH2;
    uint32 CRC_PSA_SIGREGL2 = crc->PSA_SIGREGL2;

    /* USER CODE BEGIN (23) */
    /* USER CODE END */
    switch( channel )
    {
        case 0U:
            /*SAFETYMCUSW 51 S MR:12.3 <APPROVED> "Needs shifting for 64-bit value" */
            status = ( ( ( uint64 ) ( CRC_PSA_SIGREGL1 ) << 32U )
                       | ( uint64 ) ( CRC_PSA_SIGREGH1 ) );
            break;
        case 1U:
            /*SAFETYMCUSW 51 S MR:12.3 <APPROVED> "Needs shifting for 64-bit value" */
            status = ( ( ( uint64 ) ( CRC_PSA_SIGREGL2 ) << 32U )
                       | ( uint64 ) ( CRC_PSA_SIGREGH2 ) );
            break;
        default:
            break;
    }
    return status;

    /* USER CODE BEGIN (24) */
    /* USER CODE END */
}

/** @fn void crc1GetConfigValue(crc_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the CRC1 configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : CRC_SourceId_012 */
/* DesignId : CRC_DesignId_012 */
/* Requirements : CONQ_CRC_SR15 */
void crc1GetConfigValue( crc_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTRL0 = CRC1_CTRL0_CONFIGVALUE;
        config_reg->CONFIG_CTRL1 = CRC1_CTRL1_CONFIGVALUE;
        config_reg->CONFIG_CTRL2 = CRC1_CTRL2_CONFIGVALUE;
        config_reg->CONFIG_INTS = CRC1_INTS_CONFIGVALUE;
        config_reg->CONFIG_PCOUNT_REG1 = CRC1_PCOUNT_REG1_CONFIGVALUE;
        config_reg->CONFIG_SCOUNT_REG1 = CRC1_SCOUNT_REG1_CONFIGVALUE;
        config_reg->CONFIG_WDTOPLD1 = CRC1_WDTOPLD1_CONFIGVALUE;
        config_reg->CONFIG_BCTOPLD1 = CRC1_BCTOPLD1_CONFIGVALUE;
        config_reg->CONFIG_PCOUNT_REG2 = CRC1_PCOUNT_REG2_CONFIGVALUE;
        config_reg->CONFIG_SCOUNT_REG2 = CRC1_SCOUNT_REG2_CONFIGVALUE;
        config_reg->CONFIG_WDTOPLD2 = CRC1_WDTOPLD2_CONFIGVALUE;
        config_reg->CONFIG_BCTOPLD2 = CRC1_BCTOPLD2_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Register read back support" */
        config_reg->CONFIG_CTRL0 = crcREG1->CTRL0;
        config_reg->CONFIG_CTRL1 = crcREG1->CTRL1;
        config_reg->CONFIG_CTRL2 = crcREG1->CTRL2;
        config_reg->CONFIG_INTS = crcREG1->INTS;
        config_reg->CONFIG_PCOUNT_REG1 = crcREG1->PCOUNT_REG1;
        config_reg->CONFIG_SCOUNT_REG1 = crcREG1->SCOUNT_REG1;
        config_reg->CONFIG_WDTOPLD1 = crcREG1->WDTOPLD1;
        config_reg->CONFIG_BCTOPLD1 = crcREG1->BCTOPLD1;
        config_reg->CONFIG_PCOUNT_REG2 = crcREG1->PCOUNT_REG2;
        config_reg->CONFIG_SCOUNT_REG2 = crcREG1->SCOUNT_REG2;
        config_reg->CONFIG_WDTOPLD2 = crcREG1->WDTOPLD2;
        config_reg->CONFIG_BCTOPLD2 = crcREG1->BCTOPLD2;
    }
}

/** @fn void crc2GetConfigValue(crc_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the CRC2 configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : CRC_SourceId_013 */
/* DesignId : CRC_DesignId_012 */
/* Requirements : CONQ_CRC_SR15 */
void crc2GetConfigValue( crc_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_CTRL0 = CRC2_CTRL0_CONFIGVALUE;
        config_reg->CONFIG_CTRL1 = CRC2_CTRL1_CONFIGVALUE;
        config_reg->CONFIG_CTRL2 = CRC2_CTRL2_CONFIGVALUE;
        config_reg->CONFIG_INTS = CRC2_INTS_CONFIGVALUE;
        config_reg->CONFIG_PCOUNT_REG1 = CRC2_PCOUNT_REG1_CONFIGVALUE;
        config_reg->CONFIG_SCOUNT_REG1 = CRC2_SCOUNT_REG1_CONFIGVALUE;
        config_reg->CONFIG_WDTOPLD1 = CRC2_WDTOPLD1_CONFIGVALUE;
        config_reg->CONFIG_BCTOPLD1 = CRC2_BCTOPLD1_CONFIGVALUE;
        config_reg->CONFIG_PCOUNT_REG2 = CRC2_PCOUNT_REG2_CONFIGVALUE;
        config_reg->CONFIG_SCOUNT_REG2 = CRC2_SCOUNT_REG2_CONFIGVALUE;
        config_reg->CONFIG_WDTOPLD2 = CRC2_WDTOPLD2_CONFIGVALUE;
        config_reg->CONFIG_BCTOPLD2 = CRC2_BCTOPLD2_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Register read back support" */
        config_reg->CONFIG_CTRL0 = crcREG2->CTRL0;
        config_reg->CONFIG_CTRL1 = crcREG2->CTRL1;
        config_reg->CONFIG_CTRL2 = crcREG2->CTRL2;
        config_reg->CONFIG_INTS = crcREG2->INTS;
        config_reg->CONFIG_PCOUNT_REG1 = crcREG2->PCOUNT_REG1;
        config_reg->CONFIG_SCOUNT_REG1 = crcREG2->SCOUNT_REG1;
        config_reg->CONFIG_WDTOPLD1 = crcREG2->WDTOPLD1;
        config_reg->CONFIG_BCTOPLD1 = crcREG2->BCTOPLD1;
        config_reg->CONFIG_PCOUNT_REG2 = crcREG2->PCOUNT_REG2;
        config_reg->CONFIG_SCOUNT_REG2 = crcREG2->SCOUNT_REG2;
        config_reg->CONFIG_WDTOPLD2 = crcREG2->WDTOPLD2;
        config_reg->CONFIG_BCTOPLD2 = crcREG2->BCTOPLD2;
    }
}
