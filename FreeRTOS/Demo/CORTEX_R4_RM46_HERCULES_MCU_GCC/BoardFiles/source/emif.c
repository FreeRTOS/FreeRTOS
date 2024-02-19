/** @file emif.c
 *   @brief emif Driver Implementation File
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

#include "emif.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @fn void emif_SDRAMInit(void)
 *   @brief Initializes the emif Driver for SDRAM
 *
 *   This function has been deprecated.
 *   As per the errata EMIF#5, EMIF SDRAM initialization must performed with EMIF clock
 * below 40MHz. Hence the init function needs to be called from the startup before the PLL
 * is configured. A new function emif_SDRAM_StartupInit has been added and is called from
 * the startup. This function need not be called from the main, and is preserved for
 * compatibilty.
 */

void emif_SDRAMInit( void )
{
    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    /* USER CODE BEGIN (3) */
    /* USER CODE END */
}

/** @fn void emif_ASYNC1Init(void)
 *   @brief Initializes the emif Driver for ASYNC memories
 *
 *   This function initializes the emif driver for Asynchronous memories like Nor and Nand
 * Flashes,Asynchronous RAM.
 */
/* SourceId : EMIF_SourceId_002 */
/* DesignId : EMIF_DesignId_002 */
/* Requirements: HL_SR335 */
void emif_ASYNC1Init( void )
{
    /* USER CODE BEGIN (4) */
    /* USER CODE END */
    emifREG->CE2CFG = 0x00000000U;
    emifREG->CE2CFG = ( uint32 ) ( ( uint32 ) 0U << 31U )
                    | ( uint32 ) ( ( uint32 ) 0U << 30U )
                    | ( uint32 ) ( ( uint32 ) 15U << 26U )
                    | ( uint32 ) ( ( uint32 ) 63U << 20U )
                    | ( uint32 ) ( ( uint32 ) 7U << 17U )
                    | ( uint32 ) ( ( uint32 ) 15U << 13U )
                    | ( uint32 ) ( ( uint32 ) 63U << 7U )
                    | ( uint32 ) ( ( uint32 ) 7U << 4U )
                    | ( uint32 ) ( ( uint32 ) 0U << 2U )
                    | ( uint32 ) ( ( uint32 ) emif_8_bit_port );

    emifREG->AWCC = ( emifREG->AWCC & 0xC0FF0000U )
                  | ( uint32 ) ( ( uint32 ) emif_pin_high << 29U )
                  | ( uint32 ) ( ( uint32 ) emif_pin_low << 28U )
                  | ( uint32 ) ( ( uint32 ) emif_wait_pin0 << 16U )
                  | ( uint32 ) ( ( uint32 ) 0U );

    emifREG->PMCR = ( emifREG->PMCR & 0xFFFFFF00U ) | ( uint32 ) ( ( uint32 ) 0U << 2U )
                  | ( uint32 ) ( ( uint32 ) emif_4_words << 1U )
                  | ( uint32 ) ( ( uint32 ) 0U );
    /* USER CODE BEGIN (5) */
    /* USER CODE END */
}

/** @fn void emif_ASYNC2Init(void)
 *   @brief Initializes the emif Driver for ASYNC memories
 *
 *   This function initializes the emif driver for Asynchronous memories like Nor and Nand
 * Flashes,Asynchronous RAM.
 */
/* SourceId : EMIF_SourceId_003 */
/* DesignId : EMIF_DesignId_002 */
/* Requirements: HL_SR335 */
void emif_ASYNC2Init( void )
{
    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    emifREG->CE3CFG = 0x00000000U;
    emifREG->CE3CFG = ( uint32 ) ( ( uint32 ) 0U << 31U )
                    | ( uint32 ) ( ( uint32 ) 0U << 30U )
                    | ( uint32 ) ( ( uint32 ) 15U << 26U )
                    | ( uint32 ) ( ( uint32 ) 63U << 20U )
                    | ( uint32 ) ( ( uint32 ) 7U << 17U )
                    | ( uint32 ) ( ( uint32 ) 15U << 13U )
                    | ( uint32 ) ( ( uint32 ) 63U << 7U )
                    | ( uint32 ) ( ( uint32 ) 7U << 4U )
                    | ( uint32 ) ( ( uint32 ) 0U << 2U )
                    | ( uint32 ) ( ( uint32 ) emif_8_bit_port );

    emifREG->AWCC = ( emifREG->AWCC & 0xC0FF0000U )
                  | ( uint32 ) ( ( uint32 ) emif_pin_high << 29U )
                  | ( uint32 ) ( ( uint32 ) emif_pin_low << 28U )
                  | ( uint32 ) ( ( uint32 ) emif_wait_pin0 << 18U )
                  | ( uint32 ) ( ( uint32 ) 0U );

    emifREG->PMCR = ( emifREG->PMCR & 0xFFFF00FFU ) | ( uint32 ) ( ( uint32 ) 0U << 10U )
                  | ( uint32 ) ( ( uint32 ) emif_4_words << 9U )
                  | ( uint32 ) ( ( uint32 ) 0U << 8U );
    /* USER CODE BEGIN (7) */
    /* USER CODE END */
}

/** @fn void emif_ASYNC3Init(void)
 *   @brief Initializes the emif Driver for ASYNC memories
 *
 *   This function initializes the emif driver for Asynchronous memories like Nor and Nand
 * Flashes,Asynchronous RAM.
 */
/* SourceId : EMIF_SourceId_004 */
/* DesignId : EMIF_DesignId_002 */
/* Requirements: HL_SR335 */
void emif_ASYNC3Init( void )
{
    /* USER CODE BEGIN (8) */
    /* USER CODE END */

    emifREG->CE4CFG = 0x00000000U;
    emifREG->CE4CFG = ( uint32 ) ( ( uint32 ) 0U << 31U )
                    | ( uint32 ) ( ( uint32 ) 0U << 30U )
                    | ( uint32 ) ( ( uint32 ) 15U << 26U )
                    | ( uint32 ) ( ( uint32 ) 63U << 20U )
                    | ( uint32 ) ( ( uint32 ) 7U << 17U )
                    | ( uint32 ) ( ( uint32 ) 15U << 13U )
                    | ( uint32 ) ( ( uint32 ) 63U << 7U )
                    | ( uint32 ) ( ( uint32 ) 7U << 4U )
                    | ( uint32 ) ( ( uint32 ) 0U << 2U )
                    | ( uint32 ) ( ( uint32 ) emif_8_bit_port );

    emifREG->AWCC = ( emifREG->AWCC & 0xC0FF0000U )
                  | ( uint32 ) ( ( uint32 ) emif_pin_high << 29U )
                  | ( uint32 ) ( ( uint32 ) emif_pin_low << 28U )
                  | ( uint32 ) ( ( uint32 ) emif_wait_pin0 << 20U )
                  | ( uint32 ) ( ( uint32 ) 0U );

    emifREG->PMCR = ( emifREG->PMCR & 0xFF00FFFFU ) | ( uint32 ) ( ( uint32 ) 0U << 18U )
                  | ( uint32 ) ( ( uint32 ) emif_4_words << 17U )
                  | ( uint32 ) ( ( uint32 ) 0U << 16U );

    /* USER CODE BEGIN (9) */
    /* USER CODE END */
}

/* USER CODE BEGIN (10) */
/* USER CODE END */

/** @fn void emifGetConfigValue(emif_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the EMIF configuration registers
 *
 *   @param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *   @param[in] type:    whether initial or current value of the configuration registers
 * need to be stored
 *                       - InitialValue: initial value of the configuration registers will
 * be stored in the struct pointed by config_reg
 *                       - CurrentValue: initial value of the configuration registers will
 * be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : EMIF_SourceId_005 */
/* DesignId : EMIF_DesignId_003 */
/* Requirements: HL_SR336 */
void emifGetConfigValue( emif_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_AWCC = EMIF_AWCC_CONFIGVALUE;
        config_reg->CONFIG_SDCR = EMIF_SDCR_CONFIGVALUE;
        config_reg->CONFIG_SDRCR = EMIF_SDRCR_CONFIGVALUE;
        config_reg->CONFIG_CE2CFG = EMIF_CE2CFG_CONFIGVALUE;
        config_reg->CONFIG_CE3CFG = EMIF_CE3CFG_CONFIGVALUE;
        config_reg->CONFIG_CE4CFG = EMIF_CE4CFG_CONFIGVALUE;
        config_reg->CONFIG_CE5CFG = EMIF_CE5CFG_CONFIGVALUE;
        config_reg->CONFIG_SDTIMR = EMIF_SDTIMR_CONFIGVALUE;
        config_reg->CONFIG_SDSRETR = EMIF_SDSRETR_CONFIGVALUE;
        config_reg->CONFIG_INTMSK = EMIF_INTMSK_CONFIGVALUE;
        config_reg->CONFIG_PMCR = EMIF_PMCR_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_AWCC = emifREG->AWCC;
        config_reg->CONFIG_SDCR = emifREG->SDCR;
        config_reg->CONFIG_SDRCR = emifREG->SDRCR;
        config_reg->CONFIG_CE2CFG = emifREG->CE2CFG;
        config_reg->CONFIG_CE3CFG = emifREG->CE3CFG;
        config_reg->CONFIG_CE4CFG = emifREG->CE4CFG;
        config_reg->CONFIG_CE5CFG = emifREG->CE5CFG;
        config_reg->CONFIG_SDTIMR = emifREG->SDTIMR;
        config_reg->CONFIG_SDSRETR = emifREG->SDSRETR;
        config_reg->CONFIG_INTMSK = emifREG->INTMSK;
        config_reg->CONFIG_PMCR = emifREG->PMCR;
    }
}

/** @fn void emif_SDRAM_StartupInit(void)
 *   @brief Initializes the emif Driver for SDRAM
 *
 *   This function initializes the emif driver for SDRAM (SDRAM initialization function).
 *   SDRAM Configuration Procedure B as documented in the TRM is implemented.
 *
 *   Note: This function is called in the startup. Do not call the function inside main.
 */

/* SourceId : EMIF_SourceId_001 */
/* DesignId : EMIF_DesignId_001 */
/* Requirements: HL_SR334 */
void emif_SDRAM_StartupInit( void )
{
    /* USER CODE BEGIN (11) */
    /* USER CODE END */

    volatile uint32 buffer;

    /* Procedure B Step 1:  EMIF Clock Frequency is assumed to be configured in the
     * startup */

    /* Procedure B  Step 2:  Program SDTIMR and SDSRETR to satisfy requirements of SDRAM
     * Device */
    emifREG->SDTIMR = ( uint32 ) ( ( uint32 ) 0U << 27U )
                    | ( uint32 ) ( ( uint32 ) 0U << 24U )
                    | ( uint32 ) ( ( uint32 ) 0U << 23U )
                    | ( uint32 ) ( ( uint32 ) 0U << 20U )
                    | ( uint32 ) ( ( uint32 ) 0U << 19U )
                    | ( uint32 ) ( ( uint32 ) 0U << 16U )
                    | ( uint32 ) ( ( uint32 ) 0U << 12U )
                    | ( uint32 ) ( ( uint32 ) 0U << 8U )
                    | ( uint32 ) ( ( uint32 ) 0U << 7U )
                    | ( uint32 ) ( ( uint32 ) 0U << 4U )
                    | ( uint32 ) ( ( uint32 ) 0U << 3U );

    emifREG->SDSRETR = ( uint32 ) 0U;

    /* Procedure B  Step 3:  Program the RR Field of SDRCR to provide 200us of
     * initialization time */
    emifREG->SDRCR = 8000005U;

    /* Procedure B  Step 4:  Program SDRCR to Trigger Initialization Sequence */

    /**  -general clearing of register
     *    -for NM for setting 16 bit data bus
     *    -cas latency
     *    -BIT11_9CLOCK to allow the cl field to be written
     *    -selecting the banks
     *    -setting the pagesize
     */
    emifREG->SDCR = ( uint32 ) ( ( uint32 ) 0U << 31U )
                  | ( uint32 ) ( ( uint32 ) 1U << 14U )
                  | ( uint32 ) ( ( uint32 ) 0U << 9U )
                  | ( uint32 ) ( ( uint32 ) 1U << 8U )
                  | ( uint32 ) ( ( uint32 ) 0U << 4U )
                  | ( uint32 ) ( ( uint32 ) elements_256 );

    /* Procedure B  Step 5:  Read of SDRAM memory location causes processor to wait until
     * SDRAM Initialization completes */
    buffer = *PTR;
    /* prevents optimization */
    buffer = buffer;

    /* Procedure B  Step 6:  Program the RR field to the default Refresh Interval of the
     * SDRAM*/
    emifREG->SDRCR = 0U;

    /* Place the EMIF in Self Refresh Mode For Clock Change          */
    /* Must only write to the upper byte of the SDCR to avoid        */
    /* a second intiialization sequence                              */
    /* The byte address depends on endian (0x3U in LE, 0x00 in BE32) */
    *( ( unsigned char * ) ( &emifREG->SDCR ) + 0x3U ) = 0x80U;

    /* USER CODE BEGIN (12) */
    /* USER CODE END */
}
