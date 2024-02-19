/** @file adc.c
 *   @brief ADC Driver Source File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - API Functions
 *   - Interrupt Handlers
 *   .
 *   which are relevant for the ADC driver.
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

/* Include Files */

#include "adc.h"
#include "sys_vim.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @fn void adcInit(void)
 *   @brief Initializes ADC Driver
 *
 *   This function initializes the ADC driver.
 *
 */
/* USER CODE BEGIN (2) */
/* USER CODE END */
/* SourceId : ADC_SourceId_001 */
/* DesignId : ADC_DesignId_001 */
/* Requirements : HL_SR185 */
void adcInit( void )
{
    /* USER CODE BEGIN (3) */
    /* USER CODE END */

    /** @b Initialize @b ADC1: */

    /** - Reset ADC module */
    adcREG1->RSTCR = 1U;
    adcREG1->RSTCR = 0U;

    /** - Enable 12-BIT ADC  */
    adcREG1->OPMODECR |= 0x80000000U;

    /** - Setup prescaler */
    adcREG1->CLOCKCR = 10U;

    /** - Setup memory boundaries */
    adcREG1->BNDCR = ( uint32 ) ( ( uint32 ) 8U << 16U ) | ( 8U + 8U );
    adcREG1->BNDEND = ( adcREG1->BNDEND & 0xFFFF0000U ) | ( 2U );

    /** - Setup event group conversion mode
     *     - Setup data format
     *     - Enable/Disable channel id in conversion result
     *     - Enable/Disable continuous conversion
     */
    adcREG1->GxMODECR[ 0U ] = ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U
                            | ( uint32 ) 0x00000000U;

    /** - Setup event group hardware trigger
     *     - Setup hardware trigger edge
     *     - Setup hardware trigger source
     */
    adcREG1->EVSRC = ( uint32 ) 0x00000000U | ( uint32 ) ADC1_EVENT;

    /** - Setup event group sample window */
    adcREG1->EVSAMP = 1U;

    /** - Setup event group sample discharge
     *     - Setup discharge prescaler
     *     - Enable/Disable discharge
     */
    adcREG1->EVSAMPDISEN = ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) 0x00000000U;

    /** - Setup group 1 conversion mode
     *     - Setup data format
     *     - Enable/Disable channel id in conversion result
     *     - Enable/Disable continuous conversion
     */
    adcREG1->GxMODECR[ 1U ] = ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U
                            | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Setup group 1 hardware trigger
     *     - Setup hardware trigger edge
     *     - Setup hardware trigger source
     */
    adcREG1->G1SRC = ( uint32 ) 0x00000000U | ( uint32 ) ADC1_EVENT;

    /** - Setup group 1 sample window */
    adcREG1->G1SAMP = 1U;

    /** - Setup group 1 sample discharge
     *     - Setup discharge prescaler
     *     - Enable/Disable discharge
     */
    adcREG1->G1SAMPDISEN = ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) 0x00000000U;

    /** - Setup group 2 conversion mode
     *     - Setup data format
     *     - Enable/Disable channel id in conversion result
     *     - Enable/Disable continuous conversion
     */
    adcREG1->GxMODECR[ 2U ] = ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U
                            | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Setup group 2 hardware trigger
     *     - Setup hardware trigger edge
     *     - Setup hardware trigger source
     */
    adcREG1->G2SRC = ( uint32 ) 0x00000000U | ( uint32 ) ADC1_EVENT;

    /** - Setup group 2 sample window */
    adcREG1->G2SAMP = 1U;

    /** - Setup group 2 sample discharge
     *     - Setup discharge prescaler
     *     - Enable/Disable discharge
     */
    adcREG1->G2SAMPDISEN = ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) 0x00000000U;

    /** - ADC1 EVT pin output value */
    adcREG1->EVTOUT = 0U;

    /** - ADC1 EVT pin direction */
    adcREG1->EVTDIR = 0U;

    /** - ADC1 EVT pin open drain enable */
    adcREG1->EVTPDR = 0U;

    /** - ADC1 EVT pin pullup / pulldown selection */
    adcREG1->EVTPSEL = 1U;

    /** - ADC1 EVT pin pullup / pulldown enable*/
    adcREG1->EVTDIS = 0U;

    /** - Enable ADC module */
    adcREG1->OPMODECR |= 0x80140001U;

    /** - Wait for buffer initialization complete */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( ( adcREG1->BNDEND & 0xFFFF0000U ) >> 16U ) != 0U )
    {
    } /* Wait */

    /** - Setup parity */
    adcREG1->PARCR = 0x00000005U;

    /** @b Initialize @b ADC2: */

    /** - Reset ADC module */
    adcREG2->RSTCR = 1U;
    adcREG2->RSTCR = 0U;

    /** - Enable 12-BIT ADC  */
    adcREG2->OPMODECR |= 0x80000000U;

    /** - Setup prescaler */
    adcREG2->CLOCKCR = 10U;

    /** - Setup memory boundaries */
    adcREG2->BNDCR = ( uint32 ) ( ( uint32 ) 8U << 16U ) | ( 8U + 8U );
    adcREG2->BNDEND = ( adcREG2->BNDEND & 0xFFFF0000U ) | ( 2U );

    /** - Setup event group conversion mode
     *     - Setup data format
     *     - Enable/Disable channel id in conversion result
     *     - Enable/Disable continuous conversion
     */
    adcREG2->GxMODECR[ 0U ] = ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U
                            | ( uint32 ) 0x00000000U;

    /** - Setup event group hardware trigger
     *     - Setup hardware trigger edge
     *     - Setup hardware trigger source
     */
    adcREG2->EVSRC = ( uint32 ) 0x00000000U | ( uint32 ) ADC2_EVENT;

    /** - Setup event group sample window */
    adcREG2->EVSAMP = 1U;

    /** - Setup event group sample discharge
     *     - Setup discharge prescaler
     *     - Enable/Disable discharge
     */
    adcREG2->EVSAMPDISEN = ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) 0x00000000U;

    /** - Setup group 1 conversion mode
     *     - Setup data format
     *     - Enable/Disable channel id in conversion result
     *     - Enable/Disable continuous conversion
     */
    adcREG2->GxMODECR[ 1U ] = ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U
                            | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Setup group 1 hardware trigger
     *     - Setup hardware trigger edge
     *     - Setup hardware trigger source
     */
    adcREG2->G1SRC = ( uint32 ) 0x00000000U | ( uint32 ) ADC2_EVENT;

    /** - Setup group 1 sample window */
    adcREG2->G1SAMP = 1U;

    /** - Setup group 1 sample discharge
     *     - Setup discharge prescaler
     *     - Enable/Disable discharge
     */
    adcREG2->G1SAMPDISEN = ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) 0x00000000U;

    /** - Setup group 2 conversion mode
     *     - Setup data format
     *     - Enable/Disable channel id in conversion result
     *     - Enable/Disable continuous conversion
     */
    adcREG2->GxMODECR[ 2U ] = ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U
                            | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U;

    /** - Setup group 2 hardware trigger
     *     - Setup hardware trigger edge
     *     - Setup hardware trigger source
     */
    adcREG2->G2SRC = ( uint32 ) 0x00000000U | ( uint32 ) ADC2_EVENT;

    /** - Setup group 2 sample window */
    adcREG2->G2SAMP = 1U;

    /** - Setup group 2 sample discharge
     *     - Setup discharge prescaler
     *     - Enable/Disable discharge
     */
    adcREG2->G2SAMPDISEN = ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) 0x00000000U;

    /** - ADC2 EVT pin output value */
    adcREG2->EVTOUT = 0U;

    /** - ADC2 EVT pin direction */
    adcREG2->EVTDIR = 0U;

    /** - ADC2 EVT pin open drain enable */
    adcREG2->EVTPDR = 0U;

    /** - ADC2 EVT pin pullup / pulldown selection */
    adcREG2->EVTPSEL = 1U;

    /** - ADC2 EVT pin pullup / pulldown enable*/
    adcREG2->EVTDIS = 0U;

    /** - Enable ADC module */
    adcREG2->OPMODECR |= 0x80140001U;

    /** - Wait for buffer initialization complete */
    /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
    while( ( ( adcREG2->BNDEND & 0xFFFF0000U ) >> 16U ) != 0U )
    {
    } /* Wait */

    /** - Setup parity */
    adcREG2->PARCR = 0x00000005U;

    /**   @note This function has to be called before the driver can be used.\n
     *           This function has to be executed in privileged mode.\n
     */
    /* USER CODE BEGIN (4) */
    /* USER CODE END */
}

/* USER CODE BEGIN (5) */
/* USER CODE END */

/** - s_adcSelect is used as constant table for channel selection */
static const uint32 s_adcSelect[ 2U ][ 3U ] = {
    { 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U,
      0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U,
      0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U },
    { 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U,
      0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U,
      0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U
          | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U }
};

/** - s_adcFiFoSize is used as constant table for channel selection */
static const uint32 s_adcFiFoSize[ 2U ][ 3U ] = { { 16U, 16U, 16U }, { 16U, 16U, 16U } };

/* USER CODE BEGIN (6) */
/* USER CODE END */

/** @fn void adcStartConversion(adcBASE_t *adc, uint32 group)
 *   @brief Starts an ADC conversion
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *   @param[in] group Hardware group of ADC module:
 *              - adcGROUP0: ADC event group
 *              - adcGROUP1: ADC group 1
 *              - adcGROUP2: ADC group 2
 *
 *   This function starts a conversion of the ADC hardware group.
 *
 */
/* SourceId : ADC_SourceId_002 */
/* DesignId : ADC_DesignId_002 */
/* Requirements : HL_SR186 */
void adcStartConversion( adcBASE_t * adc, uint32 group )
{
    uint32 index = ( adc == adcREG1 ) ? 0U : 1U;

    /* USER CODE BEGIN (7) */
    /* USER CODE END */

    /** - Setup FiFo size */
    adc->GxINTCR[ group ] = s_adcFiFoSize[ index ][ group ];

    /** - Start Conversion */
    adc->GxSEL[ group ] = s_adcSelect[ index ][ group ];

    /**   @note The function adcInit has to be called before this function can be used. */

    /* USER CODE BEGIN (8) */
    /* USER CODE END */
}

/* USER CODE BEGIN (9) */
/* USER CODE END */

/** @fn void adcStopConversion(adcBASE_t *adc, uint32 group)
 *   @brief Stops an ADC conversion
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *   @param[in] group Hardware group of ADC module:
 *              - adcGROUP0: ADC event group
 *              - adcGROUP1: ADC group 1
 *              - adcGROUP2: ADC group 2
 *
 *   This function stops a conversion of the ADC hardware group.
 *
 */
/* SourceId : ADC_SourceId_003 */
/* DesignId : ADC_DesignId_003 */
/* Requirements : HL_SR187 */
void adcStopConversion( adcBASE_t * adc, uint32 group )
{
    /* USER CODE BEGIN (10) */
    /* USER CODE END */

    /** - Stop Conversion */
    adc->GxSEL[ group ] = 0U;

    /**   @note The function adcInit has to be called before this function can be used. */

    /* USER CODE BEGIN (11) */
    /* USER CODE END */
}

/* USER CODE BEGIN (12) */
/* USER CODE END */

/** @fn void adcResetFiFo(adcBASE_t *adc, uint32 group)
 *   @brief Resets FiFo read and write pointer.
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *   @param[in] group Hardware group of ADC module:
 *              - adcGROUP0: ADC event group
 *              - adcGROUP1: ADC group 1
 *              - adcGROUP2: ADC group 2
 *
 *   This function resets the FiFo read and write pointers.
 *
 */
/* SourceId : ADC_SourceId_004 */
/* DesignId : ADC_DesignId_004*/
/* Requirements : HL_SR188 */
void adcResetFiFo( adcBASE_t * adc, uint32 group )
{
    /* USER CODE BEGIN (13) */
    /* USER CODE END */

    /** - Reset FiFo */
    adc->GxFIFORESETCR[ group ] = 1U;

    /**   @note The function adcInit has to be called before this function can be used.\n
     *           the conversion should be stopped before calling this function.
     */

    /* USER CODE BEGIN (14) */
    /* USER CODE END */
}

/* USER CODE BEGIN (15) */
/* USER CODE END */

/** @fn uint32 adcGetData(adcBASE_t *adc, uint32 group, adcData_t * data)
 *   @brief Gets converted a ADC values
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *   @param[in] group Hardware group of ADC module:
 *              - adcGROUP0: ADC event group
 *              - adcGROUP1: ADC group 1
 *              - adcGROUP2: ADC group 2
 *   @param[out] data Pointer to store ADC converted data
 *   @return The function will return the number of converted values copied into data
 * buffer:
 *
 *   This function writes a ADC message into a ADC message box.
 *
 */
/* SourceId : ADC_SourceId_005 */
/* DesignId : ADC_DesignId_005 */
/* Requirements : HL_SR189 */
uint32 adcGetData( adcBASE_t * adc, uint32 group, adcData_t * data )
{
    uint32 i;
    uint32 buf;
    uint32 mode;
    uint32 index = ( adc == adcREG1 ) ? 0U : 1U;

    uint32 intcr_reg = adc->GxINTCR[ group ];
    uint32 count = ( intcr_reg >= 256U ) ? s_adcFiFoSize[ index ][ group ]
                                         : ( s_adcFiFoSize[ index ][ group ]
                                             - ( uint32 ) ( intcr_reg & 0xFFU ) );
    adcData_t * ptr = data;

    /* USER CODE BEGIN (16) */
    /* USER CODE END */

    mode = ( adc->OPMODECR & ADC_12_BIT_MODE );

    if( mode == ADC_12_BIT_MODE )
    {
        /** -  Get conversion data and channel/pin id */
        for( i = 0U; i < count; i++ )
        {
            buf = adc->GxBUF[ group ].BUF0;
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            ptr->value = ( uint16 ) ( buf & 0xFFFU );
            ptr->id = ( uint32 ) ( ( buf >> 16U ) & 0x1FU );
            /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
            ptr++;
        }
    }
    else
    {
        /** -  Get conversion data and channel/pin id */
        for( i = 0U; i < count; i++ )
        {
            buf = adc->GxBUF[ group ].BUF0;
            /*SAFETYMCUSW 45 D MR:21.1 <APPROVED> "Valid non NULL input parameters are
             * only allowed in this driver" */
            ptr->value = ( uint16 ) ( buf & 0x3FFU );
            ptr->id = ( uint32 ) ( ( buf >> 10U ) & 0x1FU );
            /*SAFETYMCUSW 567 S MR:17.1,17.4 <APPROVED> "Pointer increment needed" */
            ptr++;
        }
    }

    adc->GxINTFLG[ group ] = 9U;

    /**   @note The function adcInit has to be called before this function can be used.\n
     *           The user is responsible to initialize the message box.
     */

    /* USER CODE BEGIN (17) */
    /* USER CODE END */

    return count;
}

/* USER CODE BEGIN (18) */
/* USER CODE END */

/** @fn uint32 adcIsFifoFull(adcBASE_t *adc, uint32 group)
 *   @brief Checks if FiFo buffer is full
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *   @param[in] group Hardware group of ADC module:
 *              - adcGROUP0: ADC event group
 *              - adcGROUP1: ADC group 1
 *              - adcGROUP2: ADC group 2
 *   @return The function will return:
 *           - 0: When FiFo buffer is not full
 *           - 1: When FiFo buffer is full
 *           - 3: When FiFo buffer overflow occurred
 *
 *   This function checks FiFo buffer status.
 *
 */
/* SourceId : ADC_SourceId_006 */
/* DesignId : ADC_DesignId_006 */
/* Requirements : HL_SR190 */
uint32 adcIsFifoFull( adcBASE_t * adc, uint32 group )
{
    uint32 flags;

    /* USER CODE BEGIN (19) */
    /* USER CODE END */

    /** - Read FiFo flags */
    flags = adc->GxINTFLG[ group ] & 3U;

    /**   @note The function adcInit has to be called before this function can be used. */

    /* USER CODE BEGIN (20) */
    /* USER CODE END */

    return flags;
}

/* USER CODE BEGIN (21) */
/* USER CODE END */

/** @fn uint32 adcIsConversionComplete(adcBASE_t *adc, uint32 group)
 *   @brief Checks if Conversion is complete
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *   @param[in] group Hardware group of ADC module:
 *              - adcGROUP0: ADC event group
 *              - adcGROUP1: ADC group 1
 *              - adcGROUP2: ADC group 2
 *   @return The function will return:
 *           - 0: When is not finished
 *           - 8: When conversion is complete
 *
 *   This function checks if conversion is complete.
 *
 */
/* SourceId : ADC_SourceId_007 */
/* DesignId : ADC_DesignId_007 */
/* Requirements : HL_SR191 */
uint32 adcIsConversionComplete( adcBASE_t * adc, uint32 group )
{
    uint32 flags;

    /* USER CODE BEGIN (22) */
    /* USER CODE END */

    /** - Read conversion flags */
    flags = adc->GxINTFLG[ group ] & 8U;

    /**   @note The function adcInit has to be called before this function can be used. */

    /* USER CODE BEGIN (23) */
    /* USER CODE END */

    return flags;
}

/* USER CODE BEGIN (24) */
/* USER CODE END */

/** @fn void adcCalibration(adcBASE_t *adc)
 *   @brief Computes offset error using Calibration mode
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *   This function computes offset error using Calibration mode
 *
 */
/* SourceId : ADC_SourceId_008 */
/* DesignId : ADC_DesignId_010 */
/* Requirements : HL_SR194 */
void adcCalibration( adcBASE_t * adc )
{
    /* USER CODE BEGIN (25) */
    /* USER CODE END */

    uint32 conv_val[ 5U ] = { 0U, 0U, 0U, 0U, 0U };
    uint32 loop_index = 0U;
    uint32 offset_error = 0U;
    uint32 backup_mode;

    /** - Backup Mode before Calibration  */
    backup_mode = adc->OPMODECR;

    /** - Enable 12-BIT ADC  */
    adc->OPMODECR |= 0x80000000U;

    /* Disable all channels for conversion */
    adc->GxSEL[ 0U ] = 0x00U;
    adc->GxSEL[ 1U ] = 0x00U;
    adc->GxSEL[ 2U ] = 0x00U;

    for( loop_index = 0U; loop_index < 4U; loop_index++ )
    {
        /* Disable Self Test and Calibration mode */
        adc->CALCR = 0x0U;

        switch( loop_index )
        {
            case 0U: /* Test 1 : Bride En = 0 , HiLo =0 */
                adc->CALCR = 0x0U;
                break;

            case 1U: /* Test 1 : Bride En = 0 , HiLo =1 */
                adc->CALCR = 0x0100U;
                break;

            case 2U: /* Test 1 : Bride En = 1 , HiLo =0 */
                adc->CALCR = 0x0200U;
                break;

            case 3U: /* Test 1 : Bride En = 1 , HiLo =1 */
                adc->CALCR = 0x0300U;
                break;

            default:
                break;
        }

        /* Enable Calibration mode */
        adc->CALCR |= 0x1U;

        /* Start calibration conversion */
        adc->CALCR |= 0x00010000U;

        /* Wait for calibration conversion to complete */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
        while( ( adc->CALCR & 0x00010000U ) == 0x00010000U )
        {
        } /* Wait */

        /* Read converted value */
        conv_val[ loop_index ] = adc->CALR;
    }

    /* Disable Self Test and Calibration mode */
    adc->CALCR = 0x0U;

    /* Compute the Offset error correction value */
    conv_val[ 4U ] = conv_val[ 0U ] + conv_val[ 1U ] + conv_val[ 2U ] + conv_val[ 3U ];

    conv_val[ 4U ] = ( conv_val[ 4U ] / 4U );

    offset_error = conv_val[ 4U ] - 0x7FFU;

    /*Write the offset error to the Calibration register */
    /* Load 2;s complement of the computed value to ADCALR register */
    offset_error = ~offset_error;
    offset_error = offset_error & 0xFFFU;
    offset_error = offset_error + 1U;

    adc->CALR = offset_error;

    /** - Restore Mode after Calibration  */
    adc->OPMODECR = backup_mode;

    /**   @note The function adcInit has to be called before using this function. */

    /* USER CODE BEGIN (26) */
    /* USER CODE END */
}

/** @fn void adcMidPointCalibration(adcBASE_t *adc)
 *   @brief Computes offset error using Mid Point Calibration mode
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *	@return This function will return offset error using Mid Point Calibration mode
 *
 *   This function computes offset error using Mid Point Calibration mode
 *
 */
/* SourceId : ADC_SourceId_009 */
/* DesignId : ADC_DesignId_011 */
/* Requirements : HL_SR195 */
uint32 adcMidPointCalibration( adcBASE_t * adc )
{
    /* USER CODE BEGIN (27) */
    /* USER CODE END */

    uint32 conv_val[ 3U ] = { 0U, 0U, 0U };
    uint32 loop_index = 0U;
    uint32 offset_error = 0U;
    uint32 backup_mode;

    /** - Backup Mode before Calibration  */
    backup_mode = adc->OPMODECR;

    /** - Enable 12-BIT ADC  */
    adc->OPMODECR |= 0x80000000U;

    /* Disable all channels for conversion */
    adc->GxSEL[ 0U ] = 0x00U;
    adc->GxSEL[ 1U ] = 0x00U;
    adc->GxSEL[ 2U ] = 0x00U;

    for( loop_index = 0U; loop_index < 2U; loop_index++ )
    {
        /* Disable Self Test and Calibration mode */
        adc->CALCR = 0x0U;

        switch( loop_index )
        {
            case 0U: /* Test 1 : Bride En = 0 , HiLo =0 */
                adc->CALCR = 0x0U;
                break;

            case 1U: /* Test 1 : Bride En = 0 , HiLo =1 */
                adc->CALCR = 0x0100U;
                break;

            default:
                break;
        }

        /* Enable Calibration mode */
        adc->CALCR |= 0x1U;

        /* Start calibration conversion */
        adc->CALCR |= 0x00010000U;

        /* Wait for calibration conversion to complete */
        /*SAFETYMCUSW 28 D MR:NA <APPROVED> "Hardware status bit read check" */
        while( ( adc->CALCR & 0x00010000U ) == 0x00010000U )
        {
        } /* Wait */

        /* Read converted value */
        conv_val[ loop_index ] = adc->CALR;
    }

    /* Disable Self Test and Calibration mode */
    adc->CALCR = 0x0U;

    /* Compute the Offset error correction value */
    conv_val[ 2U ] = ( conv_val[ 0U ] ) + ( conv_val[ 1U ] );

    conv_val[ 2U ] = ( conv_val[ 2U ] / 2U );

    offset_error = conv_val[ 2U ] - 0x7FFU;

    /* Write the offset error to the Calibration register           */
    /* Load 2's complement of the computed value to ADCALR register */
    offset_error = ~offset_error;
    offset_error = offset_error + 1U;
    offset_error = offset_error & 0xFFFU;

    adc->CALR = offset_error;

    /** - Restore Mode after Calibration  */
    adc->OPMODECR = backup_mode;

    return ( offset_error );

    /**   @note The function adcInit has to be called before this function can be used. */

    /* USER CODE BEGIN (28) */
    /* USER CODE END */
}

/* USER CODE BEGIN (29) */
/* USER CODE END */

/** @fn void adcEnableNotification(adcBASE_t *adc, uint32 group)
 *   @brief Enable notification
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *   @param[in] group Hardware group of ADC module:
 *              - adcGROUP0: ADC event group
 *              - adcGROUP1: ADC group 1
 *              - adcGROUP2: ADC group 2
 *
 *   This function will enable the notification of a conversion.
 *   In single conversion mode for conversion complete and
 *   in continuous conversion mode when the FiFo buffer is full.
 *
 */
/* SourceId : ADC_SourceId_010 */
/* DesignId : ADC_DesignId_008 */
/* Requirements : HL_SR192 */
void adcEnableNotification( adcBASE_t * adc, uint32 group )
{
    uint32 notif = ( ( ( uint32 ) ( adc->GxMODECR[ group ] ) & 2U ) == 2U ) ? 1U : 8U;

    /* USER CODE BEGIN (30) */
    /* USER CODE END */

    adc->GxINTENA[ group ] = notif;

    /**   @note The function adcInit has to be called before this function can be used.\n
     *           This function should be called before the conversion is started
     */

    /* USER CODE BEGIN (31) */
    /* USER CODE END */
}

/* USER CODE BEGIN (32) */
/* USER CODE END */

/** @fn void adcDisableNotification(adcBASE_t *adc, uint32 group)
 *   @brief Disable notification
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *   @param[in] group Hardware group of ADC module:
 *              - adcGROUP0: ADC event group
 *              - adcGROUP1: ADC group 1
 *              - adcGROUP2: ADC group 2
 *
 *   This function will disable the notification of a conversion.
 */
/* SourceId : ADC_SourceId_011 */
/* DesignId : ADC_DesignId_009 */
/* Requirements : HL_SR193 */
void adcDisableNotification( adcBASE_t * adc, uint32 group )
{
    /* USER CODE BEGIN (33) */
    /* USER CODE END */

    adc->GxINTENA[ group ] = 0U;

    /**   @note The function adcInit has to be called before this function can be used. */

    /* USER CODE BEGIN (34) */
    /* USER CODE END */
}

/** @fn void adcSetEVTPin(adcBASE_t *adc, uint32 value)
 *   @brief Set ADCEVT pin
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *   @param[in] value Value to be set: 0 or 1
 *
 *   This function will set the ADC EVT pin if configured as an output pin.
 */
/* SourceId : ADC_SourceId_020 */
/* DesignId : ADC_DesignId_014 */
/* Requirements : HL_SR529 */
void adcSetEVTPin( adcBASE_t * adc, uint32 value )
{
    adc->EVTOUT = value;
}

/** @fn uint32 adcGetEVTPin(adcBASE_t *adc)
 *   @brief Set ADCEVT pin
 *   @param[in] adc Pointer to ADC module:
 *              - adcREG1: ADC1 module pointer
 *   @return Value of the ADC EVT pin: 0 or 1
 *
 *   This function will return the value of ADC EVT pin.
 */
/* SourceId : ADC_SourceId_021 */
/* DesignId : ADC_DesignId_015 */
/* Requirements : HL_SR529 */
uint32 adcGetEVTPin( adcBASE_t * adc )
{
    return adc->EVTIN;
}

/** @fn void adc1GetConfigValue(adc_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
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
/* SourceId : ADC_SourceId_012 */
/* DesignId : ADC_DesignId_012 */
/* Requirements : HL_SR203 */
void adc1GetConfigValue( adc_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_OPMODECR = ADC1_OPMODECR_CONFIGVALUE;
        config_reg->CONFIG_CLOCKCR = ADC1_CLOCKCR_CONFIGVALUE;
        config_reg->CONFIG_GxMODECR[ 0U ] = ADC1_G0MODECR_CONFIGVALUE;
        config_reg->CONFIG_GxMODECR[ 1U ] = ADC1_G1MODECR_CONFIGVALUE;
        config_reg->CONFIG_GxMODECR[ 2U ] = ADC1_G2MODECR_CONFIGVALUE;
        config_reg->CONFIG_G0SRC = ADC1_G0SRC_CONFIGVALUE;
        config_reg->CONFIG_G1SRC = ADC1_G1SRC_CONFIGVALUE;
        config_reg->CONFIG_G2SRC = ADC1_G2SRC_CONFIGVALUE;
        config_reg->CONFIG_BNDCR = ADC1_BNDCR_CONFIGVALUE;
        config_reg->CONFIG_BNDEND = ADC1_BNDEND_CONFIGVALUE;
        config_reg->CONFIG_G0SAMP = ADC1_G0SAMP_CONFIGVALUE;
        config_reg->CONFIG_G1SAMP = ADC1_G1SAMP_CONFIGVALUE;
        config_reg->CONFIG_G2SAMP = ADC1_G2SAMP_CONFIGVALUE;
        config_reg->CONFIG_G0SAMPDISEN = ADC1_G0SAMPDISEN_CONFIGVALUE;
        config_reg->CONFIG_G1SAMPDISEN = ADC1_G1SAMPDISEN_CONFIGVALUE;
        config_reg->CONFIG_G2SAMPDISEN = ADC1_G2SAMPDISEN_CONFIGVALUE;
        config_reg->CONFIG_PARCR = ADC1_PARCR_CONFIGVALUE;
    }
    else
    {
        config_reg->CONFIG_OPMODECR = adcREG1->OPMODECR;
        config_reg->CONFIG_CLOCKCR = adcREG1->CLOCKCR;
        config_reg->CONFIG_GxMODECR[ 0U ] = adcREG1->GxMODECR[ 0U ];
        config_reg->CONFIG_GxMODECR[ 1U ] = adcREG1->GxMODECR[ 1U ];
        config_reg->CONFIG_GxMODECR[ 2U ] = adcREG1->GxMODECR[ 2U ];
        config_reg->CONFIG_G0SRC = adcREG1->EVSRC;
        config_reg->CONFIG_G1SRC = adcREG1->G1SRC;
        config_reg->CONFIG_G2SRC = adcREG1->G2SRC;
        config_reg->CONFIG_BNDCR = adcREG1->BNDCR;
        config_reg->CONFIG_BNDEND = adcREG1->BNDEND;
        config_reg->CONFIG_G0SAMP = adcREG1->EVSAMP;
        config_reg->CONFIG_G1SAMP = adcREG1->G1SAMP;
        config_reg->CONFIG_G2SAMP = adcREG1->G2SAMP;
        config_reg->CONFIG_G0SAMPDISEN = adcREG1->EVSAMPDISEN;
        config_reg->CONFIG_G1SAMPDISEN = adcREG1->G1SAMPDISEN;
        config_reg->CONFIG_G2SAMPDISEN = adcREG1->G2SAMPDISEN;
        config_reg->CONFIG_PARCR = adcREG1->PARCR;
    }
}

/** @fn void adc2GetConfigValue(adc_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
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
/* SourceId : ADC_SourceId_013 */
/* DesignId : ADC_DesignId_012 */
/* Requirements : HL_SR203 */
void adc2GetConfigValue( adc_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_OPMODECR = ADC2_OPMODECR_CONFIGVALUE;
        config_reg->CONFIG_CLOCKCR = ADC2_CLOCKCR_CONFIGVALUE;
        config_reg->CONFIG_GxMODECR[ 0U ] = ADC2_G0MODECR_CONFIGVALUE;
        config_reg->CONFIG_GxMODECR[ 1U ] = ADC2_G1MODECR_CONFIGVALUE;
        config_reg->CONFIG_GxMODECR[ 2U ] = ADC2_G2MODECR_CONFIGVALUE;
        config_reg->CONFIG_G0SRC = ADC2_G0SRC_CONFIGVALUE;
        config_reg->CONFIG_G1SRC = ADC2_G1SRC_CONFIGVALUE;
        config_reg->CONFIG_G2SRC = ADC2_G2SRC_CONFIGVALUE;
        config_reg->CONFIG_BNDCR = ADC2_BNDCR_CONFIGVALUE;
        config_reg->CONFIG_BNDEND = ADC2_BNDEND_CONFIGVALUE;
        config_reg->CONFIG_G0SAMP = ADC2_G0SAMP_CONFIGVALUE;
        config_reg->CONFIG_G1SAMP = ADC2_G1SAMP_CONFIGVALUE;
        config_reg->CONFIG_G2SAMP = ADC2_G2SAMP_CONFIGVALUE;
        config_reg->CONFIG_G0SAMPDISEN = ADC2_G0SAMPDISEN_CONFIGVALUE;
        config_reg->CONFIG_G1SAMPDISEN = ADC2_G1SAMPDISEN_CONFIGVALUE;
        config_reg->CONFIG_G2SAMPDISEN = ADC2_G2SAMPDISEN_CONFIGVALUE;
        config_reg->CONFIG_PARCR = ADC2_PARCR_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_OPMODECR = adcREG2->OPMODECR;
        config_reg->CONFIG_CLOCKCR = adcREG2->CLOCKCR;
        config_reg->CONFIG_GxMODECR[ 0U ] = adcREG2->GxMODECR[ 0U ];
        config_reg->CONFIG_GxMODECR[ 1U ] = adcREG2->GxMODECR[ 1U ];
        config_reg->CONFIG_GxMODECR[ 2U ] = adcREG2->GxMODECR[ 2U ];
        config_reg->CONFIG_G0SRC = adcREG2->EVSRC;
        config_reg->CONFIG_G1SRC = adcREG2->G1SRC;
        config_reg->CONFIG_G2SRC = adcREG2->G2SRC;
        config_reg->CONFIG_BNDCR = adcREG2->BNDCR;
        config_reg->CONFIG_BNDEND = adcREG2->BNDEND;
        config_reg->CONFIG_G0SAMP = adcREG2->EVSAMP;
        config_reg->CONFIG_G1SAMP = adcREG2->G1SAMP;
        config_reg->CONFIG_G2SAMP = adcREG2->G2SAMP;
        config_reg->CONFIG_G0SAMPDISEN = adcREG2->EVSAMPDISEN;
        config_reg->CONFIG_G1SAMPDISEN = adcREG2->G1SAMPDISEN;
        config_reg->CONFIG_G2SAMPDISEN = adcREG2->G2SAMPDISEN;
        config_reg->CONFIG_PARCR = adcREG2->PARCR;
    }
}

/* USER CODE BEGIN (35) */
/* USER CODE END */
