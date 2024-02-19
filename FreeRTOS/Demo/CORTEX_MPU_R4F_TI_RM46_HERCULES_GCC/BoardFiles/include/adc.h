/** @file adc.h
 *   @brief ADC Driver Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
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

#ifndef __ADC_H__
#define __ADC_H__

#include "reg_adc.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* ADC General Definitions */

/** @def adcGROUP0
 *   @brief Alias name for ADC event group
 *
 *   @note This value should be used for API argument @a group
 */
#define adcGROUP0       0U

/** @def adcGROUP1
 *   @brief Alias name for ADC group 1
 *
 *   @note This value should be used for API argument @a group
 */
#define adcGROUP1       1U

/** @def adcGROUP2
 *   @brief Alias name for ADC group 2
 *
 *   @note This value should be used for API argument @a group
 */
#define adcGROUP2       2U

/** @def ADC_12_BIT_MODE
 *   @brief Alias name for ADC 12-bit mode of operation
 */
#define ADC_12_BIT_MODE 0x80000000U

/** @enum adcResolution
 *   @brief Alias names for data resolution
 *   This enumeration is used to provide alias names for the data resolution:
 *     - 12 bit resolution
 *     - 10 bit resolution
 *     - 8  bit resolution
 */
enum adcResolution
{
    ADC_12_BIT = 0x00000000U, /**< Alias for 12 bit data resolution */
    ADC_10_BIT = 0x00000100U, /**< Alias for 10 bit data resolution */
    ADC_8_BIT = 0x00000200U   /**< Alias for 8 bit data resolution  */
};

/** @enum adcFiFoStatus
 *   @brief Alias names for FiFo status
 *   This enumeration is used to provide alias names for the current FiFo states:
 *     - FiFo is not full
 *     - FiFo is full
 *     - FiFo overflow occurred
 */

enum adcFiFoStatus
{
    ADC_FIFO_IS_NOT_FULL = 0U, /**< Alias for FiFo is not full       */
    ADC_FIFO_IS_FULL = 1U,     /**< Alias for FiFo is full           */
    ADC_FIFO_OVERFLOW = 3U     /**< Alias for FiFo overflow occurred  */
};

/** @enum adcConversionStatus
 *   @brief Alias names for conversion status
 *   This enumeration is used to provide alias names for the current conversion states:
 *     - Conversion is not finished
 *     - Conversion is finished
 */

enum adcConversionStatus
{
    ADC_CONVERSION_IS_NOT_FINISHED = 0U, /**< Alias for current conversion is not finished
                                          */
    ADC_CONVERSION_IS_FINISHED = 8U /**< Alias for current conversion is  finished    */
};

/** @enum adc1HwTriggerSource
 *   @brief Alias names for hardware trigger source
 *   This enumeration is used to provide alias names for the hardware trigger sources:
 */

enum adc1HwTriggerSource
{
    ADC1_EVENT = 0U,     /**< Alias for event pin             */
    ADC1_HET1_8 = 1U,    /**< Alias for HET1 pin 8            */
    ADC1_HET1_10 = 2U,   /**< Alias for HET1 pin 10           */
    ADC1_RTI_COMP0 = 3U, /**< Alias for RTI compare 0 match   */
    ADC1_HET1_12 = 4U,   /**< Alias for HET1 pin 12           */
    ADC1_HET1_14 = 5U,   /**< Alias for HET1 pin 14           */
    ADC1_GIOB0 = 6U,     /**< Alias for GIO port b pin 0      */
    ADC1_GIOB1 = 7U,     /**< Alias for GIO port b pin 1      */

    ADC1_HET2_5 = 1U,  /**< Alias for HET2 pin 5            */
    ADC1_HET1_27 = 2U, /**< Alias for HET1 pin 27           */
    ADC1_HET1_17 = 4U, /**< Alias for HET1 pin 17           */
    ADC1_HET1_19 = 5U, /**< Alias for HET1 pin 19           */
    ADC1_HET1_11 = 6U, /**< Alias for HET1 pin 11           */
    ADC1_HET2_13 = 7U, /**< Alias for HET2 pin 13           */

    ADC1_EPWM_B = 1U,  /**< Alias for B Signal EPWM         */
    ADC1_EPWM_A1 = 3U, /**< Alias for A1 Signal EPWM        */
    ADC1_HET2_1 = 5U,  /**< Alias for HET2 pin 1            */
    ADC1_EPWM_A2 = 6U, /**< Alias for A2 Signal EPWM        */
    ADC1_EPWM_AB = 7U  /**< Alias for AB Signal EPWM        */
};

/** @enum adc2HwTriggerSource
 *   @brief Alias names for hardware trigger source
 *   This enumeration is used to provide alias names for the hardware trigger sources:
 */

enum adc2HwTriggerSource
{
    ADC2_EVENT = 0U,     /**< Alias for event pin             */
    ADC2_HET1_8 = 1U,    /**< Alias for HET1 pin 8            */
    ADC2_HET1_10 = 2U,   /**< Alias for HET1 pin 10           */
    ADC2_RTI_COMP0 = 3U, /**< Alias for RTI compare 0 match   */
    ADC2_HET1_12 = 4U,   /**< Alias for HET1 pin 12           */
    ADC2_HET1_14 = 5U,   /**< Alias for HET1 pin 14           */
    ADC2_GIOB0 = 6U,     /**< Alias for GIO port b pin 0      */
    ADC2_GIOB1 = 7U,     /**< Alias for GIO port b pin 1      */
    ADC2_HET2_5 = 1U,    /**< Alias for HET2 pin 5            */
    ADC2_HET1_27 = 2U,   /**< Alias for HET1 pin 27           */
    ADC2_HET1_17 = 4U,   /**< Alias for HET1 pin 17           */
    ADC2_HET1_19 = 5U,   /**< Alias for HET1 pin 19           */
    ADC2_HET1_11 = 6U,   /**< Alias for HET1 pin 11           */
    ADC2_HET2_13 = 7U,   /**< Alias for HET2 pin 13           */

    ADC2_EPWM_B = 1U,  /**< Alias for B Signal EPWM         */
    ADC2_EPWM_A1 = 3U, /**< Alias for A1 Signal EPWM        */
    ADC2_HET2_1 = 5U,  /**< Alias for HET2 pin 1            */
    ADC2_EPWM_A2 = 6U, /**< Alias for A2 Signal EPWM        */
    ADC2_EPWM_AB = 7U  /**< Alias for AB Signal EPWM        */
};

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @struct adcData
 *   @brief ADC Conversion data structure
 *
 *   This type is used to pass adc conversion data.
 */

/** @typedef adcData_t
 *   @brief ADC Data Type Definition
 */
typedef struct adcData
{
    uint32 id;    /**< Channel/Pin Id        */
    uint16 value; /**< Conversion data value */
} adcData_t;

/* USER CODE BEGIN (2) */
/* USER CODE END */

typedef struct adc_config_reg
{
    uint32 CONFIG_OPMODECR;
    uint32 CONFIG_CLOCKCR;
    uint32 CONFIG_GxMODECR[ 3U ];
    uint32 CONFIG_G0SRC;
    uint32 CONFIG_G1SRC;
    uint32 CONFIG_G2SRC;
    uint32 CONFIG_BNDCR;
    uint32 CONFIG_BNDEND;
    uint32 CONFIG_G0SAMP;
    uint32 CONFIG_G1SAMP;
    uint32 CONFIG_G2SAMP;
    uint32 CONFIG_G0SAMPDISEN;
    uint32 CONFIG_G1SAMPDISEN;
    uint32 CONFIG_G2SAMPDISEN;
    uint32 CONFIG_PARCR;
} adc_config_reg_t;

#define ADC1_OPMODECR_CONFIGVALUE 0x81140001U
#define ADC1_CLOCKCR_CONFIGVALUE  ( 10U )

#define ADC1_G0MODECR_CONFIGVALUE \
    ( ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )
#define ADC1_G1MODECR_CONFIGVALUE                                             \
    ( ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U )
#define ADC1_G2MODECR_CONFIGVALUE                                             \
    ( ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U )

#define ADC1_G0SRC_CONFIGVALUE       ( ( uint32 ) 0x00000000U | ( uint32 ) ADC1_EVENT )
#define ADC1_G1SRC_CONFIGVALUE       ( ( uint32 ) 0x00000000U | ( uint32 ) ADC1_EVENT )
#define ADC1_G2SRC_CONFIGVALUE       ( ( uint32 ) 0x00000000U | ( uint32 ) ADC1_EVENT )

#define ADC1_BNDCR_CONFIGVALUE       ( ( uint32 ) ( ( uint32 ) 8U << 16U ) | ( 8U + 8U ) )
#define ADC1_BNDEND_CONFIGVALUE      ( 2U )

#define ADC1_G0SAMP_CONFIGVALUE      ( 1U )
#define ADC1_G1SAMP_CONFIGVALUE      ( 1U )
#define ADC1_G2SAMP_CONFIGVALUE      ( 1U )

#define ADC1_G0SAMPDISEN_CONFIGVALUE ( ( uint32 ) ( ( uint32 ) 0U << 8U ) | 0x00000000U )
#define ADC1_G1SAMPDISEN_CONFIGVALUE ( ( uint32 ) ( ( uint32 ) 0U << 8U ) | 0x00000000U )
#define ADC1_G2SAMPDISEN_CONFIGVALUE ( ( uint32 ) ( ( uint32 ) 0U << 8U ) | 0x00000000U )

#define ADC1_PARCR_CONFIGVALUE       ( 0x00000005U )

#define ADC2_OPMODECR_CONFIGVALUE    0x81140001U
#define ADC2_CLOCKCR_CONFIGVALUE     ( 10U )

#define ADC2_G0MODECR_CONFIGVALUE \
    ( ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )
#define ADC2_G1MODECR_CONFIGVALUE                                             \
    ( ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U )
#define ADC2_G2MODECR_CONFIGVALUE                                             \
    ( ( uint32 ) ADC_12_BIT | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U )

#define ADC2_G0SRC_CONFIGVALUE       ( ( uint32 ) 0x00000000U | ( uint32 ) ADC2_EVENT )
#define ADC2_G1SRC_CONFIGVALUE       ( ( uint32 ) 0x00000000U | ( uint32 ) ADC2_EVENT )
#define ADC2_G2SRC_CONFIGVALUE       ( ( uint32 ) 0x00000000U | ( uint32 ) ADC2_EVENT )

#define ADC2_BNDCR_CONFIGVALUE       ( ( uint32 ) ( ( uint32 ) 8U << 16U ) | ( 8U + 8U ) )
#define ADC2_BNDEND_CONFIGVALUE      ( 2U )

#define ADC2_G0SAMP_CONFIGVALUE      ( 1U )
#define ADC2_G1SAMP_CONFIGVALUE      ( 1U )
#define ADC2_G2SAMP_CONFIGVALUE      ( 1U )

#define ADC2_G0SAMPDISEN_CONFIGVALUE ( ( uint32 ) ( ( uint32 ) 0U << 8U ) | 0x00000000U )
#define ADC2_G1SAMPDISEN_CONFIGVALUE ( ( uint32 ) ( ( uint32 ) 0U << 8U ) | 0x00000000U )
#define ADC2_G2SAMPDISEN_CONFIGVALUE ( ( uint32 ) ( ( uint32 ) 0U << 8U ) | 0x00000000U )

#define ADC2_PARCR_CONFIGVALUE       ( 0x00000005U )

/**
 *  @defgroup ADC ADC
 *  @brief Analog To Digital Converter Module.
 *
 *  The microcontroller includes two 12-bit ADC modules with selectable 10-bit or 12-bit
 *resolution
 *
 *	Related Files
 *   - reg_adc.h
 *   - adc.h
 *   - adc.c
 *  @addtogroup ADC
 *  @{
 */

/* ADC Interface Functions */

void adcInit( void );
void adcStartConversion( adcBASE_t * adc, uint32 group );
void adcStopConversion( adcBASE_t * adc, uint32 group );
void adcResetFiFo( adcBASE_t * adc, uint32 group );
uint32 adcGetData( adcBASE_t * adc, uint32 group, adcData_t * data );
uint32 adcIsFifoFull( adcBASE_t * adc, uint32 group );
uint32 adcIsConversionComplete( adcBASE_t * adc, uint32 group );
void adcEnableNotification( adcBASE_t * adc, uint32 group );
void adcDisableNotification( adcBASE_t * adc, uint32 group );
void adcCalibration( adcBASE_t * adc );
uint32 adcMidPointCalibration( adcBASE_t * adc );
void adcSetEVTPin( adcBASE_t * adc, uint32 value );
uint32 adcGetEVTPin( adcBASE_t * adc );

void adc1GetConfigValue( adc_config_reg_t * config_reg, config_value_type_t type );
void adc2GetConfigValue( adc_config_reg_t * config_reg, config_value_type_t type );

/** @fn void adcNotification(adcBASE_t *adc, uint32 group)
 *   @brief Group notification
 *   @param[in] adc Pointer to ADC node:
 *              - adcREG1: ADC1 module pointer
 *              - adcREG2: ADC2 module pointer
 *   @param[in] group number of ADC node:
 *              - adcGROUP0: ADC event group
 *              - adcGROUP1: ADC group 1
 *              - adcGROUP2: ADC group 2
 *
 *   @note This function has to be provide by the user.
 */
void adcNotification( adcBASE_t * adc, uint32 group );

/* USER CODE BEGIN (3) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif
#endif /* ifndef __ADC_H__ */
