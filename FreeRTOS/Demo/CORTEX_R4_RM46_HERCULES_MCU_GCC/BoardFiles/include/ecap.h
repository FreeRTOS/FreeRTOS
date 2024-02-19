/** @file ecap.h
 *   @brief ECAP Driver Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the ECAP driver.
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

#ifndef __ECAP_H__
#define __ECAP_H__

#include "reg_ecap.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/** @brief Enumeration to define the capture (CAP) interrupts
 */
typedef enum
{
    ecapInt_CTR_CMP = 0x0080U, /*< Denotes CTR = CMP interrupt        */
    ecapInt_CTR_PRD = 0x0040U, /*< Denotes CTR = PRD interrupt        */
    ecapInt_CTR_OVF = 0x0020U, /*< Denotes CTROVF interrupt           */
    ecapInt_CEVT4 = 0x0010U,   /*< Denotes CEVT4 interrupt            */
    ecapInt_CEVT3 = 0x0008U,   /*< Denotes CEVT3 interrupt            */
    ecapInt_CEVT2 = 0x0004U,   /*< Denotes CEVT2 interrupt            */
    ecapInt_CEVT1 = 0x0002U,   /*< Denotes CEVT1 interrupt            */
    ecapInt_Global = 0x0001U,  /*< Denotes Capture global interrupt   */
    ecapInt_All = 0x00FFU      /*< Denotes All interrupts             */
} ecapInterrupt_t;

/** @brief Enumeration to define the capture (CAP) prescaler values
 */
typedef enum
{
    ecapPrescale_By_1 = ( ( uint16 ) 0U << 9U ),   /*< Divide by 1   */
    ecapPrescale_By_2 = ( ( uint16 ) 1U << 9U ),   /*< Divide by 2   */
    ecapPrescale_By_4 = ( ( uint16 ) 2U << 9U ),   /*< Divide by 4   */
    ecapPrescale_By_6 = ( ( uint16 ) 3U << 9U ),   /*< Divide by 6   */
    ecapPrescale_By_8 = ( ( uint16 ) 4U << 9U ),   /*< Divide by 8   */
    ecapPrescale_By_10 = ( ( uint16 ) 5U << 9U ),  /*< Divide by 10  */
    ecapPrescale_By_12 = ( ( uint16 ) 6U << 9U ),  /*< Divide by 12  */
    ecapPrescale_By_14 = ( ( uint16 ) 7U << 9U ),  /*< Divide by 14  */
    ecapPrescale_By_16 = ( ( uint16 ) 8U << 9U ),  /*< Divide by 16  */
    ecapPrescale_By_18 = ( ( uint16 ) 9U << 9U ),  /*< Divide by 18  */
    ecapPrescale_By_20 = ( ( uint16 ) 10U << 9U ), /*< Divide by 20  */
    ecapPrescale_By_22 = ( ( uint16 ) 11U << 9U ), /*< Divide by 22  */
    ecapPrescale_By_24 = ( ( uint16 ) 12U << 9U ), /*< Divide by 24  */
    ecapPrescale_By_26 = ( ( uint16 ) 13U << 9U ), /*< Divide by 26  */
    ecapPrescale_By_28 = ( ( uint16 ) 14U << 9U ), /*< Divide by 28  */
    ecapPrescale_By_30 = ( ( uint16 ) 15U << 9U ), /*< Divide by 30  */
    ecapPrescale_By_32 = ( ( uint16 ) 16U << 9U ), /*< Divide by 32  */
    ecapPrescale_By_34 = ( ( uint16 ) 17U << 9U ), /*< Divide by 34  */
    ecapPrescale_By_36 = ( ( uint16 ) 18U << 9U ), /*< Divide by 36  */
    ecapPrescale_By_38 = ( ( uint16 ) 19U << 9U ), /*< Divide by 38  */
    ecapPrescale_By_40 = ( ( uint16 ) 20U << 9U ), /*< Divide by 40  */
    ecapPrescale_By_42 = ( ( uint16 ) 21U << 9U ), /*< Divide by 42  */
    ecapPrescale_By_44 = ( ( uint16 ) 22U << 9U ), /*< Divide by 44  */
    ecapPrescale_By_46 = ( ( uint16 ) 23U << 9U ), /*< Divide by 46  */
    ecapPrescale_By_48 = ( ( uint16 ) 24U << 9U ), /*< Divide by 48  */
    ecapPrescale_By_50 = ( ( uint16 ) 25U << 9U ), /*< Divide by 50  */
    ecapPrescale_By_52 = ( ( uint16 ) 26U << 9U ), /*< Divide by 52  */
    ecapPrescale_By_54 = ( ( uint16 ) 27U << 9U ), /*< Divide by 54  */
    ecapPrescale_By_56 = ( ( uint16 ) 28U << 9U ), /*< Divide by 56  */
    ecapPrescale_By_58 = ( ( uint16 ) 29U << 9U ), /*< Divide by 58  */
    ecapPrescale_By_60 = ( ( uint16 ) 30U << 9U ), /*< Divide by 60  */
    ecapPrescale_By_62 = ( ( uint16 ) 31U << 9U )  /*< Divide by 62  */
} ecapPrescale_t;

/** @brief Enumeration to define the Sync Out options
 */
typedef enum
{
    SyncOut_SyncIn = ( ( uint16 ) 0U << 6U ), /*< Sync In used for Sync Out   */
    SyncOut_CTRPRD = ( ( uint16 ) 1U << 6U ), /*< CTR = PRD used for Sync Out */
    SyncOut_None = ( ( uint16 ) 2U << 6U )    /*< Disables Sync Out           */
} ecapSyncOut_t;

/** @brief Enumeration to define the Polarity
 */
typedef enum
{
    RISING_EDGE = 0U,
    FALLING_EDGE = 1U
} ecapEdgePolarity_t;

typedef enum
{
    ACTIVE_HIGH = 0U,
    ACTIVE_LOW = 1U
} ecapAPWMPolarity_t;

/** @brief Enumeration to define the Mode of operation
 */
typedef enum
{
    CONTINUOUS = 0U,
    ONE_SHOT = 1U
} ecapMode_t;

/** @brief Enumeration to define the capture events
 */
typedef enum
{
    CAPTURE_EVENT1 = 0U,
    CAPTURE_EVENT2 = 1U,
    CAPTURE_EVENT3 = 2U,
    CAPTURE_EVENT4 = 3U
} ecapEvent_t;

typedef enum
{
    RESET_ENABLE = 1U,
    RESET_DISABLE = 0U
} ecapReset_t;

typedef struct ecap_config_reg
{
    uint32 CONFIG_CTRPHS;
    uint16 CONFIG_ECCTL1;
    uint16 CONFIG_ECCTL2;
    uint16 CONFIG_ECEINT;
} ecap_config_reg_t;

#define ECAP1_CTRPHS_CONFIGVALUE 0x00000000U
#define ECAP1_ECCTL1_CONFIGVALUE                      \
    ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 9U ) )
#define ECAP1_ECCTL2_CONFIGVALUE                       \
    ( ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )         \
      | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 9U ) | ( uint16 ) 0x00000010U )
#define ECAP1_ECEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )

#define ECAP2_CTRPHS_CONFIGVALUE 0x00000000U
#define ECAP2_ECCTL1_CONFIGVALUE                      \
    ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 9U ) )
#define ECAP2_ECCTL2_CONFIGVALUE                       \
    ( ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )         \
      | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 9U ) | ( uint16 ) 0x00000010U )
#define ECAP2_ECEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )

#define ECAP3_CTRPHS_CONFIGVALUE 0x00000000U
#define ECAP3_ECCTL1_CONFIGVALUE                      \
    ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 9U ) )
#define ECAP3_ECCTL2_CONFIGVALUE                       \
    ( ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )         \
      | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 9U ) | ( uint16 ) 0x00000010U )
#define ECAP3_ECEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )

#define ECAP4_CTRPHS_CONFIGVALUE 0x00000000U
#define ECAP4_ECCTL1_CONFIGVALUE                      \
    ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 9U ) )
#define ECAP4_ECCTL2_CONFIGVALUE                       \
    ( ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )         \
      | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 9U ) | ( uint16 ) 0x00000010U )
#define ECAP4_ECEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )

#define ECAP5_CTRPHS_CONFIGVALUE 0x00000000U
#define ECAP5_ECCTL1_CONFIGVALUE                      \
    ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 9U ) )
#define ECAP5_ECCTL2_CONFIGVALUE                       \
    ( ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )         \
      | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 9U ) | ( uint16 ) 0x00000010U )
#define ECAP5_ECEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )

#define ECAP6_CTRPHS_CONFIGVALUE 0x00000000U
#define ECAP6_ECCTL1_CONFIGVALUE                      \
    ( ( uint16 ) ( ( uint16 ) RISING_EDGE << 0U )     \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 1U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 2U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 3U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 4U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 5U ) \
      | ( uint16 ) ( ( uint16 ) RISING_EDGE << 6U )   \
      | ( uint16 ) ( ( uint16 ) RESET_DISABLE << 7U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 8U ) | ( uint16 ) ( ( uint16 ) 0U << 9U ) )
#define ECAP6_ECCTL2_CONFIGVALUE                       \
    ( ( uint16 ) ( ( uint16 ) ONE_SHOT << 0U )         \
      | ( uint16 ) ( ( uint16 ) CAPTURE_EVENT1 << 1U ) \
      | ( uint16 ) ( ( uint16 ) 0U << 9U ) | ( uint16 ) 0x00000010U )
#define ECAP6_ECEINT_CONFIGVALUE \
    ( 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U | 0x0000U )

/**
 *  @defgroup eCAP eCAP
 *  @brief Enhanced Capture Module.
 *
 *  The enhanced Capture (eCAP) module is essential in systems where accurate timing of
 *external events is important. This microcontroller implements 6 instances of the eCAP
 *module.
 *
 *	Related Files
 *   - reg_ecap.h
 *   - ecap.h
 *   - ecap.c
 *  @addtogroup eCAP
 *  @{
 */
void ecapInit( void );
void ecapSetCounter( ecapBASE_t * ecap, uint32 value );
void ecapEnableCounterLoadOnSync( ecapBASE_t * ecap, uint32 phase );
void ecapDisableCounterLoadOnSync( ecapBASE_t * ecap );
void ecapSetEventPrescaler( ecapBASE_t * ecap, ecapPrescale_t prescale );
void ecapSetCaptureEvent1( ecapBASE_t * ecap,
                           ecapEdgePolarity_t edgePolarity,
                           ecapReset_t resetenable );
void ecapSetCaptureEvent2( ecapBASE_t * ecap,
                           ecapEdgePolarity_t edgePolarity,
                           ecapReset_t resetenable );
void ecapSetCaptureEvent3( ecapBASE_t * ecap,
                           ecapEdgePolarity_t edgePolarity,
                           ecapReset_t resetenable );
void ecapSetCaptureEvent4( ecapBASE_t * ecap,
                           ecapEdgePolarity_t edgePolarity,
                           ecapReset_t resetenable );
void ecapSetCaptureMode( ecapBASE_t * ecap, ecapMode_t capMode, ecapEvent_t event );
void ecapEnableCapture( ecapBASE_t * ecap );
void ecapDisableCapture( ecapBASE_t * ecap );
void ecapStartCounter( ecapBASE_t * ecap );
void ecapStopCounter( ecapBASE_t * ecap );
void ecapSetSyncOut( ecapBASE_t * ecap, ecapSyncOut_t syncOutSrc );
void ecapEnableAPWMmode( ecapBASE_t * ecap,
                         ecapAPWMPolarity_t pwmPolarity,
                         uint32 period,
                         uint32 duty );
void ecapDisableAPWMMode( ecapBASE_t * ecap );
void ecapEnableInterrupt( ecapBASE_t * ecap, ecapInterrupt_t interrupts );
void ecapDisableInterrupt( ecapBASE_t * ecap, ecapInterrupt_t interrupts );
uint16 ecapGetEventStatus( ecapBASE_t * ecap, ecapInterrupt_t events );
void ecapClearFlag( ecapBASE_t * ecap, ecapInterrupt_t events );
uint32 ecapGetCAP1( ecapBASE_t * ecap );
uint32 ecapGetCAP2( ecapBASE_t * ecap );
uint32 ecapGetCAP3( ecapBASE_t * ecap );
uint32 ecapGetCAP4( ecapBASE_t * ecap );
void ecap1GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type );
void ecap2GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type );
void ecap3GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type );
void ecap4GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type );
void ecap5GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type );
void ecap6GetConfigValue( ecap_config_reg_t * config_reg, config_value_type_t type );

/** @brief Interrupt callback
 *   @param[in] ecap	 Handle to CAP object
 *   @param[in] flags Copy of  interrupt flags
 */
void ecapNotification( ecapBASE_t * ecap, uint16 flags );

/**@}*/

#ifdef __cplusplus
}
#endif /*extern "C"  */

/* USER CODE BEGIN (1) */
/* USER CODE END */
#endif /*end of _CAP_H_ definition  */
