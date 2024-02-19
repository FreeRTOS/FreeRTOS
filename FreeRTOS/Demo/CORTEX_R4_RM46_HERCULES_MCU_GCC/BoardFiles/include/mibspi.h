/** @file mibspi.h
 *   @brief MIBSPI Driver Definition File
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

#ifndef __MIBSPI_H__
#define __MIBSPI_H__

#include "reg_mibspi.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/** @enum triggerEvent
 *   @brief Transfer Group Trigger Event
 */
enum triggerEvent
{
    TRG_NEVER = 0U,
    TRG_RISING = 1U,
    TRG_FALLING = 2U,
    TRG_BOTH = 3U,
    TRG_HIGH = 5U,
    TRG_LOW = 6U,
    TRG_ALWAYS = 7U
};

/** @enum triggerSource
 *   @brief Transfer Group Trigger Source
 */
enum triggerSource
{
    TRG_DISABLED,
    TRG_GIOA0,
    TRG_GIOA1,
    TRG_GIOA2,
    TRG_GIOA3,
    TRG_GIOA4,
    TRG_GIOA5,
    TRG_GIOA6,
    TRG_GIOA7,
    TRG_HET1_8,
    TRG_HET1_10,
    TRG_HET1_12,
    TRG_HET1_14,
    TRG_HET1_16,
    TRG_HET1_18,
    TRG_TICK
};

/** @enum mibspiPinSelect
 *   @brief mibspi Pin Select
 */
enum mibspiPinSelect
{
    PIN_CS0 = 0U,
    PIN_CS1 = 1U,
    PIN_CS2 = 2U,
    PIN_CS3 = 3U,
    PIN_CS4 = 4U,
    PIN_CS5 = 5U,
    PIN_CS6 = 6U,
    PIN_CS7 = 7U,
    PIN_ENA = 8U,
    PIN_CLK = 9U,
    PIN_SIMO = 10U,
    PIN_SOMI = 11U,
    PIN_SIMO_1 = 17U,
    PIN_SIMO_2 = 18U,
    PIN_SIMO_3 = 19U,
    PIN_SIMO_4 = 20U,
    PIN_SIMO_5 = 21U,
    PIN_SIMO_6 = 22U,
    PIN_SIMO_7 = 23U,
    PIN_SOMI_1 = 25U,
    PIN_SOMI_2 = 26U,
    PIN_SOMI_3 = 27U,
    PIN_SOMI_4 = 28U,
    PIN_SOMI_5 = 29U,
    PIN_SOMI_6 = 30U,
    PIN_SOMI_7 = 31U
};

/** @enum chipSelect
 *   @brief Transfer Group Chip Select
 */
enum chipSelect
{
    CS_NONE = 0xFFU,
    CS_0 = 0xFEU,
    CS_1 = 0xFDU,
    CS_2 = 0xFBU,
    CS_3 = 0xF7U,
    CS_4 = 0xEFU,
    CS_5 = 0xDFU,
    CS_6 = 0xBFU,
    CS_7 = 0x7FU
};

/** @typedef mibspiPmode_t
 *   @brief Mibspi Parellel mode Type Definition
 *
 *   This type is used to represent Mibspi Parellel mode.
 */
typedef enum mibspiPmode
{
    PMODE_NORMAL = 0x0U,
    PMODE_2_DATALINE = 0x1U,
    PMODE_4_DATALINE = 0x2U,
    PMODE_8_DATALINE = 0x3U
} mibspiPmode_t;

/** @typedef mibspiDFMT_t
 *   @brief Mibspi Data format selection Type Definition
 *
 *   This type is used to represent Mibspi Data format selection.
 */
typedef enum mibspiDFMT
{
    DATA_FORMAT0 = 0x0U,
    DATA_FORMAT1 = 0x1U,
    DATA_FORMAT2 = 0x2U,
    DATA_FORMAT3 = 0x3U
} mibspiDFMT_t;

typedef struct mibspi_config_reg
{
    uint32 CONFIG_GCR1;
    uint32 CONFIG_INT0;
    uint32 CONFIG_LVL;
    uint32 CONFIG_PCFUN;
    uint32 CONFIG_PCDIR;
    uint32 CONFIG_PCPDR;
    uint32 CONFIG_PCDIS;
    uint32 CONFIG_PCPSL;
    uint32 CONFIG_DELAY;
    uint32 CONFIG_FMT0;
    uint32 CONFIG_FMT1;
    uint32 CONFIG_FMT2;
    uint32 CONFIG_FMT3;
    uint32 CONFIG_MIBSPIE;
    uint32 CONFIG_LTGPEND;
    uint32 CONFIG_TGCTRL[ 8U ];
    uint32 CONFIG_UERRCTRL;
} mibspi_config_reg_t;

#define MIBSPI1_GCR1_CONFIGVALUE ( 0x01000000U | ( uint32 ) ( ( uint32 ) 1U << 1U ) | 1U )
#define MIBSPI1_INT0_CONFIGVALUE                                                \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 6U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 1U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 0U ) )
#define MIBSPI1_LVL_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 4U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

#define MIBSPI1_PCFUN_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 11U ) | ( uint32 ) ( ( uint32 ) 1U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 17U ) | ( uint32 ) ( ( uint32 ) 1U << 25U ) )
#define MIBSPI1_PCDIR_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 4U ) | ( uint32 ) ( ( uint32 ) 1U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 25U ) )
#define MIBSPI1_PCPDR_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 25U ) )
#define MIBSPI1_PCDIS_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 25U ) )
#define MIBSPI1_PCPSL_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 4U ) | ( uint32 ) ( ( uint32 ) 1U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 11U ) | ( uint32 ) ( ( uint32 ) 1U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 17U ) | ( uint32 ) ( ( uint32 ) 1U << 25U ) )

#define MIBSPI1_DELAY_CONFIGVALUE                                               \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

#define MIBSPI1_FMT0_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define MIBSPI1_FMT1_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define MIBSPI1_FMT2_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define MIBSPI1_FMT3_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )

#define MIBSPI1_MIBSPIE_CONFIGVALUE 1U
#define MIBSPI1_LTGPEND_CONFIGVALUE \
    ( ( uint32 ) ( ( uint32 ) ( ( 8U + 0U + 0U + 0U + 0U + 0U + 0U + 0U ) - 1U ) << 8U ) )

#define MIBSPI1_TGCTRL0_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) 0U << 8U ) ) )
#define MIBSPI1_TGCTRL1_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) 8U << 8U ) ) )
#define MIBSPI1_TGCTRL2_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U ) << 8U ) ) )
#define MIBSPI1_TGCTRL3_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U ) << 8U ) ) )
#define MIBSPI1_TGCTRL4_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U ) << 8U ) ) )
#define MIBSPI1_TGCTRL5_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U + 0U ) << 8U ) ) )
#define MIBSPI1_TGCTRL6_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U + 0U + 0U ) << 8U ) ) )
#define MIBSPI1_TGCTRL7_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U + 0U + 0U + 0U ) << 8U ) ) )

#define MIBSPI1_UERRCTRL_CONFIGVALUE ( 0x00000005U )

#define MIBSPI3_GCR1_CONFIGVALUE     ( 0x01000000U | ( uint32 ) ( ( uint32 ) 1U << 1U ) | 1U )
#define MIBSPI3_INT0_CONFIGVALUE                                                \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 6U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 1U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 0U ) )
#define MIBSPI3_LVL_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 4U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

#define MIBSPI3_PCFUN_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 11U ) | ( uint32 ) ( ( uint32 ) 1U << 24U ) )
#define MIBSPI3_PCDIR_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 4U ) | ( uint32 ) ( ( uint32 ) 1U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) )
#define MIBSPI3_PCPDR_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) )
#define MIBSPI3_PCDIS_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) )
#define MIBSPI3_PCPSL_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 4U ) | ( uint32 ) ( ( uint32 ) 1U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 11U ) | ( uint32 ) ( ( uint32 ) 1U << 24U ) )

#define MIBSPI3_DELAY_CONFIGVALUE                                               \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

#define MIBSPI3_FMT0_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define MIBSPI3_FMT1_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define MIBSPI3_FMT2_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define MIBSPI3_FMT3_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )

#define MIBSPI3_MIBSPIE_CONFIGVALUE 1U
#define MIBSPI3_LTGPEND_CONFIGVALUE \
    ( ( uint32 ) ( ( uint32 ) ( ( 8U + 0U + 0U + 0U + 0U + 0U + 0U + 0U ) - 1U ) << 8U ) )

#define MIBSPI3_TGCTRL0_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) 0U << 8U ) ) )
#define MIBSPI3_TGCTRL1_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) 8U << 8U ) ) )
#define MIBSPI3_TGCTRL2_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U ) << 8U ) ) )
#define MIBSPI3_TGCTRL3_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U ) << 8U ) ) )
#define MIBSPI3_TGCTRL4_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U ) << 8U ) ) )
#define MIBSPI3_TGCTRL5_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U + 0U ) << 8U ) ) )
#define MIBSPI3_TGCTRL6_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U + 0U + 0U ) << 8U ) ) )
#define MIBSPI3_TGCTRL7_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U + 0U + 0U + 0U ) << 8U ) ) )

#define MIBSPI3_UERRCTRL_CONFIGVALUE ( 0x00000005U )

#define MIBSPI5_GCR1_CONFIGVALUE     ( 0x01000000U | ( uint32 ) ( ( uint32 ) 1U << 1U ) | 1U )
#define MIBSPI5_INT0_CONFIGVALUE                                                \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 6U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 1U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 0U ) )
#define MIBSPI5_LVL_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 4U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

#define MIBSPI5_PCFUN_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 11U ) | ( uint32 ) ( ( uint32 ) 1U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 17U ) | ( uint32 ) ( ( uint32 ) 1U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 19U ) | ( uint32 ) ( ( uint32 ) 1U << 25U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 26U ) | ( uint32 ) ( ( uint32 ) 1U << 27U ) )
#define MIBSPI5_PCDIR_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 19U ) | ( uint32 ) ( ( uint32 ) 0U << 25U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 26U ) | ( uint32 ) ( ( uint32 ) 0U << 27U ) )
#define MIBSPI5_PCPDR_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 19U ) | ( uint32 ) ( ( uint32 ) 0U << 25U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 26U ) | ( uint32 ) ( ( uint32 ) 0U << 27U ) )
#define MIBSPI5_PCDIS_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 19U ) | ( uint32 ) ( ( uint32 ) 0U << 25U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 26U ) | ( uint32 ) ( ( uint32 ) 0U << 27U ) )
#define MIBSPI5_PCPSL_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 1U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 11U ) | ( uint32 ) ( ( uint32 ) 1U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 17U ) | ( uint32 ) ( ( uint32 ) 1U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 19U ) | ( uint32 ) ( ( uint32 ) 1U << 25U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 26U ) | ( uint32 ) ( ( uint32 ) 1U << 27U ) )

#define MIBSPI5_DELAY_CONFIGVALUE                                               \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

#define MIBSPI5_FMT0_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define MIBSPI5_FMT1_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define MIBSPI5_FMT2_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )
#define MIBSPI5_FMT3_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 23U )    \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 21U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 17U )  \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 109U << 8U ) \
      | ( uint32 ) ( ( uint32 ) 16U << 0U ) )

#define MIBSPI5_MIBSPIE_CONFIGVALUE 1U
#define MIBSPI5_LTGPEND_CONFIGVALUE \
    ( ( uint32 ) ( ( uint32 ) ( ( 8U + 0U + 0U + 0U + 0U + 0U + 0U + 0U ) - 1U ) << 8U ) )

#define MIBSPI5_TGCTRL0_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) 0U << 8U ) ) )
#define MIBSPI5_TGCTRL1_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) 8U << 8U ) ) )
#define MIBSPI5_TGCTRL2_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U ) << 8U ) ) )
#define MIBSPI5_TGCTRL3_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U ) << 8U ) ) )
#define MIBSPI5_TGCTRL4_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U ) << 8U ) ) )
#define MIBSPI5_TGCTRL5_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U + 0U ) << 8U ) ) )
#define MIBSPI5_TGCTRL6_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U + 0U + 0U ) << 8U ) ) )
#define MIBSPI5_TGCTRL7_CONFIGVALUE                                                 \
    ( 0xFFFF7FFFU                                                                   \
      & ( ( uint32 ) ( ( uint32 ) 1U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
          | ( uint32 ) ( ( uint32 ) TRG_ALWAYS << 20U )                             \
          | ( uint32 ) ( ( uint32 ) TRG_DISABLED << 16U )                           \
          | ( uint32 ) ( ( uint32 ) ( 8U + 0U + 0U + 0U + 0U + 0U + 0U ) << 8U ) ) )

#define MIBSPI5_UERRCTRL_CONFIGVALUE ( 0x00000005U )

/**
 *  @defgroup MIBSPI MIBSPI
 *  @brief Multi-Buffered Serial Peripheral Interface Module.
 *
 *  The MibSPI/MibSPIP is a high-speed synchronous serial input/output port that allows a
 * serial bit stream of programmed length (2 to 16 bits) to be shifted in and out of the
 * device at a programmed bit-transfer rate. The MibSPI has a programmable buffer memory
 * that enables programmed transmission to be completed without CPU intervention
 *
 *    Related Files
 *   - reg_mibspi.h
 *   - mibspi.h
 *   - mibspi.c
 *  @addtogroup MIBSPI
 *  @{
 */

/* MIBSPI Interface Functions */
void mibspiInit( void );
void mibspiSetFunctional( mibspiBASE_t * mibspi, uint32 port );
void mibspiSetData( mibspiBASE_t * mibspi, uint32 group, uint16 * data );
uint32 mibspiGetData( mibspiBASE_t * mibspi, uint32 group, uint16 * data );
void mibspiTransfer( mibspiBASE_t * mibspi, uint32 group );
boolean mibspiIsTransferComplete( mibspiBASE_t * mibspi, uint32 group );
void mibspiEnableGroupNotification( mibspiBASE_t * mibspi, uint32 group, uint32 level );
void mibspiDisableGroupNotification( mibspiBASE_t * mibspi, uint32 group );
void mibspiEnableLoopback( mibspiBASE_t * mibspi, loopBackType_t Loopbacktype );
void mibspiDisableLoopback( mibspiBASE_t * mibspi );
void mibspiPmodeSet( mibspiBASE_t * mibspi, mibspiPmode_t Pmode, mibspiDFMT_t DFMT );
void mibspi1GetConfigValue( mibspi_config_reg_t * config_reg, config_value_type_t type );
void mibspi3GetConfigValue( mibspi_config_reg_t * config_reg, config_value_type_t type );
void mibspi5GetConfigValue( mibspi_config_reg_t * config_reg, config_value_type_t type );

/** @fn void mibspiNotification(mibspiBASE_t *mibspi, uint32 flags)
 *   @brief Error interrupt callback
 *   @param[in] mibspi   - mibSpi module base address
 *   @param[in] flags - Copy of error interrupt flags
 *
 * This is a error callback that is provided by the application and is call upon
 * an error interrupt.  The paramer passed to the callback is a copy of the error
 * interrupt flag register.
 */
void mibspiNotification( mibspiBASE_t * mibspi, uint32 flags );

/** @fn void mibspiGroupNotification(mibspiBASE_t *mibspi, uint32 group)
 *   @brief Transfer complete notification callback
 *   @param[in] mibspi   - mibSpi module base address
 *   @param[in] group - Transfer group
 *
 * This is a callback function provided by the application.  It is call when
 * a transfer is complete.  The parameter is the transfer group that triggered
 * the interrupt.
 */
void mibspiGroupNotification( mibspiBASE_t * mibspi, uint32 group );

/* USER CODE BEGIN (1) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif

#endif /* ifndef __MIBSPI_H__ */
