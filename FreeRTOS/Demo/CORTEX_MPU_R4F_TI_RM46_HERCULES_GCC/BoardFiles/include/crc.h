/** @file CRC.h
 *   @brief CRC Driver Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
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

#ifndef __CRC_H__
#define __CRC_H__

#include "reg_crc.h"

#ifdef __cplusplus
extern "C" {
#endif
/* USER CODE BEGIN (0) */
/* USER CODE END */

/* CRC General Definitions */

/** @def CRCLEVEL_ACTIVE
 *   @brief Alias name for CRC error operation level active
 */
#define CRCLEVEL_ACTIVE 0x00U

/** @def CRC_AUTO
 *   @brief Alias name for CRC auto mode
 */
#define CRC_AUTO        0x00000001U

/** @def CRC_SEMI_CPU
 *   @brief Alias name for semi cpu mode setting
 */
#define CRC_SEMI_CPU    0x00000002U

/** @def CRC_FULL_CPU
 *   @brief Alias name for CRC cpu full mode
 */
#define CRC_FULL_CPU    0x00000003U

/** @def CRC_CH4_TO
 *   @brief Alias name for channel4 time out interrupt flag
 */
#define CRC_CH4_TO      0x10000000U

/** @def CRC_CH4_UR
 *   @brief Alias name for channel4 underrun interrupt flag
 */
#define CRC_CH4_UR      0x08000000U

/** @def CRC_CH4_OR
 *   @brief Alias name for channel4 overrun interrupt flag
 */
#define CRC_CH4_OR      0x04000000U

/** @def CRC_CH4_FAIL
 *   @brief Alias name for channel4 crc fail interrupt flag
 */
#define CRC_CH4_FAIL    0x02000000U

/** @def CRC_CH4_CC
 *   @brief Alias name for channel4 compression complete interrupt flag
 */
#define CRC_CH4_CC      0x01000000U

/** @def CRC_CH3_TO
 *   @brief Alias name for channel3 time out interrupt flag
 */
#define CRC_CH3_TO      0x00100000U

/** @def CRC_CH3_UR
 *   @brief Alias name for channel3 underrun interrupt flag
 */
#define CRC_CH3_UR      0x00080000U

/** @def CRC_CH3_OR
 *   @brief Alias name for channel3 overrun interrupt flag
 */
#define CRC_CH3_OR      0x00040000U

/** @def CRC_CH3_FAIL
 *   @brief Alias name for channel3 crc fail interrupt flag
 */
#define CRC_CH3_FAIL    0x00020000U

/** @def CRC_CH3_CC
 *   @brief Alias name for channel3 compression complete interrupt flag
 */
#define CRC_CH3_CC      0x00010000U

/** @def CRC_CH2_TO
 *   @brief Alias name for channel2 time out interrupt flag
 */
#define CRC_CH2_TO      0x00001000U

/** @def CRC_CH2_UR
 *   @brief Alias name for channel2 underrun interrupt flag
 */
#define CRC_CH2_UR      0x00000800U

/** @def CRC_CH2_OR
 *   @brief Alias name for channel2 overrun interrupt flag
 */
#define CRC_CH2_OR      0x00000400U

/** @def CRC_CH2_FAIL
 *   @brief Alias name for channel2 crc fail interrupt flag
 */
#define CRC_CH2_FAIL    0x00000200U

/** @def CRC_CH2_CC
 *   @brief Alias name for channel2 compression complete interrupt flag
 */
#define CRC_CH2_CC      0x00000100U

/** @def CRC_CH1_TO
 *   @brief Alias name for channel1 time out interrupt flag
 */
#define CRC_CH1_TO      0x00000010U

/** @def CRC_CH1_UR
 *   @brief Alias name for channel1 underrun interrupt flag
 */
#define CRC_CH1_UR      0x00000008U

/** @def CRC_CH1_OR
 *   @brief Alias name for channel1 overrun interrupt flag
 */
#define CRC_CH1_OR      0x00000004U

/** @def CRC_CH1_FAIL
 *   @brief Alias name for channel1 crc fail interrupt flag
 */
#define CRC_CH1_FAIL    0x00000002U

/** @def CRC_CH1_CC
 *   @brief Alias name for channel1 compression complete interrupt flag
 */
#define CRC_CH1_CC      0x00000001U

/** @def CRC_CH1
 *   @brief Alias name for channel1
 */
#define CRC_CH1         0x00000000U

/** @def CRC_CH1
 *   @brief Alias name for channel2
 */
#define CRC_CH2         0x00000001U

/** @def CRC_CH3
 *   @brief Alias name for channel3
 */
#define CRC_CH3         0x00000002U

/** @def CRC_CH4
 *   @brief Alias name for channel4
 */
#define CRC_CH4         0x00000003U

/** @struct crcModConfig
 *   @brief CRC mode specific parameters
 *
 *   This type is used to pass crc mode specific parameters
 */

/** @typedef crcModConfig_t
 *   @brief CRC Data Type Definition
 */
typedef struct crcModConfig
{
    uint32 mode;           /**< Mode of operation        */
    uint32 crc_channel;    /**< CRC channel-0,1       */
    uint64 * src_data_pat; /**< Pattern data */
    uint32 data_length;    /**< Pattern data length.Number of 64 bit size word*/
} crcModConfig_t;

/** @struct crcConfig
 *   @brief CRC configuration for different modes
 *
 *   This type is used to pass crc configuration
 */

/** @typedef crcConfig_t
 *   @brief CRC Data Type Definition
 */
typedef struct crcConfig
{
    uint32 crc_channel;   /**< CRC channel-0,1         */
    uint32 mode;          /**< Mode of operation        */
    uint32 pcount;        /**< Pattern count*/
    uint32 scount;        /**< Sector count  */
    uint32 wdg_preload;   /**< Watchdog period */
    uint32 block_preload; /**< Block period*/
} crcConfig_t;

/* USER CODE BEGIN (1) */
/* USER CODE END */

typedef struct crc_config_reg
{
    uint32 CONFIG_CTRL0;
    uint32 CONFIG_CTRL1;
    uint32 CONFIG_CTRL2;
    uint32 CONFIG_INTS;
    uint32 CONFIG_PCOUNT_REG1;
    uint32 CONFIG_SCOUNT_REG1;
    uint32 CONFIG_WDTOPLD1;
    uint32 CONFIG_BCTOPLD1;
    uint32 CONFIG_PCOUNT_REG2;
    uint32 CONFIG_SCOUNT_REG2;
    uint32 CONFIG_WDTOPLD2;
    uint32 CONFIG_BCTOPLD2;
} crc_config_reg_t;

#define CRC_CTRL0_CONFIGVALUE 0x00000000U
#define CRC_CTRL1_CONFIGVALUE 0x00000000U
#define CRC_CTRL2_CONFIGVALUE                                          \
    ( ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( CRC_FULL_CPU ) \
      | ( uint32 ) ( ( uint32 ) CRC_FULL_CPU << 8U ) )
#define CRC_INTS_CONFIGVALUE                                                            \
    ( 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U \
      | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U )
#define CRC_PCOUNT_REG1_CONFIGVALUE ( 0x00000000U )
#define CRC_SCOUNT_REG1_CONFIGVALUE ( 0x00000000U )
#define CRC_WDTOPLD1_CONFIGVALUE    ( 0x00000000U )
#define CRC_BCTOPLD1_CONFIGVALUE    ( 0x00000000U )
#define CRC_PCOUNT_REG2_CONFIGVALUE ( 0x00000000U )
#define CRC_SCOUNT_REG2_CONFIGVALUE ( 0x00000000U )
#define CRC_WDTOPLD2_CONFIGVALUE    ( 0x00000000U )
#define CRC_BCTOPLD2_CONFIGVALUE    ( 0x00000000U )

/**
 *  @defgroup CRC CRC
 *  @brief Cyclic Redundancy Check Controller Module.
 *
 *  The CRC controller is a module that is used to perform CRC (Cyclic Redundancy Check)
 *to verify the integrity of memory system. A signature representing the contents of the
 *memory is obtained when the contents of the memory are read into CRC controller. The
 *responsibility of CRC controller is to calculate the signature for a set of data and
 *then compare the calculated signature value against a pre-determined good signature
 *value. CRC controller supports two channels to perform CRC calculation on multiple
 *  memories in parallel and can be used on any memory system.
 *
 *	Related Files
 *   - reg_crc.h
 *   - crc.h
 *   - crc.c
 *  @addtogroup CRC
 *  @{
 */

/* CRC Interface Functions */
void crcInit( void );
void crcSendPowerDown( crcBASE_t * crc );
void crcSignGen( crcBASE_t * crc, crcModConfig_t * param );
void crcSetConfig( crcBASE_t * crc, crcConfig_t * param );
uint64 crcGetPSASig( crcBASE_t * crc, uint32 channel );
uint64 crcGetSectorSig( crcBASE_t * crc, uint32 channel );
uint32 crcGetFailedSector( crcBASE_t * crc, uint32 channel );
uint32 crcGetIntrPend( crcBASE_t * crc, uint32 channel );
void crcChannelReset( crcBASE_t * crc, uint32 channel );
void crcEnableNotification( crcBASE_t * crc, uint32 flags );
void crcDisableNotification( crcBASE_t * crc, uint32 flags );
void crcGetConfigValue( crc_config_reg_t * config_reg, config_value_type_t type );

/** @fn void crcNotification(crcBASE_t *crc, uint32 flags)
 *   @brief Interrupt callback
 *   @param[in] crc   - crc module base address
 *   @param[in] flags - copy of error interrupt flags
 *
 * This is a callback that is provided by the application and is called upon
 * an interrupt.  The parameter passed to the callback is a copy of the
 * interrupt flag register.
 */
void crcNotification( crcBASE_t * crc, uint32 flags );

/* USER CODE BEGIN (2) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif /*extern "C" */

#endif /* ifndef __CRC_H__ */
