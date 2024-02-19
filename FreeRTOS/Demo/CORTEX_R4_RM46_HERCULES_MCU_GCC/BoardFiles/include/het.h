/** @file het.h
 *   @brief HET Driver Definition File
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

#ifndef __HET_H__
#define __HET_H__

#include "reg_het.h"
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/** @def pwm0
 *   @brief Pwm signal 0
 *
 *   Alias for pwm signal 0
 */
#define pwm0             0U

/** @def pwm1
 *   @brief Pwm signal 1
 *
 *   Alias for pwm signal 1
 */
#define pwm1             1U

/** @def pwm2
 *   @brief Pwm signal 2
 *
 *   Alias for pwm signal 2
 */
#define pwm2             2U

/** @def pwm3
 *   @brief Pwm signal 3
 *
 *   Alias for pwm signal 3
 */
#define pwm3             3U

/** @def pwm4
 *   @brief Pwm signal 4
 *
 *   Alias for pwm signal 4
 */
#define pwm4             4U

/** @def pwm5
 *   @brief Pwm signal 5
 *
 *   Alias for pwm signal 5
 */
#define pwm5             5U

/** @def pwm6
 *   @brief Pwm signal 6
 *
 *   Alias for pwm signal 6
 */
#define pwm6             6U

/** @def pwm7
 *   @brief Pwm signal 7
 *
 *   Alias for pwm signal 7
 */
#define pwm7             7U

/** @def edge0
 *   @brief Edge signal 0
 *
 *   Alias for edge signal 0
 */
#define edge0            0U

/** @def edge1
 *   @brief Edge signal 1
 *
 *   Alias for edge signal 1
 */
#define edge1            1U

/** @def edge2
 *   @brief Edge signal 2
 *
 *   Alias for edge signal 2
 */
#define edge2            2U

/** @def edge3
 *   @brief Edge signal 3
 *
 *   Alias for edge signal 3
 */
#define edge3            3U

/** @def edge4
 *   @brief Edge signal 4
 *
 *   Alias for edge signal 4
 */
#define edge4            4U

/** @def edge5
 *   @brief Edge signal 5
 *
 *   Alias for edge signal 5
 */
#define edge5            5U

/** @def edge6
 *   @brief Edge signal 6
 *
 *   Alias for edge signal 6
 */
#define edge6            6U

/** @def edge7
 *   @brief Edge signal 7
 *
 *   Alias for edge signal 7
 */
#define edge7            7U

/** @def cap0
 *   @brief Capture signal 0
 *
 *   Alias for capture signal 0
 */
#define cap0             0U

/** @def cap1
 *   @brief Capture signal 1
 *
 *   Alias for capture signal 1
 */
#define cap1             1U

/** @def cap2
 *   @brief Capture signal 2
 *
 *   Alias for capture signal 2
 */
#define cap2             2U

/** @def cap3
 *   @brief Capture signal 3
 *
 *   Alias for capture signal 3
 */
#define cap3             3U

/** @def cap4
 *   @brief Capture signal 4
 *
 *   Alias for capture signal 4
 */
#define cap4             4U

/** @def cap5
 *   @brief Capture signal 5
 *
 *   Alias for capture signal 5
 */
#define cap5             5U

/** @def cap6
 *   @brief Capture signal 6
 *
 *   Alias for capture signal 6
 */
#define cap6             6U

/** @def cap7
 *   @brief Capture signal 7
 *
 *   Alias for capture signal 7
 */
#define cap7             7U

/** @def pwmEND_OF_DUTY
 *   @brief Pwm end of duty
 *
 *   Alias for pwm end of duty notification
 */
#define pwmEND_OF_DUTY   2U

/** @def pwmEND_OF_PERIOD
 *   @brief Pwm end of period
 *
 *   Alias for pwm end of period notification
 */
#define pwmEND_OF_PERIOD 4U

/** @def pwmEND_OF_BOTH
 *   @brief Pwm end of duty and period
 *
 *   Alias for pwm end of duty and period notification
 */
#define pwmEND_OF_BOTH   6U

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @struct hetBase
 *   @brief HET Register Definition
 *
 *   This structure is used to access the HET module registers.
 */

/** @typedef hetBASE_t
 *   @brief HET Register Frame Type Definition
 *
 *   This type is used to access the HET Registers.
 */

enum hetPinSelect
{
    PIN_HET_0 = 0U,
    PIN_HET_1 = 1U,
    PIN_HET_2 = 2U,
    PIN_HET_3 = 3U,
    PIN_HET_4 = 4U,
    PIN_HET_5 = 5U,
    PIN_HET_6 = 6U,
    PIN_HET_7 = 7U,
    PIN_HET_8 = 8U,
    PIN_HET_9 = 9U,
    PIN_HET_10 = 10U,
    PIN_HET_11 = 11U,
    PIN_HET_12 = 12U,
    PIN_HET_13 = 13U,
    PIN_HET_14 = 14U,
    PIN_HET_15 = 15U,
    PIN_HET_16 = 16U,
    PIN_HET_17 = 17U,
    PIN_HET_18 = 18U,
    PIN_HET_19 = 19U,
    PIN_HET_20 = 20U,
    PIN_HET_21 = 21U,
    PIN_HET_22 = 22U,
    PIN_HET_23 = 23U,
    PIN_HET_24 = 24U,
    PIN_HET_25 = 25U,
    PIN_HET_26 = 26U,
    PIN_HET_27 = 27U,
    PIN_HET_28 = 28U,
    PIN_HET_29 = 29U,
    PIN_HET_30 = 30U,
    PIN_HET_31 = 31U
};

/** @struct hetSignal
 *   @brief HET Signal Definition
 *
 *   This structure is used to define a pwm signal.
 */

/** @typedef hetSIGNAL_t
 *   @brief HET Signal Type Definition
 *
 *   This type is used to access HET Signal Information.
 */
typedef struct hetSignal
{
    uint32 duty;    /**< Duty cycle in % of the period  */
    float64 period; /**< Period in us                   */
} hetSIGNAL_t;

/* Configuration registers */
typedef struct het_config_reg
{
    uint32 CONFIG_GCR;
    uint32 CONFIG_PFR;
    uint32 CONFIG_INTENAS;
    uint32 CONFIG_INTENAC;
    uint32 CONFIG_PRY;
    uint32 CONFIG_AND;
    uint32 CONFIG_HRSH;
    uint32 CONFIG_XOR;
    uint32 CONFIG_DIR;
    uint32 CONFIG_PDR;
    uint32 CONFIG_PULDIS;
    uint32 CONFIG_PSL;
    uint32 CONFIG_PCR;
} het_config_reg_t;

/* Configuration registers initial value for HET1*/
#define HET1_DIR_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET1_PDR_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET1_PULDIS_CONFIGVALUE                                                  \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET1_PSL_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET1_HRSH_CONFIGVALUE                                                    \
    ( ( uint32 ) 0x00008000U | ( uint32 ) 0x00004000U | ( uint32 ) 0x00002000U   \
      | ( uint32 ) 0x00001000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000008U | ( uint32 ) 0x00000004U | ( uint32 ) 0x00000002U \
      | ( uint32 ) 0x00000001U )

#define HET1_AND_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U )

#define HET1_XOR_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U )

#define HET1_PFR_CONFIGVALUE ( ( ( uint32 ) 7U << 8U ) | ( uint32 ) 0U )

#define HET1_PRY_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET1_INTENAC_CONFIGVALUE                                                 \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET1_INTENAS_CONFIGVALUE                                                 \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET1_PCR_CONFIGVALUE ( ( uint32 ) 0x00000005U )
#define HET1_GCR_CONFIGVALUE 0x00030001U

/* Configuration registers initial value for HET2*/
#define HET2_DIR_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U )

#define HET2_PDR_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U )

#define HET2_PULDIS_CONFIGVALUE                                                  \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U )

#define HET2_PSL_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U )

#define HET2_HRSH_CONFIGVALUE                                                    \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000008U \
      | ( uint32 ) 0x00000004U | ( uint32 ) 0x00000002U | ( uint32 ) 0x00000001U )

#define HET2_AND_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET2_XOR_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET2_PFR_CONFIGVALUE ( ( ( uint32 ) 7U << 8U ) | ( uint32 ) 0U )

#define HET2_PRY_CONFIGVALUE                                                     \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET2_INTENAC_CONFIGVALUE                                                 \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET2_INTENAS_CONFIGVALUE                                                 \
    ( ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U   \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U \
      | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U | ( uint32 ) 0x00000000U )

#define HET2_PCR_CONFIGVALUE ( ( uint32 ) 0x00000005U )
#define HET2_GCR_CONFIGVALUE 0x00030001U

/**
 *  @defgroup HET HET
 *  @brief HighEnd Timer Module.
 *
 *  The HET is a software-controlled timer with a dedicated specialized timer micromachine
 *and a set of 30 instructions. The HET micromachine is connected to a port of up to 32
 *input/output (I/O) pins.
 *
 *	Related Files
 *   - reg_het.h
 *   - het.h
 *   - het.c
 *   - reg_htu.h
 *   - htu.h
 *   - std_nhet.h
 *  @addtogroup HET
 *  @{
 */

/* HET Interface Functions */
void hetInit( void );

/* PWM Interface Functions */
void pwmStart( hetRAMBASE_t * hetRAM, uint32 pwm );
void pwmStop( hetRAMBASE_t * hetRAM, uint32 pwm );
void pwmSetDuty( hetRAMBASE_t * hetRAM, uint32 pwm, uint32 pwmDuty );
void pwmSetSignal( hetRAMBASE_t * hetRAM, uint32 pwm, hetSIGNAL_t signal );
void pwmGetSignal( hetRAMBASE_t * hetRAM, uint32 pwm, hetSIGNAL_t * signal );
void pwmEnableNotification( hetBASE_t * hetREG, uint32 pwm, uint32 notification );
void pwmDisableNotification( hetBASE_t * hetREG, uint32 pwm, uint32 notification );
void pwmNotification( hetBASE_t * hetREG, uint32 pwm, uint32 notification );

/* Edge Interface Functions */
void edgeResetCounter( hetRAMBASE_t * hetRAM, uint32 edge );
uint32 edgeGetCounter( hetRAMBASE_t * hetRAM, uint32 edge );
void edgeEnableNotification( hetBASE_t * hetREG, uint32 edge );
void edgeDisableNotification( hetBASE_t * hetREG, uint32 edge );
void edgeNotification( hetBASE_t * hetREG, uint32 edge );

/* Captured Signal Interface Functions */
void capGetSignal( hetRAMBASE_t * hetRAM, uint32 cap, hetSIGNAL_t * signal );

/* Timestamp Interface Functions */
void hetResetTimestamp( hetRAMBASE_t * hetRAM );
uint32 hetGetTimestamp( hetRAMBASE_t * hetRAM );
void het1GetConfigValue( het_config_reg_t * config_reg, config_value_type_t type );
void het2GetConfigValue( het_config_reg_t * config_reg, config_value_type_t type );

/** @fn void hetNotification(hetBASE_t *het, uint32 offset)
 *   @brief het interrupt callback
 *   @param[in] het - Het module base address
 *              - hetREG1: HET1 module base address pointer
 *              - hetREG2: HET2 module base address pointer
 *   @param[in] offset - het interrupt offset / Source number
 *
 *   @note This function has to be provide by the user.
 *
 * This is a interrupt callback that is provided by the application and is call upon
 * an het interrupt.  The parameter passed to the callback is a copy of the interrupt
 * offset register which is used to decode the interrupt source.
 */
void hetNotification( hetBASE_t * het, uint32 offset );

/* USER CODE BEGIN (2) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif /*extern "C" */

#endif /* ifndef __HET_H__ */
