/** @file esm.h
 *   @brief Error Signaling Module Driver Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   .
 *   which are relevant for the Esm driver.
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

#ifndef __ESM_H__
#define __ESM_H__

#include "reg_esm.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* ESM General Definitions */

/** @def esmGROUP1
 *   @brief Alias name for ESM group 1
 *
 *   This is an alias name for the ESM group 1.
 *
 *   @note This value should be used for API argument @a group
 */
#define esmGROUP1    0U

/** @def esmGROUP2
 *   @brief Alias name for ESM group 2
 *
 *   This is an alias name for the ESM group 2.
 *
 *   @note This value should be used for API argument @a group
 */
#define esmGROUP2    1U

/** @def esmGROUP3
 *   @brief Alias name for ESM group 3
 *
 *   This is an alias name for the ESM group 3.
 *
 *   @note This value should be used for API argument @a group
 */
#define esmGROUP3    2U

/** @def esmCHANNEL0
 *   @brief Alias name for ESM group x channel 0
 *
 *   This is an alias name for the ESM group x channel 0.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL0  0x0000000000000001ULL

/** @def esmCHANNEL1
 *   @brief Alias name for ESM group x channel 1
 *
 *   This is an alias name for the ESM group x channel 1.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL1  0x0000000000000002ULL

/** @def esmCHANNEL2
 *   @brief Alias name for ESM group x channel 2
 *
 *   This is an alias name for the ESM group x channel 2.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL2  0x0000000000000004ULL

/** @def esmCHANNEL3
 *   @brief Alias name for ESM group x channel 3
 *
 *   This is an alias name for the ESM group x channel 3.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL3  0x0000000000000008ULL

/** @def esmCHANNEL4
 *   @brief Alias name for ESM group x channel 4
 *
 *   This is an alias name for the ESM group x channel 4.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL4  0x0000000000000010ULL

/** @def esmCHANNEL5
 *   @brief Alias name for ESM group x channel 5
 *
 *   This is an alias name for the ESM group x channel 5.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL5  0x0000000000000020ULL

/** @def esmCHANNEL6
 *   @brief Alias name for ESM group x channel 6
 *
 *   This is an alias name for the ESM group x channel 6.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL6  0x0000000000000040ULL

/** @def esmCHANNEL7
 *   @brief Alias name for ESM group x channel 7
 *
 *   This is an alias name for the ESM group x channel 7.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL7  0x0000000000000080ULL

/** @def esmCHANNEL8
 *   @brief Alias name for ESM group x channel 8
 *
 *   This is an alias name for the ESM group x channel 8.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL8  0x0000000000000100ULL

/** @def esmCHANNEL9
 *   @brief Alias name for ESM group x channel 9
 *
 *   This is an alias name for the ESM group x channel 9.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL9  0x0000000000000200ULL

/** @def esmCHANNEL10
 *   @brief Alias name for ESM group x channel 10
 *
 *   This is an alias name for the ESM group x channel 10.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL10 0x0000000000000400ULL

/** @def esmCHANNEL11
 *   @brief Alias name for ESM group x channel 11
 *
 *   This is an alias name for the ESM group x channel 11.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL11 0x0000000000000800ULL

/** @def esmCHANNEL12
 *   @brief Alias name for ESM group x channel 12
 *
 *   This is an alias name for the ESM group x channel 12.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL12 0x0000000000001000ULL

/** @def esmCHANNEL13
 *   @brief Alias name for ESM group x channel 13
 *
 *   This is an alias name for the ESM group x channel 13.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL13 0x0000000000002000ULL

/** @def esmCHANNEL14
 *   @brief Alias name for ESM group x channel 14
 *
 *   This is an alias name for the ESM group x channel 14.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL14 0x0000000000004000ULL

/** @def esmCHANNEL15
 *   @brief Alias name for ESM group x channel 15
 *
 *   This is an alias name for the ESM group x channel 15.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL15 0x0000000000008000ULL

/** @def esmCHANNEL16
 *   @brief Alias name for ESM group x channel 16
 *
 *   This is an alias name for the ESM group x channel 16.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL16 0x0000000000010000ULL

/** @def esmCHANNEL17
 *   @brief Alias name for ESM group x channel 17
 *
 *   This is an alias name for the ESM group x channel 17.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL17 0x0000000000020000ULL

/** @def esmCHANNEL18
 *   @brief Alias name for ESM group x channel 18
 *
 *   This is an alias name for the ESM group x channel 18.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL18 0x0000000000040000ULL

/** @def esmCHANNEL19
 *   @brief Alias name for ESM group x channel 19
 *
 *   This is an alias name for the ESM group x channel 19.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL19 0x0000000000080000ULL

/** @def esmCHANNEL20
 *   @brief Alias name for ESM group x channel 20
 *
 *   This is an alias name for the ESM group x channel 20.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL20 0x0000000000100000ULL

/** @def esmCHANNEL21
 *   @brief Alias name for ESM group x channel 21
 *
 *   This is an alias name for the ESM group x channel 21.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL21 0x0000000000200000ULL

/** @def esmCHANNEL22
 *   @brief Alias name for ESM group x channel 22
 *
 *   This is an alias name for the ESM group x channel 22.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL22 0x0000000000400000ULL

/** @def esmCHANNEL23
 *   @brief Alias name for ESM group x channel 23
 *
 *   This is an alias name for the ESM group x channel 23.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL23 0x0000000000800000ULL

/** @def esmCHANNEL24
 *   @brief Alias name for ESM group x channel 24
 *
 *   This is an alias name for the ESM group x channel 24.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL24 0x0000000001000000ULL

/** @def esmCHANNEL25
 *   @brief Alias name for ESM group x channel 25
 *
 *   This is an alias name for the ESM group x channel 25.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL25 0x0000000002000000ULL

/** @def esmCHANNEL26
 *   @brief Alias name for ESM group x channel 26
 *
 *   This is an alias name for the ESM group x channel 26.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL26 0x0000000004000000ULL

/** @def esmCHANNEL27
 *   @brief Alias name for ESM group x channel 27
 *
 *   This is an alias name for the ESM group x channel 27.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL27 0x0000000008000000ULL

/** @def esmCHANNEL28
 *   @brief Alias name for ESM group x channel 28
 *
 *   This is an alias name for the ESM group x channel 28.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL28 0x0000000010000000ULL

/** @def esmCHANNEL29
 *   @brief Alias name for ESM group x channel 29
 *
 *   This is an alias name for the ESM group x channel 29.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL29 0x0000000020000000ULL

/** @def esmCHANNEL30
 *   @brief Alias name for ESM group x channel 30
 *
 *   This is an alias name for the ESM group x channel 30.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL30 0x0000000040000000ULL

/** @def esmCHANNEL31
 *   @brief Alias name for ESM group x channel 31
 *
 *   This is an alias name for the ESM group x channel 31.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL31 0x0000000080000000ULL

/** @def esmCHANNEL32
 *   @brief Alias name for ESM group x channel 32
 *
 *   This is an alias name for the ESM group x channel 32.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL32 0x0000000100000000ULL

/** @def esmCHANNEL33
 *   @brief Alias name for ESM group x channel 33
 *
 *   This is an alias name for the ESM group x channel 33.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL33 0x0000000200000000ULL

/** @def esmCHANNEL34
 *   @brief Alias name for ESM group x channel 34
 *
 *   This is an alias name for the ESM group x channel 34.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL34 0x0000000400000000ULL

/** @def esmCHANNEL35
 *   @brief Alias name for ESM group x channel 35
 *
 *   This is an alias name for the ESM group x channel 35.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL35 0x0000000800000000ULL

/** @def esmCHANNEL36
 *   @brief Alias name for ESM group x channel 36
 *
 *   This is an alias name for the ESM group x channel 36.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL36 0x0000001000000000ULL

/** @def esmCHANNEL37
 *   @brief Alias name for ESM group x channel 37
 *
 *   This is an alias name for the ESM group x channel 37.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL37 0x0000002000000000ULL

/** @def esmCHANNEL38
 *   @brief Alias name for ESM group x channel 38
 *
 *   This is an alias name for the ESM group x channel 38.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL38 0x0000004000000000ULL

/** @def esmCHANNEL39
 *   @brief Alias name for ESM group x channel 39
 *
 *   This is an alias name for the ESM group x channel 39.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL39 0x0000008000000000ULL

/** @def esmCHANNEL40
 *   @brief Alias name for ESM group x channel 40
 *
 *   This is an alias name for the ESM group x channel 40.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL40 0x0000010000000000ULL

/** @def esmCHANNEL41
 *   @brief Alias name for ESM group x channel 41
 *
 *   This is an alias name for the ESM group x channel 41.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL41 0x0000020000000000ULL

/** @def esmCHANNEL42
 *   @brief Alias name for ESM group x channel 42
 *
 *   This is an alias name for the ESM group x channel 42.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL42 0x0000040000000000ULL

/** @def esmCHANNEL43
 *   @brief Alias name for ESM group x channel 43
 *
 *   This is an alias name for the ESM group x channel 43.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL43 0x0000080000000000ULL

/** @def esmCHANNEL44
 *   @brief Alias name for ESM group x channel 44
 *
 *   This is an alias name for the ESM group x channel 44.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL44 0x0000100000000000ULL

/** @def esmCHANNEL45
 *   @brief Alias name for ESM group x channel 45
 *
 *   This is an alias name for the ESM group x channel 45.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL45 0x0000200000000000ULL

/** @def esmCHANNEL46
 *   @brief Alias name for ESM group x channel 46
 *
 *   This is an alias name for the ESM group x channel 46.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL46 0x0000400000000000ULL

/** @def esmCHANNEL47
 *   @brief Alias name for ESM group x channel 47
 *
 *   This is an alias name for the ESM group x channel 47.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL47 0x0000800000000000ULL

/** @def esmCHANNEL48
 *   @brief Alias name for ESM group x channel 48
 *
 *   This is an alias name for the ESM group x channel 48.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL48 0x0001000000000000ULL

/** @def esmCHANNEL49
 *   @brief Alias name for ESM group x channel 49
 *
 *   This is an alias name for the ESM group x channel 49.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL49 0x0002000000000000ULL

/** @def esmCHANNEL50
 *   @brief Alias name for ESM group x channel 50
 *
 *   This is an alias name for the ESM group x channel 50.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL50 0x0004000000000000ULL

/** @def esmCHANNEL51
 *   @brief Alias name for ESM group x channel 51
 *
 *   This is an alias name for the ESM group x channel 51.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL51 0x0008000000000000ULL

/** @def esmCHANNEL52
 *   @brief Alias name for ESM group x channel 52
 *
 *   This is an alias name for the ESM group x channel 52.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL52 0x0010000000000000ULL

/** @def esmCHANNEL53
 *   @brief Alias name for ESM group x channel 53
 *
 *   This is an alias name for the ESM group x channel 53.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL53 0x0020000000000000ULL

/** @def esmCHANNEL54
 *   @brief Alias name for ESM group x channel 54
 *
 *   This is an alias name for the ESM group x channel 54.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL54 0x0040000000000000ULL

/** @def esmCHANNEL55
 *   @brief Alias name for ESM group x channel 55
 *
 *   This is an alias name for the ESM group x channel 55.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL55 0x0080000000000000ULL

/** @def esmCHANNEL56
 *   @brief Alias name for ESM group x channel 56
 *
 *   This is an alias name for the ESM group x channel 56.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL56 0x0100000000000000ULL

/** @def esmCHANNEL57
 *   @brief Alias name for ESM group x channel 57
 *
 *   This is an alias name for the ESM group x channel 57.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL57 0x0200000000000000ULL

/** @def esmCHANNEL58
 *   @brief Alias name for ESM group x channel 58
 *
 *   This is an alias name for the ESM group x channel 58.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL58 0x0400000000000000ULL

/** @def esmCHANNEL59
 *   @brief Alias name for ESM group x channel 59
 *
 *   This is an alias name for the ESM group x channel 59.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL59 0x0800000000000000ULL

/** @def esmCHANNEL60
 *   @brief Alias name for ESM group x channel 60
 *
 *   This is an alias name for the ESM group x channel 60.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL60 0x1000000000000000ULL

/** @def esmCHANNEL61
 *   @brief Alias name for ESM group x channel 61
 *
 *   This is an alias name for the ESM group x channel 61.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL61 0x2000000000000000ULL

/** @def esmCHANNEL62
 *   @brief Alias name for ESM group x channel 62
 *
 *   This is an alias name for the ESM group x channel 62.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL62 0x4000000000000000ULL

/** @def esmCHANNEL63
 *   @brief Alias name for ESM group x channel 63
 *
 *   This is an alias name for the ESM group x channel 63.
 *
 *   @note This value should be used for API argument @a channel
 */
#define esmCHANNEL63 0x8000000000000000ULL

/** @typedef esmSelfTestFlag_t
 *   @brief ESM Self-Test Status Type Definition
 *
 *   This type is used to represent ESM Self-Test Status.
 */
typedef enum esmSelfTestFlag
{
    esmSelfTest_Passed = 0U,
    esmSelfTest_Active = 1U,
    esmSelfTest_NotStarted = 2U,
    esmSelfTest_Failed = 3U
} esmSelfTestFlag_t;

/* Configuration registers */
typedef struct esm_config_reg
{
    uint32 CONFIG_EEPAPR1;
    uint32 CONFIG_IESR1;
    uint32 CONFIG_ILSR1;
    uint32 CONFIG_LTCPR;
    uint32 CONFIG_EKR;
    uint32 CONFIG_IEPSR4;
    uint32 CONFIG_IESR4;
    uint32 CONFIG_ILSR4;
} esm_config_reg_t;

/* Configuration registers initial value */
#define ESM_EEPAPR1_CONFIGVALUE                                                   \
    ( ( uint32 ) ( ( uint32 ) 0U << 31U ) | ( uint32 ) ( ( uint32 ) 0U << 30U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 29U ) | ( uint32 ) ( ( uint32 ) 0U << 28U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 27U ) | ( uint32 ) ( ( uint32 ) 0U << 26U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 25U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 23U ) | ( uint32 ) ( ( uint32 ) 0U << 22U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 21U ) | ( uint32 ) ( ( uint32 ) 0U << 20U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 19U ) | ( uint32 ) ( ( uint32 ) 0U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 15U ) | ( uint32 ) ( ( uint32 ) 0U << 14U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 13U ) | ( uint32 ) ( ( uint32 ) 0U << 12U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 10U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 7U ) | ( uint32 ) ( ( uint32 ) 0U << 6U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 5U ) | ( uint32 ) ( ( uint32 ) 0U << 4U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )
#define ESM_IESR1_CONFIGVALUE                                                     \
    ( ( uint32 ) ( ( uint32 ) 0U << 31U ) | ( uint32 ) ( ( uint32 ) 0U << 30U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 29U ) | ( uint32 ) ( ( uint32 ) 0U << 28U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 27U ) | ( uint32 ) ( ( uint32 ) 0U << 26U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 25U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 23U ) | ( uint32 ) ( ( uint32 ) 0U << 22U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 21U ) | ( uint32 ) ( ( uint32 ) 0U << 20U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 19U ) | ( uint32 ) ( ( uint32 ) 0U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 15U ) | ( uint32 ) ( ( uint32 ) 0U << 14U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 13U ) | ( uint32 ) ( ( uint32 ) 0U << 12U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 10U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 7U ) | ( uint32 ) ( ( uint32 ) 0U << 6U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 5U ) | ( uint32 ) ( ( uint32 ) 0U << 4U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )
#define ESM_ILSR1_CONFIGVALUE                                                     \
    ( ( uint32 ) ( ( uint32 ) 0U << 31U ) | ( uint32 ) ( ( uint32 ) 0U << 30U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 29U ) | ( uint32 ) ( ( uint32 ) 0U << 28U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 27U ) | ( uint32 ) ( ( uint32 ) 0U << 26U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 25U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 23U ) | ( uint32 ) ( ( uint32 ) 0U << 22U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 21U ) | ( uint32 ) ( ( uint32 ) 0U << 20U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 19U ) | ( uint32 ) ( ( uint32 ) 0U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 15U ) | ( uint32 ) ( ( uint32 ) 0U << 14U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 13U ) | ( uint32 ) ( ( uint32 ) 0U << 12U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 10U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 7U ) | ( uint32 ) ( ( uint32 ) 0U << 6U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 5U ) | ( uint32 ) ( ( uint32 ) 0U << 4U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )
#define ESM_LTCPR_CONFIGVALUE ( 16384U - 1U )
#define ESM_EKR_CONFIGVALUE   0U
#define ESM_IEPSR4_CONFIGVALUE                                                    \
    ( ( uint32 ) ( ( uint32 ) 0U << 31U ) | ( uint32 ) ( ( uint32 ) 0U << 30U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 29U ) | ( uint32 ) ( ( uint32 ) 0U << 28U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 27U ) | ( uint32 ) ( ( uint32 ) 0U << 26U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 25U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 23U ) | ( uint32 ) ( ( uint32 ) 0U << 22U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 21U ) | ( uint32 ) ( ( uint32 ) 0U << 20U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 19U ) | ( uint32 ) ( ( uint32 ) 0U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 15U ) | ( uint32 ) ( ( uint32 ) 0U << 14U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 13U ) | ( uint32 ) ( ( uint32 ) 0U << 12U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 10U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 7U ) | ( uint32 ) ( ( uint32 ) 0U << 6U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 5U ) | ( uint32 ) ( ( uint32 ) 0U << 4U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )
#define ESM_IESR4_CONFIGVALUE                                                     \
    ( ( uint32 ) ( ( uint32 ) 0U << 31U ) | ( uint32 ) ( ( uint32 ) 0U << 30U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 29U ) | ( uint32 ) ( ( uint32 ) 0U << 28U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 27U ) | ( uint32 ) ( ( uint32 ) 0U << 26U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 25U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 23U ) | ( uint32 ) ( ( uint32 ) 0U << 22U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 21U ) | ( uint32 ) ( ( uint32 ) 0U << 20U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 19U ) | ( uint32 ) ( ( uint32 ) 0U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 15U ) | ( uint32 ) ( ( uint32 ) 0U << 14U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 13U ) | ( uint32 ) ( ( uint32 ) 0U << 12U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 10U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 7U ) | ( uint32 ) ( ( uint32 ) 0U << 6U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 5U ) | ( uint32 ) ( ( uint32 ) 0U << 4U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )
#define ESM_ILSR4_CONFIGVALUE                                                     \
    ( ( uint32 ) ( ( uint32 ) 0U << 31U ) | ( uint32 ) ( ( uint32 ) 0U << 30U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 29U ) | ( uint32 ) ( ( uint32 ) 0U << 28U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 27U ) | ( uint32 ) ( ( uint32 ) 0U << 26U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 25U ) | ( uint32 ) ( ( uint32 ) 0U << 24U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 23U ) | ( uint32 ) ( ( uint32 ) 0U << 22U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 21U ) | ( uint32 ) ( ( uint32 ) 0U << 20U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 19U ) | ( uint32 ) ( ( uint32 ) 0U << 18U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 17U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 15U ) | ( uint32 ) ( ( uint32 ) 0U << 14U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 13U ) | ( uint32 ) ( ( uint32 ) 0U << 12U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 11U ) | ( uint32 ) ( ( uint32 ) 0U << 10U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 9U ) | ( uint32 ) ( ( uint32 ) 0U << 8U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 7U ) | ( uint32 ) ( ( uint32 ) 0U << 6U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 5U ) | ( uint32 ) ( ( uint32 ) 0U << 4U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 3U ) | ( uint32 ) ( ( uint32 ) 0U << 2U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 1U ) | ( uint32 ) ( ( uint32 ) 0U << 0U ) )

/* USER CODE BEGIN (1) */
/* USER CODE END */

/**
 *  @defgroup ESM ESM
 *  @brief Error Signaling Module.
 *
 *  The ESM module aggregates device errors and provides internal and external error
 *response based on error severity.
 *
 *	Related Files
 *   - reg_esm.h
 *   - esm.h
 *   - esm.c
 *  @addtogroup ESM
 *  @{
 */

/* Esm Interface Functions */
void esmInit( void );
uint32 esmError( void );
void esmEnableError( uint64 channels );
void esmDisableError( uint64 channels );
void esmTriggerErrorPinReset( void );
void esmActivateNormalOperation( void );
void esmEnableInterrupt( uint64 channels );
void esmDisableInterrupt( uint64 channels );
void esmSetInterruptLevel( uint64 channels, uint64 flags );
void esmClearStatus( uint32 group, uint64 channels );
void esmClearStatusBuffer( uint64 channels );
void esmSetCounterPreloadValue( uint32 value );

uint64 esmGetStatus( uint32 group, uint64 channels );
uint64 esmGetStatusBuffer( uint64 channels );

esmSelfTestFlag_t esmEnterSelfTest( void );
esmSelfTestFlag_t esmSelfTestStatus( void );

void esmGetConfigValue( esm_config_reg_t * config_reg, config_value_type_t type );

/** @fn void esmGroup1Notification(uint32 channel)
 *   @brief Interrupt callback
 *   @param[in] channel - Group 1 channel
 *
 *   This is a callback that is provided by the application and is called upon
 *   an interrupt. The parameter passed to the callback is group 1 channel caused the
 * interrupt.
 *   @note Callback parameter channel is not a masked value. Do not use the macros
 * esmCHANNELx for comparison.
 */
void esmGroup1Notification( uint32 channel );

/** @fn void esmGroup2Notification(uint32 channel)
 *   @brief Interrupt callback
 *   @param[in] channel - Group 2 channel
 *
 *   This is a callback that is provided by the application and is called upon
 *   an interrupt. The parameter passed to the callback is group 2 channel caused the
 * interrupt.
 *   @note Callback parameter channel is not a masked value. Do not use the macros
 * esmCHANNELx for comparison.
 */
void esmGroup2Notification( uint32 channel );

/**@}*/
/* USER CODE BEGIN (2) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif /*extern "C" */

#endif /* ifndef __ESM_H__ */
