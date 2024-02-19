/** @file rtp.h
 *   @brief RTP Driver Definition File
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

#ifndef __RTP_H__
#define __RTP_H__

#include "reg_rtp.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* Configuration registers */
typedef struct rtp_config_reg
{
    uint32 CONFIG_PC0;
    uint32 CONFIG_PC1;
    uint32 CONFIG_PC3;
    uint32 CONFIG_PC6;
    uint32 CONFIG_PC7;
    uint32 CONFIG_PC8;
} rtp_config_reg_t;

#define RTP_PC3_CONFIGVALUE                                                       \
    ( ( uint32 ) 0U | ( uint32 ) ( ( uint32 ) 0U << 1U )                          \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 17U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 18U ) )

#define RTP_PC1_CONFIGVALUE                                                       \
    ( ( uint32 ) 1U | ( uint32 ) ( ( uint32 ) 1U << 1U )                          \
      | ( uint32 ) ( ( uint32 ) 1U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 1U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 1U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 1U << 17U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 18U ) )

#define RTP_PC6_CONFIGVALUE                                                       \
    ( ( uint32 ) 0U | ( uint32 ) ( ( uint32 ) 0U << 1U )                          \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 17U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 18U ) )

#define RTP_PC8_CONFIGVALUE                                                       \
    ( ( uint32 ) 1U | ( uint32 ) ( ( uint32 ) 1U << 1U )                          \
      | ( uint32 ) ( ( uint32 ) 1U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 4U ) | ( uint32 ) ( ( uint32 ) 1U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 6U ) | ( uint32 ) ( ( uint32 ) 1U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 12U ) | ( uint32 ) ( ( uint32 ) 1U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 14U ) | ( uint32 ) ( ( uint32 ) 1U << 15U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 16U ) | ( uint32 ) ( ( uint32 ) 1U << 17U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 18U ) )

#define RTP_PC7_CONFIGVALUE                                                       \
    ( ( uint32 ) 0U | ( uint32 ) ( ( uint32 ) 0U << 1U )                          \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 17U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 18U ) )

#define RTP_PC0_CONFIGVALUE                                                       \
    ( ( uint32 ) 1U | ( uint32 ) ( ( uint32 ) 1U << 1U )                          \
      | ( uint32 ) ( ( uint32 ) 1U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 4U ) | ( uint32 ) ( ( uint32 ) 1U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 6U ) | ( uint32 ) ( ( uint32 ) 1U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 8U ) | ( uint32 ) ( ( uint32 ) 1U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 1U << 10U ) | ( uint32 ) ( ( uint32 ) 1U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 12U ) | ( uint32 ) ( ( uint32 ) 1U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 14U ) | ( uint32 ) ( ( uint32 ) 1U << 15U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 16U ) | ( uint32 ) ( ( uint32 ) 1U << 17U ) \
      | ( uint32 ) ( ( uint32 ) 1U << 18U ) )

/**
 *  @defgroup RTP RTP
 *  @brief RAM Trace Port.
 *
 *  RAM Trace Port (RTP) module provides the features to datalog the RAM contents of the
 *devices or accesses to peripherals without program intrusion. It can trace all data
 *write or read accesses to internal RAM.
 *
 *	Related Files
 *   - reg_rtp.h
 *   - rtp.h
 *   - rtp.c
 *  @addtogroup RTP
 *  @{
 */

/* RTP Interface Functions */
void rtpInit( void );
void rtpGetConfigValue( rtp_config_reg_t * config_reg, config_value_type_t type );

/* USER CODE BEGIN (1) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif /*extern "C" */

#endif
