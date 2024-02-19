/** @file gio.h
 *   @brief GIO Driver Definition File
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

#ifndef __GIO_H__
#define __GIO_H__

#include "reg_gio.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

typedef struct gio_config_reg
{
    uint32 CONFIG_INTDET;
    uint32 CONFIG_POL;
    uint32 CONFIG_INTENASET;
    uint32 CONFIG_LVLSET;

    uint32 CONFIG_PORTADIR;
    uint32 CONFIG_PORTAPDR;
    uint32 CONFIG_PORTAPSL;
    uint32 CONFIG_PORTAPULDIS;

    uint32 CONFIG_PORTBDIR;
    uint32 CONFIG_PORTBPDR;
    uint32 CONFIG_PORTBPSL;
    uint32 CONFIG_PORTBPULDIS;
} gio_config_reg_t;

#define GIO_INTDET_CONFIGVALUE 0U
#define GIO_POL_CONFIGVALUE                                                       \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) )

#define GIO_INTENASET_CONFIGVALUE                                                 \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) )

#define GIO_LVLSET_CONFIGVALUE                                                    \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) )

#define GIO_PORTADIR_CONFIGVALUE                                                \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U ) )
#define GIO_PORTAPDR_CONFIGVALUE                                                \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U ) )
#define GIO_PORTAPSL_CONFIGVALUE                                                \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U ) )
#define GIO_PORTAPULDIS_CONFIGVALUE                                             \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U ) )

#define GIO_PORTBDIR_CONFIGVALUE                                                \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U ) )
#define GIO_PORTBPDR_CONFIGVALUE                                                \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U ) )
#define GIO_PORTBPSL_CONFIGVALUE                                                \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U ) )
#define GIO_PORTBPULDIS_CONFIGVALUE                                             \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U ) )

/**
 *  @defgroup GIO GIO
 *  @brief General-Purpose Input/Output Module.
 *
 *  The GIO module provides the family of devices with input/output (I/O) capability.
 *  The I/O pins are bidirectional and bit-programmable.
 *  The GIO module also supports external interrupt capability.
 *
 *	Related Files
 *   - reg_gio.h
 *   - gio.h
 *   - gio.c
 *  @addtogroup GIO
 *  @{
 */

/* GIO Interface Functions */
void gioInit( void );
void gioSetDirection( gioPORT_t * port, uint32 dir );
void gioSetBit( gioPORT_t * port, uint32 bit, uint32 value );
void gioSetPort( gioPORT_t * port, uint32 value );
uint32 gioGetBit( gioPORT_t * port, uint32 bit );
uint32 gioGetPort( gioPORT_t * port );
void gioToggleBit( gioPORT_t * port, uint32 bit );
void gioEnableNotification( gioPORT_t * port, uint32 bit );
void gioDisableNotification( gioPORT_t * port, uint32 bit );
void gioNotification( gioPORT_t * port, uint32 bit );
void gioGetConfigValue( gio_config_reg_t * config_reg, config_value_type_t type );

/* USER CODE BEGIN (1) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif /*extern "C" */

#endif
