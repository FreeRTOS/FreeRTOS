/** @file pom.h
 *   @brief POM Driver Definition File
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

#ifndef __POM_H__
#define __POM_H__

#include "reg_pom.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/** @enum pom_region_size
 *   @brief Alias names for pom region size
 *   This enumeration is used to provide alias names for POM region size:
 */
enum pom_region_size
{
    SIZE_32BYTES = 0U,
    SIZE_64BYTES = 1U,
    SIZE_128BYTES = 2U,
    SIZE_256BYTES = 3U,
    SIZE_512BYTES = 4U,
    SIZE_1KB = 5U,
    SIZE_2KB = 6U,
    SIZE_4KB = 7U,
    SIZE_8KB = 8U,
    SIZE_16KB = 9U,
    SIZE_32KB = 10U,
    SIZE_64KB = 11U,
    SIZE_128KB = 12U,
    SIZE_256KB = 13U
};

/** @def INTERNAL_RAM
 *   @brief Alias name for Internal RAM
 */
#define INTERNAL_RAM 0x08000000U

/** @def SDRAM
 *   @brief Alias name for SD RAM
 */
#define SDRAM        0x80000000U

/** @def ASYNC_MEMORY
 *   @brief Alias name for Async RAM
 */
#define ASYNC_MEMORY 0x60000000U

typedef uint32 REGION_t;

/** @struct REGION_CONFIG_ST
 *   @brief POM region configuration
 */
typedef struct
{
    uint32 Prog_Reg_Sta_Addr;
    uint32 Ovly_Reg_Sta_Addr;
    uint32 Reg_Size;
} REGION_CONFIG_t;

/* USER CODE BEGIN (1) */
/* USER CODE END */

/* Configuration registers */
typedef struct pom_config_reg
{
    uint32 CONFIG_POMGLBCTRL;
    uint32 CONFIG_POMPROGSTART0;
    uint32 CONFIG_POMOVLSTART0;
    uint32 CONFIG_POMREGSIZE0;
    uint32 CONFIG_POMPROGSTART1;
    uint32 CONFIG_POMOVLSTART1;
    uint32 CONFIG_POMREGSIZE1;
    uint32 CONFIG_POMPROGSTART2;
    uint32 CONFIG_POMOVLSTART2;
    uint32 CONFIG_POMREGSIZE2;
    uint32 CONFIG_POMPROGSTART3;
    uint32 CONFIG_POMOVLSTART3;
    uint32 CONFIG_POMREGSIZE3;
    uint32 CONFIG_POMPROGSTART4;
    uint32 CONFIG_POMOVLSTART4;
    uint32 CONFIG_POMREGSIZE4;
    uint32 CONFIG_POMPROGSTART5;
    uint32 CONFIG_POMOVLSTART5;
    uint32 CONFIG_POMREGSIZE5;
    uint32 CONFIG_POMPROGSTART6;
    uint32 CONFIG_POMOVLSTART6;
    uint32 CONFIG_POMREGSIZE6;
    uint32 CONFIG_POMPROGSTART7;
    uint32 CONFIG_POMOVLSTART7;
    uint32 CONFIG_POMREGSIZE7;
    uint32 CONFIG_POMPROGSTART8;
    uint32 CONFIG_POMOVLSTART8;
    uint32 CONFIG_POMREGSIZE8;
    uint32 CONFIG_POMPROGSTART9;
    uint32 CONFIG_POMOVLSTART9;
    uint32 CONFIG_POMREGSIZE9;
    uint32 CONFIG_POMPROGSTART10;
    uint32 CONFIG_POMOVLSTART10;
    uint32 CONFIG_POMREGSIZE10;
    uint32 CONFIG_POMPROGSTART11;
    uint32 CONFIG_POMOVLSTART11;
    uint32 CONFIG_POMREGSIZE11;
    uint32 CONFIG_POMPROGSTART12;
    uint32 CONFIG_POMOVLSTART12;
    uint32 CONFIG_POMREGSIZE12;
    uint32 CONFIG_POMPROGSTART13;
    uint32 CONFIG_POMOVLSTART13;
    uint32 CONFIG_POMREGSIZE13;
    uint32 CONFIG_POMPROGSTART14;
    uint32 CONFIG_POMOVLSTART14;
    uint32 CONFIG_POMREGSIZE14;
    uint32 CONFIG_POMPROGSTART15;
    uint32 CONFIG_POMOVLSTART15;
    uint32 CONFIG_POMREGSIZE15;
    uint32 CONFIG_POMPROGSTART16;
    uint32 CONFIG_POMOVLSTART16;
    uint32 CONFIG_POMREGSIZE16;
    uint32 CONFIG_POMPROGSTART17;
    uint32 CONFIG_POMOVLSTART17;
    uint32 CONFIG_POMREGSIZE17;
    uint32 CONFIG_POMPROGSTART18;
    uint32 CONFIG_POMOVLSTART18;
    uint32 CONFIG_POMREGSIZE18;
    uint32 CONFIG_POMPROGSTART19;
    uint32 CONFIG_POMOVLSTART19;
    uint32 CONFIG_POMREGSIZE19;
    uint32 CONFIG_POMPROGSTART20;
    uint32 CONFIG_POMOVLSTART20;
    uint32 CONFIG_POMREGSIZE20;
    uint32 CONFIG_POMPROGSTART21;
    uint32 CONFIG_POMOVLSTART21;
    uint32 CONFIG_POMREGSIZE21;
    uint32 CONFIG_POMPROGSTART22;
    uint32 CONFIG_POMOVLSTART22;
    uint32 CONFIG_POMREGSIZE22;
    uint32 CONFIG_POMPROGSTART23;
    uint32 CONFIG_POMOVLSTART23;
    uint32 CONFIG_POMREGSIZE23;
    uint32 CONFIG_POMPROGSTART24;
    uint32 CONFIG_POMOVLSTART24;
    uint32 CONFIG_POMREGSIZE24;
    uint32 CONFIG_POMPROGSTART25;
    uint32 CONFIG_POMOVLSTART25;
    uint32 CONFIG_POMREGSIZE25;
    uint32 CONFIG_POMPROGSTART26;
    uint32 CONFIG_POMOVLSTART26;
    uint32 CONFIG_POMREGSIZE26;
    uint32 CONFIG_POMPROGSTART27;
    uint32 CONFIG_POMOVLSTART27;
    uint32 CONFIG_POMREGSIZE27;
    uint32 CONFIG_POMPROGSTART28;
    uint32 CONFIG_POMOVLSTART28;
    uint32 CONFIG_POMREGSIZE28;
    uint32 CONFIG_POMPROGSTART29;
    uint32 CONFIG_POMOVLSTART29;
    uint32 CONFIG_POMREGSIZE29;
    uint32 CONFIG_POMPROGSTART30;
    uint32 CONFIG_POMOVLSTART30;
    uint32 CONFIG_POMREGSIZE30;
    uint32 CONFIG_POMPROGSTART31;
    uint32 CONFIG_POMOVLSTART31;
    uint32 CONFIG_POMREGSIZE31;
} pom_config_reg_t;

/**
 *  @defgroup POM POM
 *  @brief Parameter Overlay Module.
 *
 *  The POM provides a mechanism to redirect accesses to non-volatile memory into a
 * volatile memory internal or external to the device. The data requested by the CPU will
 * be fetched from the overlay memory instead of the main non-volatile memory.
 *
 *    Related Files
 *   - reg_pom.h
 *   - pom.h
 *   - pom.c
 *  @addtogroup POM
 *  @{
 */

/* POM Interface Functions */
void POM_Region_Config( REGION_CONFIG_t * Reg_Config_Ptr, REGION_t Region_Num );
void POM_Reset( void );
void POM_Init( void );
void POM_Enable( void );
void pomGetConfigValue( pom_config_reg_t * config_reg, config_value_type_t type );

/* USER CODE BEGIN (2) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif /*extern "C" */
#endif /* __POM_H_*/
