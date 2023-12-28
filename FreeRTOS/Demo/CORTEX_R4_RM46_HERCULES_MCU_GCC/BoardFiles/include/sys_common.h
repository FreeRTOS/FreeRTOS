/** @file sys_common.h
 *   @brief Common Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - General Definitions
 *   .
 *   which are relevant for all drivers.
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

#ifndef __SYS_COMMON_H__
#define __SYS_COMMON_H__

#include "hal_stdtypes.h"

#ifdef __cplusplus
extern "C" {
#endif
/* USER CODE BEGIN (0) */
/* USER CODE END */

/************************************************************/
/* Type Definitions                                         */
/************************************************************/

#ifndef _TBOOLEAN_DECLARED
typedef boolean tBoolean;
    #define _TBOOLEAN_DECLARED
#endif

/** @enum loopBackType
 *   @brief Loopback type definition
 */

/** @typedef loopBackType_t
 *   @brief Loopback type Type Definition
 *
 *   This type is used to select the module Loopback type Digital or Analog loopback.
 */
typedef enum loopBackType
{
    Digital_Lbk = 0U,
    Analog_Lbk = 1U
} loopBackType_t;

/** @enum config_value_type
 *   @brief config type definition
 */

/** @typedef config_value_type_t
 *   @brief config type Type Definition
 *
 *   This type is used to specify the Initial and Current value.
 */
typedef enum config_value_type
{
    InitialValue,
    CurrentValue
} config_value_type_t;

#ifndef __little_endian__
    #define __little_endian__ 1
#endif
#ifndef __LITTLE_ENDIAN__
    #define __LITTLE_ENDIAN__ 1
#endif

/* USER CODE BEGIN (1) */
/* USER CODE END */

/********************************************************************************/
/* The ASSERT macro, which does the actual assertion checking.  Typically, this */
/* will be for procedure arguments.                                             */
/********************************************************************************/
#ifdef DEBUG
    #define ASSERT( expr )                       \
        {                                        \
            if( !( expr ) )                      \
            {                                    \
                __error__( __FILE__, __LINE__ ); \
            }                                    \
        }
#else
    #define ASSERT( expr )
#endif

/* USER CODE BEGIN (2) */
/* USER CODE END */

/* USER CODE BEGIN (3) */
/* USER CODE END */
#ifdef __cplusplus
}
#endif

#endif /* ifndef __SYS_COMMON_H__ */
