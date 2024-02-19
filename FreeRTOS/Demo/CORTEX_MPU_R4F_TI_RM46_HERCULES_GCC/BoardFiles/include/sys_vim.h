/** @file sys_vim.h
 *   @brief Vectored Interrupt Module Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - VIM Type Definitions
 *   - VIM General Definitions
 *   .
 *   which are relevant for Vectored Interrupt Controller.
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

#ifndef __SYS_VIM_H__
#define __SYS_VIM_H__

#include "reg_vim.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* VIM Type Definitions */

/** @typedef t_isrFuncPTR
 *   @brief ISR Function Pointer Type Definition
 *
 *   This type is used to access the ISR handler.
 */
typedef void ( *t_isrFuncPTR )( void );

/** @enum systemInterrupt
 *   @brief Alias names for clock sources
 *
 *   This enumeration is used to provide alias names for the clock sources:
 *     - IRQ
 *     - FIQ
 */
typedef enum systemInterrupt
{
    SYS_IRQ = 0U, /**< Alias for IRQ interrupt */
    SYS_FIQ = 1U  /**< Alias for FIQ interrupt */
} systemInterrupt_t;

/* USER CODE BEGIN (1) */
/* USER CODE END */

/* VIM General Configuration */

#define VIM_CHANNELS 128U

/* USER CODE BEGIN (2) */
/* USER CODE END */

/* Interrupt Handlers */

extern void esmHighInterrupt( void ) __attribute__( ( weak, interrupt( "FIQ" ) ) );
extern void phantomInterrupt( void ) __attribute__( ( weak, interrupt( "IRQ" ) ) );
extern void FreeRTOS_Tick_Handler( void ) __attribute__( ( weak, interrupt( "IRQ" ) ) );
extern void FreeRTOS_IRQ_Handler( void ) __attribute__( ( weak, interrupt( "IRQ" ) ) );
extern void vPortYieldWithinAPI( void ) __attribute__( ( weak, interrupt( "IRQ" ) ) );

/* USER CODE BEGIN (3) */
/* USER CODE END */

#define VIM_PARFLG   ( *( volatile uint32 * ) 0xFFFFFDECU )
#define VIM_PARCTL   ( *( volatile uint32 * ) 0xFFFFFDF0U )
#define VIM_ADDERR   ( *( volatile uint32 * ) 0xFFFFFDF4U )
#define VIM_FBPARERR ( *( volatile uint32 * ) 0xFFFFFDF8U )

#define VIMRAMPARLOC ( *( volatile uint32 * ) 0xFFF82400U )
#define VIMRAMLOC    ( *( volatile uint32 * ) 0xFFF82000U )

/* Configuration registers */
typedef struct vim_config_reg
{
    uint32 CONFIG_FIRQPR0;
    uint32 CONFIG_FIRQPR1;
    uint32 CONFIG_FIRQPR2;
    uint32 CONFIG_FIRQPR3;
    uint32 CONFIG_REQMASKSET0;
    uint32 CONFIG_REQMASKSET1;
    uint32 CONFIG_REQMASKSET2;
    uint32 CONFIG_REQMASKSET3;
    uint32 CONFIG_WAKEMASKSET0;
    uint32 CONFIG_WAKEMASKSET1;
    uint32 CONFIG_WAKEMASKSET2;
    uint32 CONFIG_WAKEMASKSET3;
    uint32 CONFIG_CAPEVT;
    uint32 CONFIG_CHANCTRL[ 32U ];
} vim_config_reg_t;

/* Configuration registers initial value */
#define VIM_FIRQPR0_CONFIGVALUE                                                         \
    ( ( uint32 ) ( ( uint32 ) SYS_FIQ << 0U ) | ( uint32 ) ( ( uint32 ) SYS_FIQ << 1U ) \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 2U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 3U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 4U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 5U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 6U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 7U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 8U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 9U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 10U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 11U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 12U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 13U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 14U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 15U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 16U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 17U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 18U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 19U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 20U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 21U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 22U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 23U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 24U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 25U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 26U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 27U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 28U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 29U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 30U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 31U ) )

#define VIM_FIRQPR1_CONFIGVALUE                                                         \
    ( ( uint32 ) ( ( uint32 ) SYS_IRQ << 0U ) | ( uint32 ) ( ( uint32 ) SYS_IRQ << 1U ) \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 2U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 3U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 4U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 5U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 6U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 7U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 8U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 9U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 10U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 11U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 12U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 13U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 14U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 15U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 16U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 17U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 18U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 19U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 20U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 21U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 22U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 23U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 24U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 25U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 26U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 27U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 28U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 29U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 30U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 31U ) )

#define VIM_FIRQPR2_CONFIGVALUE                                                         \
    ( ( uint32 ) ( ( uint32 ) SYS_IRQ << 0U ) | ( uint32 ) ( ( uint32 ) SYS_IRQ << 1U ) \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 2U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 3U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 4U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 5U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 6U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 7U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 8U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 9U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 10U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 11U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 12U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 13U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 14U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 15U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 16U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 17U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 18U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 19U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 20U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 21U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 22U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 23U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 24U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 25U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 26U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 27U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 28U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 29U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 30U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 31U ) )

#define VIM_FIRQPR3_CONFIGVALUE                                                         \
    ( ( uint32 ) ( ( uint32 ) SYS_IRQ << 0U ) | ( uint32 ) ( ( uint32 ) SYS_IRQ << 1U ) \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 2U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 3U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 4U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 5U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 6U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 7U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 8U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 9U )                                         \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 10U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 11U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 12U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 13U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 14U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 15U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 16U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 17U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 18U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 19U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 20U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 21U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 22U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 23U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 24U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 25U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 26U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 27U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 28U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 29U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 30U )                                        \
      | ( uint32 ) ( ( uint32 ) SYS_IRQ << 31U ) )

#define VIM_REQMASKSET0_CONFIGVALUE                                               \
    ( ( uint32 ) ( ( uint32 ) 1U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 1U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 17U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 18U ) | ( uint32 ) ( ( uint32 ) 0U << 19U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 1U << 21U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 23U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 25U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 26U ) | ( uint32 ) ( ( uint32 ) 0U << 27U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 28U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 31U ) )

#define VIM_REQMASKSET1_CONFIGVALUE                                               \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 17U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 18U ) | ( uint32 ) ( ( uint32 ) 0U << 19U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 21U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 23U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 25U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 26U ) | ( uint32 ) ( ( uint32 ) 0U << 27U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 28U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 31U ) )

#define VIM_REQMASKSET2_CONFIGVALUE                                               \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 17U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 18U ) | ( uint32 ) ( ( uint32 ) 0U << 19U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 21U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 23U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 25U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 26U ) | ( uint32 ) ( ( uint32 ) 0U << 27U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 28U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 31U ) )

#define VIM_REQMASKSET3_CONFIGVALUE                                               \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 1U )     \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 0U << 3U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 4U ) | ( uint32 ) ( ( uint32 ) 0U << 5U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 6U ) | ( uint32 ) ( ( uint32 ) 0U << 7U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 8U ) | ( uint32 ) ( ( uint32 ) 0U << 9U )   \
      | ( uint32 ) ( ( uint32 ) 0U << 10U ) | ( uint32 ) ( ( uint32 ) 0U << 11U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 12U ) | ( uint32 ) ( ( uint32 ) 0U << 13U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 14U ) | ( uint32 ) ( ( uint32 ) 0U << 15U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 16U ) | ( uint32 ) ( ( uint32 ) 0U << 17U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 18U ) | ( uint32 ) ( ( uint32 ) 0U << 19U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 20U ) | ( uint32 ) ( ( uint32 ) 0U << 21U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 22U ) | ( uint32 ) ( ( uint32 ) 0U << 23U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 24U ) | ( uint32 ) ( ( uint32 ) 0U << 25U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 26U ) | ( uint32 ) ( ( uint32 ) 0U << 27U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 28U ) | ( uint32 ) ( ( uint32 ) 0U << 29U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 30U ) | ( uint32 ) ( ( uint32 ) 0U << 31U ) )

#define VIM_WAKEMASKSET0_CONFIGVALUE 0xFFFFFFFFU
#define VIM_WAKEMASKSET1_CONFIGVALUE 0xFFFFFFFFU
#define VIM_WAKEMASKSET2_CONFIGVALUE 0xFFFFFFFFU
#define VIM_WAKEMASKSET3_CONFIGVALUE 0xFFFFFFFFU
#define VIM_CAPEVT_CONFIGVALUE \
    ( ( uint32 ) ( ( uint32 ) 0U << 0U ) | ( uint32 ) ( ( uint32 ) 0U << 16U ) )

#define VIM_CHANCTRL0_CONFIGVALUE  0x00010203U
#define VIM_CHANCTRL1_CONFIGVALUE  0x04050607U
#define VIM_CHANCTRL2_CONFIGVALUE  0x08090A0BU
#define VIM_CHANCTRL3_CONFIGVALUE  0x0C0D0E0FU
#define VIM_CHANCTRL4_CONFIGVALUE  0x10111213U
#define VIM_CHANCTRL5_CONFIGVALUE  0x14151617U
#define VIM_CHANCTRL6_CONFIGVALUE  0x18191A1BU
#define VIM_CHANCTRL7_CONFIGVALUE  0x1C1D1E1FU
#define VIM_CHANCTRL8_CONFIGVALUE  0x20212223U
#define VIM_CHANCTRL9_CONFIGVALUE  0x24252627U
#define VIM_CHANCTRL10_CONFIGVALUE 0x28292A2BU
#define VIM_CHANCTRL11_CONFIGVALUE 0x2C2D2E2FU
#define VIM_CHANCTRL12_CONFIGVALUE 0x30313233U
#define VIM_CHANCTRL13_CONFIGVALUE 0x34353637U
#define VIM_CHANCTRL14_CONFIGVALUE 0x38393A3BU
#define VIM_CHANCTRL15_CONFIGVALUE 0x3C3D3E3FU
#define VIM_CHANCTRL16_CONFIGVALUE 0x40414243U
#define VIM_CHANCTRL17_CONFIGVALUE 0x44454647U
#define VIM_CHANCTRL18_CONFIGVALUE 0x48494A4BU
#define VIM_CHANCTRL19_CONFIGVALUE 0x4C4D4E4FU
#define VIM_CHANCTRL20_CONFIGVALUE 0x50515253U
#define VIM_CHANCTRL21_CONFIGVALUE 0x54555657U
#define VIM_CHANCTRL22_CONFIGVALUE 0x58595A5BU
#define VIM_CHANCTRL23_CONFIGVALUE 0x5C5D5E5FU
#define VIM_CHANCTRL24_CONFIGVALUE 0x60616263U
#define VIM_CHANCTRL25_CONFIGVALUE 0x64656667U
#define VIM_CHANCTRL26_CONFIGVALUE 0x68696A6BU
#define VIM_CHANCTRL27_CONFIGVALUE 0x6C6D6E6FU
#define VIM_CHANCTRL28_CONFIGVALUE 0x70717273U
#define VIM_CHANCTRL29_CONFIGVALUE 0x74757677U
#define VIM_CHANCTRL30_CONFIGVALUE 0x78797A7BU
#define VIM_CHANCTRL31_CONFIGVALUE 0x7C7D7E7FU

/**
 * @defgroup VIM VIM
 * @brief Vectored Interrupt Manager
 *
 * The vectored interrupt manager (VIM) provides hardware assistance for prioritizing and
 * controlling the many interrupt sources present on a device. Interrupts are caused by
 * events outside of the normal flow of program execution.
 *
 * Related files:
 * - reg_vim.h
 * - sys_vim.h
 * - sys_vim.c
 *
 * @addtogroup VIM
 * @{
 */
/*VIM Interface functions*/
void vimInit( void );
void vimChannelMap( uint32 request, uint32 channel, t_isrFuncPTR handler );
void vimEnableInterrupt( uint32 channel, systemInterrupt_t inttype );
void vimDisableInterrupt( uint32 channel );
void vimGetConfigValue( vim_config_reg_t * config_reg, config_value_type_t type );
/*@}*/
#endif /* ifndef __SYS_VIM_H__ */
