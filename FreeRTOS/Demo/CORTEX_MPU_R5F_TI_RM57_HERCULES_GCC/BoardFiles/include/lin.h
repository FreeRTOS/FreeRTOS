/** @file lin.h
 *   @brief LIN Driver Definition File
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

#ifndef __LIN_H__
#define __LIN_H__

#include "reg_lin.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

/** @def LIN_BREAK_INT
 *   @brief Alias for break detect interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_BREAK_INT   0x00000001U

/** @def LIN_WAKEUP_INT
 *   @brief Alias for wakeup interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_WAKEUP_INT  0x00000002U

/** @def LIN_TO_INT
 *   @brief Alias for time out interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_TO_INT      0x00000010U

/** @def LIN_TOAWUS_INT
 *   @brief Alias for time out after wakeup signal interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_TOAWUS_INT  0x00000040U

/** @def LIN_TOA3WUS_INT
 *   @brief Alias for time out after 3 wakeup signals interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_TOA3WUS_INT 0x00000080U

/** @def LIN_TX_READY
 *   @brief Alias for transmit buffer ready flag
 *
 *   Used with linIsTxReady.
 */
#define LIN_TX_READY    0x00000100U

/** @def LIN_RX_INT
 *   @brief Alias for receive buffer ready interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_RX_INT      0x00000200U

/** @def LIN_ID_INT
 *   @brief Alias for received matching identifier interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_ID_INT      0x00002000U

/** @def LIN_PE_INT
 *   @brief Alias for parity error interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_PE_INT      0x01000000U

/** @def LIN_OE_INT
 *   @brief Alias for overrun error interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_OE_INT      0x02000000U

/** @def LIN_FE_INT
 *   @brief Alias for framing error interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_FE_INT      0x04000000U

/** @def LIN_NRE_INT
 *   @brief Alias for no response error interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_NRE_INT     0x08000000U

/** @def LIN_ISFE_INT
 *   @brief Alias for inconsistent sync field error interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_ISFE_INT    0x10000000U

/** @def LIN_CE_INT
 *   @brief Alias for checksum error interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_CE_INT      0x20000000U

/** @def LIN_PBE_INT
 *   @brief Alias for physical bus error interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_PBE_INT     0x40000000U

/** @def LIN_BE_INT
 *   @brief Alias for bit error interrupt flag
 *
 *   Used with linEnableNotification, linDisableNotification.
 */
#define LIN_BE_INT      0x80000000U

/** @struct linBase
 *   @brief LIN Register Definition
 *
 *   This structure is used to access the LIN module registers.
 */
/** @typedef linBASE_t
 *   @brief LIN Register Frame Type Definition
 *
 *   This type is used to access the LIN Registers.
 */

enum linPinSelect
{
    PIN_LIN_TX = 4U,
    PIN_LIN_RX = 2U
};

/* Configuration registers */
typedef struct lin_config_reg
{
    uint32 CONFIG_GCR0;
    uint32 CONFIG_GCR1;
    uint32 CONFIG_GCR2;
    uint32 CONFIG_SETINT;
    uint32 CONFIG_SETINTLVL;
    uint32 CONFIG_FORMAT;
    uint32 CONFIG_BRSR;
    uint32 CONFIG_FUN;
    uint32 CONFIG_DIR;
    uint32 CONFIG_ODR;
    uint32 CONFIG_PD;
    uint32 CONFIG_PSL;
    uint32 CONFIG_COMP;
    uint32 CONFIG_MASK;
    uint32 CONFIG_MBRSR;
} lin_config_reg_t;

/* Configuration registers initial value for LIN*/
#define LIN1_GCR0_CONFIGVALUE 0x00000001U
#define LIN1_GCR1_CONFIGVALUE                           \
    ( 0x03000CC0U | ( uint32 ) ( ( uint32 ) 1U << 12U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 5U ) )
#define LIN1_GCR2_CONFIGVALUE 0x00000000U
#define LIN1_SETINTLVL_CONFIGVALUE                                                      \
    ( 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U \
      | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U             \
      | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U )

#define LIN1_SETINT_CONFIGVALUE                                                         \
    ( 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U \
      | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U             \
      | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U )

#define LIN1_FORMAT_CONFIGVALUE ( ( uint32 ) ( ( uint32 ) ( 8U - 1U ) << 16U ) )
#define LIN1_BRSR_CONFIGVALUE   ( 233U )
#define LIN1_COMP_CONFIGVALUE \
    ( ( uint32 ) ( ( uint32 ) ( 1U - 1U ) << 8U ) | ( 13U - 13U ) )
#define LIN1_MASK_CONFIGVALUE  ( ( uint32 ) ( ( uint32 ) 0xFFU << 16U ) | 0xFFU )
#define LIN1_MBRSR_CONFIGVALUE ( 3370U )
#define LIN1_FUN_CONFIGVALUE   ( 4U | 2U | 0U )
#define LIN1_DIR_CONFIGVALUE   ( 0U | 0U | 0U )
#define LIN1_ODR_CONFIGVALUE   ( 0U | 0U | 0U )
#define LIN1_PD_CONFIGVALUE    ( 0U | 0U | 0U )
#define LIN1_PSL_CONFIGVALUE   ( 4U | 2U | 1U )

/* Configuration registers initial value for LIN*/
#define LIN2_GCR0_CONFIGVALUE  0x00000001U
#define LIN2_GCR1_CONFIGVALUE                           \
    ( 0x03000CC0U | ( uint32 ) ( ( uint32 ) 1U << 12U ) \
      | ( uint32 ) ( ( uint32 ) 0U << 2U ) | ( uint32 ) ( ( uint32 ) 1U << 5U ) )
#define LIN2_GCR2_CONFIGVALUE 0x00000000U
#define LIN2_SETINTLVL_CONFIGVALUE                                                      \
    ( 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U \
      | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U             \
      | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U )

#define LIN2_SETINT_CONFIGVALUE                                                         \
    ( 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U \
      | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U             \
      | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U | 0x00000000U )

#define LIN2_FORMAT_CONFIGVALUE ( ( uint32 ) ( ( uint32 ) ( 8U - 1U ) << 16U ) )
#define LIN2_BRSR_CONFIGVALUE   ( 233U )
#define LIN2_COMP_CONFIGVALUE \
    ( ( uint32 ) ( ( uint32 ) ( 1U - 1U ) << 8U ) | ( 13U - 13U ) )
#define LIN2_MASK_CONFIGVALUE  ( ( uint32 ) ( ( uint32 ) 0xFFU << 16U ) | 0xFFU )
#define LIN2_MBRSR_CONFIGVALUE ( 3370U )
#define LIN2_FUN_CONFIGVALUE   ( 4U | 2U | 0U )
#define LIN2_DIR_CONFIGVALUE   ( 0U | 0U | 0U )
#define LIN2_ODR_CONFIGVALUE   ( 0U | 0U | 0U )
#define LIN2_PD_CONFIGVALUE    ( 0U | 0U | 0U )
#define LIN2_PSL_CONFIGVALUE   ( 4U | 2U | 1U )

/**
 *  @defgroup LIN LIN
 *  @brief Local Interconnect Network Module.
 *
 *  The LIN standard is based on the SCI (UART) serial data link format. The communication
 *concept is single-master/multiple-slave with a message identification for multi-cast
 *transmission between any network nodes.
 *
 *	Related Files
 *   - reg_lin.h
 *   - lin.h
 *   - lin.c
 *  @addtogroup LIN
 *  @{
 */

/* LIN Interface Functions */
void linInit( void );
void linSetFunctional( linBASE_t * lin, uint32 port );
void linSendHeader( linBASE_t * lin, uint8 identifier );
void linSendWakupSignal( linBASE_t * lin );
void linEnterSleep( linBASE_t * lin );
void linSoftwareReset( linBASE_t * lin );
uint32 linIsTxReady( linBASE_t * lin );
void linSetLength( linBASE_t * lin, uint32 length );
void linSend( linBASE_t * lin, uint8 * data );
uint32 linIsRxReady( linBASE_t * lin );
uint32 linTxRxError( linBASE_t * lin );
uint32 linGetIdentifier( linBASE_t * lin );
void linGetData( linBASE_t * lin, uint8 * const data );
void linEnableNotification( linBASE_t * lin, uint32 flags );
void linDisableNotification( linBASE_t * lin, uint32 flags );
void linEnableLoopback( linBASE_t * lin, loopBackType_t Loopbacktype );
void linDisableLoopback( linBASE_t * lin );
void lin1GetConfigValue( lin_config_reg_t * config_reg, config_value_type_t type );
void lin2GetConfigValue( lin_config_reg_t * config_reg, config_value_type_t type );
uint32 linGetStatusFlag( linBASE_t * lin );
void linClearStatusFlag( linBASE_t * lin, uint32 flags );

/** @fn void linNotification(linBASE_t *lin, uint32 flags)
 *   @brief Interrupt callback
 *   @param[in] lin   - lin module base address
 *   @param[in] flags - copy of error interrupt flags
 *
 * This is a callback that is provided by the application and is called upon
 * an interrupt.  The parameter passed to the callback is a copy of the
 * interrupt flag register.
 */
void linNotification( linBASE_t * lin, uint32 flags );

/* USER CODE BEGIN (1) */
/* USER CODE END */

/**@}*/
#ifdef __cplusplus
}
#endif

#endif
