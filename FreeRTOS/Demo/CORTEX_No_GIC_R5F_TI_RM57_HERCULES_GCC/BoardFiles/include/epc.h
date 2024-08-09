/** @file epc.h
 *   @brief EPC Driver Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the EPC driver.
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

#ifndef SYS_EPC_H_
#define SYS_EPC_H_

#include "reg_epc.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (0) */
/* USER CODE END */

enum CAMIndex
{
    CAMIndex_0 = 0U,
    CAMIndex_1 = 1U,
    CAMIndex_2 = 2U,
    CAMIndex_3 = 3U,
    CAMIndex_4 = 4U,
    CAMIndex_5 = 5U,
    CAMIndex_6 = 6U,
    CAMIndex_7 = 7U,
    CAMIndex_8 = 8U,
    CAMIndex_9 = 9U,
    CAMIndex_10 = 10U,
    CAMIndex_11 = 11U,
    CAMIndex_12 = 12U,
    CAMIndex_13 = 13U,
    CAMIndex_14 = 14U,
    CAMIndex_15 = 15U,
    CAMIndex_16 = 16U,
    CAMIndex_17 = 17U,
    CAMIndex_18 = 18U,
    CAMIndex_19 = 19U,
    CAMIndex_20 = 20U,
    CAMIndex_21 = 21U,
    CAMIndex_22 = 22U,
    CAMIndex_23 = 23U,
    CAMIndex_24 = 24U,
    CAMIndex_25 = 25U,
    CAMIndex_26 = 26U,
    CAMIndex_27 = 27U,
    CAMIndex_28 = 28U,
    CAMIndex_29 = 29U,
    CAMIndex_30 = 30U,
    CAMIndex_31 = 31U
};

/**
 * @defgroup EPC EPC
 * @brief Error Profiling Controller
 *
 * Related files:
 * - reg_epc.h
 * - sys_epc.h
 * - sys_epc.c
 *
 * @addtogroup EPC
 * @{
 */

void epcEnableIP1ErrorGen( void );
void epcDisableIP1ErrorGen( void );
void epcEnableIP2ErrorGen( void );
void epcDisableIP2ErrorGen( void );
void epcEnableSERREvent( void );
void epcDisableSERREvent( void );
void epcEnableInterrupt( void );
void epcDisableInterrupt( void );
void epcCAMInit( void );
boolean epcDiagnosticTest( void );
boolean epcAddCAMEEntry( uint32 address );
boolean epcCheckCAMEntry( uint32 index );

void epcCAMFullNotification( void );
void epcFIFOFullNotification( uint32 epcFIFOStatus );

/**@}*/

/* USER CODE BEGIN (1) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif /*extern "C" */

#endif /* SYS_EPC_H_ */
