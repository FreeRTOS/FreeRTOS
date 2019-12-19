/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef __BOARD_H_
#define __BOARD_H_

#include "chip.h"
/* board_api.h is included at the bottom of this file after DEBUG setup */

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup BOARD_LPCXPRESSO_54102 LPC54102 LPCXpresso LQFP board support software API functions
 * @ingroup LPCOPEN_5410X_BOARD_LPCXPRESSO_54102
 * The board support software API functions provide some simple abstracted
 * functions used across multiple LPCOpen board examples. See @ref BOARD_COMMON_API
 * for the functions defined by this board support layer.<br>
 * @{
 */

/** @defgroup BOARD_LPCXPRESSO_54102_OPTIONS BOARD: LPC54102 LPCXpresso LQFP board build options
 * This board has options that configure its operation at build-time.<br>
 * @{
 */

/** Define DEBUG_ENABLE to enable IO via the DEBUGSTR, DEBUGOUT, and
    DEBUGIN macros. If not defined, DEBUG* functions will be optimized
    out of the code at build time.
 */
#define DEBUG_ENABLE

/** Define DEBUG_SEMIHOSTING along with DEBUG_ENABLE to enable IO support
    via semihosting. You may need to use a C library that supports
    semihosting with this option.
 */
// #define DEBUG_SEMIHOSTING

/** Board UART used for debug output and input using the DEBUG* macros. This
    is also the port used for Board_UARTPutChar, Board_UARTGetChar, and
    Board_UARTPutSTR functions. Although you can setup multiple UARTs here,
    the board code only supports UART0 in the Board_UART_Init() function,
    so be sure to change it there too if not using UART0.
 */
#define DEBUG_UART          0

/** Bit rate for the debug UART in Hz */
#define DEBUGBAUDRATE       (115200)

/** Main system clock rate in Hz for this board. Select a clock rate between
    1500000Hz and 150000000Hz for the main system (CPU) clock for this board. */
#define BOARD_MAINCLOCKRATE     (12000000)

/** External clock rate on the CLKIN pin in Hz for this board. If not used,
    set this to 0. Otherwise, set it to the exact rate in Hz this pin is
    being driven at. */
#define BOARD_EXTCLKINRATE      (0)

/** Set the BOARD_USECLKINSRC definition to (1) to use the external clock
    input pin as the PLL source. The BOARD_ECTCLKINRATE definition must
    be setup with the correct rate in the CLKIN pin. Set this to (0) to
    use the IRC for the PLL source. */
#define BOARD_USECLKINSRC       (0)

/**
 * @}
 */

/* Board name */
#define BOARD_NXP_LPCXPRESSO_54102

/** Board version definition, supports LQFP version of the board */
#define BOARD_REV1_LQFP

/**
 * @}
 */

#include "board_api.h"

#ifdef __cplusplus
}
#endif

#define E_V1_BOARD //Elink_Matt@20160730 add
#define ELINK_N18_V5
//#define CONNECTED_DEMO

#endif /* __BOARD_H_ */
