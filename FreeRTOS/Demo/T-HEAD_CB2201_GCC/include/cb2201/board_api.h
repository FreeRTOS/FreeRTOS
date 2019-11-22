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
#ifndef __BOARD_API_H_
#define __BOARD_API_H_

#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The DEBUG* functions are selected based on system configuration.
   Code that uses the DEBUG* functions will have their I/O routed to
   the UART, semihosting, or nowhere. */
#if defined(DEBUG_ENABLE)
#if defined(DEBUG_SEMIHOSTING)
#define DEBUGINIT()
#define DEBUGOUT(...) printf(__VA_ARGS__)
#define DEBUGSTR(str) printf(str)
#define DEBUGIN() (int) EOF

#else
#define DEBUGINIT() Board_Debug_Init()
#define DEBUGOUT(...) printf(__VA_ARGS__)
#define DEBUGSTR(str) Board_UARTPutSTR(str)
#define DEBUGIN() Board_UARTGetChar()
#endif /* defined(DEBUG_SEMIHOSTING) */

#else
#define DEBUGINIT()
#define DEBUGOUT(...)
#define DEBUGSTR(str)
#define DEBUGIN() (int) EOF
#endif /* defined(DEBUG_ENABLE) */

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __BOARD_API_H_ */
