/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 *  \section Purpose
 * 
 *  Small set of functions for simple and portable LED usage.
 * 
 *  \section Usage
 * 
 *  -# Configure one or more LEDs using LED_Configure and
 *     LED_ConfigureAll.
 *  -# Set, clear and toggle LEDs using LED_Set, LED_Clear and
 *     LED_Toggle.
 * 
 *  LEDs are numbered starting from 0; the number of LEDs depend on the
 *  board being used. All the functions defined here will compile properly
 *  regardless of whether the LED is defined or not; they will simply
 *  return 0 when a LED which does not exist is given as an argument.
 *  Also, these functions take into account how each LED is connected on to
 *  board; thus, \ref LED_Set might change the level on the corresponding pin
 *  to 0 or 1, but it will always light the LED on; same thing for the other
 *  methods.
 */

#ifndef _LED_
#define _LED_

#include <stdint.h>

//------------------------------------------------------------------------------
//         Global Functions
//------------------------------------------------------------------------------

extern uint32_t LED_Configure( uint32_t dwLed ) ;

extern uint32_t LED_Set( uint32_t dwLed ) ;

extern uint32_t LED_Clear( uint32_t dwLed ) ;

extern uint32_t LED_Toggle( uint32_t dwLed ) ;

#endif /* #ifndef LED_H */

