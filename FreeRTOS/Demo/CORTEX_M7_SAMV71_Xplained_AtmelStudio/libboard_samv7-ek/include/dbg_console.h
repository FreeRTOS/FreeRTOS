/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
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
  *  \file
  *
  *  Include function prototype for the UART console.
  */

#ifndef _DBG_CONSOLE_
#define _DBG_CONSOLE_

#include <stdint.h>

extern void DBG_Configure( uint32_t dwBaudrate, uint32_t dwMasterClock ) ;
extern void DBG_PutChar( uint8_t uc ) ;
extern uint32_t DBG_GetChar( void ) ;
extern uint32_t DBG_IsRxReady( void ) ;


extern void DBG_DumpFrame( uint8_t* pucFrame, uint32_t dwSize ) ;
extern void DBG_DumpMemory( uint8_t* pucBuffer, uint32_t dwSize, uint32_t dwAddress ) ;
extern uint32_t DBG_GetInteger( int32_t* pdwValue ) ;
extern uint32_t DBG_GetIntegerMinMax( int32_t* pdwValue, int32_t dwMin, int32_t dwMax ) ;
extern uint32_t DBG_GetHexa32( uint32_t* pdwValue ) ;

#endif /* _DBG_CONSOLE_ */
