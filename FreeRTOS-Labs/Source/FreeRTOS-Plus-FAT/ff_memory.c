/*
 * FreeRTOS+FAT build 191128 - Note:  FreeRTOS+FAT is still in the lab!
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Authors include James Walmsley, Hein Tibosch and Richard Barry
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 *
 */

/**
 *	@file		ff_memory.c
 *	@ingroup	MEMORY
 *
 *	@defgroup	MEMORY	FreeRTOS+FAT Memory Access Routines
 *	@brief		Handles memory access in a portable way.
 *
 *	Provides simple, fast, and portable access to memory routines.
 *	These are only used to read data from buffers. That are LITTLE ENDIAN
 *	due to the FAT specification.
 *
 *	These routines may need to be modified to your platform.
 *
 **/

#include "ff_headers.h"

/*
 * Here below 3 x 2 access functions that allow the code
 * not to worry about the endianness of the MCU.
 */


#if( ffconfigINLINE_MEMORY_ACCESS == 0 )

uint8_t FF_getChar( const uint8_t *pBuffer, uint32_t aOffset )
{
	return ( uint8_t ) ( pBuffer[ aOffset ] );
}

uint16_t FF_getShort( const uint8_t *pBuffer, uint32_t aOffset )
{
FF_T_UN16 u16;

	pBuffer += aOffset;
	u16.bytes.u8_1 = pBuffer[ 1 ];
	u16.bytes.u8_0 = pBuffer[ 0 ];

	return u16.u16;
}

uint32_t FF_getLong( const uint8_t *pBuffer, uint32_t aOffset )
{
FF_T_UN32 u32;

	pBuffer += aOffset;
	u32.bytes.u8_3 = pBuffer[ 3 ];
	u32.bytes.u8_2 = pBuffer[ 2 ];
	u32.bytes.u8_1 = pBuffer[ 1 ];
	u32.bytes.u8_0 = pBuffer[ 0 ];

	return u32.u32;
}

void FF_putChar( uint8_t *pBuffer, uint32_t aOffset, uint32_t Value )
{
	pBuffer[ aOffset ] = ( uint8_t ) Value;
}

void FF_putShort( uint8_t *pBuffer, uint32_t aOffset, uint32_t Value )
{
FF_T_UN16 u16;

	u16.u16 = ( uint16_t ) Value;
	pBuffer += aOffset;
	pBuffer[ 0 ] = u16.bytes.u8_0;
	pBuffer[ 1 ] = u16.bytes.u8_1;
}

void FF_putLong( uint8_t *pBuffer, uint32_t aOffset, uint32_t Value )
{
FF_T_UN32 u32;

	u32.u32 = Value;
	pBuffer += aOffset;
	pBuffer[ 0 ] = u32.bytes.u8_0;
	pBuffer[ 1 ] = u32.bytes.u8_1;
	pBuffer[ 2 ] = u32.bytes.u8_2;
	pBuffer[ 3 ] = u32.bytes.u8_3;
}

#endif
