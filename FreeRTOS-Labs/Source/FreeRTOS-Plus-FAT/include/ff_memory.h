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
 *	@file		ff_memory.h
 *	@ingroup	MEMORY
 **/

#ifndef _FF_MEMORY_H_
#define _FF_MEMORY_H_

/*
 * When sector data is written or analysed, some values might be stored unaligned.
 * The routines below treat all values as little arrays of either 2 or 4 bytes.
 * Also on big endian platforms, the order of bytes will be swapped.
 */
/*---------- PROTOTYPES */

#if( ffconfigBYTE_ORDER == pdFREERTOS_LITTLE_ENDIAN )
	/*
	 * FAT is little endian.
	 * On a little endian CPU, bytes will be copied to the structures below 1-to-1 :
	 */
	typedef struct
	{
		uint8_t u8_0;	/* the first byte */
		uint8_t u8_1;	/* the second byte */
	} FF_TShort_t;

	typedef struct
	{
		uint8_t u8_0;
		uint8_t u8_1;
		uint8_t u8_2;
		uint8_t u8_3;
	} FF_TLong_t;
#elif( ffconfigBYTE_ORDER == pdFREERTOS_BIG_ENDIAN )
	/*
	 * On a big endian CPU, all bytes will be swapped, either 2 or 4 bytes:
	 */
	typedef struct
	{
		uint8_t u8_1;	/* the second byte */
		uint8_t u8_0;	/* the first byte */
	} FF_TShort_t;

	typedef struct
	{
		uint8_t u8_3;
		uint8_t u8_2;
		uint8_t u8_1;
		uint8_t u8_0;
	} FF_TLong_t;
#else
	#error Little or Big Endian? - Please set ffconfigBYTE_ORDER to either pdFREERTOS_LITTLE_ENDIAN or pdFREERTOS_BIG_ENDIAN 1 in FreeRTOSFATConfig.h
#endif

/*! 16-bit union. */
typedef union
{
   uint16_t u16;
   FF_TShort_t bytes;
} FF_T_UN16;

/*! 32-bit union. */
typedef union
{
  uint32_t u32;
  FF_TLong_t bytes;
} FF_T_UN32;

/*	HT inlined these functions:
 */

#if( ffconfigINLINE_MEMORY_ACCESS != 0 )

	static portINLINE uint8_t FF_getChar( const uint8_t *pBuffer, uint32_t aOffset )
	{
		return ( uint8_t ) ( pBuffer[ aOffset ] );
	}

	static portINLINE uint16_t FF_getShort( const uint8_t *pBuffer, uint32_t aOffset )
	{
	FF_T_UN16 u16;

		pBuffer += aOffset;
		u16.bytes.u8_1 = pBuffer[ 1 ];
		u16.bytes.u8_0 = pBuffer[ 0 ];

		return u16.u16;
	}

	static portINLINE uint32_t FF_getLong( const uint8_t *pBuffer, uint32_t aOffset )
	{
	FF_T_UN32 u32;

		pBuffer += aOffset;
		u32.bytes.u8_3 = pBuffer[ 3 ];
		u32.bytes.u8_2 = pBuffer[ 2 ];
		u32.bytes.u8_1 = pBuffer[ 1 ];
		u32.bytes.u8_0 = pBuffer[ 0 ];

		return u32.u32;
	}

	static portINLINE void FF_putChar( uint8_t *pBuffer, uint32_t aOffset, uint32_t Value )
	{
		pBuffer[ aOffset ] = ( uint8_t ) Value;
	}

	static portINLINE void FF_putShort( uint8_t *pBuffer, uint32_t aOffset, uint32_t Value )
	{
	FF_T_UN16 u16;

		u16.u16 = ( uint16_t ) Value;
		pBuffer += aOffset;
		pBuffer[ 0 ] = u16.bytes.u8_0;
		pBuffer[ 1 ] = u16.bytes.u8_1;
	}

	static portINLINE void FF_putLong( uint8_t *pBuffer, uint32_t aOffset, uint32_t Value )
	{
	FF_T_UN32 u32;

		u32.u32 = Value;
		pBuffer += aOffset;
		pBuffer[ 0 ] = u32.bytes.u8_0;
		pBuffer[ 1 ] = u32.bytes.u8_1;
		pBuffer[ 2 ] = u32.bytes.u8_2;
		pBuffer[ 3 ] = u32.bytes.u8_3;
	}

#else	/* ffconfigINLINE_MEMORY_ACCESS */

	uint8_t FF_getChar( const uint8_t *pBuffer, uint32_t aOffset );
	uint16_t FF_getShort( const uint8_t *pBuffer, uint32_t aOffset );
	uint32_t FF_getLong( const uint8_t *pBuffer, uint32_t aOffset );
	void FF_putChar( uint8_t *pBuffer, uint32_t aOffset, uint32_t Value );
	void FF_putShort( uint8_t *pBuffer, uint32_t aOffset, uint32_t Value );
	void FF_putLong( uint8_t *pBuffer, uint32_t aOffset, uint32_t Value );

#endif	/* ffconfigINLINE_MEMORY_ACCESS */

#endif	/* _FF_MEMORY_H_ */

