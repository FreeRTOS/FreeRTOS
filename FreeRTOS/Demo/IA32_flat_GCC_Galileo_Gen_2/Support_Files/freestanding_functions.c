/*
 * FreeRTOS Kernel V10.3.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */


/*
 * The library functions not provided by libgcc for freestanding environments.
 * The implementation of the functions in this file have made NO attempt
 * whatsoever to be optimised!
 */

#warning The functions in this file are very basic, and not optimised.

#include <stddef.h>

/*-----------------------------------------------------------*/

void *memcpy( void *pvDest, const void *pvSource, size_t xBytes )
{
/* The compiler used during development seems to err unless these volatiles are
included at -O3 optimisation.  */
volatile unsigned char *pcDest = ( volatile unsigned char * ) pvDest, *pcSource = ( volatile unsigned char * ) pvSource;
size_t x;

	/* Extremely crude standard library implementations in lieu of having a C
	library. */
	if( pvDest != pvSource )
	{
		for( x = 0; x < xBytes; x++ )
		{
			pcDest[ x ] = pcSource[ x ];
		}
	}

	return pvDest;
}
/*-----------------------------------------------------------*/

void *memset( void *pvDest, int iValue, size_t xBytes )
{
/* The compiler used during development seems to err unless these volatiles are
included at -O3 optimisation.  */
volatile unsigned char * volatile pcDest = ( volatile unsigned char * volatile ) pvDest;
volatile size_t x;

	/* Extremely crude standard library implementations in lieu of having a C
	library. */
	for( x = 0; x < xBytes; x++ )
	{
		pcDest[ x ] = ( unsigned char ) iValue;
	}

	return pvDest;
}
/*-----------------------------------------------------------*/

int memcmp( const void *pvMem1, const void *pvMem2, unsigned long ulBytes )
{
const volatile unsigned char *pucMem1 = pvMem1, *pucMem2 = pvMem2;
register unsigned long x;

	/* Extremely crude standard library implementations in lieu of having a C
	library. */
    for( x = 0; x < ulBytes; x++ )
    {
        if( pucMem1[ x ] != pucMem2[ x ] )
        {
            break;
        }
    }

    return ulBytes - x;
}
/*-----------------------------------------------------------*/

int strcmp( const char *pcString1, const char *pcString2 )
{
volatile int iReturn, iIndex = 0;

	/* Extremely crude standard library implementations in lieu of having a C
	library. */

	while( ( pcString1[ iIndex ] != 0x00 ) && ( pcString2[ iIndex ] != 0x00 ) )
	{
		iIndex++;
	}

	if( ( pcString1[ iIndex ] == 0x00 ) && ( pcString2[ iIndex ] == 0x00 ) )
	{
		iReturn = 0;
	}
	else
	{
		iReturn = ~0;
	}

	return iReturn;
}


