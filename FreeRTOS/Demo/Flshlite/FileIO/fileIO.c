/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#include <stdio.h>
#include <conio.h>
#include <string.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "fileio.h"

void vDisplayMessage( const char * const pcMessageToPrint )
{
	#ifdef USE_STDIO
		taskENTER_CRITICAL();
			printf( "%s", pcMessageToPrint );
			fflush( stdout );
		taskEXIT_CRITICAL();
	#else
		/* Stop warnings. */
		( void ) pcMessageToPrint;
	#endif
}
/*-----------------------------------------------------------*/

void vWriteMessageToDisk( const char * const pcMessage )
{
#ifdef USE_STDIO
const char * const pcFileName = "c:\\RTOSlog.txt";
const char * const pcSeparator = "\r\n-----------------------\r\n";
FILE *pf;

	taskENTER_CRITICAL();
	{	
		pf = fopen( pcFileName, "a" );
		if( pf != NULL )
		{
			fwrite( pcMessage, strlen( pcMessage ), ( unsigned short ) 1, pf );
			fwrite( pcSeparator, strlen( pcSeparator ), ( unsigned short ) 1, pf );
			fclose( pf );
		}
	}
	taskEXIT_CRITICAL();
#else
	/* Stop warnings. */
	( void ) pcMessage;
#endif /*USE_STDIO*/
}
/*-----------------------------------------------------------*/

void vWriteBufferToDisk( const char * const pcBuffer, unsigned long ulBufferLength )
{
#ifdef USE_STDIO
const char * const pcFileName = "c:\\trace.bin";
FILE *pf;

	taskENTER_CRITICAL();
	{
		pf = fopen( pcFileName, "wb" );
		if( pf )
		{
			fwrite( pcBuffer, ( size_t ) ulBufferLength, ( unsigned short ) 1, pf );
			fclose( pf );
		}
	}
	taskEXIT_CRITICAL();
#else
	/* Stop warnings. */
	( void ) pcBuffer;
    ( void ) ulBufferLength;
#endif /*USE_STDIO*/
}


