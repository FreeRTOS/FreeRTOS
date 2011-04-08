/*
    FreeRTOS V7.0.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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


