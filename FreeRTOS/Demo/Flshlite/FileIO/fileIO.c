/*
    FreeRTOS V8.1.0 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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


