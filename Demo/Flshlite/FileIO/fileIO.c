/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

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

void vDisplayMessage( const portCHAR * const pcMessageToPrint )
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

void vWriteMessageToDisk( const portCHAR * const pcMessage )
{
#ifdef USE_STDIO
const portCHAR * const pcFileName = "c:\\RTOSlog.txt";
const portCHAR * const pcSeparator = "\r\n-----------------------\r\n";
FILE *pf;

	taskENTER_CRITICAL();
	{	
		pf = fopen( pcFileName, "a" );
		if( pf != NULL )
		{
			fwrite( pcMessage, strlen( pcMessage ), ( unsigned portSHORT ) 1, pf );
			fwrite( pcSeparator, strlen( pcSeparator ), ( unsigned portSHORT ) 1, pf );
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

void vWriteBufferToDisk( const portCHAR * const pcBuffer, unsigned portLONG ulBufferLength )
{
#ifdef USE_STDIO
const portCHAR * const pcFileName = "c:\\trace.bin";
FILE *pf;

	taskENTER_CRITICAL();
	{
		pf = fopen( pcFileName, "wb" );
		if( pf )
		{
			fwrite( pcBuffer, ( size_t ) ulBufferLength, ( unsigned portSHORT ) 1, pf );
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


