/*
    FreeRTOS V9.0.0rc2 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*******************************************************************************
 * See the URL in the comments within main.c for the location of the online
 * documentation.
 ******************************************************************************/

/* Standard includes. */
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* File system includes. */
#include <redposix.h>

/* The number of bytes read/written to the example files at a time. */
#define fsRAM_BUFFER_SIZE	200

/* The volume prefix is an empty string, for convenience since there is only one
volume in this demo.
*/
#define fsVOLUME_NAME		""

/*-----------------------------------------------------------*/

/*
 * Creates and verifies different files on the volume, demonstrating the use of
 * various different API functions.
 */
void vCreateAndVerifySampleFiles( void );

/*
 * Create a set of example files in the root directory of the volume using
 * f_write().
 */
static void prvCreateDemoFiles( void );

/*
 * Use f_read() to read back and verify the files that were created by
 * prvCreateDemoFiles().
 */
static void prvVerifyDemoFiles( void );

/*-----------------------------------------------------------*/

/* A buffer used to both create content to write to disk, and read content back
from a disk.  Note there is no mutual exclusion on this buffer. */
static char cRAMBuffer[ fsRAM_BUFFER_SIZE ];

/* Names of directories that are created. */
static const char *pcDirectory1 = "/SUB1", *pcDirectory2 = "/SUB1/SUB2";

/*-----------------------------------------------------------*/

void vCreateAndVerifySampleFiles( void )
{
int32_t lStatus;

	/* First initialize the Reliance Edge driver. */
	lStatus = red_init();

	/* Format the volume. */
	if( lStatus == 0 )
	{
		lStatus = red_format( fsVOLUME_NAME );
	}

	/* Mount the volume. */
	if( lStatus == 0 )
	{
		lStatus = red_mount( fsVOLUME_NAME );
	}

	if( lStatus == 0 )
	{
		/* Create a set of files using red_write(). */
		prvCreateDemoFiles();

		/* Read back and verify the files that were created using red_write(). */
		prvVerifyDemoFiles();
	}
}
/*-----------------------------------------------------------*/

static void prvCreateDemoFiles( void )
{
BaseType_t xFileNumber, xWriteNumber;
char cFilePath[ 64 ];
const BaseType_t xMaxFiles = 5;
uint32_t ulEventMask;
int32_t lBytesWritten, lFildes, lStatus;
int iByte;

	/* Save the current transaction point settings. */
	lStatus = red_gettransmask( fsVOLUME_NAME, &ulEventMask );
	configASSERT( lStatus == 0 );

	/* Disable automatic transaction points so that all of the files can be
	created in one atomic operation. */
	lStatus = red_settransmask( fsVOLUME_NAME, RED_TRANSACT_MANUAL );
	configASSERT( lStatus == 0 );

	/* Create xMaxFiles files.  Each created file will be
	( xFileNumber * fsRAM_BUFFER_SIZE ) bytes in length, and filled
	with a different repeating character. */
	for( xFileNumber = 1; xFileNumber <= xMaxFiles; xFileNumber++ )
	{
		/* Generate a file name. */
		sprintf( cFilePath, "/root%03d.txt", xFileNumber );

		/* Print out the file name and the directory into which the file is
		being written. */
		printf( "Creating file %s\r\n", cFilePath );

		/* Open the file, creating the file if it does not already exist. */
		lFildes = red_open( cFilePath, RED_O_CREAT|RED_O_TRUNC|RED_O_WRONLY );
		configASSERT( lFildes != -1 );

		/* Fill the RAM buffer with data that will be written to the file.  This
		is just a repeating ascii character that indicates the file number. */
		memset( cRAMBuffer, ( int ) ( '0' + xFileNumber ), fsRAM_BUFFER_SIZE );

		/* Write the RAM buffer to the opened file a number of times.  The
		number of times the RAM buffer is written to the file depends on the
		file number, so the length of each created file will be different. */
		for( xWriteNumber = 0; xWriteNumber < xFileNumber; xWriteNumber++ )
		{
			lBytesWritten = red_write( lFildes, cRAMBuffer, fsRAM_BUFFER_SIZE );
			configASSERT( lBytesWritten == fsRAM_BUFFER_SIZE );
		}

		/* Close the file so another file can be created. */
		lStatus = red_close( lFildes );
		configASSERT( lStatus == 0 );
	}

	/* Commit a transaction point, atomically adding the set of files to the
	transacted state. */
	lStatus = red_transact( fsVOLUME_NAME );
	configASSERT( lStatus == 0 );

	/* Create a sub directory. */
	printf( "Creating directory %s\r\n", pcDirectory1 );

	lStatus = red_mkdir( pcDirectory1 );
	configASSERT( lStatus == 0 );

	/* Create a subdirectory in the new directory. */
	printf( "Creating directory %s\r\n", pcDirectory2 );

	lStatus = red_mkdir( pcDirectory2 );
	configASSERT( lStatus == 0 );

	/* Generate the file name. */
	sprintf( cFilePath, "%s/file.txt", pcDirectory2 );

	/* Print out the file name and the directory into which the file is being
	written. */
	printf( "Writing file %s\r\n", cFilePath );

	lFildes = red_open( cFilePath, RED_O_CREAT|RED_O_TRUNC|RED_O_WRONLY );

	/* Write the file.  It is filled with incrementing ascii characters starting
	from '0'. */
	for( iByte = 0; iByte < fsRAM_BUFFER_SIZE; iByte++ )
	{
		cRAMBuffer[ iByte ] = ( char ) ( ( int ) '0' + iByte );
	}

	lBytesWritten = red_write( lFildes, cRAMBuffer, fsRAM_BUFFER_SIZE );
	configASSERT( lBytesWritten == fsRAM_BUFFER_SIZE );

	/* Finished so close the file. */
	lStatus = red_close( lFildes );
	configASSERT( lStatus == 0 );

	/* Commit a transaction point, atomically adding the set of files and
	directories to the transacted state. */
	lStatus = red_transact( fsVOLUME_NAME );
	configASSERT( lStatus == 0 );

	/* Restore previous transaction point settings. */
	lStatus = red_settransmask( fsVOLUME_NAME, ulEventMask );
	configASSERT( lStatus == 0 );
}
/*-----------------------------------------------------------*/

static void prvVerifyDemoFiles( void )
{
BaseType_t xFileNumber, xReadNumber;
char cFilePath[ 64 ];
const BaseType_t xMaxFiles = 5;
long lChar;
int32_t lBytesRead, lFildes, lStatus;
int iByte;

	/* Read back the files that were created by prvCreateDemoFiles(). */
	for( xFileNumber = 1; xFileNumber <= xMaxFiles; xFileNumber++ )
	{
		/* Generate the file name. */
		sprintf( cFilePath, "/root%03d.txt", xFileNumber );

		/* Print out the file name and the directory from which the file is
		being read. */
		printf( "Reading file %s\r\n", cFilePath );

		/* Open the file for reading. */
		lFildes = red_open( cFilePath, RED_O_RDONLY );
		configASSERT( lFildes != -1 );

		/* Read the file into the RAM buffer, checking the file contents are as
		expected.  The size of the file depends on the file number. */
		for( xReadNumber = 0; xReadNumber < xFileNumber; xReadNumber++ )
		{
			/* Start with the RAM buffer clear. */
			memset( cRAMBuffer, 0x00, fsRAM_BUFFER_SIZE );

			lBytesRead = red_read( lFildes, cRAMBuffer, fsRAM_BUFFER_SIZE );
			configASSERT( lBytesRead == fsRAM_BUFFER_SIZE );

			/* Check the RAM buffer is filled with the expected data.  Each
			file contains a different repeating ascii character that indicates
			the number of the file. */
			for( lChar = 0; lChar < fsRAM_BUFFER_SIZE; lChar++ )
			{
				configASSERT( cRAMBuffer[ lChar ] == ( '0' + ( char ) xFileNumber ) );
			}
		}

		/* Close the file. */
		lStatus = red_close( lFildes );
		configASSERT( lStatus == 0 );
	}

	/* Generate the file name. */
	sprintf( cFilePath, "%s/file.txt", pcDirectory2 );

	/* Print out the file name and the directory from which the file is being
	read. */
	printf( "Reading file %s\r\n", cFilePath );

	/* This time the file is opened for reading. */
	lFildes = red_open( cFilePath, RED_O_RDONLY );
	configASSERT( lFildes != -1 );

	/* Read the file. */
	lBytesRead = red_read( lFildes, cRAMBuffer, fsRAM_BUFFER_SIZE );
	configASSERT( lBytesRead == fsRAM_BUFFER_SIZE );

	/* Verify the file 1 byte at a time. */
	for( iByte = 0; iByte < fsRAM_BUFFER_SIZE; iByte++ )
	{
		configASSERT( cRAMBuffer[ iByte ] == ( char ) ( ( int ) '0' + iByte ) );
	}

	/* Finished so close the file. */
	lStatus = red_close( lFildes );
	configASSERT( lStatus == 0 );
}




