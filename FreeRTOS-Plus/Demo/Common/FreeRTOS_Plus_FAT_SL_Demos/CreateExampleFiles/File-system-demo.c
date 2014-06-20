/*
    FreeRTOS V8.0.1 - Copyright (C) 2014 Real Time Engineers Ltd.
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

/*******************************************************************************
 * See the URL in the comments within main.c for the location of the online
 * documentation.
 ******************************************************************************/

/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* File system includes. */
#include "fat_sl.h"
#include "api_mdriver_ram.h"

/* 8.3 format, plus null terminator. */
#define fsMAX_FILE_NAME_LEN				13

/* The number of bytes read/written to the example files at a time. */
#define fsRAM_BUFFER_SIZE 				200

/* The number of bytes written to the file that uses f_putc() and f_getc(). */
#define fsPUTC_FILE_SIZE				100

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
static void prvCreateDemoFilesUsing_f_write( void );

/*
 * Use f_read() to read back and verify the files that were created by
 * prvCreateDemoFilesUsing_f_write().
 */
static void prvVerifyDemoFileUsing_f_read( void );

/*
 * Create an example file in a sub-directory using f_putc().
 */
static void prvCreateDemoFileUsing_f_putc( void );

/*
 * Use f_getc() to read back and verify the file that was created by
 * prvCreateDemoFileUsing_f_putc().
 */
static void prvVerifyDemoFileUsing_f_getc( void );

/*-----------------------------------------------------------*/

/* A buffer used to both create content to write to disk, and read content back
from a disk.  Note there is no mutual exclusion on this buffer. */
static char cRAMBuffer[ fsRAM_BUFFER_SIZE ];

/* Names of directories that are created. */
static const char *pcRoot = "/", *pcDirectory1 = "SUB1", *pcDirectory2 = "SUB2", *pcFullPath = "/SUB1/SUB2";

/*-----------------------------------------------------------*/

void vCreateAndVerifySampleFiles( void )
{
unsigned char ucStatus;

	/* First create the volume. */
	ucStatus = f_initvolume( ram_initfunc );

	/* It is expected that the volume is not formatted. */
	if( ucStatus == F_ERR_NOTFORMATTED )
	{
		/* Format the created volume. */
		ucStatus = f_format( F_FAT12_MEDIA );
	}

	if( ucStatus == F_NO_ERROR )
	{
		/* Create a set of files using f_write(). */
		prvCreateDemoFilesUsing_f_write();

		/* Read back and verify the files that were created using f_write(). */
		prvVerifyDemoFileUsing_f_read();

		/* Create sub directories two deep then create a file using putc. */
		prvCreateDemoFileUsing_f_putc();

		/* Read back and verify the file created by
		prvCreateDemoFileUsing_f_putc(). */
		prvVerifyDemoFileUsing_f_getc();
	}
}
/*-----------------------------------------------------------*/

static void prvCreateDemoFilesUsing_f_write( void )
{
BaseType_t xFileNumber, xWriteNumber;
char cFileName[ fsMAX_FILE_NAME_LEN ];
const BaseType_t xMaxFiles = 5;
long lItemsWritten;
F_FILE *pxFile;

	/* Create xMaxFiles files.  Each created file will be
	( xFileNumber * fsRAM_BUFFER_SIZE ) bytes in length, and filled
	with a different repeating character. */
	for( xFileNumber = 1; xFileNumber <= xMaxFiles; xFileNumber++ )
	{
		/* Generate a file name. */
		sprintf( cFileName, "root%03d.txt", ( int ) xFileNumber );

		/* Obtain the current working directory and print out the file name and
		the	directory into which the file is being written. */
		f_getcwd( cRAMBuffer, fsRAM_BUFFER_SIZE );

		/* Open the file, creating the file if it does not already exist. */
		pxFile = f_open( cFileName, "w" );
		configASSERT( pxFile );

		/* Fill the RAM buffer with data that will be written to the file.  This
		is just a repeating ascii character that indicates the file number. */
		memset( cRAMBuffer, ( int ) ( '0' + xFileNumber ), fsRAM_BUFFER_SIZE );

		/* Write the RAM buffer to the opened file a number of times.  The
		number of times the RAM buffer is written to the file depends on the
		file number, so the length of each created file will be different. */
		for( xWriteNumber = 0; xWriteNumber < xFileNumber; xWriteNumber++ )
		{
			lItemsWritten = f_write( cRAMBuffer, fsRAM_BUFFER_SIZE, 1, pxFile );
			configASSERT( lItemsWritten == 1 );
		}

		/* Close the file so another file can be created. */
		f_close( pxFile );
	}
}
/*-----------------------------------------------------------*/

static void prvVerifyDemoFileUsing_f_read( void )
{
BaseType_t xFileNumber, xReadNumber;
char cFileName[ fsMAX_FILE_NAME_LEN ];
const BaseType_t xMaxFiles = 5;
long lItemsRead, lChar;
F_FILE *pxFile;

	/* Read back the files that were created by
	prvCreateDemoFilesUsing_f_write(). */
	for( xFileNumber = 1; xFileNumber <= xMaxFiles; xFileNumber++ )
	{
		/* Generate the file name. */
		sprintf( cFileName, "root%03d.txt", ( int ) xFileNumber );

		/* Obtain the current working directory and print out the file name and
		the	directory from which the file is being read. */
		f_getcwd( cRAMBuffer, fsRAM_BUFFER_SIZE );

		/* Open the file for reading. */
		pxFile = f_open( cFileName, "r" );
		configASSERT( pxFile );

		/* Read the file into the RAM buffer, checking the file contents are as
		expected.  The size of the file depends on the file number. */
		for( xReadNumber = 0; xReadNumber < xFileNumber; xReadNumber++ )
		{
			/* Start with the RAM buffer clear. */
			memset( cRAMBuffer, 0x00, fsRAM_BUFFER_SIZE );

			lItemsRead = f_read( cRAMBuffer, fsRAM_BUFFER_SIZE, 1, pxFile );
			configASSERT( lItemsRead == 1 );

			/* Check the RAM buffer is filled with the expected data.  Each
			file contains a different repeating ascii character that indicates
			the number of the file. */
			for( lChar = 0; lChar < fsRAM_BUFFER_SIZE; lChar++ )
			{
				configASSERT( cRAMBuffer[ lChar ] == ( '0' + ( char ) xFileNumber ) );
			}
		}

		/* Close the file. */
		f_close( pxFile );
	}
}
/*-----------------------------------------------------------*/

static void prvCreateDemoFileUsing_f_putc( void )
{
unsigned char ucReturn;
int iByte, iReturned;
F_FILE *pxFile;
char cFileName[ fsMAX_FILE_NAME_LEN ];

	/* Obtain and print out the working directory. */
	f_getcwd( cRAMBuffer, fsRAM_BUFFER_SIZE );

	/* Create a sub directory. */
	ucReturn = f_mkdir( pcDirectory1 );
	configASSERT( ucReturn == F_NO_ERROR );

	/* Move into the created sub-directory. */
	ucReturn = f_chdir( pcDirectory1 );
	configASSERT( ucReturn == F_NO_ERROR );

	/* Obtain and print out the working directory. */
	f_getcwd( cRAMBuffer, fsRAM_BUFFER_SIZE );

	/* Create a subdirectory in the new directory. */
	ucReturn = f_mkdir( pcDirectory2 );
	configASSERT( ucReturn == F_NO_ERROR );

	/* Move into the directory just created - now two directories down from
	the root. */
	ucReturn = f_chdir( pcDirectory2 );
	configASSERT( ucReturn == F_NO_ERROR );

	/* Obtain and print out the working directory. */
	f_getcwd( cRAMBuffer, fsRAM_BUFFER_SIZE );
	configASSERT( strcmp( cRAMBuffer, pcFullPath ) == 0 );

	/* Generate the file name. */
	sprintf( cFileName, "%s.txt", pcDirectory2 );

	/* Print out the file name and the directory into which the file is being
	written. */
	pxFile = f_open( cFileName, "w" );

	/* Create a file 1 byte at a time.  The file is filled with incrementing
	ascii characters starting from '0'. */
	for( iByte = 0; iByte < fsPUTC_FILE_SIZE; iByte++ )
	{
		iReturned = f_putc( ( ( int ) '0' + iByte ), pxFile );
		configASSERT( iReturned ==  ( ( int ) '0' + iByte ) );
	}

	/* Finished so close the file. */
	f_close( pxFile );

	/* Move back to the root directory. */
	ucReturn = f_chdir( "../.." );
	configASSERT( ucReturn == F_NO_ERROR );

	/* Obtain and print out the working directory. */
	f_getcwd( cRAMBuffer, fsRAM_BUFFER_SIZE );
	configASSERT( strcmp( cRAMBuffer, pcRoot ) == 0 );
}
/*-----------------------------------------------------------*/

static void prvVerifyDemoFileUsing_f_getc( void )
{
unsigned char ucReturn;
int iByte, iReturned;
F_FILE *pxFile;
char cFileName[ fsMAX_FILE_NAME_LEN ];

	/* Move into the directory in which the file was created. */
	ucReturn = f_chdir( pcFullPath );
	configASSERT( ucReturn == F_NO_ERROR );

	/* Obtain and print out the working directory. */
	f_getcwd( cRAMBuffer, fsRAM_BUFFER_SIZE );
	configASSERT( strcmp( cRAMBuffer, pcFullPath ) == 0 );

	/* Generate the file name. */
	sprintf( cFileName, "%s.txt", pcDirectory2 );

	/* This time the file is opened for reading. */
	pxFile = f_open( cFileName, "r" );

	/* Read the file 1 byte at a time. */
	for( iByte = 0; iByte < fsPUTC_FILE_SIZE; iByte++ )
	{
		iReturned = f_getc( pxFile );
		configASSERT( iReturned ==  ( ( int ) '0' + iByte ) );
	}

	/* Finished so close the file. */
	f_close( pxFile );

	/* Move back to the root directory. */
	ucReturn = f_chdir( "../.." );
	configASSERT( ucReturn == F_NO_ERROR );

	/* Obtain and print out the working directory. */
	f_getcwd( cRAMBuffer, fsRAM_BUFFER_SIZE );
}




