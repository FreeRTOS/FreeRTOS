/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd.
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

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS+CLI includes. */
#include "FreeRTOS_CLI.h"

/* File system includes. */
#include "fat_sl.h"
#include "api_mdriver_ram.h"
#include "test.h"

#ifdef _WINDOWS_
	#define snprintf _snprintf
#endif

#define cliNEW_LINE		"\r\n"

/*******************************************************************************
 * See the URL in the comments within main.c for the location of the online
 * documentation.
 ******************************************************************************/

/*
 * Print out information on a single file.
 */
static void prvCreateFileInfoString( char *pcBuffer, F_FIND *pxFindStruct );

/*
 * Copies an existing file into a newly created file.
 */
static portBASE_TYPE prvPerformCopy( const char *pcSourceFile,
							int32_t lSourceFileLength,
							const char *pcDestinationFile,
							char *pxWriteBuffer,
							size_t xWriteBufferLen );

/*
 * Implements the DIR command.
 */
static portBASE_TYPE prvDIRCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the CD command.
 */
static portBASE_TYPE prvCDCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the DEL command.
 */
static portBASE_TYPE prvDELCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the TYPE command.
 */
static portBASE_TYPE prvTYPECommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the COPY command.
 */
static portBASE_TYPE prvCOPYCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the TEST command.
 */
static portBASE_TYPE prvTESTFSCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/* Structure that defines the DIR command line command, which lists all the
files in the current directory. */
static const CLI_Command_Definition_t xDIR =
{
	"dir", /* The command string to type. */
	"\r\ndir:\r\n Lists the files in the current directory\r\n",
	prvDIRCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/* Structure that defines the CD command line command, which changes the
working directory. */
static const CLI_Command_Definition_t xCD =
{
	"cd", /* The command string to type. */
	"\r\ncd <dir name>:\r\n Changes the working directory\r\n",
	prvCDCommand, /* The function to run. */
	1 /* One parameter is expected. */
};

/* Structure that defines the TYPE command line command, which prints the
contents of a file to the console. */
static const CLI_Command_Definition_t xTYPE =
{
	"type", /* The command string to type. */
	"\r\ntype <filename>:\r\n Prints file contents to the terminal\r\n",
	prvTYPECommand, /* The function to run. */
	1 /* One parameter is expected. */
};

/* Structure that defines the DEL command line command, which deletes a file. */
static const CLI_Command_Definition_t xDEL =
{
	"del", /* The command string to type. */
	"\r\ndel <filename>:\r\n deletes a file or directory\r\n",
	prvDELCommand, /* The function to run. */
	1 /* One parameter is expected. */
};

/* Structure that defines the COPY command line command, which deletes a file. */
static const CLI_Command_Definition_t xCOPY =
{
	"copy", /* The command string to type. */
	"\r\ncopy <source file> <dest file>:\r\n Copies <source file> to <dest file>\r\n",
	prvCOPYCommand, /* The function to run. */
	2 /* Two parameters are expected. */
};

/* Structure that defines the TEST command line command, which executes some
file system driver tests. */
static const CLI_Command_Definition_t xTEST_FS =
{
	"test-fs", /* The command string to type. */
	"\r\ntest-fs:\r\n Executes file system tests.  ALL FILES WILL BE DELETED!!!\r\n",
	prvTESTFSCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/*-----------------------------------------------------------*/

void vRegisterFileSystemCLICommands( void )
{
	/* Register all the command line commands defined immediately above. */
	FreeRTOS_CLIRegisterCommand( &xDIR );
	FreeRTOS_CLIRegisterCommand( &xCD );
	FreeRTOS_CLIRegisterCommand( &xTYPE );
	FreeRTOS_CLIRegisterCommand( &xDEL );
	FreeRTOS_CLIRegisterCommand( &xCOPY );
	FreeRTOS_CLIRegisterCommand( &xTEST_FS );
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvTYPECommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
portBASE_TYPE xParameterStringLength, xReturn = pdTRUE;
static F_FILE *pxFile = NULL;
int iChar;
size_t xByte;
size_t xColumns = 50U;

	/* Ensure there is always a null terminator after each character written. */
	memset( pcWriteBuffer, 0x00, xWriteBufferLen );

	/* Ensure the buffer leaves space for the \r\n. */
	configASSERT( xWriteBufferLen > ( strlen( cliNEW_LINE ) * 2 ) );
	xWriteBufferLen -= strlen( cliNEW_LINE );

	if( xWriteBufferLen < xColumns )
	{
		/* Ensure the loop that uses xColumns as an end condition does not
		write off the end of the buffer. */
		xColumns = xWriteBufferLen;
	}

	if( pxFile == NULL )
	{
		/* The file has not been opened yet.  Find the file name. */
		pcParameter = FreeRTOS_CLIGetParameter
						(
							pcCommandString,		/* The command string itself. */
							1,						/* Return the first parameter. */
							&xParameterStringLength	/* Store the parameter string length. */
						);

		/* Sanity check something was returned. */
		configASSERT( pcParameter );

		/* Attempt to open the requested file. */
		pxFile = f_open( ( const char * ) pcParameter, "r" );
	}

	if( pxFile != NULL )
	{
		/* Read the next chunk of data from the file. */
		for( xByte = 0; xByte < xColumns; xByte++ )
		{
			iChar = f_getc( pxFile );

			if( iChar == -1 )
			{
				/* No more characters to return. */
				f_close( pxFile );
				pxFile = NULL;
				break;
			}
			else
			{
				pcWriteBuffer[ xByte ] = ( char ) iChar;
			}
		}
	}

	if( pxFile == NULL )
	{
		/* Either the file was not opened, or all the data from the file has
		been returned and the file is now closed. */
		xReturn = pdFALSE;
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return xReturn;
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvCDCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
portBASE_TYPE xParameterStringLength;
unsigned char ucReturned;
size_t xStringLength;

	/* Obtain the parameter string. */
	pcParameter = FreeRTOS_CLIGetParameter
					(
						pcCommandString,		/* The command string itself. */
						1,						/* Return the first parameter. */
						&xParameterStringLength	/* Store the parameter string length. */
					);

	/* Sanity check something was returned. */
	configASSERT( pcParameter );

	/* Attempt to move to the requested directory. */
	ucReturned = f_chdir( pcParameter );

	if( ucReturned == F_NO_ERROR )
	{
		sprintf( pcWriteBuffer, "In: " );
		xStringLength = strlen( ( const char * ) pcWriteBuffer );
		f_getcwd( &( pcWriteBuffer[ xStringLength ] ), ( unsigned char ) ( xWriteBufferLen - xStringLength ) );
	}
	else
	{
		sprintf( pcWriteBuffer, "Error" );
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvDIRCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
static F_FIND *pxFindStruct = NULL;
unsigned char ucReturned;
portBASE_TYPE xReturn = pdFALSE;

	/* This assumes pcWriteBuffer is long enough. */
	( void ) pcCommandString;

	/* Ensure the buffer leaves space for the \r\n. */
	configASSERT( xWriteBufferLen > ( strlen( cliNEW_LINE ) * 2 ) );
	xWriteBufferLen -= strlen( cliNEW_LINE );

	if( pxFindStruct == NULL )
	{
		/* This is the first time this function has been executed since the Dir
		command was run.  Create the find structure. */
		pxFindStruct = ( F_FIND * ) pvPortMalloc( sizeof( F_FIND ) );

		if( pxFindStruct != NULL )
		{
			ucReturned = f_findfirst( "*.*", pxFindStruct );

			if( ucReturned == F_NO_ERROR )
			{
				prvCreateFileInfoString( pcWriteBuffer, pxFindStruct );
				xReturn = pdPASS;
			}
			else
			{
				snprintf( pcWriteBuffer, xWriteBufferLen, "Error: f_findfirst() failed." );
			}
		}
		else
		{
			snprintf( pcWriteBuffer, xWriteBufferLen, "Failed to allocate RAM (using heap_4.c will prevent fragmentation)." );
		}
	}
	else
	{
		/* The find struct has already been created.  Find the next file in
		the directory. */
		ucReturned = f_findnext( pxFindStruct );

		if( ucReturned == F_NO_ERROR )
		{
			prvCreateFileInfoString( pcWriteBuffer, pxFindStruct );
			xReturn = pdPASS;
		}
		else
		{
			/* There are no more files.  Free the find structure. */
			vPortFree( pxFindStruct );
			pxFindStruct = NULL;

			/* No string to return. */
			pcWriteBuffer[ 0 ] = 0x00;
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return xReturn;
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvDELCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
portBASE_TYPE xParameterStringLength;
unsigned char ucReturned;

	/* This function assumes xWriteBufferLen is large enough! */
	( void ) xWriteBufferLen;

	/* Obtain the parameter string. */
	pcParameter = FreeRTOS_CLIGetParameter
					(
						pcCommandString,		/* The command string itself. */
						1,						/* Return the first parameter. */
						&xParameterStringLength	/* Store the parameter string length. */
					);

	/* Sanity check something was returned. */
	configASSERT( pcParameter );

	/* Attempt to delete the file. */
	ucReturned = f_delete( ( const char * ) pcParameter );

	if( ucReturned == F_NO_ERROR )
	{
		sprintf( pcWriteBuffer, "%s was deleted", pcParameter );
	}
	else
	{
		sprintf( pcWriteBuffer, "Error" );
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvTESTFSCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
unsigned portBASE_TYPE uxOriginalPriority;

	/* Avoid compiler warnings. */
	( void ) xWriteBufferLen;
	( void ) pcCommandString;

	/* Limitations in the interaction with the Windows TCP/IP stack require
	the command console to run at the idle priority.  Raise the priority for
	the duration of the tests to ensure there are not multiple switches to the
	idle task as in the simulated environment the idle task hook function may
	include a (relatively) long delay. */
	uxOriginalPriority = uxTaskPriorityGet( NULL );
	vTaskPrioritySet( NULL, configMAX_PRIORITIES - 1 );

	f_dotest( 0 );

	/* Reset back to the original priority. */
	vTaskPrioritySet( NULL, uxOriginalPriority );

	sprintf( pcWriteBuffer, "%s", "Test results were sent to Windows console" );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvCOPYCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
char *pcSourceFile;
const char *pcDestinationFile;
portBASE_TYPE xParameterStringLength;
long lSourceLength, lDestinationLength = 0;

	/* Obtain the name of the destination file. */
	pcDestinationFile = FreeRTOS_CLIGetParameter
						(
							pcCommandString,		/* The command string itself. */
							2,						/* Return the second parameter. */
							&xParameterStringLength	/* Store the parameter string length. */
						);

	/* Sanity check something was returned. */
	configASSERT( pcDestinationFile );

	/* Obtain the name of the source file. */
	pcSourceFile = ( char * ) FreeRTOS_CLIGetParameter
								(
									pcCommandString,		/* The command string itself. */
									1,						/* Return the first parameter. */
									&xParameterStringLength	/* Store the parameter string length. */
								);

	/* Sanity check something was returned. */
	configASSERT( pcSourceFile );

	/* Terminate the string. */
	pcSourceFile[ xParameterStringLength ] = 0x00;

	/* See if the source file exists, obtain its length if it does. */
	lSourceLength = f_filelength( ( const char * ) pcSourceFile );

	if( lSourceLength == 0 )
	{
		sprintf( pcWriteBuffer, "Source file does not exist" );
	}
	else
	{
		/* See if the destination file exists. */
		lDestinationLength = f_filelength( ( const char * ) pcDestinationFile );

		if( lDestinationLength != 0 )
		{
			sprintf( pcWriteBuffer, "Error: Destination file already exists" );
		}
	}

	/* Continue only if the source file exists and the destination file does
	not exist. */
	if( ( lSourceLength != 0 ) && ( lDestinationLength == 0 ) )
	{
		if( prvPerformCopy( pcSourceFile, lSourceLength, pcDestinationFile, pcWriteBuffer, xWriteBufferLen ) == pdPASS )
		{
			sprintf( pcWriteBuffer, "Copy made" );
		}
		else
		{
			sprintf( pcWriteBuffer, "Error during copy" );
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvPerformCopy( const char *pcSourceFile,
									int32_t lSourceFileLength,
									const char *pcDestinationFile,
									char *pxWriteBuffer,
									size_t xWriteBufferLen )
{
int32_t lBytesRead = 0, lBytesToRead, lBytesRemaining;
F_FILE *pxFile;
portBASE_TYPE xReturn = pdPASS;

	/* NOTE:  Error handling has been omitted for clarity. */

	while( lBytesRead < lSourceFileLength )
	{
		/* How many bytes are left? */
		lBytesRemaining = lSourceFileLength - lBytesRead;

		/* How many bytes should be read this time around the loop.  Can't
		read more bytes than will fit into the buffer. */
		if( lBytesRemaining > ( long ) xWriteBufferLen )
		{
			lBytesToRead = ( long ) xWriteBufferLen;
		}
		else
		{
			lBytesToRead = lBytesRemaining;
		}

		/* Open the source file, seek past the data that has already been
		read from the file, read the next block of data, then close the
		file again so the destination file can be opened. */
		pxFile = f_open( ( const char * ) pcSourceFile, "r" );
		if( pxFile != NULL )
		{
			f_seek( pxFile, lBytesRead, F_SEEK_SET );
			f_read( pxWriteBuffer, lBytesToRead, 1, pxFile );
			f_close( pxFile );
		}
		else
		{
			xReturn = pdFAIL;
			break;
		}

		/* Open the destination file and write the block of data to the end of
		the file. */
		pxFile = f_open( ( const char * ) pcDestinationFile, "a" );
		if( pxFile != NULL )
		{
			f_write( pxWriteBuffer, lBytesToRead, 1, pxFile );
			f_close( pxFile );
		}
		else
		{
			xReturn = pdFAIL;
			break;
		}

		lBytesRead += lBytesToRead;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvCreateFileInfoString( char *pcBuffer, F_FIND *pxFindStruct )
{
const char *pcWritableFile = "writable file", *pcReadOnlyFile = "read only file", *pcDirectory = "directory";
const char * pcAttrib;

	/* Point pcAttrib to a string that describes the file. */
	if( ( pxFindStruct->attr & F_ATTR_DIR ) != 0 )
	{
		pcAttrib = pcDirectory;
	}
	else if( pxFindStruct->attr & F_ATTR_READONLY )
	{
		pcAttrib = pcReadOnlyFile;
	}
	else
	{
		pcAttrib = pcWritableFile;
	}

	/* Create a string that includes the file name, the file size and the
	attributes string. */
	sprintf( pcBuffer, "%s [%s] [size=%d]", pxFindStruct->filename, pcAttrib, pxFindStruct->filesize );
}
