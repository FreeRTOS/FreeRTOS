/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* FreeRTOS+CLI includes. */
#include "FreeRTOS_CLI.h"

/* File system includes. */
#include "fat_sl.h"
#include "api_mdriver_ram.h"

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
static BaseType_t prvPerformCopy( const char *pcSourceFile,
									int32_t lSourceFileLength,
									const char *pcDestinationFile,
									char *pxWriteBuffer,
									size_t xWriteBufferLen );

/*
 * Implements the DIR command.
 */
static BaseType_t prvDIRCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the CD command.
 */
static BaseType_t prvCDCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the DEL command.
 */
static BaseType_t prvDELCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the TYPE command.
 */
static BaseType_t prvTYPECommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the COPY command.
 */
static BaseType_t prvCOPYCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

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


/*-----------------------------------------------------------*/

void vRegisterFileSystemCLICommands( void )
{
	/* Register all the command line commands defined immediately above. */
	FreeRTOS_CLIRegisterCommand( &xDIR );
	FreeRTOS_CLIRegisterCommand( &xCD );
	FreeRTOS_CLIRegisterCommand( &xTYPE );
	FreeRTOS_CLIRegisterCommand( &xDEL );
	FreeRTOS_CLIRegisterCommand( &xCOPY );
}
/*-----------------------------------------------------------*/

static BaseType_t prvTYPECommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
BaseType_t xParameterStringLength, xReturn = pdTRUE;
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
		pxFile = f_open( pcParameter, "r" );
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

static BaseType_t prvCDCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
BaseType_t xParameterStringLength;
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
		xStringLength = strlen( pcWriteBuffer );
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

static BaseType_t prvDIRCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
static F_FIND *pxFindStruct = NULL;
unsigned char ucReturned;
BaseType_t xReturn = pdFALSE;

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

static BaseType_t prvDELCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
BaseType_t xParameterStringLength;
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
	ucReturned = f_delete( pcParameter );

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

static BaseType_t prvCOPYCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
char *pcSourceFile, *pcDestinationFile;
BaseType_t xParameterStringLength;
long lSourceLength, lDestinationLength = 0;

	/* Obtain the name of the destination file. */
	pcDestinationFile = ( char * ) FreeRTOS_CLIGetParameter
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
	lSourceLength = f_filelength( pcSourceFile );

	if( lSourceLength == 0 )
	{
		sprintf( pcWriteBuffer, "Source file does not exist" );
	}
	else
	{
		/* See if the destination file exists. */
		lDestinationLength = f_filelength( pcDestinationFile );

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

static BaseType_t prvPerformCopy( const char *pcSourceFile,
									int32_t lSourceFileLength,
									const char *pcDestinationFile,
									char *pxWriteBuffer,
									size_t xWriteBufferLen )
{
int32_t lBytesRead = 0, lBytesToRead, lBytesRemaining;
F_FILE *pxFile;
BaseType_t xReturn = pdPASS;

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
		pxFile = f_open( pcSourceFile, "r" );
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
		pxFile = f_open( pcDestinationFile, "a" );
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
	sprintf( pcBuffer, "%s [%s] [size=%d]", pxFindStruct->filename, pcAttrib, ( int ) pxFindStruct->filesize );
}
