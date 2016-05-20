/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
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
#include <redposix.h>
#include <redtests.h>

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
static void prvCreateFileInfoString( char *pcBuffer, REDDIRENT *pxDirent );

/*
 * Copies an existing file into a newly created file.
 */
static BaseType_t prvPerformCopy( int32_t lSourceFildes,
							int32_t lDestinationFiledes,
							char *pxWriteBuffer,
							size_t xWriteBufferLen );

/*
 * Implements the DIR command.
 */
static BaseType_t prvDIRCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the DEL command.
 */
static BaseType_t prvDELCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the TYPE command.
 */
static BaseType_t prvTYPECommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the APPEND command.
 */
static BaseType_t prvAPPENDCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the COPY command.
 */
static BaseType_t prvCOPYCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the CREATE command.
 */
static BaseType_t prvCREATECommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the MKDIR command.
 */
static BaseType_t prvMKDIRCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the RENAME command.
 */
static BaseType_t prvRENAMECommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the LINK command.
 */
static BaseType_t prvLINKCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the STAT command.
 */
static BaseType_t prvSTATCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the STATFS command.
 */
static BaseType_t prvSTATFSCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the FORMAT command.
 */
static BaseType_t prvFORMATCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the TRANSACT command.
 */
static BaseType_t prvTRANSACTCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the TRANSMASKGET command.
 */
static BaseType_t prvTRANSMASKGETCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the TRANSMASKSET command.
 */
static BaseType_t prvTRANSMASKSETCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the ABORT command.
 */
static BaseType_t prvABORTCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );

/*
 * Implements the TEST command.
 */
static BaseType_t prvTESTFSCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString );


/* Structure that defines the DIR command line command, which lists all the
files in the current directory. */
static const CLI_Command_Definition_t xDIR =
{
	"dir", /* The command string to type. */
	"\r\ndir <filename>:\r\n Lists the files in the named directory\r\n",
	prvDIRCommand, /* The function to run. */
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

/* Structure that defines the APPEND command line command, which appends data
to a file. */
static const CLI_Command_Definition_t xAPPEND =
{
	"append", /* The command string to type. */
	"\r\nappend <filename> <character> <length>:\r\n Appends data to a file (created if it does not exist)\r\n",
	prvAPPENDCommand, /* The function to run. */
	3 /* Three parameters are expected. */
};

/* Structure that defines the DEL command line command, which deletes a file. */
static const CLI_Command_Definition_t xDEL =
{
	"del", /* The command string to type. */
	"\r\ndel <filename>:\r\n deletes a file or directory\r\n",
	prvDELCommand, /* The function to run. */
	1 /* One parameter is expected. */
};

/* Structure that defines the COPY command line command, which copies a file. */
static const CLI_Command_Definition_t xCOPY =
{
	"copy", /* The command string to type. */
	"\r\ncopy <source file> <dest file>:\r\n Copies <source file> to <dest file>\r\n",
	prvCOPYCommand, /* The function to run. */
	2 /* Two parameters are expected. */
};

/* Structure that defines the CREATE command line command, which creates an
empty file. */
static const CLI_Command_Definition_t xCREATE =
{
	"create", /* The command string to type. */
	"\r\ncreate <filename>:\r\n Creates an empty file\r\n",
	prvCREATECommand, /* The function to run. */
	1 /* One parameter is expected. */
};

/* Structure that defines the MKDIR command line command, which creates an
empty directory. */
static const CLI_Command_Definition_t xMKDIR =
{
	"mkdir", /* The command string to type. */
	"\r\nmkdir <filename>:\r\n Creates an empty directory\r\n",
	prvMKDIRCommand, /* The function to run. */
	1 /* One parameter is expected. */
};

/* Structure that defines the RENAME command line command, which renames a file. */
static const CLI_Command_Definition_t xRENAME =
{
	"rename", /* The command string to type. */
	"\r\nrename <source file> <dest file>:\r\n Rename <source file> to <dest file>\r\n",
	prvRENAMECommand, /* The function to run. */
	2 /* Two parameters are expected. */
};

/* Structure that defines the LINK command line command, which creates a hard
link. */
static const CLI_Command_Definition_t xLINK =
{
	"link", /* The command string to type. */
	"\r\nlink <source file> <dest file>:\r\n Create hard link <dest file> pointing at <source file>\r\n",
	prvLINKCommand, /* The function to run. */
	2 /* Two parameters are expected. */
};

/* Structure that defines the STAT command line command, which shows various
information about a file. */
static const CLI_Command_Definition_t xSTAT =
{
	"stat", /* The command string to type. */
	"\r\nstat <filename>:\r\n Show file information\r\n",
	prvSTATCommand, /* The function to run. */
	1 /* One parameter is expected. */
};

/* Structure that defines the STATFS command line command, which shows various
file system information. */
static const CLI_Command_Definition_t xSTATFS =
{
	"statfs", /* The command string to type. */
	"\r\nstatfs:\r\n Show file system information.\r\n",
	prvSTATFSCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/* Structure that defines the FORMAT command line command, which re-formats the
file system. */
static const CLI_Command_Definition_t xFORMAT =
{
	"format", /* The command string to type. */
	"\r\nformat:\r\n Re-formats the file system volume.  ALL FILES WILL BE DELETED!\r\n",
	prvFORMATCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/* Structure that defines the TRANSACT command line command, which commits a
transaction point. */
static const CLI_Command_Definition_t xTRANSACT =
{
	"transact", /* The command string to type. */
	"\r\ntransact:\r\n Commit a Reliance Edge transaction point\r\n",
	prvTRANSACTCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/* Structure that defines the TRANSMASKGET command line command, which retrieves
the current automatic transaction event mask. */
static const CLI_Command_Definition_t xTRANSMASKGET =
{
	"transmaskget", /* The command string to type. */
	"\r\ntransmaskget:\r\n Retrieve the Reliance Edge automatic transaction mask\r\n",
	prvTRANSMASKGETCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/* Structure that defines the TRANSMASKSET command line command, which sets the
automatic transaction event mask. */
static const CLI_Command_Definition_t xTRANSMASKSET =
{
	"transmaskset", /* The command string to type. */
	"\r\ntransmaskset <hex mask>:\r\n Set the Reliance Edge automatic transaction mask\r\n",
	prvTRANSMASKSETCommand, /* The function to run. */
	1 /* One parameter is expected. */
};

/* Structure that defines the ABORT command line command, which rolls back
changes which have not been transacted. */
static const CLI_Command_Definition_t xABORT =
{
	"abort", /* The command string to type. */
	"\r\nabort:\r\n Roll back all changes not part of the last transaction point\r\n",
	prvABORTCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/* Structure that defines the TEST-FS command line command, which executes some
file system driver tests. */
static const CLI_Command_Definition_t xTEST_FS =
{
	"test-fs", /* The command string to type. */
	"\r\ntest-fs:\r\n Executes file system tests.  ALL FILES WILL BE DELETED!\r\n",
	prvTESTFSCommand, /* The function to run. */
	0 /* No parameters are expected. */
};

/*-----------------------------------------------------------*/

void vRegisterFileSystemCLICommands( void )
{
	/* Register all the command line commands defined immediately above. */
	FreeRTOS_CLIRegisterCommand( &xDIR );
	FreeRTOS_CLIRegisterCommand( &xTYPE );
	FreeRTOS_CLIRegisterCommand( &xAPPEND );
	FreeRTOS_CLIRegisterCommand( &xDEL );
	FreeRTOS_CLIRegisterCommand( &xCOPY );
	FreeRTOS_CLIRegisterCommand( &xCREATE );
	FreeRTOS_CLIRegisterCommand( &xMKDIR );
	FreeRTOS_CLIRegisterCommand( &xRENAME );
	FreeRTOS_CLIRegisterCommand( &xLINK );
	FreeRTOS_CLIRegisterCommand( &xSTAT );
	FreeRTOS_CLIRegisterCommand( &xSTATFS );
	FreeRTOS_CLIRegisterCommand( &xFORMAT );
	FreeRTOS_CLIRegisterCommand( &xTRANSACT );
	FreeRTOS_CLIRegisterCommand( &xTRANSMASKGET );
	FreeRTOS_CLIRegisterCommand( &xTRANSMASKSET );
	FreeRTOS_CLIRegisterCommand( &xABORT );
	FreeRTOS_CLIRegisterCommand( &xTEST_FS );
}
/*-----------------------------------------------------------*/

static BaseType_t prvDIRCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
static REDDIR *pxDir = NULL;
REDDIRENT *pxDirent;
const char *pcParameter;
BaseType_t xParameterStringLength, xReturn = pdFALSE;

	/* This assumes pcWriteBuffer is long enough. */
	( void ) pcCommandString;

	/* Ensure the buffer leaves space for the \r\n. */
	configASSERT( xWriteBufferLen > ( strlen( cliNEW_LINE ) * 2 ) );
	xWriteBufferLen -= strlen( cliNEW_LINE );

	if( pxDir == NULL )
	{
		/* Retrieve the directory to DIR. */
		pcParameter = FreeRTOS_CLIGetParameter
						(
							pcCommandString,		/* The command string itself. */
							1,						/* Return the first parameter. */
							&xParameterStringLength	/* Store the parameter string length. */
						);

		/* Sanity check something was returned. */
		configASSERT( pcParameter );

		/* This is the first time this function has been executed since the Dir
		command was run.  Open the directory. */
		pxDir = red_opendir( pcParameter );
	}

	if( pxDir )
	{
		/* red_readdir() returns NULL either on error or upon reaching the
		end of the directory.  Clear errno so these conditions can be
		distinguished. */
		red_errno = 0;
		pxDirent = red_readdir( pxDir );

		if( pxDirent )
		{
			prvCreateFileInfoString( pcWriteBuffer, pxDirent );
			xReturn = pdPASS;
		}
		else if( red_errno == 0 )
		{
			/* There are no more files.  Close the directory. */
			red_closedir( pxDir );
			pxDir = NULL;

			/* No string to return. */
			pcWriteBuffer[ 0 ] = 0x00;
		}
		else
		{
			snprintf( pcWriteBuffer, xWriteBufferLen, "Error %d reading directory.", ( int ) red_errno );
		}
	}
	else
	{
		/* User-friendly messages for common errors. */
		switch( red_errno )
		{
			case RED_ENOENT :
				snprintf( pcWriteBuffer, xWriteBufferLen, "Directory not found." );
				break;

			case RED_ENOTDIR :
				snprintf( pcWriteBuffer, xWriteBufferLen, "Directory not found or not a directory." );
				break;

			default :
				snprintf( pcWriteBuffer, xWriteBufferLen, "Error %d opening directory.", ( int ) red_errno );
				break;
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvTYPECommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
BaseType_t xParameterStringLength, xReturn = pdTRUE;
static int32_t lFildes = -1;
REDSTAT finfo;
int32_t lStatus, lBytesRead;
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

	if( lFildes == -1 )
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
		lFildes = red_open( pcParameter, RED_O_RDONLY );
		if( lFildes == -1 )
		{
			/* User-friendly messages for common errors. */
			switch( red_errno )
			{
				case RED_ENOENT :
				case RED_ENOTDIR :
					snprintf( pcWriteBuffer, xWriteBufferLen, "File not found." );
					break;

				default :
					snprintf( pcWriteBuffer, xWriteBufferLen, "Error %d opening file.", ( int ) red_errno );
					break;
			}
		}
		else
		{
			/* Make sure this is a file, not a directory. */
			lStatus = red_fstat( lFildes, &finfo );
			if( lStatus == 0 )
			{
				if( RED_S_ISDIR( finfo.st_mode ) )
				{
					snprintf( pcWriteBuffer, xWriteBufferLen, "Cannot TYPE a directory." );
					red_close( lFildes );
					lFildes = -1;
				}
			}
			else
			{
				snprintf( pcWriteBuffer, xWriteBufferLen, "Error %d querying file.", ( int ) red_errno );
				red_close( lFildes );
				lFildes = -1;
			}
		}
	}

	if( lFildes != -1 )
	{
		/* Read the next chunk of data from the file. */
		lBytesRead = red_read( lFildes, pcWriteBuffer, xColumns );

		if( lBytesRead < ( int32_t ) xColumns )
		{
			/* Error or no more characters to return. */
			red_close( lFildes );
			lFildes = -1;
		}
	}

	if( lFildes == -1 )
	{
		/* Either the file was not opened, or all the data from the file has
		been returned and the file is now closed. */
		xReturn = pdFALSE;
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvAPPENDCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
char *pcFileName = NULL;
const char *pcCharacter = NULL, *pcLength;
BaseType_t xParameterStringLength, xGoodParameters = pdTRUE;
int32_t lFildes, lAppendLength = -1, lThisWrite, lTotalWritten, lBytesWritten;

	/* This function assumes xWriteBufferLen is large enough! */
	( void ) xWriteBufferLen;

	/* Find the length to write. */
	pcLength = FreeRTOS_CLIGetParameter
					(
						pcCommandString,		/* The command string itself. */
						3,						/* Return the third parameter. */
						&xParameterStringLength	/* Store the parameter string length. */
					);
	configASSERT( pcLength );

	/* Convert the string into a number. */
	lAppendLength = RedAtoI( pcLength );
	if( lAppendLength < 0 )
	{
		strcpy( pcWriteBuffer, "Third parameter cannot be a negative number." );
		xGoodParameters = pdFALSE;
	}

	if( xGoodParameters )
	{
		/* Find the character to write. */
		pcCharacter = FreeRTOS_CLIGetParameter
						(
							pcCommandString,		/* The command string itself. */
							2,						/* Return the second parameter. */
							&xParameterStringLength	/* Store the parameter string length. */
						);
		configASSERT( pcCharacter );

		if( xParameterStringLength != 1 )
		{
			strcpy( pcWriteBuffer, "Second parameter must be a single character." );
			xGoodParameters = pdFALSE;
		}
	}

	if( xGoodParameters )
	{
		/* Find the file name. */
		pcFileName = ( char * ) FreeRTOS_CLIGetParameter
								(
									pcCommandString,		/* The command string itself. */
									1,						/* Return the first parameter. */
									&xParameterStringLength	/* Store the parameter string length. */
								);
		configASSERT( pcFileName );

		/* Terminate the string. */
		pcFileName[ xParameterStringLength ] = 0x00;
	}

	if( xGoodParameters )
	{
		/* Attempt to open the requested file. */
		lFildes = red_open( pcFileName, RED_O_WRONLY|RED_O_APPEND|RED_O_CREAT );

		if( lFildes == -1 )
		{
			/* User-friendly messages for common errors. */
			switch( red_errno )
			{
				case RED_ENOENT :
				case RED_ENOTDIR :
					strcpy( pcWriteBuffer, "Bad file path." );
					break;

				case RED_EISDIR :
					strcpy( pcWriteBuffer, "Cannot append to a directory." );
					break;

				default :
					sprintf( pcWriteBuffer, "Error %d opening file.", ( int ) red_errno );
					break;
			}
		}
		else
		{
			/* Put the requested character into the buffer. */
			memset( pcWriteBuffer, pcCharacter[0], xWriteBufferLen );

			/* Append the data. */
			for( lTotalWritten = 0; lTotalWritten < lAppendLength; lTotalWritten += lThisWrite )
			{
				lThisWrite = lAppendLength - lTotalWritten;
				if( lThisWrite > ( int32_t ) xWriteBufferLen )
				{
					lThisWrite = ( int32_t ) xWriteBufferLen;
				}

				lBytesWritten = red_write( lFildes, pcWriteBuffer, lThisWrite );
				if( lBytesWritten == -1 )
				{
					/* User-friendly messages for common errors. */
					switch( red_errno )
					{
						case RED_ENOSPC :
							strcpy( pcWriteBuffer, "Out of disk space." );
							break;

						default :
							sprintf( pcWriteBuffer, "Error %d writing to file.", ( int ) red_errno );
							break;
					}

					break;
				}
				else if( lBytesWritten != lThisWrite )
				{
					/*	Some data was written, but not all of it.  This only
					happens when the disk is full or the file reached its
					maximum size.  That latter is unlikely in this demo. */
					strcpy( pcWriteBuffer, "Out of disk space." );
					break;
				}
			}

			if( lTotalWritten == lAppendLength )
			{
				strcpy( pcWriteBuffer, "Append successful." );
			}

			red_close( lFildes );
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvDELCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
BaseType_t xParameterStringLength;
int32_t lStatus;

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

	/* Attempt to delete the file or directory. */
	lStatus = red_unlink( pcParameter );

	if( lStatus == 0 )
	{
		sprintf( pcWriteBuffer, "%s was deleted", pcParameter );
	}
	else
	{
		/* User-friendly messages for common errors. */
		switch( red_errno )
		{
			case RED_ENOTDIR :
			case RED_ENOENT :
				sprintf( pcWriteBuffer, "File not found." );
				break;

			case RED_ENOTEMPTY :
				sprintf( pcWriteBuffer, "Cannot remove directory: not empty." );
				break;

			default :
				sprintf( pcWriteBuffer, "Error %d deleting file.", ( int ) red_errno );
				break;
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvCOPYCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
char *pcSourceFile;
const char *pcDestinationFile;
BaseType_t xParameterStringLength;
int32_t lSourceFildes, lDestinationFildes;

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

	/* See if the source file exists, openm it if it does. */
	lSourceFildes = red_open( pcSourceFile, RED_O_RDONLY );

	if( lSourceFildes == -1 )
	{
		sprintf( pcWriteBuffer, "Source file does not exist" );
	}
	else
	{
		/* Create the destination file, error if it already exists. */
		lDestinationFildes = red_open( pcDestinationFile, RED_O_CREAT|RED_O_EXCL|RED_O_WRONLY );

		if( lDestinationFildes == -1 )
		{
			sprintf( pcWriteBuffer, "Error: Destination file already exists" );
		}
		else
		{
			if( prvPerformCopy( lSourceFildes, lDestinationFildes, pcWriteBuffer, xWriteBufferLen ) == pdPASS )
			{
				sprintf( pcWriteBuffer, "Copy made" );
			}
			else
			{
				sprintf( pcWriteBuffer, "Error during copy" );
			}

			red_close( lDestinationFildes );
		}

		red_close( lSourceFildes );
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvCREATECommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
BaseType_t xParameterStringLength;
int32_t lFildes;

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

	/* Attempt to create the file. */
	lFildes = red_open( pcParameter, RED_O_CREAT|RED_O_EXCL|RED_O_RDWR );

	if( lFildes != -1 )
	{
		sprintf( pcWriteBuffer, "%s was created", pcParameter );
		red_close( lFildes );
	}
	else
	{
		/* User-friendly messages for common errors. */
		switch( red_errno )
		{
			case RED_ENOTDIR :
			case RED_ENOENT :
				sprintf( pcWriteBuffer, "Bad file path." );
				break;

			case RED_EEXIST :
				sprintf( pcWriteBuffer, "File already exists." );
				break;

			default :
				sprintf( pcWriteBuffer, "Error %d creating file.", ( int ) red_errno );
				break;
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvMKDIRCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
BaseType_t xParameterStringLength;
int32_t lStatus;

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

	/* Attempt to create the file. */
	lStatus = red_mkdir( pcParameter );

	if( lStatus == 0 )
	{
		sprintf( pcWriteBuffer, "%s was created", pcParameter );
	}
	else
	{
		/* User-friendly messages for common errors. */
		switch( red_errno )
		{
			case RED_ENOTDIR :
			case RED_ENOENT :
				sprintf( pcWriteBuffer, "Bad file path." );
				break;

			case RED_EEXIST :
				sprintf( pcWriteBuffer, "Directory already exists." );
				break;

			default :
				sprintf( pcWriteBuffer, "Error %d creating directory.", ( int ) red_errno );
				break;
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvRENAMECommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcDestinationFile;
char *pcSourceFile;
BaseType_t xParameterStringLength;
int32_t lStatus;

	/* This function assumes xWriteBufferLen is large enough! */
	( void ) xWriteBufferLen;

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

	/* Attempt to rename the file. */
	lStatus = red_rename( pcSourceFile, pcDestinationFile );

	if( lStatus == 0 )
	{
		sprintf( pcWriteBuffer, "%s was renamed to %s", pcSourceFile, pcDestinationFile );
	}
	else
	{
		/* User-friendly messages for common errors. */
		switch( red_errno )
		{
			case RED_ENOTDIR :
			case RED_ENOENT :
			case RED_EISDIR :
				sprintf( pcWriteBuffer, "Bad file path." );
				break;

			/* This will only be seen if POSIX rename is disabled. */
			case RED_EEXIST :
				sprintf( pcWriteBuffer, "Destination already exists." );
				break;

			default :
				sprintf( pcWriteBuffer, "Error %d renaming file.", ( int ) red_errno );
				break;
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvLINKCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcDestinationFile;
char *pcSourceFile;
BaseType_t xParameterStringLength;
int32_t lStatus;

	/* This function assumes xWriteBufferLen is large enough! */
	( void ) xWriteBufferLen;

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

	/* Attempt to create the hard link. */
	lStatus = red_link( pcSourceFile, pcDestinationFile );

	if( lStatus == 0 )
	{
		sprintf( pcWriteBuffer, "%s was linked to %s", pcDestinationFile, pcSourceFile );
	}
	else
	{
		/* User-friendly messages for common errors. */
		switch( red_errno )
		{
			case RED_ENOTDIR :
			case RED_ENOENT :
				sprintf( pcWriteBuffer, "Bad file path." );
				break;

			case RED_EPERM :
				sprintf( pcWriteBuffer, "Cannot link a directory." );
				break;

			case RED_EMLINK :
				sprintf( pcWriteBuffer, "Too many hard links." );
				break;

			default :
				sprintf( pcWriteBuffer, "Error %d linking file.", ( int ) red_errno );
				break;
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvSTATCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter, *pcModeString;
BaseType_t xParameterStringLength;
REDSTAT finfo;
int32_t lFildes, lStatus;

	/* Ensure the buffer leaves space for the \r\n. */
	configASSERT( xWriteBufferLen > ( strlen( cliNEW_LINE ) * 2 ) );
	xWriteBufferLen -= strlen( cliNEW_LINE );

	/* Find the file name. */
	pcParameter = FreeRTOS_CLIGetParameter
					(
						pcCommandString,		/* The command string itself. */
						1,						/* Return the first parameter. */
						&xParameterStringLength	/* Store the parameter string length. */
					);

	/* Sanity check something was returned. */
	configASSERT( pcParameter );

	/* Attempt to open the requested file. */
	lFildes = red_open( pcParameter, RED_O_RDONLY );
	if( lFildes == -1 )
	{
		/* User-friendly messages for common errors. */
		switch( red_errno )
		{
			case RED_ENOENT :
			case RED_ENOTDIR :
				snprintf( pcWriteBuffer, xWriteBufferLen, "File not found." );
				break;

			default :
				snprintf( pcWriteBuffer, xWriteBufferLen, "Error %d opening file.", ( int ) red_errno );
				break;
		}
	}
	else
	{
		lStatus = red_fstat( lFildes, &finfo );
		if( lStatus == 0 )
		{
			if( RED_S_ISDIR( finfo.st_mode ) )
			{
				pcModeString = "dir";
			}
			else
			{
				pcModeString = "file";
			}

			snprintf( pcWriteBuffer, xWriteBufferLen, "ino=%lu mode=0x%04x(%s) nlink=%x size=%lu blocks=%lu",
				( unsigned long ) finfo.st_ino, ( unsigned ) finfo.st_mode, pcModeString,
				( unsigned ) finfo.st_nlink, (unsigned long) finfo.st_size, (unsigned long) finfo.st_blocks );
		}
		else
		{
			snprintf( pcWriteBuffer, xWriteBufferLen, "Error %d querying file.", ( int ) red_errno );
		}

		red_close( lFildes );
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvSTATFSCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
REDSTATFS fsinfo;
int32_t lStatus;

	/* Avoid compiler warnings. */
	( void ) pcCommandString;

	/* Ensure the buffer leaves space for the \r\n. */
	configASSERT( xWriteBufferLen > ( strlen( cliNEW_LINE ) * 2 ) );
	xWriteBufferLen -= strlen( cliNEW_LINE );

	lStatus = red_statvfs( "", &fsinfo );

	if( lStatus == -1 )
	{
		snprintf( pcWriteBuffer, xWriteBufferLen, "Error %d querying file system.", ( int ) red_errno );
	}
	else
	{
		snprintf( pcWriteBuffer, xWriteBufferLen,
			"Block size: %lu\r\n"
			"Block count: %lu\r\n"
			"Free blocks: %lu\r\n"
			"Inode count: %lu\r\n"
			"Free inodes: %lu\r\n",
			( unsigned long ) fsinfo.f_bsize, ( unsigned long ) fsinfo.f_blocks,
			( unsigned long ) fsinfo.f_bfree, ( unsigned long ) fsinfo.f_files,
			( unsigned long ) fsinfo.f_ffree );
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvFORMATCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
int32_t lStatus;

	/* Avoid compiler warnings. */
	( void ) pcCommandString;

	/* This function assumes xWriteBufferLen is large enough! */
	( void ) xWriteBufferLen;

	/* File system volumes cannot be formatted while mounted. */
	lStatus = red_umount( "" );
	if( lStatus == -1 )
	{
		sprintf( pcWriteBuffer, "Error %d during unmount.",  ( int ) red_errno );
	}
	else
	{
		/* Re-format the file system volume. */
		lStatus = red_format( "" );

		if( lStatus == -1 )
		{
			sprintf( pcWriteBuffer, "Error %d during format.",  ( int ) red_errno );
		}
		else
		{
			/* Mount again so that other commands will work properly. */
			lStatus = red_mount( "" );

			if( lStatus == -1 )
			{
				sprintf( pcWriteBuffer, "Error %d during mount.",  ( int ) red_errno );
			}
			else
			{
				strcpy( pcWriteBuffer, "Format successful." );
			}
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvTRANSACTCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
int32_t lStatus;

	/* Avoid compiler warnings. */
	( void ) pcCommandString;

	/* This function assumes xWriteBufferLen is large enough! */
	( void ) xWriteBufferLen;

	/* Save the original transaction mask settings. */
	lStatus = red_transact( "" );

	if( lStatus == -1 )
	{
		sprintf( pcWriteBuffer, "Error %d during transaction point.",  ( int ) red_errno );
	}
	else
	{
		strcpy( pcWriteBuffer, "Transaction point successful." );
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvTRANSMASKGETCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
uint32_t ulEventMask;
int32_t lStatus;

	/* Avoid compiler warnings. */
	( void ) pcCommandString;

	/* Ensure the buffer leaves space for the \r\n. */
	configASSERT( xWriteBufferLen > ( strlen( cliNEW_LINE ) * 2 ) );
	xWriteBufferLen -= strlen( cliNEW_LINE );

	lStatus = red_gettransmask( "", &ulEventMask );
	if( lStatus == -1 )
	{
		snprintf( pcWriteBuffer, xWriteBufferLen, "Error %d retrieving automatic transaction event mask.",  ( int ) red_errno );
	}
	else
	{
		snprintf( pcWriteBuffer, xWriteBufferLen,
			"Current automatic transaction event mask: 0x%04lx\r\n"
			"RED_TRANSACT_UMOUNT   (0x0001): %s\r\n"
			"RED_TRANSACT_CREAT    (0x0002): %s\r\n"
			"RED_TRANSACT_UNLINK   (0x0004): %s\r\n"
			"RED_TRANSACT_MKDIR    (0x0008): %s\r\n"
			"RED_TRANSACT_RENAME   (0x0010): %s\r\n"
			"RED_TRANSACT_LINK     (0x0020): %s\r\n"
			"RED_TRANSACT_CLOSE    (0x0040): %s\r\n"
			"RED_TRANSACT_WRITE    (0x0080): %s\r\n"
			"RED_TRANSACT_FSYNC    (0x0100): %s\r\n"
			"RED_TRANSACT_TRUNCATE (0x0200): %s\r\n"
			"RED_TRANSACT_VOLFULL  (0x0400): %s\r\n",
			( unsigned long ) ulEventMask,
			( ulEventMask & RED_TRANSACT_UMOUNT )   ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_CREAT )    ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_UNLINK )   ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_MKDIR )    ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_RENAME )   ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_LINK )     ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_CLOSE )    ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_WRITE )    ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_FSYNC )    ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_TRUNCATE ) ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_VOLFULL )  ? "Enabled" : "Disabled" );
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvTRANSMASKSETCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
const char *pcParameter;
BaseType_t xParameterStringLength;
uint32_t ulEventMask;
int32_t lStatus;

	/* Ensure the buffer leaves space for the \r\n. */
	configASSERT( xWriteBufferLen > ( strlen( cliNEW_LINE ) * 2 ) );
	xWriteBufferLen -= strlen( cliNEW_LINE );

	/* Obtain the parameter string. */
	pcParameter = FreeRTOS_CLIGetParameter
					(
						pcCommandString,		/* The command string itself. */
						1,						/* Return the first parameter. */
						&xParameterStringLength	/* Store the parameter string length. */
					);

	/* Sanity check something was returned. */
	configASSERT( pcParameter );

	if( ( pcParameter[0] == '0' ) && ( ( pcParameter[1] == 'x' ) || ( pcParameter[1] == 'X' ) ) )
	{
		pcParameter += 2;
	}

	/* Convert the argument into a value. */
	RedHtoUL( pcParameter, &ulEventMask );

	/* Set the new transaction mask. */
	lStatus = red_settransmask( "", ulEventMask );
	if( lStatus == -1 )
	{
		/* User-friendly messages for common errors. */
		switch( red_errno )
		{
			case RED_EINVAL:
				snprintf( pcWriteBuffer, xWriteBufferLen, "Invalid bits in transaction mask." );
				break;

			default :
				snprintf( pcWriteBuffer, xWriteBufferLen, "Error %d setting transaction mask.", ( int ) red_errno );
				break;
		}
	}
	else
	{
		snprintf( pcWriteBuffer, xWriteBufferLen,
			"Successfully set automatic transaction mask.  Enabled events:\r\n"
			"RED_TRANSACT_UMOUNT   (0x0001): %s\r\n"
			"RED_TRANSACT_CREAT    (0x0002): %s\r\n"
			"RED_TRANSACT_UNLINK   (0x0004): %s\r\n"
			"RED_TRANSACT_MKDIR    (0x0008): %s\r\n"
			"RED_TRANSACT_RENAME   (0x0010): %s\r\n"
			"RED_TRANSACT_LINK     (0x0020): %s\r\n"
			"RED_TRANSACT_CLOSE    (0x0040): %s\r\n"
			"RED_TRANSACT_WRITE    (0x0080): %s\r\n"
			"RED_TRANSACT_FSYNC    (0x0100): %s\r\n"
			"RED_TRANSACT_TRUNCATE (0x0200): %s\r\n"
			"RED_TRANSACT_VOLFULL  (0x0400): %s\r\n",
			( ulEventMask & RED_TRANSACT_UMOUNT )   ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_CREAT )    ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_UNLINK )   ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_MKDIR )    ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_RENAME )   ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_LINK )     ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_CLOSE )    ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_WRITE )    ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_FSYNC )    ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_TRUNCATE ) ? "Enabled" : "Disabled",
			( ulEventMask & RED_TRANSACT_VOLFULL )  ? "Enabled" : "Disabled" );
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvABORTCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
uint32_t ulEventMask;
int32_t lStatus;

	/* Avoid compiler warnings. */
	( void ) pcCommandString;

	/* This function assumes xWriteBufferLen is large enough! */
	( void ) xWriteBufferLen;

	/* Save the original transaction mask settings. */
	lStatus = red_gettransmask( "", &ulEventMask );

	if( lStatus == -1 )
	{
		sprintf( pcWriteBuffer, "Error %d querying transaction mask.",  ( int ) red_errno );
	}
	else
	{
		/* Make it so that red_umount() will not automatically commit a new
		transaction point. */
		lStatus = red_settransmask( "", ulEventMask & ~( ( uint32_t ) RED_TRANSACT_UMOUNT ) );

		if( lStatus == -1 )
		{
			sprintf( pcWriteBuffer, "Error %d setting transaction mask.",  ( int ) red_errno );
		}
		else
		{
			/* Unmount.  Since red_umount() will not transact, all changes which
			were not already transacted are rolled back. */
			lStatus = red_umount( "" );

			if( lStatus == -1 )
			{
				sprintf( pcWriteBuffer, "Error %d during unmount.",  ( int ) red_errno );
			}
			else
			{
				/* Mount.  Mount always starts from the last transaction point. */
				lStatus = red_mount( "" );

				if( lStatus == -1 )
				{
					sprintf( pcWriteBuffer, "Error %d during mount.",  ( int ) red_errno );
				}
				else
				{
					strcpy( pcWriteBuffer, "Working state changes succesfully aborted." );
				}
			}

			/* Restore the original transaction mask settings. */
			red_settransmask( "", ulEventMask );
		}
	}

	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvTESTFSCommand( char *pcWriteBuffer, size_t xWriteBufferLen, const char *pcCommandString )
{
UBaseType_t uxOriginalPriority;
FSSTRESSPARAM param;

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

	/* Delete all files to avoid inteferring with the test. */
	red_umount( "" );
	red_format( "" );
	red_mount( "" );

	FsstressDefaultParams(&param);
	param.fVerbose = pdTRUE;
	param.ulNops = 10000;
	param.ulSeed = 1;
	FsstressStart(&param);

	/* Clean up after the test. */
	red_umount( "" );
	red_format( "" );
	red_mount( "" );

	/* Reset back to the original priority. */
	vTaskPrioritySet( NULL, uxOriginalPriority );

	sprintf( pcWriteBuffer, "%s", "Test results were sent to Windows console" );
	strcat( pcWriteBuffer, cliNEW_LINE );

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvPerformCopy( int32_t lSourceFildes,
									int32_t lDestinationFiledes,
									char *pxWriteBuffer,
									size_t xWriteBufferLen )
{
int32_t lBytesRead;
BaseType_t xReturn = pdPASS;

	/* Assuming both files are at offset zero. */

	for( ;; )
	{
		/* Read the next block of data. */
		lBytesRead = red_read( lSourceFildes, pxWriteBuffer, xWriteBufferLen );
		if( lBytesRead <= 0 )
		{
			if( lBytesRead == -1)
			{
				/* Error reading from file. */
				xReturn = pdFAIL;
			}
			else
			{
				/* No error: reached end of file, time to stop. */
			}

			break;
		}

		/* Write the block of data to the end of the file. */
		if( red_write( lDestinationFiledes, pxWriteBuffer, lBytesRead ) != lBytesRead )
		{
			xReturn = pdFAIL;
			break;
		}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvCreateFileInfoString( char *pcBuffer, REDDIRENT *pxDirent )
{
const char *pcFile = "file", *pcDirectory = "directory";
const char *pcAttrib;

	/* Point pcAttrib to a string that describes the file. */
	if( RED_S_ISDIR(pxDirent->d_stat.st_mode) )
	{
		pcAttrib = pcDirectory;
	}
	else
	{
		pcAttrib = pcFile;
	}

	/* Create a string that includes the file name, the file size and the
	attributes string. */
	sprintf( pcBuffer, "%s [%s] [size=%d]", pxDirent->d_name, pcAttrib, pxDirent->d_stat.st_size );
}
