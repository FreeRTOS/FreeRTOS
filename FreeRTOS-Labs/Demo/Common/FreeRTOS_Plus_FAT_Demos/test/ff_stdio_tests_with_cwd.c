/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

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

/*
 * Non-systematic sanity checks for the API defined in ff_stdio.c.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+FAT headers. */
#include "ff_headers.h"
#include "ff_stdio.h"

/* The number of bytes read/written to the example files at a time. */
#define fsRAM_BUFFER_SIZE 				200

/* The number of bytes written to the file that uses f_putc() and f_getc(). */
#define fsPUTC_FILE_SIZE				100

/* The number of tasks to create if the stdio tests will be executed in
multiple tasks simultaneously. */
#define fsTASKS_TO_CREATE 5

/*
 * Examples and basic tests of the ff_truncate() function.
 */
static void prvTest_ff_truncate( const char *pcMountPath );

/*
 * Examples and basic tests of the ff_findNNN() functions.
 */
static void prvTest_ff_findfirst_ff_findnext_ff_findclose( const char *pcMountPath );

/*
 * Examples and basic tests of the ff_fopen() function.
 */
static void prvTest_ff_fopen( const char *pcMountPath );

/*
 * Examples and basic tests of the ff_rename() function.
 */
static void prvTest_ff_rename( const char *pcMountPath );

/*
 * Examples and basic tests of the ff_mkdir, ff_chdir() and ff_rmdir()
 * functions.
 */
static void prvTest_ff_fmkdir_ff_chdir_ff_rmdir( const char *pcMountPath );

/*
 * Non-systematic sanity check that aligned and unaligned data can be written
 * within and across sectors.
 */
static void prvTest_ff_fseek_ff_rewind( const char *pcMountPath );

/*
 * Examples and basic tests of the ff_fgets() function.
 */
#if( ffconfigFPRINTF_SUPPORT == 1 )

	static void prvTest_ff_fgets_ff_printf( const char *pcMountPath );

#endif /* ffconfigFPRINTF_SUPPORT */

/*
 * Non-systematic sanity check that aligned and unaligned data can be written
 * within and across sectors.
 */
static void prvAlignmentReadWriteTests( const char *pcMountPath );

/*
 * A task that repeatedly creates, tests, then deletes files as an ad hoc test
 * of accessing the file system from more than one task simultaneously.
 */
static void prvFileSystemAccessTask( void *pvParameters );

/*-----------------------------------------------------------*/

void vStdioWithCWDTest( const char *pcMountPath )
{
	/* Non-systematic sanity checks for the API defined in ff_stdio.c. */

	/* Must come after the prvCreateDemoFilesUsing_fwrite() and
	prvCreateDemoFileUsing_fputc() functions as it expects the files created by
	those functions to exist. */
	prvTest_ff_findfirst_ff_findnext_ff_findclose( pcMountPath );

	prvTest_ff_truncate( pcMountPath );
	prvTest_ff_fmkdir_ff_chdir_ff_rmdir( pcMountPath );
	prvTest_ff_fopen( pcMountPath );
	prvTest_ff_rename( pcMountPath );
	prvAlignmentReadWriteTests( pcMountPath );
	prvTest_ff_fseek_ff_rewind( pcMountPath );

	#if( ffconfigFPRINTF_SUPPORT == 1 )
	{
		prvTest_ff_fgets_ff_printf( pcMountPath );
	}
	#endif
}
/*-----------------------------------------------------------*/

static void prvTest_ff_fmkdir_ff_chdir_ff_rmdir( const char *pcMountPath )
{
int iReturned;
char *pcRAMBuffer, *pcFileName;

	/* Allocate buffers used to hold date written to/from the disk, and the
	file names. */
	pcRAMBuffer = ( char * ) pvPortMalloc( fsRAM_BUFFER_SIZE );
	pcFileName = ( char * ) pvPortMalloc( ffconfigMAX_FILENAME );
	configASSERT( pcRAMBuffer );
	configASSERT( pcFileName );

	/* Try changing to an invalid absolute directory.  This should fail. */
	iReturned = ff_chdir( "/not_a_directory" );
	configASSERT( iReturned == -1 );

	/* Try changing to the root.  This should not fail. */
	iReturned = ff_chdir( "/" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Try changing to an invalid relative directory.  This should also fail. */
	iReturned = ff_chdir( "not_a_directory" );
	configASSERT( iReturned == -1 );

	/* Ensure in the root of the mount being used. */
	iReturned = ff_chdir( pcMountPath );

	/* This time the directory should have been entered. */
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* For test purposes, move back, then try moving to the root of the mount
	using a relative path. */
	iReturned = ff_chdir( "/" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Ensure in the root of the mount being used but using a relative path,
	so move past the '/' at the beginning of pcMountPath. */
	iReturned = ff_chdir( pcMountPath + 1 );

	/* This time the directory should have been entered. */
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Create nested subdirectories from the root of the mount. */
	iReturned = ff_mkdir( "sub1" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
	iReturned = ff_mkdir( "sub1/sub2" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
	iReturned = ff_mkdir( "sub1/sub2/sub3" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
	iReturned = ff_mkdir( "sub1/sub2/sub3/sub4/" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* This is the non-recursive version, so the following is expected to
	fail. */
	iReturned = ff_mkdir( "sub1/sub2/subx/suby" );
	configASSERT( iReturned == -1 );

	/* Move into sub3. */
	iReturned = ff_chdir( "sub1/sub2/sub3" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Make more directories using relative paths. */
	iReturned = ff_mkdir( "../../sub2/sub3/sub4/sub5" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Sub6 does not exist, expect this to fail. */
	iReturned = ff_chdir( "../../sub2/sub3/sub4/sub6" );
	configASSERT( iReturned == -1 );

	/* Sub5 does exist, expect this to pass. */
	iReturned = ff_chdir( "../../sub2/../../sub1/sub2/sub3/../sub3/sub4/sub5" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Create a string that contains the expected CWD. */
	snprintf( pcRAMBuffer, fsRAM_BUFFER_SIZE, "%s/%s", pcMountPath, "sub1/sub2/sub3/sub4/sub5" );

	/* Attempt to get the CWD, but using a buffer too small.  There is no room
	for the NULL terminator in the line below. */
	configASSERT( ff_getcwd( pcFileName, strlen( pcRAMBuffer ) ) == NULL );

	/* Ensure the CWD is as expected. */
	configASSERT( ff_getcwd( pcFileName, ffconfigMAX_FILENAME ) == pcFileName );
	configASSERT( strcmp( pcFileName, pcRAMBuffer ) == 0 );

	/* Should not be possible to delete a directory in the CWD (although it is
	possible to delete the CWD if it is empty!). */
	iReturned = ff_rmdir( "../../sub4" );
	configASSERT( iReturned == -1 );

	/* It should be possible to remove sub5 as it does not contain anything. */
	iReturned = ff_chdir( "../.." );
	configASSERT( iReturned == 0 );
	iReturned = ff_rmdir( "sub4/sub5" );
	configASSERT( iReturned == 0 );

	/* Should not now be possible to move to sub4/sub5. */
	iReturned = ff_chdir( "sub4/sub5" );
	configASSERT( iReturned == -1 );

	/* Still possible to move to sub4 though. */
	iReturned = ff_chdir( "sub4" );
	configASSERT( iReturned == 0 );

	vPortFree( pcRAMBuffer );
	vPortFree( pcFileName );
}
/*-----------------------------------------------------------*/

#if( ffconfigFPRINTF_SUPPORT == 1 )

	static void prvTest_ff_fgets_ff_printf( const char *pcMountPath )
	{
	FF_FILE *pxFile;
	int iReturned, iString;
	const char *const pcTestFileName = "TestFile.txt";
	const char *const pcStringStart = "Test string";
	const int iMaxStrings = 1000;
	char pcReadString[ 17 ], pcExpectedString[ 17 ], *pcReturned;
	const char *pcMaximumStringLength = "Test string 999\n";

		/* For coverage this test wants the buffers to be exactly equal to the
		maximum string length.  A one is added as the string must also hold the
		null terminator. */
		configASSERT( ( strlen( pcMaximumStringLength ) + 1 ) == sizeof( pcReadString ) );

		/* Move to the root of the mount. */
		iReturned = ff_chdir( pcMountPath );
		configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

		/* Open a test file for writing. */
		pxFile = ff_fopen( pcTestFileName, "w+" );
		configASSERT( pxFile );

		/* Write the strings to the file. */
		for( iString = 0; iString < iMaxStrings; iString++ )
		{
			/* Call ff_fprintf() to write the formatted string to the file. */
			iReturned = ff_fprintf( pxFile, "%s %d\n", pcStringStart, iString );

			/* Generate the expected string so the return value of ff_fprintf()
			can be checked. */
			sprintf( pcExpectedString, "%s %d\n", pcStringStart, iString );
			configASSERT( iReturned == ( int ) strlen( pcExpectedString ) );
		}

		/* Read back and check the strings. */
		ff_rewind( pxFile );
		configASSERT( ff_ftell( pxFile ) == 0 );

		for( iString = 0; iString < iMaxStrings; iString++ )
		{
			/* Generate the expected string. */
			sprintf( pcExpectedString, "%s %d\n", pcStringStart, iString );

			/* Read back the next string. */
			memset( pcReadString, 0x00, sizeof( pcReadString ) );
			pcReturned = ff_fgets( pcReadString, sizeof( pcReadString ), pxFile );

			/* The string should have been read back successfully. */
			configASSERT( pcReturned == pcReadString );
			configASSERT( strcmp( pcReadString, pcExpectedString ) == 0 );
		}

		/* Should be at the end of the file now. */
		configASSERT( ff_feof( pxFile ) != 0 );

		/* Asking for one byte should always pass because the single byte will
		just be the NULL terminator, but asking for two bytes should fail as the
		EOF has been reached. */
		configASSERT( ff_fgets( pcReadString, 1, pxFile ) == pcReadString );
		configASSERT( strlen( pcReadString ) == 0 );
		configASSERT( ff_fgets( pcReadString, 2, pxFile ) == NULL );

		/* Back to the start. */
		configASSERT( ff_feof( pxFile ) != 0 );
		iReturned = ff_fseek( pxFile, 0, FF_SEEK_SET );
		configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
		configASSERT( ff_ftell( pxFile ) == 0 );
		configASSERT( ff_feof( pxFile ) == 0 );

		/* This time don't read all the way to a newline.  Just read the string
		without the number on the end.  The +1 is included to accommodate the
		NULL terminator. */
		pcReturned = ff_fgets( pcReadString, strlen( pcStringStart ) + 1, pxFile );

		/* The read should have been successful. */
		configASSERT( pcReturned == pcReadString );
		configASSERT( strcmp( pcReadString, pcStringStart ) == 0 );

		/* Move to the end of the file. */
		iReturned = ff_fseek( pxFile, 0, FF_SEEK_END );
		configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

		/* Write a string without a \n on the end. */
		ff_fprintf( pxFile, pcStringStart );

		/* Now seek back and read some characters while attempting to read off
		the end of the file. */
		iReturned = ff_fseek( pxFile, 0 - (int ) strlen( pcStringStart ), FF_SEEK_CUR );
		configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

		pcReturned = ff_fgets( pcReadString, sizeof( pcReadString ), pxFile );
		/* pcReturned will contain the last string "Test string", without a linefeed. */
		configASSERT( pcReturned == pcReadString );
		configASSERT( strcmp( pcReadString, pcStringStart ) == 0 );

		pcReturned = ff_fgets( pcReadString, sizeof( pcReadString ), pxFile );
		/* pcReturned will be NULL because EOF has been reached. */
		configASSERT( pcReturned == NULL );

		ff_fclose( pxFile );
	}

#endif /* ffconfigFPRINTF_SUPPORT */
/*-----------------------------------------------------------*/

static void prvTest_ff_fseek_ff_rewind( const char *pcMountPath )
{
FF_FILE *pxFile;
int iReturned;
const size_t xFileSize = 7776UL;
const size_t xNum32BitValues = xFileSize / sizeof( uint32_t );
uint32_t x, y;

	/* Move to the root of the mount. */
	iReturned = ff_chdir( pcMountPath );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Ensure the file does not already exist. */
	ff_remove( "seek_rewind_test_file" );

	/* Open a test file. */
	pxFile = ff_fopen( "seek_rewind_test_file", "a+" );
	configASSERT( pxFile );

	/* Fill the file with known data. */
	for( x = 0; x < xNum32BitValues; x++ )
	{
		iReturned = ff_fwrite( &x, 1, sizeof( x ), pxFile );
		configASSERT( iReturned == sizeof( uint32_t ) );
		configASSERT( ff_ftell( pxFile ) == ( long ) ( ( x + 1U ) * sizeof( uint32_t ) ) );
	}

	/* Use rewind to get back to the beginning of the file. */
	ff_rewind( pxFile );
	configASSERT( ff_ftell( pxFile ) == 0 );

	/* Expect 0 to be read from the start. */
	iReturned = ff_fread( &x, 1, sizeof( x ), pxFile );
	configASSERT( iReturned == sizeof( x ) );
	configASSERT( x == 0 );

	/* Move to the end of the file. */
	iReturned = ff_fseek( pxFile, 0, FF_SEEK_END );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
	configASSERT( ff_ftell( pxFile ) == ( long ) xFileSize );

	/* Try moving past the front of the file.  An error should be returned and
	the position should not change. */
	iReturned = ff_fseek( pxFile, 0 - ( ( long ) xFileSize * 2 ), FF_SEEK_END );
	configASSERT( iReturned != pdFREERTOS_ERRNO_NONE );
	configASSERT( ff_ftell( pxFile ) == ( long ) xFileSize );

	/* Reading from here should fail (EOF). */
	iReturned = ( int ) ff_fread( &x, 1, 1, pxFile );
	configASSERT( iReturned == 0 );

	/* Now go backwards through the file, reading each uint32_t on the way. */
	for( y = ( xNum32BitValues - 1 ); y >= sizeof( uint32_t ); y -= sizeof( x ) )
	{
		iReturned = ff_fseek( pxFile, ( long ) y * sizeof( uint32_t ), FF_SEEK_SET );
		configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
		configASSERT( ff_ftell( pxFile ) == ( long ) ( y * sizeof( uint32_t ) ) );

		/* Data read from here should equal the position. */
		iReturned = ( int ) ff_fread( &x, 1, sizeof( x ), pxFile );
		configASSERT( iReturned == sizeof( x ) );
		configASSERT( x == y );
	}

	/* Move forward through the file doing the same thing.  Start at the
	front. */
	iReturned = ff_fseek( pxFile, 0 - ( ( long ) xFileSize ), FF_SEEK_END );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
	configASSERT( ff_ftell( pxFile ) == ( long ) 0 );

	for( y = 0; y < xNum32BitValues; y++ )
	{
		iReturned = ff_fseek( pxFile, ( long ) ( y * sizeof( x ) ), FF_SEEK_CUR );
		configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
		configASSERT( ff_ftell( pxFile ) == ( long ) ( y * sizeof( uint32_t ) ) );

		/* Data read from here should equal the position. */
		iReturned = ( int ) ff_fread( &x, 1, sizeof( x ), pxFile );
		configASSERT( iReturned == sizeof( x ) );
		configASSERT( x == y );

		/* Move back to the start of the file. */
		iReturned = ff_fseek( pxFile, 0 - ( long ) ( ( y + 1 ) * sizeof( x ) ), FF_SEEK_CUR );
		configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
		configASSERT( ff_ftell( pxFile ) == 0 );
	}

	ff_fclose( pxFile );
}
/*-----------------------------------------------------------*/

static void prvTest_ff_findfirst_ff_findnext_ff_findclose( const char* pcMountPath )
{
int iReturned;
size_t i;
uint8_t ucFoundFiles[ 8 ];
FF_FindData_t *pxFindStruct = NULL;
const char *pcExpectedRootFiles[] =
{
	".",
	"..",
	"SUB1",
	"root001.txt",
	"root002.txt",
	"root003.txt",
	"root004.txt",
	"root005.txt"
};

const char *pcExpectedSUB1Files[] =
{
	".",
	"..",
	"SUB2",
};

	/* There should be one place in the ucFoundFiles[] array for every place in
	the pcExpectedRootFiles[] array. */
	configASSERT( sizeof( ucFoundFiles ) == ( sizeof( pcExpectedRootFiles ) / sizeof( char * ) ) );

	/* No files found yet. */
	memset( ucFoundFiles, 0x00, sizeof( ucFoundFiles ) );

	/* Move to the root of the mount. */
	iReturned = ff_chdir( pcMountPath );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* FF_FindData_t is quite large, so best to malloc() it on stack challenged
	architectures. */
	pxFindStruct = ( FF_FindData_t * ) pvPortMalloc( sizeof( FF_FindData_t ) );
	configASSERT( pxFindStruct );

	if( pxFindStruct != NULL )
	{
		/* Must be initialised to 0. */
		memset( pxFindStruct, 0x00, sizeof( FF_FindData_t ) );

		/* The first parameter to ff_findfist() is the directory being searched,
		wildcards are not (currently) supported, so as this is searching the
		current working directory the string is empty. */
		if( ff_findfirst( "", pxFindStruct ) == pdFREERTOS_ERRNO_NONE )
		{
			do
			{
				/* Which file was found? */
				for( i = 0; i < sizeof( ucFoundFiles ); i++ )
				{
					if( strcmp( pcExpectedRootFiles[ i ], pxFindStruct->pcFileName ) == 0 )
					{
						/* The file at this index was found. */
						ucFoundFiles[ i ] = pdTRUE;
						break;
					}
				}

			} while( ff_findnext( pxFindStruct ) == pdFREERTOS_ERRNO_NONE );
		}

		/* Were all the files found? */
		for( i = 0; i < sizeof( ucFoundFiles ); i++ )
		{
			configASSERT( ucFoundFiles[ i ] == pdTRUE );
		}


		/* Next check a file can be read from the SUB1 directory.  First reset
		the FF_FindData_t structure. */
		memset( pxFindStruct, 0x00, sizeof( FF_FindData_t ) );
		memset( ucFoundFiles, 0x00, sizeof( ucFoundFiles ) );

		if( ff_findfirst( "SUB1", pxFindStruct ) == pdFREERTOS_ERRNO_NONE )
		{
			do
			{
				/* Which file was found? */
				for( i = 0; i < ( sizeof( pcExpectedSUB1Files ) / sizeof( char * ) ); i++ )
				{
					if( strcmp( pcExpectedSUB1Files[ i ], pxFindStruct->pcFileName ) == 0 )
					{
						/* The file at this index was found. */
						ucFoundFiles[ i ] = pdTRUE;
						break;
					}
				}

			} while( ff_findnext( pxFindStruct ) == pdFREERTOS_ERRNO_NONE );
		}

		/* Were all the files found? */
		for( i = 0; i < ( sizeof( pcExpectedSUB1Files ) / sizeof( char * ) ); i++ )
		{
			configASSERT( ucFoundFiles[ i ] == pdTRUE );
		}

		/* Must free the find struct again. */
		vPortFree( pxFindStruct );
	}
}
/*-----------------------------------------------------------*/

static void prvTest_ff_truncate( const char *pcMountPath )
{
int iReturned, x;
FF_FILE *pxFile;
/*_RB_ Cannot have / on end due to ff_findfirst() being using if ff_stat().  The
original file name has to be used at one point as both the findfirst() and fstat()
functions both use the thread local file name, and having the / on the end prevents
strcmp being used const char * const pcTestFileName = "truncate.bin/"; */
const char * const pcTestFileName = "truncate.bin";
FF_Stat_t xStat;
int cChar;

	/* Move to the root of the mount. */
	iReturned = ff_chdir( pcMountPath );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Ensure the file does not already exist. */
	ff_remove( pcTestFileName );

	/* This time the file definitely should not exist. */
	configASSERT( ff_remove( pcTestFileName ) == -1 );

	/* Try closing the file before it is opened. */
	pxFile = NULL;
	configASSERT( ff_fclose( pxFile ) == -1 );

	/* Create a 1000 byte file. */
	pxFile = ff_truncate( pcTestFileName, 1000L );

	/* Check the file has the expected size. */
	ff_fclose( pxFile );
	ff_stat( pcTestFileName, &xStat );
	configASSERT( xStat.st_size == 1000L );

	/* The file should have been created full of zeros. */
	pxFile = ff_fopen( pcTestFileName, "r" );
	configASSERT( pxFile != NULL );

	/* Calling ff_filelength() should pass as the file is not read only. */
	configASSERT( ff_filelength( pxFile ) == 1000 );

	/* Should not be able to write now. */
	iReturned = ff_fputc( 0xff, pxFile );
	configASSERT( iReturned != 0xff );

	for( x = 0; x < 1000; x++ )
	{
		cChar = ff_fgetc( pxFile );
		configASSERT( cChar == 0 );
	}

	/* Should now be at the end of the file. */
	configASSERT( ff_fgetc( pxFile ) == FF_EOF );
	configASSERT( ff_feof( pxFile ) != 0 );

	/* ff_seteof() should fail as the file is read only.  As should
	ff_fprintf(). */
	configASSERT( ff_seteof( pxFile ) == -1 );
	#if( ffconfigFPRINTF_SUPPORT != 0 )
	{
		configASSERT( ff_fprintf( pxFile, "this should fail" ) == -1 );
	}
	#endif

	/* Fill the file with 0xff. */
	ff_fclose( pxFile );
	pxFile = ff_fopen( pcTestFileName, "r+" );
	configASSERT( pxFile != NULL );

	for( x = 0; x < 1000; x++ )
	{
		configASSERT( ff_fputc( 0xff, pxFile ) == 0xff );
	}

	/* Extend the file to 2000 bytes using ff_truncate(). */
	ff_fclose( pxFile );
	pxFile = ff_truncate( pcTestFileName, 2000L );
	configASSERT( pxFile );

	/* Ensure the file is indeed 2000 bytes long. */
	ff_fclose( pxFile );
	ff_stat( pcTestFileName, &xStat );
	configASSERT( xStat.st_size == 2000L );

	/* Now the first 1000 bytes should be 0xff, and the second 1000 bytes should
	be 0x00. */
	pxFile = ff_fopen( pcTestFileName, "r+" );
	configASSERT( pxFile );
	configASSERT( ff_ftell( pxFile ) == 0 );

	for( x = 0; x < 1000; x++ )
	{
		cChar = ff_fgetc( pxFile );
		configASSERT( cChar == 0xff );
	}

	for( x = 0; x < 1000; x++ )
	{
		cChar = ff_fgetc( pxFile );
		configASSERT( cChar == 0x00 );
	}

	/* Use ff_fseek() then ff_seteof() to make the file 1750 bytes long. */
	configASSERT( ff_fseek( pxFile, 1750L, FF_SEEK_SET ) == pdFREERTOS_ERRNO_NONE );
	configASSERT( ff_ftell( pxFile ) == 1750 );
	configASSERT( ff_seteof( pxFile ) == pdFREERTOS_ERRNO_NONE );

	/* Attempting another read should result in EOF. */
	configASSERT( ff_feof( pxFile ) != 0 );
	configASSERT( ff_fgetc( pxFile ) == FF_EOF );

	/* This time use truncate to make the file shorter by another 250 bytes. */
	ff_fclose( pxFile );
	ff_stat( pcTestFileName, &xStat );
	configASSERT( xStat.st_size == 1750L );
	pxFile = ff_truncate( pcTestFileName, 1500L );

	/* Ensure the file is indeed 1500 bytes long. */
	ff_fclose( pxFile );
	ff_stat( pcTestFileName, &xStat );
	configASSERT( xStat.st_size == 1500L );

	/* Now the first 1000 bytes should be 0xff, and the second 500 bytes should
	be 0x00. */
	pxFile = ff_fopen( pcTestFileName, "r" );
	configASSERT( pxFile );
	configASSERT( ff_ftell( pxFile ) == 0 );

	for( x = 0; x < 1000; x++ )
	{
		cChar = ff_fgetc( pxFile );
		configASSERT( cChar == 0xff );
	}

	for( x = 0; x < 500; x++ )
	{
		cChar = ff_fgetc( pxFile );
		configASSERT( cChar == 0x00 );
	}

	/* Attempting another read should result in EOF. */
	configASSERT( ff_feof( pxFile ) != 0 );
	configASSERT( ff_fgetc( pxFile ) == FF_EOF );

	/* Now truncate the file to 0. */
	ff_fclose( pxFile );
	pxFile = ff_truncate( pcTestFileName, 0L );
	configASSERT( pxFile );

	/* Don't expect to be able to delete an open file. */
	configASSERT( ff_remove( pcTestFileName ) == -1 );

	/* Ensure the file is indeed 0 bytes long. */
	ff_fclose( pxFile );
	ff_stat( pcTestFileName, &xStat );
	configASSERT( xStat.st_size == 0L );

	/* Do expect to be able to delete the file after it is closed. */
	configASSERT( ff_remove( pcTestFileName ) == 0 );
}
/*-----------------------------------------------------------*/

static void prvAlignmentReadWriteTests( const char *pcMountPath )
{
const char cOverflowCheckByte = 0xc5;
const size_t xSizeIncrement = 37U;
const size_t xSectorSize = 512U;
const size_t xNumSectors = 3U;
const size_t xOverwriteCheckBytes = 1U;
const size_t xBufferSize = ( xSectorSize * xNumSectors ) + xSizeIncrement;
size_t x, xSkippedBytes, x32BitValues;
char *pcBuffer;
uint32_t *pulVerifyBuffer;
uint32_t *pulVerifyValues;
FF_FILE *pxFile;
FF_Stat_t xStat;
const char* pcTestFileName = "test.bin";
int iReturned, iExpectedReturn;

	/* Start in the root of the mounted disk. */
	ff_chdir( pcMountPath );

	/* Create an array that will hold 3 whole sectors plus a few additional
	bytes, plus a byte at the end which is used to check it does not get
	overwritten. */
	pcBuffer = ( char * ) pvPortMalloc( xBufferSize + xOverwriteCheckBytes );
	configASSERT( pcBuffer );
	pulVerifyBuffer = ( uint32_t * ) pvPortMalloc( xBufferSize );

	/* Write a byte to the end of the buffer which is used to ensure nothing has
	ever written off the end of the buffer. */
	pcBuffer[ xBufferSize ] = cOverflowCheckByte;

	/* In case this test has been executed on the disk already - ensure the file
	does not exist. */
	ff_remove( pcTestFileName );

	/* Create a file that will hold the entire buffer. */
	pxFile = ff_truncate( pcTestFileName, xBufferSize );

	/* Check the file has the expected size. */
	ff_fclose( pxFile );
	ff_stat( pcTestFileName, &xStat );
	configASSERT( xStat.st_size == xBufferSize );

	/* Check the file was filled with zeros by reading it back into a buffer
	that was previously set to ff. */
	pxFile = ff_fopen( pcTestFileName, "r" );
	configASSERT( pxFile );

	memset( pcBuffer, 0xff, xBufferSize );

	/* The +1 is to ensure the xSizeIncrement bytes are also read. */
	iReturned = ff_fread( pcBuffer, xSectorSize, xNumSectors + 1U, pxFile );

	/* Expected to have read xNumSectors worth of xSectorSize, but xBufferSize
	bytes. */
	configASSERT( iReturned == ( int ) xNumSectors );

	/* Check the buffer is now full of zeros. */
	for( x = 0; x < xBufferSize; x++ )
	{
		configASSERT( pcBuffer[ x ] == 0x00 );
	}

	/* Check the byte at the end of the buffer was not overwritten. */
	configASSERT( pcBuffer[ xBufferSize ] == cOverflowCheckByte );

	/* Re-open in append mode, the move the write position to the start of the
	file. */
	ff_fclose( pxFile );
	pxFile = ff_fopen( pcTestFileName, "r+" );
	configASSERT( pxFile );
	iReturned = ( int ) ff_ftell( pxFile );
	configASSERT( iReturned == 0 ); /*_RB_ Unexpected, but how the GCC one works. */

	/* Fill the file with incrementing 32-bit number starting from various
	different offset. */
	for( xSkippedBytes = 0; xSkippedBytes < xSizeIncrement; xSkippedBytes++ )
	{
		/* The buffer is going to be written to from xSkippedBytes bytes in.
		When that is done, how many 32-bit integers will it hold. */
		x32BitValues = ( xBufferSize - xSkippedBytes ) / sizeof( uint32_t );

		/* This time start xSkippedBytes bytes into the file. */
		ff_fseek( pxFile, xSkippedBytes, FF_SEEK_SET );
		iReturned = ( int ) ff_ftell( pxFile );
		configASSERT( iReturned == ( int ) xSkippedBytes );
		iExpectedReturn = xSkippedBytes;

		memset( pulVerifyBuffer, 0x00, xBufferSize );
		pulVerifyValues = ( uint32_t * ) pulVerifyBuffer;

		for( x = 0; x < x32BitValues; x++ )
		{
			iReturned = ff_fwrite( &x, sizeof( x ), 1, pxFile );
			configASSERT( iReturned == 1 );

			/* Also write the value into the verify buffer for easy checking
			when the file is read back.  pulVerifyBuffer should remain on a
			4 byte boundary as it starts from index 0. */
			pulVerifyValues[ x ] = x;

			iExpectedReturn += sizeof( x );
			iReturned = ( int ) ff_ftell( pxFile );
			configASSERT( iExpectedReturn == iReturned );
		}

		/* Calculate the expected file position. */
		iExpectedReturn = ( x32BitValues * sizeof( uint32_t ) ) + xSkippedBytes;

		/* Check the expected file position. */
		iReturned = ff_ftell( pxFile );
		configASSERT( iReturned == iExpectedReturn );

		/* Read the entire file back into a buffer to check its contents. */
		ff_fseek( pxFile, 0, FF_SEEK_SET );
		memset( pcBuffer, 0x00, xBufferSize );
		iReturned = ff_fread( pcBuffer, iExpectedReturn, 1, pxFile );

		/* The whole file was read back in one. */
		configASSERT( iReturned == 1 );

		/* Verify the data.  The first xSkippedBytes bytes of the buffer should
		still be zero. */
		for( x = 0; x < xSkippedBytes; x++ )
		{
			configASSERT( pcBuffer[ x ] == 0 );
		}

		/* As just verified, the first xSkippedBytes bytes were skipped so the
		first xSkippedBytes bytes in pcBuffer are zero, pulVerifyBuffer was
		written to from its start, and the number of bytes written was the total
		number of uint_32 variables that would fit in the buffer. */
		configASSERT( memcmp( ( void * ) ( pcBuffer + xSkippedBytes ), ( void * ) pulVerifyBuffer, ( x32BitValues * sizeof( uint32_t ) ) ) == 0 );


		/* Read the file back one byte at a time to check its contents. */
		memset( pcBuffer, 0xff, xBufferSize );
		ff_fseek( pxFile, 0, FF_SEEK_SET );
		for( x = 0; x < ( size_t ) iExpectedReturn; x++ )
		{
			iReturned = ff_fread( &( pcBuffer[ x ] ), sizeof( char ), 1, pxFile );
			configASSERT( iReturned == sizeof( char ) );
			iReturned = ff_ftell( pxFile );
			configASSERT( iReturned == ( long ) ( x + 1U ) );
		}

		/* Verify the data using the same offsets as the previous time. */
		configASSERT( memcmp( ( void * ) ( pcBuffer + xSkippedBytes ), ( void * ) pulVerifyBuffer, ( x32BitValues * sizeof( uint32_t ) ) ) == 0 );

		/* Read the file back three bytes at a time to check its contents. */
		memset( pcBuffer, 0xff, xBufferSize );
		ff_fseek( pxFile, 0, FF_SEEK_SET );
		for( x = 0; x < ( size_t ) iExpectedReturn; x += 3 )
		{
			iReturned = ff_fread( &( pcBuffer[ x ] ), 1, 3, pxFile );

			/* 3 does not go into 4.  Don't assert check the last iteration as
			it won't be an exact multiple. */
			if( x < ( iExpectedReturn - sizeof( uint32_t ) ) )
			{
				configASSERT( iReturned == 3 );
				iReturned = ff_ftell( pxFile );
				configASSERT( iReturned == ( long )  ( x + 3 ) );
			}
		}

		/* Verify the data. */
		configASSERT( memcmp( ( void * ) ( pcBuffer + xSkippedBytes ), ( void * ) pulVerifyBuffer, ( x32BitValues * sizeof( uint32_t ) ) ) == 0 );
	}

	ff_fclose( pxFile );

	/* Check the byte at the end of the buffer was not overwritten. */
	configASSERT( pcBuffer[ xBufferSize ] == cOverflowCheckByte );

	vPortFree( pcBuffer );
	vPortFree( pulVerifyBuffer );
}
/*-----------------------------------------------------------*/

static void prvTest_ff_rename( const char *pcMountPath )
{
FF_FILE *pxFile;
int iReturned;
const char *pcStringToWrite = "This string is written to the file\n";
const char *pcSecondStringToWrite = "This is another string written to a file\n";
char cReadBuffer[ 45 ];

	/* cReadBuffer must be at least big enough to hold pcStringToWrite plus a
	null terminator. */
	configASSERT( sizeof( cReadBuffer ) >= ( strlen( pcSecondStringToWrite ) + 1 ) );

	/* Move to the root of the mount. */
	iReturned = ff_chdir( pcMountPath );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Attempt to move a file that does not exist. */
	iReturned = ff_rename( "file1.bin", "file2.bin", pdFALSE );
	configASSERT( iReturned == -1 );

	/* Create subdirectories into/from which files will be moved. */
	iReturned = ff_mkdir( "source_dir" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
	iReturned = ff_mkdir( "destination_dir" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Create a file in source_dir then write some data to it. */
	pxFile = ff_fopen( "source_dir/source.txt", "w" );
	configASSERT( pxFile != NULL );
	ff_fwrite( pcStringToWrite, strlen( pcStringToWrite ), 1, pxFile );

	/* Calling ff_filelength() should fail as the file is not read only. */
	/* configASSERT( ff_filelength( pxFile ) == 0 ); _RB_ The behavior of this function has changed, the documentation and or the test will be updated */

	/* Ensure the file exists by closing it, reopening it, and reading the
	string back. */
	iReturned = ff_fclose( pxFile );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
	ff_chdir( "source_dir" );
	pxFile = ff_fopen( "source.txt", "r" );
	configASSERT( pxFile != NULL );
	memset( cReadBuffer, 0x00, sizeof( cReadBuffer ) );
	ff_fgets( cReadBuffer, sizeof( cReadBuffer ), pxFile );
	configASSERT( strcmp( cReadBuffer, pcStringToWrite ) == 0 );

	/* Calling ff_filelength() should not fail as the file is open for
	reading. */
	configASSERT( ff_filelength( pxFile ) == strlen( pcStringToWrite ) );

	/* Should not be able to move the file because it is open. */
	iReturned = ff_rename( "source.txt", "../destination_dir/destination.txt", pdFALSE );
	configASSERT( iReturned == -1 );

	/* Close the file so it can be moved. */
	ff_fclose( pxFile );

	iReturned = ff_rename( "source.txt", "../destination_dir/destination.txt", pdFALSE );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );

	/* Attempt to open the file - it should no longer exist. */
	pxFile = ff_fopen( "source.txt", "r" );
	configASSERT( pxFile == NULL );

	/* Create a new file to try and copy it over an existing file. */
	pxFile = ff_fopen( "source.txt2", "w" );
	configASSERT( pxFile != NULL );

	/* Write different data to the file. */
	iReturned = ff_fwrite( pcSecondStringToWrite, 1, strlen( pcSecondStringToWrite ), pxFile );
	configASSERT( iReturned == ( int ) strlen( pcSecondStringToWrite ) );

	/* Now close the file and try moving it to the file that already exists.
	That should fail if the last parameter is pdFALSE. */
	ff_fclose( pxFile );
	iReturned = ff_rename( "source.txt2", "../destination_dir/destination.txt", pdFALSE );
	configASSERT( iReturned == -1 );

	/* This time the last parameter is pdTRUE, so the file should be moved even
	through the destination already existed. */
	iReturned = ff_rename( "source.txt2", "../destination_dir/destination.txt", pdTRUE );
	configASSERT( iReturned == 0 );

	/* Now open the destination file and ensure it was copied as expected. */
	iReturned = ff_chdir( "../destination_dir" );
	configASSERT( iReturned == pdFREERTOS_ERRNO_NONE );
	pxFile = ff_fopen( "destination.txt", "r" );
	configASSERT( pxFile != NULL );
	configASSERT( ff_filelength( pxFile ) == strlen( pcSecondStringToWrite ) );
	memset( cReadBuffer, 0x00, sizeof( cReadBuffer ) );
	/* +1 to get the \n on the end of the string too. */
	ff_fgets( cReadBuffer, strlen( pcSecondStringToWrite ) + 1, pxFile );
	configASSERT( strcmp( cReadBuffer, pcSecondStringToWrite ) == 0 );

	ff_fclose( pxFile );
}
/*-----------------------------------------------------------*/

static void prvTest_ff_fopen( const char *pcMountPath )
{
FF_FILE *pxFile;
FF_Stat_t xStat;
size_t xReturned, xByte;
const size_t xBytesToWrite = 10U;
char *pcRAMBuffer, *pcFileName;

	/* Allocate buffers used to hold date written to/from the disk, and the
	file names. */
	pcRAMBuffer = ( char * ) pvPortMalloc( fsRAM_BUFFER_SIZE );
	pcFileName = ( char * ) pvPortMalloc( ffconfigMAX_FILENAME );
	configASSERT( pcRAMBuffer );
	configASSERT( pcFileName );

	/* Generate file name. */
	snprintf( pcFileName, ffconfigMAX_FILENAME, "%s/Dummy.txt", pcMountPath );

	/* Attempt to open a file that does not exist in read only mode. */
	pxFile = ff_fopen( pcFileName, "r" );

	/* Do not expect the file to have been opened as it does not exist. */
	configASSERT( pxFile == NULL );

	/* Attempt to open the same file, this time using a "+" in addition to the
	"r". */
	pxFile = ff_fopen( pcFileName, "r+" );

	/* The file still does not exist. */
	configASSERT( pxFile == NULL );

	/* This time attempt to open the file in read/write mode. */
	pxFile = ff_fopen( pcFileName, "w" );

	/* The file should have been created. */
	configASSERT( pxFile != NULL );

	/* Write some ascii '0's to the file. */
	memset( pcRAMBuffer, ( int ) '0', fsRAM_BUFFER_SIZE );
	xReturned = ff_fwrite( pcRAMBuffer, xBytesToWrite, 1, pxFile );

	/* One item was written. */
	configASSERT( xReturned == 1 );

	/* The write position should be xBytesToWrite into the file. */
	configASSERT( ff_ftell( pxFile ) == ( long ) xBytesToWrite );

	/* The file length as reported by ff_stat() should be zero though as the
	file has not yet been committed. */
	ff_stat( pcFileName, &xStat );
	configASSERT( xStat.st_size == 0 );

	/* Close the file so it can be re-opened in append mode. */
	ff_fclose( pxFile );

	/* Now the file has been closed its size should be reported. */
	ff_stat( pcFileName, &xStat );
	configASSERT( xStat.st_size == xBytesToWrite );

	pxFile = ff_fopen( pcFileName, "a" );
	configASSERT( pxFile );

	/* Write some ascii '1's to the file. */
	memset( pcRAMBuffer, ( int ) '1', fsRAM_BUFFER_SIZE );
	xReturned = ff_fwrite( pcRAMBuffer, 1, xBytesToWrite, pxFile );
	configASSERT( xReturned == xBytesToWrite );

	/* The size reported by stat should not yet have changed. */
	ff_stat( pcFileName, &xStat );
	configASSERT( xStat.st_size == xBytesToWrite );

	/* The file should contain xBytesToWrite lots of '0' and xBytesToWrite lots
	of '1'. The file was opened in append mode so the '1's should appear after
	the	'0's.  Open the file in read mode to check the bytes appear in the file
	as expected. */
	ff_fclose( pxFile );

	/* Now the size reported by ff_stat() should have changed. */
	ff_stat( pcFileName, &xStat );
	configASSERT( xStat.st_size == ( xBytesToWrite * 2UL ) );

	pxFile = ff_fopen( pcFileName, "r" );
	configASSERT( pxFile != NULL );

	/* Start with the RAM buffer clear. */
	memset( pcRAMBuffer, 0x00, fsRAM_BUFFER_SIZE );

	/* Read the data into the RAM buffer. */
	ff_fread( pcRAMBuffer, ( 2 * xBytesToWrite ), 1, pxFile );

	/* Check each byte is as expected. */
	for( xByte = 0; xByte < ( 2 * xBytesToWrite ); xByte++ )
	{
		if( xByte < xBytesToWrite )
		{
			configASSERT( pcRAMBuffer[ xByte ] == '0' );
		}
		else
		{
			configASSERT( pcRAMBuffer[ xByte ] == '1' );
		}
	}

	/* It should not be possible to write to the file as it was opened read
	only. */
	xReturned = ff_fwrite( pcRAMBuffer, 1, 1, pxFile );
	configASSERT( xReturned == 0 );

	/* File size should not have changed. */
	ff_fclose( pxFile );
	ff_stat( pcFileName, &xStat );
	configASSERT( xStat.st_size == ( xBytesToWrite * 2UL ) );

	/* The file now contains data.  Re-open it using "w" mode again.  It should
	be truncated to zero. */
	pxFile = ff_fopen( pcFileName, "w" );
	ff_fclose( pxFile );
	ff_stat( pcFileName, &xStat );
	configASSERT( xStat.st_size == 0 );

	vPortFree( pcRAMBuffer );
	vPortFree( pcFileName );
}
/*-----------------------------------------------------------*/

void vMultiTaskStdioWithCWDTest( const char *const pcMountPath, uint16_t usStackSizeWords )
{
size_t x;
static char cDirName[ fsTASKS_TO_CREATE ][ 20 ]; /* Static as it must still be available in the task. */
char cTaskName[ 5 ];

	/* Create a set of tasks that also create, check and delete files.  These
	are left running as an ad hoc test of multiple tasks accessing the file
	system simultaneously. */
	for( x = 0; x < fsTASKS_TO_CREATE; x++ )
	{
		snprintf( &( cDirName[ x ][ 0 ] ), sizeof( cDirName ), "%s/%d", pcMountPath, x );
		snprintf( cTaskName, sizeof( cTaskName ), "FS%d", x );
		xTaskCreate( prvFileSystemAccessTask,
						cTaskName,
						usStackSizeWords, /* Not used with the Windows port. */
						( void * )  &( cDirName[ x ][ 0 ] ),
						tskIDLE_PRIORITY,
						NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvFileSystemAccessTask( void *pvParameters )
{
extern void vCreateAndVerifyExampleFiles( const char *pcMountPath );
const char * const pcBasePath = ( char * ) pvParameters;

	for( ;; )
	{
		/* Create the directory used as a base by this instance of this task. */
		ff_mkdir( pcBasePath );

		/* Create a few example files on the disk. */
		vCreateAndVerifyExampleFiles( pcBasePath );

		/* A few sanity checks only - can only be called after
		vCreateAndVerifyExampleFiles(). */
		vStdioWithCWDTest( pcBasePath );

		/* Remove the base directory again, ready for another loop. */
		ff_deltree( pcBasePath );
	}
}
/*-----------------------------------------------------------*/
