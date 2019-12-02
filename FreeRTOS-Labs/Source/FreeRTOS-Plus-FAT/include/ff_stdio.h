/*
 * FreeRTOS+FAT build 191128 - Note:  FreeRTOS+FAT is still in the lab!
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Authors include James Walmsley, Hein Tibosch and Richard Barry
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
 * https://www.FreeRTOS.org
 *
 */

/*
	ff_stdio.h

	An front-end which make +FAT look like the well-known stdio-functions
*/

#ifndef FF_STDIO_H
#define FF_STDIO_H

#if defined(__WIN32__)
	#include <dir.h>
#endif

/* Standard includes. */
#include <stdio.h>
#include <stdarg.h>

/* FreeRTOS+FAT  includes. */
#include "ff_headers.h"
#include "ff_sys.h"

#if( ffconfigDEV_SUPPORT != 0 )
	#include "ff_devices.h"
#endif

#ifdef __cplusplus
extern "C" {
#endif

/* Error return from some functions. */
#define FF_EOF	(-1)

/* Bits used in the FF_Stat_t structure. */
#define	FF_IFDIR	0040000u	/* directory */
#define	FF_IFCHR	0020000u	/* character special */
#define	FF_IFBLK	0060000u	/* block special */
#define	FF_IFREG	0100000u	/* regular */

/* Bits used in the FF_FindData_t structure. */
#define FF_FA_NORMAL	0x00
#define FF_FA_RDONLY	0x01
#define FF_FA_HIDDEN	0x02
#define FF_FA_SYSTEM	0x04
#define FF_FA_LABEL		0x08
#define FF_FA_DIREC		0x10
#define FF_FA_ARCH		0x20

/* FreeRTOS+FAT uses three thread local buffers.  The first stores errno, the
second a pointer to the CWD structure (if one is used), and the third the more
descriptive error code. */
#define stdioERRNO_THREAD_LOCAL_OFFSET 		( ffconfigCWD_THREAD_LOCAL_INDEX + 0 )
#define stdioCWD_THREAD_LOCAL_OFFSET		( ffconfigCWD_THREAD_LOCAL_INDEX + 1 )
#define stdioFF_ERROR_THREAD_LOCAL_OFFSET	( ffconfigCWD_THREAD_LOCAL_INDEX + 2 )


/* Structure used with ff_stat(). */
typedef struct FF_STAT
{
	uint32_t st_ino;	/* First data cluster number. */
    uint32_t st_size;	/* Size of the object in number of bytes. */
	uint16_t st_dev;			/* The device on which the file can be found (see ff_sys.c) */
    uint16_t st_mode;			/* The mode (attribute bits) of this file or directory. */

	#if( ffconfigTIME_SUPPORT == 1 )
		uint32_t st_atime;
		uint32_t st_mtime;
		uint32_t st_ctime;
	#endif /* ffconfigTIME_SUPPORT */
} FF_Stat_t;

/* Structure used with ff_findfirst(), ff_findnext(), etc. */
typedef struct
{
	/* private */
	UBaseType_t
		#if( ffconfigDEV_SUPPORT != 0 )
		bIsDeviceDir : 1,
		#endif
		bEntryPOwner : 1;
	struct FF_DIR_HANDLER xDirectoryHandler;
	FF_DirEnt_t       xDirectoryEntry;

	/* Public fields included so FF_DirEnt_t does not need to be public. */
    const char * pcFileName;
	uint32_t ulFileSize;
	uint8_t ucAttributes;

} FF_FindData_t;

/*-----------------------------------------------------------
 * Get and set the task's file system errno
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
/*
	int FF_GetErrno( void );
	void FF_SetErrno( int ff_errno );

	_RB_ comments are incorrect and index should use the stdioERRNO_THREAD_LOCAL_OFFSET offset.
*/

/* The errno is stored in a thread local buffer. */
static portINLINE void stdioSET_ERRNO( int iErrno )
{
	vTaskSetThreadLocalStoragePointer( NULL, ffconfigCWD_THREAD_LOCAL_INDEX, ( void * ) ( iErrno ) );
}

static portINLINE int stdioGET_ERRNO( void )
{
void *pvResult;

	pvResult = pvTaskGetThreadLocalStoragePointer( ( TaskHandle_t )NULL, ffconfigCWD_THREAD_LOCAL_INDEX );
	return ( int ) pvResult;
}

#if( ( configNUM_THREAD_LOCAL_STORAGE_POINTERS - ffconfigCWD_THREAD_LOCAL_INDEX ) < 3 )
	#error Please define space for 3 entries
#endif

/*
 * Store the FreeRTOS+FAT error code, which provides more detail than errno.
 */
static portINLINE void stdioSET_FF_ERROR( FF_Error_t iFF_ERROR )
{
	vTaskSetThreadLocalStoragePointer( NULL, stdioFF_ERROR_THREAD_LOCAL_OFFSET, ( void * ) ( iFF_ERROR ) );
}

/*
 * Read back the FreeRTOS+FAT error code, which provides more detail than
 * errno.
 */
static portINLINE FF_Error_t stdioGET_FF_ERROR( void )
{
void *pvResult;

	pvResult = pvTaskGetThreadLocalStoragePointer( NULL, stdioFF_ERROR_THREAD_LOCAL_OFFSET );
	return ( FF_Error_t ) pvResult;
}

/*-----------------------------------------------------------
 * Open and close a file
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
FF_FILE *ff_fopen( const char *pcFile, const char *pcMode );
int ff_fclose( FF_FILE *pxStream );


/*-----------------------------------------------------------
 * Seek and tell
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
int ff_fseek( FF_FILE *pxStream, long lOffset, int iWhence );
void ff_rewind( FF_FILE *pxStream );
long ff_ftell( FF_FILE *pxStream );
int ff_feof( FF_FILE *pxStream );


/*-----------------------------------------------------------
 * Read and write
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
size_t ff_fread( void *pvBuffer, size_t xSize, size_t xItems, FF_FILE * pxStream );
size_t ff_fwrite( const void *pvBuffer, size_t xSize, size_t xItems, FF_FILE * pxStream );

/* Whenever possible, use ellipsis parameter type checking.
_RB_ Compiler specifics need to be moved to the compiler specific header files. */
#if defined(__GNUC__)
	/* The GNU-C compiler will check if the parameters are correct. */
	int ff_fprintf( FF_FILE * pxStream, const char *pcFormat, ... )
		__attribute__ ( ( format ( __printf__, 2, 3 ) ) );
#else
	int ff_fprintf( FF_FILE * pxStream, const char *pcFormat, ... );
#endif

int ff_fgetc( FF_FILE * pxStream);
int ff_fputc( int iChar, FF_FILE *pxStream );
char *ff_fgets( char *pcBuffer, size_t xCount, FF_FILE *pxStream );


/*-----------------------------------------------------------
 * Change length of file (truncate)
 * File should have been opened in "w" or "a" mode
 * The actual length of the file will be made equal to the current writing
 * position
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
int ff_seteof( FF_FILE *pxStream );

/*-----------------------------------------------------------
 * Open a file in append/update mode, truncate its length to a given value,
 * or write zero's up until the required length, and return a handle to the open
 * file.  If NULL is returned, ff_errno contains an error code.
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
FF_FILE *ff_truncate( const char * pcFileName, long lTruncateSize );

/*-----------------------------------------------------------
 * Flush to disk
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
int ff_fflush( FF_FILE *pxStream );


/*-----------------------------------------------------------
 * Create directory, remove and rename files
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
#if( ffconfigMKDIR_RECURSIVE == 0 )
	int ff_mkdir( const char *pcPath );
#else
	/* If the parameter bRecursive is non-zero, the entire path will be checked
	and if necessary, created. */
	int ff_mkdir( const char *pcPath, int bRecursive );
#endif

/*-----------------------------------------------------------
 * Create path specified by the pcPath parameter.
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
int ff_mkpath( const char *pcPath );

/*-----------------------------------------------------------
 * Remove the directory specified by the pcDirectory parameter.
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
int ff_rmdir( const char *pcDirectory );

/*-----------------------------------------------------------
 * Delete a directory and, recursively, all of its contents.
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
#if( ffconfigUSE_DELTREE != 0 )
	/* By default, this function will not be compiled.  The function will
	recursively call itself, which is against the FreeRTOS coding standards, so
	IT MUST BE USED WITH CARE.

	The cost of each recursion will be roughly:
		Stack : 48 (12 stack words)
		Heap  : 112 + ffconfigMAX_FILENAME
	These numbers may change depending on CPU and compiler. */
	int ff_deltree( const char *pcPath );
#endif

/*-----------------------------------------------------------
 * Remove/delete a file.
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
int ff_remove( const char *pcPath );

/*-----------------------------------------------------------
 * Move a file, also cross-directory but not across a file system.
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
int ff_rename( const char *pcOldName, const char *pcNewName, int bDeleteIfExists );


/*-----------------------------------------------------------
 * Get the status of a file.
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
int ff_stat( const char *pcFileName, FF_Stat_t *pxStatBuffer );
/* _HT_ Keep this for a while, until the new ff_stat() is wel tested */
int ff_old_stat( const char *pcName, FF_Stat_t *pxStatBuffer );

/*-----------------------------------------------------------
 * Get the length of a file in bytes.
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
size_t ff_filelength( FF_FILE *pxFile );

/*-----------------------------------------------------------
 * Working directory and iterating through directories.
 * The most up to date API documentation is currently provided on the following URL:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_FAT/Standard_File_System_API.html
 *-----------------------------------------------------------*/
#if ffconfigHAS_CWD
	int ff_chdir( const char *pcDirectoryName );
	char *ff_getcwd( char *pcBuffer, size_t xBufferLength );
#endif

int ff_findfirst( const char *pcDirectory, FF_FindData_t *pxFindData );
int ff_findnext( FF_FindData_t *pxFindData );
int ff_isdirempty(const char *pcPath );


/* _RB_ What to do regarding documentation for the definitions below here. */

#if( ffconfig64_NUM_SUPPORT != 0 )
	int64_t ff_diskfree(const char *pcPath, uint32_t *pxSectorCount );
#else
	int32_t ff_diskfree(const char *pcPath, uint32_t *pxSectorCount );
#endif
int ff_finddir( const char *pcPath );

#if( ffconfigHAS_CWD == 1 )
	/* Obtain the CWD used by the current task. */
	void ff_free_CWD_space( void );
#endif

typedef enum _EFileAction {
	eFileCreate,
	eFileRemove,
	eFileChange,
	eFileIsDir = 0x80,
} eFileAction_t;

void callFileEvents( const char *apPath, eFileAction_t aAction );

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* FF_STDIO_H */
