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

/**
 *	@file		ff_error.c
 *	@ingroup	ERROR
 *
 *	@defgroup	ERR Error Message
 *	@brief		Used to return human readable strings for FreeRTOS+FAT error codes.
 *
 **/
#include <stdio.h>

/* _HT_ with the new GNU settings, the prototype of [v]snprintf()
is not included in stdio.h Don't know why. */
int snprintf( char *, size_t, const char *, ... );

#include "ff_headers.h"

#if !defined( ARRAY_SIZE )
	#define ARRAY_SIZE( x )	( int )( sizeof( x )/sizeof( x )[ 0 ] )
#endif


/* This if-block spans the rest of the source file.*/
#if( ffconfigDEBUG != 0 )

const struct _FFMODULETAB
{
	const char * const strModuleName;
	const uint8_t ucModuleID;
} xFreeRTOSFATModuleTable[] =
{
	{ "Unknown Module",		1},									/* 1 here is ok, as the GetError functions start at the end of the table. */
	{ "ff_ioman.c",			FF_GETMODULE( FF_MODULE_IOMAN ) },
	{ "ff_dir.c",			FF_GETMODULE( FF_MODULE_DIR ) },
	{ "ff_file.c",			FF_GETMODULE( FF_MODULE_FILE ) },
	{ "ff_fat.c",			FF_GETMODULE( FF_MODULE_FAT ) },
	{ "ff_crc.c",			FF_GETMODULE( FF_MODULE_CRC ) },
	{ "ff_format.c",		FF_GETMODULE( FF_MODULE_FORMAT ) },
	{ "ff_memory.c",		FF_GETMODULE( FF_MODULE_MEMORY ) },
	{ "ff_string.c",		FF_GETMODULE( FF_MODULE_STRING ) },
	{ "ff_locking.c",		FF_GETMODULE( FF_MODULE_LOCKING ) },
	{ "ff_time.c",			FF_GETMODULE( FF_MODULE_TIME ) },
	{ "Platform Driver",	FF_GETMODULE( FF_MODULE_DRIVER ) },
};

#if( ffconfigHAS_FUNCTION_TAB != 0 )
const struct _FFFUNCTIONTAB
{
	const char * const strFunctionName;
	const uint16_t ucFunctionID;
} xFreeRTOSFATFunctionTable[] =
{
	{ "Unknown Function",	1},
/*----- FF_IOManager_t - The FreeRTOS+FAT I/O Manager */
	{ "FF_CreateIOManger",        FF_GETMOD_FUNC( FF_CREATEIOMAN ) },
	{ "FF_DeleteIOManager",       FF_GETMOD_FUNC( FF_DESTROYIOMAN ) },
	{ "FF_Mount",                 FF_GETMOD_FUNC( FF_MOUNT ) },
	{ "FF_Unmount",               FF_GETMOD_FUNC( FF_UNMOUNT ) },
	{ "FF_FlushCache",            FF_GETMOD_FUNC( FF_FLUSHCACHE ) },
	{ "FF_GetPartitionBlockSize", FF_GETMOD_FUNC( FF_GETPARTITIONBLOCKSIZE ) },
	{ "FF_BlockRead",             FF_GETMOD_FUNC( FF_BLOCKREAD ) },
	{ "FF_BlockWrite",            FF_GETMOD_FUNC( FF_BLOCKWRITE ) },
	{ "FF_DetermineFatType",      FF_GETMOD_FUNC( FF_DETERMINEFATTYPE ) },
	{ "FF_GetEfiPartitionEntry",  FF_GETMOD_FUNC( FF_GETEFIPARTITIONENTRY ) },
	{ "FF_UserDriver",            FF_GETMOD_FUNC( FF_USERDRIVER ) },
	{ "FF_DecreaseFreeClusters",  FF_GETMOD_FUNC( FF_DECREASEFREECLUSTERS ) },
	{ "FF_IncreaseFreeClusters",  FF_GETMOD_FUNC( FF_INCREASEFREECLUSTERS ) },
	{ "FF_PartitionSearch",       FF_GETMOD_FUNC( FF_PARTITIONSEARCH ) },
	{ "FF_ParseExtended",         FF_GETMOD_FUNC( FF_PARSEEXTENDED ) },


/*----- FF_DIR - The FreeRTOS+FAT directory handling routines */
	{ "FF_FetchEntryWithContext", FF_GETMOD_FUNC( FF_FETCHENTRYWITHCONTEXT ) },
	{ "FF_PushEntryWithContext",  FF_GETMOD_FUNC( FF_PUSHENTRYWITHCONTEXT ) },
	{ "FF_GetEntry",              FF_GETMOD_FUNC( FF_GETENTRY ) },
	{ "FF_FindFirst",             FF_GETMOD_FUNC( FF_FINDFIRST ) },
	{ "FF_FindNext",              FF_GETMOD_FUNC( FF_FINDNEXT ) },
	{ "FF_RewindFind",            FF_GETMOD_FUNC( FF_REWINDFIND ) },
	{ "FF_FindFreeDirent",        FF_GETMOD_FUNC( FF_FINDFREEDIRENT ) },
	{ "FF_PutEntry",              FF_GETMOD_FUNC( FF_PUTENTRY ) },
	{ "FF_CreateShortName",       FF_GETMOD_FUNC( FF_CREATESHORTNAME ) },
	{ "FF_CreateLFNs",            FF_GETMOD_FUNC( FF_CREATELFNS ) },
	{ "FF_ExtendDirectory",       FF_GETMOD_FUNC( FF_EXTENDDIRECTORY ) },
	{ "FF_MkDir",                 FF_GETMOD_FUNC( FF_MKDIR ) },
	{ "FF_Traverse",              FF_GETMOD_FUNC( FF_TRAVERSE ) },
	{ "FF_FindDir",               FF_GETMOD_FUNC( FF_FINDDIR ) },

/*----- FF_FILE - The FreeRTOS+FAT file handling routines */
	{ "FF_GetModeBits",           FF_GETMOD_FUNC( FF_GETMODEBITS ) },
	{ "FF_Open",                  FF_GETMOD_FUNC( FF_OPEN ) },
	{ "FF_isDirEmpty",            FF_GETMOD_FUNC( FF_ISDIREMPTY ) },
	{ "FF_RmDir",                 FF_GETMOD_FUNC( FF_RMDIR ) },
	{ "FF_RmFile",                FF_GETMOD_FUNC( FF_RMFILE ) },
	{ "FF_Move",                  FF_GETMOD_FUNC( FF_MOVE ) },
	{ "FF_isEOF",                 FF_GETMOD_FUNC( FF_ISEOF ) },
	{ "FF_GetSequentialClusters", FF_GETMOD_FUNC( FF_GETSEQUENTIALCLUSTERS ) },
	{ "FF_ReadClusters",          FF_GETMOD_FUNC( FF_READCLUSTERS ) },
	{ "FF_ExtendFile",            FF_GETMOD_FUNC( FF_EXTENDFILE ) },
	{ "FF_WriteClusters",         FF_GETMOD_FUNC( FF_WRITECLUSTERS ) },
	{ "FF_Read",                  FF_GETMOD_FUNC( FF_READ ) },
	{ "FF_GetC",                  FF_GETMOD_FUNC( FF_GETC ) },
	{ "FF_GetLine",               FF_GETMOD_FUNC( FF_GETLINE ) },
	{ "FF_Tell",                  FF_GETMOD_FUNC( FF_TELL ) },
	{ "FF_Write",                 FF_GETMOD_FUNC( FF_WRITE ) },
	{ "FF_PutC",                  FF_GETMOD_FUNC( FF_PUTC ) },
	{ "FF_Seek",                  FF_GETMOD_FUNC( FF_SEEK ) },
	{ "FF_Invalidate",            FF_GETMOD_FUNC( FF_INVALIDATE ) },
	{ "FF_CheckValid",            FF_GETMOD_FUNC( FF_CHECKVALID ) },
	{ "FF_Close",                 FF_GETMOD_FUNC( FF_CLOSE ) },
	{ "FF_SetTime",               FF_GETMOD_FUNC( FF_SETTIME ) },
	{ "FF_BytesLeft",             FF_GETMOD_FUNC( FF_BYTESLEFT ) },
	{ "FF_SetFileTime",           FF_GETMOD_FUNC( FF_SETFILETIME ) },
	{ "FF_InitBuf",               FF_GETMOD_FUNC( FF_INITBUF ) },

/*----- FF_FAT - The FreeRTOS+FAT FAT handling routines */
	{ "FF_getFATEntry",           FF_GETMOD_FUNC( FF_GETFATENTRY ) },
	{ "FF_ClearCluster",          FF_GETMOD_FUNC( FF_CLEARCLUSTER ) },
	{ "FF_putFATEntry",           FF_GETMOD_FUNC( FF_PUTFATENTRY ) },
	{ "FF_FindFreeCluster",       FF_GETMOD_FUNC( FF_FINDFREECLUSTER ) },
	{ "FF_CountFreeClusters",     FF_GETMOD_FUNC( FF_COUNTFREECLUSTERS ) },

/*----- FF_UNICODE - The FreeRTOS+FAT hashing routines */
	{ "FF_Utf8ctoUtf16c",         FF_GETMOD_FUNC( FF_UTF8CTOUTF16C ) },
	{ "FF_Utf16ctoUtf8c",         FF_GETMOD_FUNC( FF_UTF16CTOUTF8C ) },
	{ "FF_Utf32ctoUtf16c",        FF_GETMOD_FUNC( FF_UTF32CTOUTF16C ) },
	{ "FF_Utf16ctoUtf32c",        FF_GETMOD_FUNC( FF_UTF16CTOUTF32C ) },

/*----- FF_FORMAT - The FreeRTOS+FAT format routine */
	{ "FF_FormatPartition",       FF_GETMOD_FUNC( FF_FORMATPARTITION ) },

/*----- FF_STDIO - The FreeRTOS+FAT stdio front-end */
	{ "ff_chmod",                 FF_GETMOD_FUNC( FF_CHMOD ) },
	{ "ff_stat",                  FF_GETMOD_FUNC( FF_STAT_FUNC ) },
};
#endif /* ffconfigHAS_FUNCTION_TAB */

#define TPASTE2( a, b )  a##b

#if( ffconfigLONG_ERR_MSG != 0 )
	/* To get the full error msg: "Not enough memory (malloc( ) returned NULL )" */
	#define ERR_ENTRY( M, E ) { M, TPASTE2( FF_ERR_, E ) }
#else
	/* To get a shorter msg: "NOT_ENOUGH_MEMORY" */
	#define ERR_ENTRY( M, E ) { #E, TPASTE2( FF_ERR_, E ) }
#endif	/* ffconfigLONG_ERR_MSG */

const struct _FFERRTAB
{
	const char * const strErrorString;
	const uint8_t		ucErrorCode;		/* Currently there are less then 256 errors, so lets keep this table small. */
} xFreeRTOSFATErrorTable[] =
{
	{"Unknown or Generic Error!",			1},
	ERR_ENTRY( "No Error",																	NONE ),
	ERR_ENTRY( "Null Pointer provided, (probably for IOMAN)",								NULL_POINTER ),
	ERR_ENTRY( "Not enough memory (malloc() returned NULL)",								NOT_ENOUGH_MEMORY ),
	ERR_ENTRY( "Device Driver returned a FATAL error!",										DEVICE_DRIVER_FAILED ),
	ERR_ENTRY( "The blocksize is not 512 multiple",											IOMAN_BAD_BLKSIZE ),
	ERR_ENTRY( "The memory size, is not a multiple of the blocksize. (Atleast 2 Blocks)",	IOMAN_BAD_MEMSIZE ),
	ERR_ENTRY( "Device is already registered, use FF_UnregisterBlkDevice() first",			IOMAN_DEV_ALREADY_REGD ),
	ERR_ENTRY( "No mountable partition was found on the specified device",					IOMAN_NO_MOUNTABLE_PARTITION ),
    ERR_ENTRY( "The format of the MBR was unrecognised",									IOMAN_INVALID_FORMAT ),
    ERR_ENTRY( "The provided partition number is out-of-range (0 - 3)",						IOMAN_INVALID_PARTITION_NUM ),
    ERR_ENTRY( "The selected partition / volume doesn't appear to be FAT formatted",		IOMAN_NOT_FAT_FORMATTED ),
    ERR_ENTRY( "Cannot register device. (BlkSize not a multiple of 512)",					IOMAN_DEV_INVALID_BLKSIZE ),
    ERR_ENTRY( "Cannot unregister device, a partition is still mounted",					IOMAN_PARTITION_MOUNTED ),
    ERR_ENTRY( "Cannot unmount the partition while there are active FILE handles",			IOMAN_ACTIVE_HANDLES ),
	ERR_ENTRY( "The GPT partition header appears to be corrupt, refusing to mount",			IOMAN_GPT_HEADER_CORRUPT ),
	ERR_ENTRY( "Disk full",                                                                 IOMAN_NOT_ENOUGH_FREE_SPACE ),
	ERR_ENTRY( "Attempted to Read a sector out of bounds",									IOMAN_OUT_OF_BOUNDS_READ ),
	ERR_ENTRY( "Attempted to Write a sector out of bounds",									IOMAN_OUT_OF_BOUNDS_WRITE ),
	ERR_ENTRY( "I/O driver is busy",                                                        IOMAN_DRIVER_BUSY ),
	ERR_ENTRY( "I/O driver returned fatal error",                                           IOMAN_DRIVER_FATAL_ERROR ),
	ERR_ENTRY( "I/O driver returned \"no medium error\"",                                   IOMAN_DRIVER_NOMEDIUM ),

    ERR_ENTRY( "Cannot open the file, file already in use",									FILE_ALREADY_OPEN ),
    ERR_ENTRY( "The specified file could not be found",										FILE_NOT_FOUND ),
    ERR_ENTRY( "Cannot open a Directory",													FILE_OBJECT_IS_A_DIR ),
	ERR_ENTRY( "Cannot open for writing: File is marked as Read-Only",						FILE_IS_READ_ONLY ),
    ERR_ENTRY( "Path not found",															FILE_INVALID_PATH ),
	ERR_ENTRY( "File operation failed - the file was not opened for writing",				FILE_NOT_OPENED_IN_WRITE_MODE ),
	ERR_ENTRY( "File operation failed - the file was not opened for reading",				FILE_NOT_OPENED_IN_READ_MODE ),
	ERR_ENTRY( "File operation failed - could not extend file",								FILE_EXTEND_FAILED ),
	ERR_ENTRY( "Destination file already exists",											FILE_DESTINATION_EXISTS ),
	ERR_ENTRY( "Source file was not found",													FILE_SOURCE_NOT_FOUND ),
	ERR_ENTRY( "Destination path (dir) was not found",										FILE_DIR_NOT_FOUND ),
	ERR_ENTRY( "Failed to create the directory Entry",										FILE_COULD_NOT_CREATE_DIRENT ),
	ERR_ENTRY( "A file handle was invalid",													FILE_BAD_HANDLE ),
#if( ffconfigREMOVABLE_MEDIA != 0 )
	ERR_ENTRY( "File handle got invalid because media was removed",							FILE_MEDIA_REMOVED ),
#endif	/* ffconfigREMOVABLE_MEDIA */
    ERR_ENTRY( "A file or folder of the same name already exists",							DIR_OBJECT_EXISTS ),
    ERR_ENTRY( "DIR_DIRECTORY_FULL",														DIR_DIRECTORY_FULL ),
    ERR_ENTRY( "DIR_END_OF_DIR",															DIR_END_OF_DIR ),
    ERR_ENTRY( "The directory is not empty",												DIR_NOT_EMPTY ),
	ERR_ENTRY( "Could not extend File or Folder - No Free Space!",							FAT_NO_FREE_CLUSTERS ),
	ERR_ENTRY( "Could not find the directory specified by the path",						DIR_INVALID_PATH ),
	ERR_ENTRY( "The Root Dir is full, and cannot be extended on Fat12 or 16 volumes",		DIR_CANT_EXTEND_ROOT_DIR ),
	ERR_ENTRY( "Not enough space to extend the directory.",									DIR_EXTEND_FAILED ),
	ERR_ENTRY( "Name exceeds the number of allowed characters for a filename",				DIR_NAME_TOO_LONG ),

#if( ffconfigUNICODE_UTF16_SUPPORT != 0 )
	ERR_ENTRY( "An invalid Unicode character was provided!",								UNICODE_INVALID_CODE ),
	ERR_ENTRY( "Not enough space in the UTF-16 buffer to encode the entire sequence",		UNICODE_DEST_TOO_SMALL ),
	ERR_ENTRY( "An invalid UTF-16 sequence was encountered",								UNICODE_INVALID_SEQUENCE ),
	ERR_ENTRY( "Filename exceeds MAX long-filename length when converted to UTF-16",		UNICODE_CONVERSION_EXCEEDED ),
#endif	/* ffconfigUNICODE_UTF16_SUPPORT */
};

/**
 *	@public
 *	@brief	Returns a pointer to a string relating to a FreeRTOS+FAT error code.
 *
 *	@param	iErrorCode	The error code.
 *
 *	@return	Pointer to a string describing the error.
 *
 **/
const char *FF_GetErrMessage( FF_Error_t iErrorCode )
{
	uint32_t stCount = ARRAY_SIZE( xFreeRTOSFATErrorTable );

	while( stCount-- )
	{
		if( ( ( UBaseType_t )xFreeRTOSFATErrorTable[ stCount ].ucErrorCode ) == FF_GETERROR( iErrorCode ) )
		{
			break;
		}
	}
	return xFreeRTOSFATErrorTable[ stCount ].strErrorString;
}

const char *FF_GetErrModule( FF_Error_t iErrorCode )
{
	uint32_t stCount = ARRAY_SIZE( xFreeRTOSFATModuleTable );
	while( stCount-- )
	{
		if( xFreeRTOSFATModuleTable[ stCount ].ucModuleID == ( uint8_t )FF_GETMODULE( iErrorCode ) )
		{
			break;
		}
	}
	return xFreeRTOSFATModuleTable[ stCount ].strModuleName;
}

#if( ffconfigHAS_FUNCTION_TAB != 0 )
	const char *FF_GetErrFunction( FF_Error_t iErrorCode )
	{
		uint32_t stCount = ARRAY_SIZE( xFreeRTOSFATFunctionTable );
		uint16_t ModuleFunc = FF_GETMOD_FUNC( iErrorCode );
		static char funcCode[32];
		while( stCount-- != 0 )
		{
			if( xFreeRTOSFATFunctionTable[ stCount ].ucFunctionID == ModuleFunc )
			{
				return xFreeRTOSFATFunctionTable[ stCount ].strFunctionName;
			}
		}
		snprintf( funcCode, sizeof( funcCode ), "Func %X", ModuleFunc );
		return ( const char * )funcCode;
	}
#endif /* ffconfigHAS_FUNCTION_TAB */

const char *FF_GetErrDescription( FF_Error_t iErrorCode, char *apBuf, int aMaxlen )
{
	if( FF_isERR( iErrorCode ) )
	{
#if( ffconfigHAS_FUNCTION_TAB != 0 )
		snprintf (apBuf, ( size_t ) aMaxlen, "%s::%s::%s",
			FF_GetErrModule( iErrorCode ),
			FF_GetErrFunction( iErrorCode ),
			FF_GetErrMessage( iErrorCode ));
#else
		snprintf (apBuf, ( size_t ) aMaxlen, "%s::%s",
			FF_GetErrModule( iErrorCode ),
			FF_GetErrMessage( iErrorCode ));
#endif /* ffconfigHAS_FUNCTION_TAB */
	}
	else
	{
		snprintf (apBuf, ( size_t ) aMaxlen, "No error");
	}
	return apBuf;
}

#endif	/* ffconfigDEBUG != 0 */
