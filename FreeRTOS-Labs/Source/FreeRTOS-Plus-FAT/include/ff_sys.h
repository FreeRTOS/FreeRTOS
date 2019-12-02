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
	ff_sys.h

	This module allow to map several separate file-sub-systems into a root directory

	For instance, a system with 3 sub sytems:

		/flash :  NAND flash driver
		/ram   :  RAM-disk driver
		/      :  SD-card driver

	In this example, the SD-card driver handles ALL files and directories which
	do not match /flash/ * or /ram/ *

	Now for instance a file call "/flash/etc/network.ini"
	will be stored as "/etc/network.ini" on the NAND drive

	This module along with ff_stdio.c make translations between absolute
	and relative paths
*/

#ifndef FF_SYS_H
#define FF_SYS_H

#ifdef __cplusplus
extern "C" {
#endif

typedef struct FILE_SUB_SYSTEM
{
	char pcPath[16];
	BaseType_t xPathlen;
	FF_IOManager_t *pxManager;
} FF_SubSystem_t;

typedef struct FF_DIR_HANDLER
{
	union
	{
		struct
		{
			unsigned
				bEndOfDir : 1,
				bFirstCalled : 1,
				bIsValid : 1,
				bAddDotEntries : 2;
		} bits;
		unsigned uFlags;
	} u;
	/*
	 * path will contain the relative path. It will be used when calling +FAT functions
	 * like FF_FindFirst() / FF_FindNext()
	 * For instance, for "/flash/etc" path will become "/etc"
	 */
	const char *pcPath;
	FF_IOManager_t *pxManager;	/* Will point to handler of this partition. */
	BaseType_t xFSIndex;		/* The index of this entry, where 0 always means: the root system. */
} FF_DirHandler_t;

/*
 * Initialise (clear) the file system table
 * This will also called by FF_FS_Add()
 */
void FF_FS_Init( void );

/*
 * Add a file system
 * The path must be absolute, e.g. start with a slash
 * The second argument is the FF_Disk_t structure that is handling the driver
 */
int FF_FS_Add( const char *pcPath, FF_Disk_t *pxDisk );

/*
 * Remove a file system
 * which ws earlier added by ff_fs_ad()
 */
void FF_FS_Remove( const char *pcPath );

/*
 * Internally used by ff_stdio:
 * The ff_dir_handler helps to iterate through a mounte directory
 *
 * FF_FS_Find() will find a ff_dir_handler for a given path
 */
int FF_FS_Find( const char *pcPath, FF_DirHandler_t *pxHandler );

/*
 * For internal use:
 * Get the file system information, based on an index
 */
int FF_FS_Get( int iIndex, FF_SubSystem_t *pxSystem );

/*
 * Returns the number of registered
 * file systems
 */
int FF_FS_Count( void );

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* FF_SYS_H */
