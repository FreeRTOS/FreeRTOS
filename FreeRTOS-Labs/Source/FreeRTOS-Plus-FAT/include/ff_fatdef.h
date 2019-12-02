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

#ifndef _FF_FATDEF_H_
#define _FF_FATDEF_H_

/*
	This file defines offsets to various data for the FAT specification.
*/

/* MBR / PBR Offsets. */

#define FF_FAT_BYTES_PER_SECTOR		0x00B
#define FF_FAT_SECTORS_PER_CLUS		0x00D
#define FF_FAT_RESERVED_SECTORS		0x00E
#define FF_FAT_NUMBER_OF_FATS		0x010
#define FF_FAT_ROOT_ENTRY_COUNT		0x011
#define FF_FAT_16_TOTAL_SECTORS		0x013
#define	FF_FAT_MEDIA_TYPE           0x015

#define FF_FAT_32_TOTAL_SECTORS		0x020
#define FF_FAT_16_SECTORS_PER_FAT	0x016
#define FF_FAT_32_SECTORS_PER_FAT	0x024
#define FF_FAT_ROOT_DIR_CLUSTER		0x02C
#define FF_FAT_EXT_BOOT_SIGNATURE	0x042

#define FF_FAT_16_VOL_LABEL			0x02B
#define FF_FAT_32_VOL_LABEL			0x047

#define FF_FAT_PTBL					0x1BE
#define FF_FAT_PTBL_LBA				0x008
#define FF_FAT_PTBL_SECT_COUNT		0x00C
#define FF_FAT_PTBL_ACTIVE          0x000
#define FF_FAT_PTBL_ID              0x004

#define FF_DOS_EXT_PART             0x05
#define FF_LINUX_EXT_PART           0x85
#define FF_WIN98_EXT_PART           0x0f

#define FF_FAT_MBR_SIGNATURE        0x1FE

#define FF_FAT_DELETED				0xE5

/* Directory Entry Offsets. */
#define FF_FAT_DIRENT_SHORTNAME		0x000
#define FF_FAT_DIRENT_ATTRIB		0x00B
#define FF_FAT_DIRENT_CREATE_TIME	0x00E	/* Creation Time. */
#define FF_FAT_DIRENT_CREATE_DATE	0x010	/* Creation Date. */
#define FF_FAT_DIRENT_LASTACC_DATE	0x012	/* Date of Last Access. */
#define FF_FAT_DIRENT_CLUS_HIGH		0x014
#define FF_FAT_DIRENT_LASTMOD_TIME	0x016	/* Time of Last modification. */
#define FF_FAT_DIRENT_LASTMOD_DATE	0x018	/* Date of Last modification. */
#define FF_FAT_DIRENT_CLUS_LOW		0x01A
#define FF_FAT_DIRENT_FILESIZE		0x01C
#define FF_FAT_LFN_ORD				0x000
#define FF_FAT_LFN_NAME_1			0x001
#define	FF_FAT_LFN_CHECKSUM			0x00D
#define FF_FAT_LFN_NAME_2			0x00E
#define FF_FAT_LFN_NAME_3			0x01C

/* Dirent Attributes. */
#define FF_FAT_ATTR_READONLY		0x01
#define FF_FAT_ATTR_HIDDEN			0x02
#define FF_FAT_ATTR_SYSTEM			0x04
#define FF_FAT_ATTR_VOLID			0x08
#define FF_FAT_ATTR_DIR				0x10
#define FF_FAT_ATTR_ARCHIVE			0x20
#define FF_FAT_ATTR_LFN				0x0F

/**
 * -- Hein_Tibosch additions for mixed case in shortnames --
 *
 * Specifically, bit 4 means lowercase extension and bit 3 lowercase basename,
 * which allows for combinations such as "example.TXT" or "HELLO.txt" but not "Mixed.txt"
 */

#define FF_FAT_CASE_OFFS			0x0C	/* After NT/XP : 2 case bits. */
#define FF_FAT_CASE_ATTR_BASE		0x08
#define FF_FAT_CASE_ATTR_EXT		0x10

#if( ffconfigLFN_SUPPORT != 0 ) && ( ffconfigINCLUDE_SHORT_NAME != 0 )
#define FF_FAT_ATTR_IS_LFN			0x40	/* artificial attribute, for debugging only. */
#endif

#endif

