/*             ----> DO NOT REMOVE THE FOLLOWING NOTICE <----

                   Copyright (c) 2014-2015 Datalight, Inc.
                       All Rights Reserved Worldwide.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; use version 2 of the License.

    This program is distributed in the hope that it will be useful,
    but "AS-IS," WITHOUT ANY WARRANTY; without even the implied warranty
    of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along
    with this program; if not, write to the Free Software Foundation, Inc.,
    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
*/
/*  Businesses and individuals that for commercial or other reasons cannot
    comply with the terms of the GPLv2 license may obtain a commercial license
    before incorporating Reliance Edge into proprietary software for
    distribution in any form.  Visit http://www.datalight.com/reliance-edge for
    more information.
*/
/** @file
    @brief Interface for the Reliance Edge POSIX-like API.

    The POSIX-like file system API is the primary file system API for
    Reliance Edge, which supports the full functionality of the file system.
    This API aims to be compatible with POSIX where reasonable, but it is
    simplified considerably to meet the needs of resource-constrained embedded
    systems.  The API has also been extended to provide access to the unique
    features of Reliance Edge, and to cover areas (like mountins and formatting)
    which do not have APIs in the POSIX specification.
*/
#ifndef REDPOSIX_H
#define REDPOSIX_H

/*  This header is intended for application use; some applications are written
    in C++.
*/
#ifdef __cplusplus
extern "C" {
#endif

#include <redconf.h>

#if REDCONF_API_POSIX == 1

#include <redtypes.h>
#include "redapimacs.h"
#include "rederrno.h"
#include "redstat.h"

/** Open for reading only. */
#define RED_O_RDONLY    0x00000001U

/** Open for writing only. */
#define RED_O_WRONLY    0x00000002U

/** Open for reading and writing. */
#define RED_O_RDWR      0x00000004U

/** File offset for all writes is end-of-file. */
#define RED_O_APPEND    0x00000008U

/** Create the file. */
#define RED_O_CREAT     0x00000010U

/** Error if path already exists. */
#define RED_O_EXCL      0x00000020U

/** Truncate file to size zero. */
#define RED_O_TRUNC     0x00000040U


/** @brief Last file system error (errno).

    Under normal circumstances, each task using the file system has an
    independent `red_errno` value.  Applications do not need to worry about
    one task obliterating an error value that another task needed to read.  The
    value is initially zero.  When one of the POSIX-like APIs return an
    indication of error, `red_errno` is set to an error value.

    In some circumstances, `red_errno` will be a global errno location which
    is shared by multiple tasks.  If the calling task is not registered as a
    file system user and all of the task slots are full, there can be no
    task-specific errno, so the global errno is used.  Likewise, if the file
    system driver is uninitialized, there are no registered file system users
    and `red_errno` always refers to the global errno.  Under these
    circumstances, multiple tasks manipulating `red_errno` could be
    problematic.  When the task count is set to one, `red_errno` always refers
    to the global errno.

    Note that `red_errno` is usable as an lvalue; i.e., in addition to reading
    the error value, the error value can be set:

    ~~~{.c}
    red_errno = 0;
    ~~~
*/
#define red_errno (*red_errnoptr())


/** @brief Positions from which to seek within a file.
*/
typedef enum
{
    /*  0/1/2 are the traditional values for SET/CUR/END, respectively.  Prior
        to the release of Unix System V in 1983, the SEEK_* symbols did not
        exist and C programs hard-coded the 0/1/2 values with those meanings.
    */
    RED_SEEK_SET = 0,   /**< Set file offset to given offset. */
    RED_SEEK_CUR = 1,   /**< Set file offset to current offset plus signed offset. */
    RED_SEEK_END = 2    /**< Set file offset to EOF plus signed offset. */
} REDWHENCE;


#if REDCONF_API_POSIX_READDIR == 1
/** @brief Opaque directory handle.
*/
typedef struct sREDHANDLE REDDIR;


/** @brief Directory entry information.
*/
typedef struct
{
    uint32_t    d_ino;  /**< File serial number (inode number). */
    char        d_name[REDCONF_NAME_MAX+1U];    /**< Name of entry. */
    REDSTAT     d_stat; /**< File information (POSIX extension). */
} REDDIRENT;
#endif


int32_t red_init(void);
int32_t red_uninit(void);
int32_t red_mount(const char *pszVolume);
int32_t red_umount(const char *pszVolume);
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX_FORMAT == 1)
int32_t red_format(const char *pszVolume);
#endif
#if REDCONF_READ_ONLY == 0
int32_t red_transact(const char *pszVolume);
#endif
#if REDCONF_READ_ONLY == 0
int32_t red_settransmask(const char *pszVolume, uint32_t ulEventMask);
#endif
int32_t red_gettransmask(const char *pszVolume, uint32_t *pulEventMask);
int32_t red_statvfs(const char *pszVolume, REDSTATFS *pStatvfs);
int32_t red_open(const char *pszPath, uint32_t ulOpenMode);
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX_UNLINK == 1)
int32_t red_unlink(const char *pszPath);
#endif
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX_MKDIR == 1)
int32_t red_mkdir(const char *pszPath);
#endif
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX_RMDIR == 1)
int32_t red_rmdir(const char *pszPath);
#endif
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX_RENAME == 1)
int32_t red_rename(const char *pszOldPath, const char *pszNewPath);
#endif
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX_LINK == 1)
int32_t red_link(const char *pszPath, const char *pszHardLink);
#endif
int32_t red_close(int32_t iFildes);
int32_t red_read(int32_t iFildes, void *pBuffer, uint32_t ulLength);
#if REDCONF_READ_ONLY == 0
int32_t red_write(int32_t iFildes, const void *pBuffer, uint32_t ulLength);
#endif
#if REDCONF_READ_ONLY == 0
int32_t red_fsync(int32_t iFildes);
#endif
int64_t red_lseek(int32_t iFildes, int64_t llOffset, REDWHENCE whence);
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX_FTRUNCATE == 1)
int32_t red_ftruncate(int32_t iFildes, uint64_t ullSize);
#endif
int32_t red_fstat(int32_t iFildes, REDSTAT *pStat);
#if REDCONF_API_POSIX_READDIR == 1
REDDIR *red_opendir(const char *pszPath);
REDDIRENT *red_readdir(REDDIR *pDirStream);
void red_rewinddir(REDDIR *pDirStream);
int32_t red_closedir(REDDIR *pDirStream);
#endif
REDSTATUS *red_errnoptr(void);

#endif /* REDCONF_API_POSIX */


#ifdef __cplusplus
}
#endif

#endif

