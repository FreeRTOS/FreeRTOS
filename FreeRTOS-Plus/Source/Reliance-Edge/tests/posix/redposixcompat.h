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
    @brief Defines macros which make the Reliance Edge POSIX-like API look more
           like the actual POSIX API.

    This file is intended for porting POSIX file system tests; it is not
    intended for application use.
*/
#ifndef REDPOSIXCOMPAT_H
#define REDPOSIXCOMPAT_H


#ifndef assert
#define assert(x) REDASSERT(x)
#endif


#undef O_RDONLY
#undef O_WRONLY
#undef O_RDWR
#undef O_APPEND
#undef O_CREAT
#undef O_EXCL
#undef O_TRUNC
#define O_RDONLY RED_O_RDONLY
#define O_WRONLY RED_O_WRONLY
#define O_RDWR RED_O_RDWR
#define O_APPEND RED_O_APPEND
#define O_CREAT RED_O_CREAT
#define O_EXCL RED_O_EXCL
#define O_TRUNC RED_O_TRUNC

#undef SEEK_SET
#undef SEEK_CUR
#undef SEEK_END
#define SEEK_SET RED_SEEK_SET
#define SEEK_CUR RED_SEEK_CUR
#define SEEK_END RED_SEEK_END

/*  Old-fashioned Linux seek names.
*/
#undef L_SET
#undef L_INCR
#undef L_XTND
#define L_SET SEEK_SET
#define L_INCR SEEK_CUR
#define L_XTND SEEK_END

#undef S_IFDIR
#undef S_IFREG
#undef S_ISDIR
#undef S_ISREG
#define S_IFDIR RED_S_IFDIR
#define S_IFREG RED_S_IFREG
#define S_ISDIR(m) RED_S_ISDIR(m)
#define S_ISREG(m) RED_S_ISREG(m)

#undef ST_RDONLY
#undef ST_NOSUID
#define ST_RDONLY RED_ST_RDONLY
#define ST_NOSUID RED_ST_NOSUID

#undef open
#undef creat
#undef unlink
#undef mkdir
#undef rmdir
#undef rename
#undef link
#undef close
#undef read
#undef write
#undef fsync
#undef fdatasync
#undef lseek
#undef ftruncate
#undef fstat
#undef opendir
#undef readdir
#undef rewinddir
#undef closedir
#define open(path, oflag) red_open(path, oflag)
#define creat(path, mode) open(path, O_WRONLY|O_CREAT|O_TRUNC)
#define unlink(path) red_unlink(path)
#define mkdir(path) red_mkdir(path)
#define rmdir(path) red_rmdir(path)
#define rename(old, new) red_rename(old, new)
#define link(path, hardlink) red_link(path, hardlink)
#define close(fd) red_close(fd)
#define read(fd, buf, len) red_read(fd, buf, len)
#define write(fd, buf, len) red_write(fd, buf, len)
#define fsync(fd) red_fsync(fd)
#define fdatasync(fd) fsync(fd)
#define lseek(fd, offset, whence) red_lseek(fd, offset, whence)
#define lseek64(fd, offset, whence) lseek(fd, offset, whence)
#define ftruncate(fd, size) red_ftruncate(fd, size)
#define fstat(fd, stat) red_fstat(fd, stat)
#define fstat64(fd, stat) fstat(fd, stat)
#define opendir(path) red_opendir(path)
#define readdir(dirp) red_readdir(dirp)
#define readdir64(dirp) readdir(dirp)
#define rewinddir(dirp) red_rewinddir(dirp)
#define closedir(dirp) red_closedir(dirp)

#undef DIR
#define DIR REDDIR

#undef errno
#define errno (*(int *)red_errnoptr())

#undef memcpy
#undef memmove
#undef memset
#undef strlen
#undef strncmp
#undef strcmp
#undef strncpy
#define memcpy(d, s, l) RedMemCpy(d, s, (uint32_t)(l))
#define memmove(d, s, l) RedMemMove(d, s, (uint32_t)(l))
#define memset(d, c, l) RedMemSet(d, (uint8_t)(c), (uint32_t)(l))
#define strlen(s) RedStrLen(s)
#define strncmp(s1, s2, l) RedStrNCmp(s1, s2, (uint32_t)(l))
#define strcmp(s1, s2) RedStrCmp(s1, s2)
#define strncpy(d, s, l) RedStrNCpy(d, s, (uint32_t)(l))


#endif


