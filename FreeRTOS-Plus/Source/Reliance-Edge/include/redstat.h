/*             ----> DO NOT REMOVE THE FOLLOWING NOTICE <----
 *
 *                 Copyright (c) 2014-2015 Datalight, Inc.
 *                     All Rights Reserved Worldwide.
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; use version 2 of the License.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but "AS-IS," WITHOUT ANY WARRANTY; without even the implied warranty
 *  of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/*  Businesses and individuals that for commercial or other reasons cannot
 *  comply with the terms of the GPLv2 license may obtain a commercial license
 *  before incorporating Reliance Edge into proprietary software for
 *  distribution in any form.  Visit http://www.datalight.com/reliance-edge for
 *  more information.
 */

/** @file
 */
#ifndef REDSTAT_H
#define REDSTAT_H


/** Mode bit for a directory. */
#define RED_S_IFDIR    0x4000U

/** Mode bit for a regular file. */
#define RED_S_IFREG    0x8000U

/** @brief Test for a directory.
 */
#define RED_S_ISDIR( m )    ( ( ( m ) & RED_S_IFDIR ) != 0U )

/** @brief Test for a regular file.
 */
#define RED_S_ISREG( m )    ( ( ( m ) & RED_S_IFREG ) != 0U )


/** File system is read-only. */
#define RED_ST_RDONLY    0x00000001U

/** File system ignores suid and sgid bits. */
#define RED_ST_NOSUID    0x00000002U


/** @brief Status information on an inode.
 */
typedef struct
{
    uint8_t st_dev;        /**< Volume number of volume containing file. */
    uint32_t st_ino;       /**< File serial number (inode number). */
    uint16_t st_mode;      /**< Mode of file. */
    uint16_t st_nlink;     /**< Number of hard links to the file. */
    uint64_t st_size;      /**< File size in bytes. */
    #if REDCONF_INODE_TIMESTAMPS == 1
        uint32_t st_atime; /**< Time of last access (seconds since 01-01-1970). */
        uint32_t st_mtime; /**< Time of last data modification (seconds since 01-01-1970). */
        uint32_t st_ctime; /**< Time of last status change (seconds since 01-01-1970). */
    #endif
    #if REDCONF_INODE_BLOCKS == 1
        uint32_t st_blocks; /**< Number of blocks allocated for this object. */
    #endif
} REDSTAT;


/** @brief Status information on a file system volume.
 */
typedef struct
{
    uint32_t f_bsize;    /**< File system block size. */
    uint32_t f_frsize;   /**< Fundamental file system block size. */
    uint32_t f_blocks;   /**< Total number of blocks on file system in units of f_frsize. */
    uint32_t f_bfree;    /**< Total number of free blocks. */
    uint32_t f_bavail;   /**< Number of free blocks available to non-privileged process. */
    uint32_t f_files;    /**< Total number of file serial numbers. */
    uint32_t f_ffree;    /**< Total number of free file serial numbers. */
    uint32_t f_favail;   /**< Number of file serial numbers available to non-privileged process. */
    uint32_t f_fsid;     /**< File system ID (useless, populated with zero). */
    uint32_t f_flag;     /**< Bit mask of f_flag values.  Includes read-only file system flag. */
    uint32_t f_namemax;  /**< Maximum filename length. */
    uint64_t f_maxfsize; /**< Maximum file size (POSIX extension). */
    uint32_t f_dev;      /**< Volume number (POSIX extension). */
} REDSTATFS;


#endif /* ifndef REDSTAT_H */
