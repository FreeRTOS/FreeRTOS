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
*/
#ifndef REDVOLUME_H
#define REDVOLUME_H


/** @brief Per-volume configuration structure.

    Contains the configuration values that may differ between volumes.  Must be
    declared in an array in redconf.c in the Reliance Edge project directory and
    statically initialized with values representing the volume configuration of
    the target system.
*/
typedef struct
{
    /** The sector size for the block device underlying the volume: the basic
        unit for reading and writing to the storage media.  Commonly ranges
        between 512 and 4096, but any power-of-two value not greater than the
        block size will work.
    */
    uint32_t    ulSectorSize;

    /** The number of sectors in this file system volume.
    */
    uint64_t    ullSectorCount;

    /** Whether a sector write on the block device underlying the volume is
        atomic.  It is atomic if when the sector write is interrupted, the
        contents of the sector are guaranteed to be either all of the new data,
        or all of the old data.  If unsure, leave as false.
    */
    bool        fAtomicSectorWrite;

    /** This is the maximum number of inodes (files and directories).  This
        number includes the root directory inode (inode 2; created during
        format), but does not include inodes 0 or 1, which do not exist on
        disk.  The number of inodes cannot be less than 1.
    */
    uint32_t    ulInodeCount;

  #if REDCONF_API_POSIX == 1
    /** The path prefix for the volume; for example, "VOL1:", "FlashDisk", etc.
    */
    const char *pszPathPrefix;
  #endif
} VOLCONF;

extern const VOLCONF gaRedVolConf[REDCONF_VOLUME_COUNT];
extern const VOLCONF * CONST_IF_ONE_VOLUME gpRedVolConf;


/** @brief Per-volume run-time data.
*/
typedef struct
{
    /** Whether the volume is currently mounted.
    */
    bool        fMounted;

  #if REDCONF_READ_ONLY == 0
    /** Whether the volume is read-only.
    */
    bool        fReadOnly;

    /** The active automatic transaction mask.
    */
    uint32_t    ulTransMask;
  #endif

    /** The power of 2 difference between sector size and block size.
    */
    uint8_t     bBlockSectorShift;

    /** The number of logical blocks in this file system volume.  The unit here
        is the global block size.
    */
    uint32_t    ulBlockCount;

    /** The total number of allocable blocks; Also the maximum count of free
        blocks.
    */
    uint32_t    ulBlocksAllocable;

    /** The maximum number of bytes that an inode is capable of addressing.
    */
    uint64_t    ullMaxInodeSize;

    /** The current metadata sequence number.  This value is included in all
        metadata nodes and incremented every time a metadata node is written.
        It is assumed to never wrap around.
    */
    uint64_t    ullSequence;
} VOLUME;

/*  Array of VOLUME structures, populated at during RedCoreInit().
*/
extern VOLUME gaRedVolume[REDCONF_VOLUME_COUNT];

/*  Volume number currently being accessed; populated during
    RedCoreVolSetCurrent().
*/
extern CONST_IF_ONE_VOLUME uint8_t gbRedVolNum;

/*  Pointer to the volume currently being accessed; populated during
    RedCoreVolSetCurrent().
*/
extern VOLUME * CONST_IF_ONE_VOLUME gpRedVolume;

#endif

