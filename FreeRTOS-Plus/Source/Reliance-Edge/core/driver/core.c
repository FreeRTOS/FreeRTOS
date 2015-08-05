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
    @brief Implements the entry-points to the core file system.
*/
#include <redfs.h>
#include <redcoreapi.h>
#include <redcore.h>


/*  Minimum number of blocks needed for metadata on any volume: the master
    block (1), the two metaroots (2), and one doubly-allocated inode (2),
    resulting in 1 + 2 + 2 = 5.
*/
#define MINIMUM_METADATA_BLOCKS (5U)


#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1)
static REDSTATUS CoreCreate(uint32_t ulPInode, const char *pszName, bool fDir, uint32_t *pulInode);
#endif
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_LINK == 1)
static REDSTATUS CoreLink(uint32_t ulPInode, const char *pszName, uint32_t ulInode);
#endif
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) && ((REDCONF_API_POSIX_UNLINK == 1) || (REDCONF_API_POSIX_RMDIR == 1))
static REDSTATUS CoreUnlink(uint32_t ulPInode, const char *pszName);
#endif
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_RENAME == 1)
static REDSTATUS CoreRename(uint32_t ulSrcPInode, const char *pszSrcName, uint32_t ulDstPInode, const char *pszDstName);
#endif
#if REDCONF_READ_ONLY == 0
static REDSTATUS CoreFileWrite(uint32_t ulInode, uint64_t ullStart, uint32_t *pulLen, const void *pBuffer);
#endif
#if TRUNCATE_SUPPORTED
static REDSTATUS CoreFileTruncate(uint32_t ulInode, uint64_t ullSize);
#endif


VOLUME gaRedVolume[REDCONF_VOLUME_COUNT];
static COREVOLUME gaCoreVol[REDCONF_VOLUME_COUNT];

const VOLCONF  * CONST_IF_ONE_VOLUME gpRedVolConf = &gaRedVolConf[0U];
VOLUME         * CONST_IF_ONE_VOLUME gpRedVolume = &gaRedVolume[0U];
COREVOLUME     * CONST_IF_ONE_VOLUME gpRedCoreVol = &gaCoreVol[0U];
METAROOT       *gpRedMR = &gaCoreVol[0U].aMR[0U];

CONST_IF_ONE_VOLUME uint8_t gbRedVolNum;


/** @brief Initialize the Reliance Edge file system driver.

    Prepares the Reliance Edge file system driver to be used.  Must be the first
    Reliance Edge function to be invoked: no volumes can be mounted until the
    driver has been initialized.

    If this function is called when the Reliance Edge driver is already
    initialized, the behavior is undefined.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
REDSTATUS RedCoreInit(void)
{
    REDSTATUS       ret = 0;
    uint8_t         bVolNum;
  #if REDCONF_OUTPUT == 1
    static uint8_t  bSignedOn = 0U; /* Whether the sign on has been printed. */

    if(bSignedOn == 0U)
    {
        RedSignOn();
        bSignedOn = 1U;
    }
  #else
    /*  Call RedSignOn() even when output is disabled, to force the copyright
        text to be referenced and pulled into the program data.
    */
    RedSignOn();
  #endif

    RedMemSet(gaRedVolume, 0U, sizeof(gaRedVolume));
    RedMemSet(gaCoreVol, 0U, sizeof(gaCoreVol));

    RedBufferInit();

    for(bVolNum = 0U; bVolNum < REDCONF_VOLUME_COUNT; bVolNum++)
    {
        VOLUME         *pVol = &gaRedVolume[bVolNum];
        COREVOLUME     *pCoreVol = &gaCoreVol[bVolNum];
        const VOLCONF  *pVolConf = &gaRedVolConf[bVolNum];

        if(    (pVolConf->ulSectorSize < SECTOR_SIZE_MIN)
            || ((REDCONF_BLOCK_SIZE % pVolConf->ulSectorSize) != 0U)
            || (pVolConf->ulInodeCount == 0U))
        {
            ret = -RED_EINVAL;
        }
      #if REDCONF_API_POSIX == 1
        else if(pVolConf->pszPathPrefix == NULL)
        {
            ret = -RED_EINVAL;
        }
        else
        {
          #if REDCONF_VOLUME_COUNT > 1U
            uint8_t bCmpVol;

            /*  Ensure there are no duplicate path prefixes.  Check against all
                previous volumes, which are already verified.
            */
            for(bCmpVol = 0U; bCmpVol < bVolNum; bCmpVol++)
            {
                const char *pszCmpPathPrefix = gaRedVolConf[bCmpVol].pszPathPrefix;

                if(RedStrCmp(pVolConf->pszPathPrefix, pszCmpPathPrefix) == 0)
                {
                    ret = -RED_EINVAL;
                    break;
                }
            }
          #endif
        }
      #endif

        if(ret == 0)
        {
            pVol->bBlockSectorShift = 0U;
            while((pVolConf->ulSectorSize << pVol->bBlockSectorShift) < REDCONF_BLOCK_SIZE)
            {
                pVol->bBlockSectorShift++;
            }

            /*  This should always be true since the block size is confirmed to
                be a power of two (checked at compile time) and above we ensured
                that (REDCONF_BLOCK_SIZE % pVolConf->ulSectorSize) == 0.
            */
            REDASSERT((pVolConf->ulSectorSize << pVol->bBlockSectorShift) == REDCONF_BLOCK_SIZE);

            pVol->ulBlockCount = (uint32_t)(pVolConf->ullSectorCount >> pVol->bBlockSectorShift);

            if(pVol->ulBlockCount < MINIMUM_METADATA_BLOCKS)
            {
                ret = -RED_EINVAL;
            }
            else
            {
              #if REDCONF_READ_ONLY == 0
                pVol->ulTransMask = REDCONF_TRANSACT_DEFAULT;
              #endif

                pVol->ullMaxInodeSize = INODE_SIZE_MAX;

                /*  To understand the following code, note that the fixed-
                    location metadata is located at the start of the disk, in
                    the following order:

                    - Master block (1 block)
                    - Metaroots (2 blocks)
                    - External imap blocks (variable * 2 blocks)
                    - Inode blocks (pVolConf->ulInodeCount * 2 blocks)
                */

                /*  The imap needs bits for all inode and allocable blocks.  If
                    that bitmap will fit into the metaroot, the inline imap is
                    used and there are no imap nodes on disk.  The minus 3 is
                    there since the imap does not include bits for the master
                    block or metaroots.
                */
                pCoreVol->fImapInline = (pVol->ulBlockCount - 3U) <= METAROOT_ENTRIES;

                if(pCoreVol->fImapInline)
                {
                  #if REDCONF_IMAP_INLINE == 1
                    pCoreVol->ulInodeTableStartBN = 3U;
                  #else
                    ret = -RED_EINVAL;
                  #endif
                }
                else
                {
                  #if REDCONF_IMAP_EXTERNAL == 1
                    pCoreVol->ulImapStartBN = 3U;

                    /*  The imap does not include bits for itself, so add two to
                        the number of imap entries for the two blocks of each
                        imap node.  This allows us to divide up the remaining
                        space, making sure to round up so all data blocks are
                        covered.
                    */
                    pCoreVol->ulImapNodeCount =
                        ((pVol->ulBlockCount - 3U) + ((IMAPNODE_ENTRIES + 2U) - 1U)) / (IMAPNODE_ENTRIES + 2U);

                    pCoreVol->ulInodeTableStartBN = pCoreVol->ulImapStartBN + (pCoreVol->ulImapNodeCount * 2U);
                  #else
                    ret = -RED_EINVAL;
                  #endif
                }
            }
        }

        if(ret == 0)
        {
            pCoreVol->ulFirstAllocableBN = pCoreVol->ulInodeTableStartBN + (pVolConf->ulInodeCount * 2U);

            if(pCoreVol->ulFirstAllocableBN > pVol->ulBlockCount)
            {
                /*  We can get here if there is not enough space for the number
                    of configured inodes.
                */
                ret = -RED_EINVAL;
            }
            else
            {
                pVol->ulBlocksAllocable = pVol->ulBlockCount - pCoreVol->ulFirstAllocableBN;
            }
        }

        if(ret != 0)
        {
            break;
        }
    }

    /*  Make sure the configured endianness is correct.
    */
    if(ret == 0)
    {
        uint16_t    uValue = 0xFF00U;
        uint8_t     abBytes[2U];

        RedMemCpy(abBytes, &uValue, sizeof(abBytes));

      #if REDCONF_ENDIAN_BIG == 1
        if(abBytes[0U] != 0xFFU)
      #else
        if(abBytes[0U] != 0x00U)
      #endif
        {
            ret = -RED_EINVAL;
        }
    }

    if(ret == 0)
    {
        ret = RedOsClockInit();

      #if REDCONF_TASK_COUNT > 1U
        if(ret == 0)
        {
            ret = RedOsMutexInit();

            if(ret != 0)
            {
                (void)RedOsClockUninit();
            }
        }
      #endif
    }

    return ret;
}


/** @brief Uninitialize the Reliance Edge file system driver.

    Tears down the Reliance Edge file system driver.  Cannot be used until all
    Reliance Edge volumes are unmounted.  A subsequent call to RedCoreInit()
    will initialize the driver again.

    The behavior of calling this function when the core is already uninitialized
    is undefined.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBUSY  At least one volume is still mounted.
*/
REDSTATUS RedCoreUninit(void)
{
    REDSTATUS ret;

  #if REDCONF_TASK_COUNT > 1U
    ret = RedOsMutexUninit();

    if(ret == 0)
  #endif
    {
        ret = RedOsClockUninit();
    }

    return ret;
}


/** @brief Set the current volume.

    All core APIs operate on the current volume.  This call must precede all
    core accesses.

    @param bVolNum  The volume number to access.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p bVolNum is an invalid volume number.
*/
REDSTATUS RedCoreVolSetCurrent(
    uint8_t     bVolNum)
{
    REDSTATUS   ret;

    if(bVolNum >= REDCONF_VOLUME_COUNT)
    {
        ret = -RED_EINVAL;
    }
    else
    {
      #if REDCONF_VOLUME_COUNT > 1U
        gbRedVolNum = bVolNum;
        gpRedVolConf = &gaRedVolConf[bVolNum];
        gpRedVolume = &gaRedVolume[bVolNum];
        gpRedCoreVol = &gaCoreVol[bVolNum];
        gpRedMR = &gpRedCoreVol->aMR[gpRedCoreVol->bCurMR];
      #endif

        ret = 0;
    }

    return ret;
}


#if FORMAT_SUPPORTED
/** @brief Format a file system volume.

    Uses the statically defined volume configuration.  After calling this
    function, the volume needs to be mounted -- see RedCoreVolMount().

    An error is returned if the volume is mounted.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBUSY  Volume is mounted.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedCoreVolFormat(void)
{
    return RedVolFormat();
}
#endif /* FORMAT_SUPPORTED */


/** @brief Mount a file system volume.

    Prepares the file system volume to be accessed.  Mount will fail if the
    volume has never been formatted, or if the on-disk format is inconsistent
    with the compile-time configuration.

    If the volume is already mounted, the behavior is undefined.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    Volume not formatted, improperly formatted, or corrupt.
*/
REDSTATUS RedCoreVolMount(void)
{
    return RedVolMount();
}


/** @brief Unmount a file system volume.

    This function discards the in-memory state for the file system and marks it
    as unmounted.  Subsequent attempts to access the volume will fail until the
    volume is mounted again.

    If unmount automatic transaction points are enabled, this function will
    commit a transaction point prior to unmounting.  If unmount automatic
    transaction points are disabled, this function will unmount without
    transacting, effectively discarding the working state.

    If the volume is already unmounted, the behavior is undefined.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    I/O error during unmount automatic transaction point.
*/
REDSTATUS RedCoreVolUnmount(void)
{
    REDSTATUS ret = 0;

  #if REDCONF_READ_ONLY == 0
    if(!gpRedVolume->fReadOnly && ((gpRedVolume->ulTransMask & RED_TRANSACT_UMOUNT) != 0U))
    {
        ret = RedVolTransact();
    }
  #endif

    if(ret == 0)
    {
        ret = RedBufferDiscardRange(0U, gpRedVolume->ulBlockCount);
    }

    if(ret == 0)
    {
        ret = RedOsBDevClose(gbRedVolNum);
    }

    if(ret == 0)
    {
        gpRedVolume->fMounted = false;
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Commit a transaction point.

    Reliance Edge is a transactional file system.  All modifications, of both
    metadata and filedata, are initially working state.  A transaction point
    is a process whereby the working state atomically becomes the committed
    state, replacing the previous committed state.  Whenever Reliance Edge is
    mounted, including after power loss, the state of the file system after
    mount is the most recent committed state.  Nothing from the committed
    state is ever missing, and nothing from the working state is ever included.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL The volume is not mounted.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EROFS  The file system volume is read-only.
*/
REDSTATUS RedCoreVolTransact(void)
{
    REDSTATUS ret;

    if(!gpRedVolume->fMounted)
    {
        ret = -RED_EINVAL;
    }
    else if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        ret = RedVolTransact();
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


#if REDCONF_API_POSIX == 1
/** @brief Query file system status information.

    @param pStatFS  The buffer to populate with volume information.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval -RED_EINVAL Volume is not mounted; or @p pStatFS is `NULL`.
*/
REDSTATUS RedCoreVolStat(
    REDSTATFS  *pStatFS)
{
    REDSTATUS   ret;

    if((pStatFS == NULL) || (!gpRedVolume->fMounted))
    {
        ret = -RED_EINVAL;
    }
    else
    {
        RedMemSet(pStatFS, 0U, sizeof(*pStatFS));

        pStatFS->f_bsize = REDCONF_BLOCK_SIZE;
        pStatFS->f_frsize = REDCONF_BLOCK_SIZE;
        pStatFS->f_blocks = gpRedVolume->ulBlockCount;
      #if RESERVED_BLOCKS > 0U
        pStatFS->f_bfree = (gpRedMR->ulFreeBlocks > RESERVED_BLOCKS) ? (gpRedMR->ulFreeBlocks - RESERVED_BLOCKS) : 0U;
      #else
        pStatFS->f_bfree = gpRedMR->ulFreeBlocks;
      #endif
        pStatFS->f_bavail = pStatFS->f_bfree;
        pStatFS->f_files = gpRedVolConf->ulInodeCount;
        pStatFS->f_ffree = gpRedMR->ulFreeInodes;
        pStatFS->f_favail = gpRedMR->ulFreeInodes;

        pStatFS->f_flag = RED_ST_NOSUID;
      #if REDCONF_READ_ONLY == 0
        if(gpRedVolume->fReadOnly)
      #endif
        {
            pStatFS->f_flag |= RED_ST_RDONLY;
        }

        pStatFS->f_namemax = REDCONF_NAME_MAX;
        pStatFS->f_maxfsize = INODE_SIZE_MAX;
        pStatFS->f_dev = gbRedVolNum;

        ret = 0;
    }

    return ret;
}
#endif /* REDCONF_API_POSIX == 1 */


#if (REDCONF_READ_ONLY == 0) && ((REDCONF_API_POSIX == 1) || (REDCONF_API_FSE_TRANSMASKSET == 1))
/** @brief Update the transaction mask.

    The following events are available when using the FSE API:

    - #RED_TRANSACT_UMOUNT
    - #RED_TRANSACT_WRITE
    - #RED_TRANSACT_TRUNCATE
    - #RED_TRANSACT_VOLFULL

    The following events are available when using the POSIX-like API:

    - #RED_TRANSACT_UMOUNT
    - #RED_TRANSACT_CREAT
    - #RED_TRANSACT_UNLINK
    - #RED_TRANSACT_MKDIR
    - #RED_TRANSACT_RENAME
    - #RED_TRANSACT_LINK
    - #RED_TRANSACT_CLOSE
    - #RED_TRANSACT_WRITE
    - #RED_TRANSACT_FSYNC
    - #RED_TRANSACT_TRUNCATE
    - #RED_TRANSACT_VOLFULL

    The #RED_TRANSACT_MANUAL macro (by itself) may be used to disable all
    automatic transaction events.  The #RED_TRANSACT_MASK macro is a bitmask of
    all transaction flags, excluding those representing excluded functionality.

    Attempting to enable events for excluded functionality will result in an
    error.

    @param ulEventMask  A bitwise-OR'd mask of automatic transaction events to
                        be set as the current transaction mode.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL The volume is not mounted; or @p ulEventMask contains
                        invalid bits.
    @retval -RED_EROFS  The file system volume is read-only.
*/
REDSTATUS RedCoreTransMaskSet(
    uint32_t  ulEventMask)
{
    REDSTATUS ret;

    if(!gpRedVolume->fMounted || ((ulEventMask & RED_TRANSACT_MASK) != ulEventMask))
    {
        ret = -RED_EINVAL;
    }
    else if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        gpRedVolume->ulTransMask = ulEventMask;
        ret = 0;
    }

    return ret;
}
#endif


#if (REDCONF_API_POSIX == 1) || (REDCONF_API_FSE_TRANSMASKGET == 1)
/** @brief Read the transaction mask.

    If the volume is read-only, the returned event mask is always zero.

    @param pulEventMask Populated with a bitwise-OR'd mask of automatic
                        transaction events which represent the current
                        transaction mode for the volume.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL The volume is not mounted; or @p pulEventMask is `NULL`.
*/
REDSTATUS RedCoreTransMaskGet(
    uint32_t *pulEventMask)
{
    REDSTATUS ret;

    if(!gpRedVolume->fMounted || (pulEventMask == NULL))
    {
        ret = -RED_EINVAL;
    }
    else
    {
      #if REDCONF_READ_ONLY == 1
        *pulEventMask = 0U;
      #else
        *pulEventMask = gpRedVolume->ulTransMask;
      #endif
        ret = 0;
    }

    return ret;
}
#endif


#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1)
/** @brief Create a file or directory.

    @param ulPInode The inode number of the parent directory.
    @param pszName  A null-terminated name for the new inode.
    @param fDir     Whether to create a directory (true) or file (false).
    @param pulInode On successful return, populated with the inode number of the
                    new file or directory.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EINVAL         The volume is not mounted; or @p pszName is not
                                a valid name; or @p pulInode is `NULL`.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_EROFS          The file system volume is read-only.
    @retval -RED_ENOTDIR        @p ulPInode is not a directory.
    @retval -RED_EBADF          @p ulPInode is not a valid inode.
    @retval -RED_ENOSPC         There is not enough space on the volume to
                                createthe new directory entry; or the directory
                                is full.
    @retval -RED_ENFILE         No available inode slots.
    @retval -RED_ENAMETOOLONG   @p pszName is too long.
    @retval -RED_EEXIST         @p pszName already exists in @p ulPInode.
*/
REDSTATUS RedCoreCreate(
    uint32_t    ulPInode,
    const char *pszName,
    bool        fDir,
    uint32_t   *pulInode)
{
    REDSTATUS   ret;

    if(!gpRedVolume->fMounted)
    {
        ret = -RED_EINVAL;
    }
    else if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        ret = CoreCreate(ulPInode, pszName, fDir, pulInode);

        if(    (ret == -RED_ENOSPC)
            && ((gpRedVolume->ulTransMask & RED_TRANSACT_VOLFULL) != 0U)
            && (gpRedCoreVol->ulAlmostFreeBlocks > 0U))
        {
            ret = RedVolTransact();

            if(ret == 0)
            {
                ret = CoreCreate(ulPInode, pszName, fDir, pulInode);
            }
        }

        if(ret == 0)
        {
            if(fDir && ((gpRedVolume->ulTransMask & RED_TRANSACT_MKDIR) != 0U))
            {
                ret = RedVolTransact();
            }
            else if(!fDir && ((gpRedVolume->ulTransMask & RED_TRANSACT_CREAT) != 0U))
            {
                ret = RedVolTransact();
            }
            else
            {
                /*  No automatic transaction for this operation.
                */
            }
        }
    }

    return ret;
}


/** @brief Create a file or directory.

    @param ulPInode The inode number of the parent directory.
    @param pszName  A null-terminated name for the new inode.
    @param fDir     Whether to create a directory (true) or file (false).
    @param pulInode On successful return, populated with the inode number of the
                    new file or directory.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_EROFS          The file system volume is read-only.
    @retval -RED_ENOTDIR        @p ulPInode is not a directory.
    @retval -RED_EBADF          @p ulPInode is not a valid inode.
    @retval -RED_ENOSPC         There is not enough space on the volume to
                                create the new directory entry; or the directory
                                is full.
    @retval -RED_ENFILE         No available inode slots.
    @retval -RED_ENAMETOOLONG   @p pszName is too long.
    @retval -RED_EEXIST         @p pszName already exists in @p ulPInode.
*/
static REDSTATUS CoreCreate(
    uint32_t    ulPInode,
    const char *pszName,
    bool        fDir,
    uint32_t   *pulInode)
{
    REDSTATUS   ret;

    if(pulInode == NULL)
    {
        ret = -RED_EINVAL;
    }
    else if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        CINODE pino;

        pino.ulInode = ulPInode;
        ret = RedInodeMount(&pino, FTYPE_DIR, false);

        if(ret == 0)
        {
            CINODE ino;

            ino.ulInode = INODE_INVALID;
            ret = RedInodeCreate(&ino, ulPInode, fDir ? RED_S_IFDIR : RED_S_IFREG);

            if(ret == 0)
            {
                ret = RedInodeBranch(&pino);

                if(ret == 0)
                {
                    ret = RedDirEntryCreate(&pino, pszName, ino.ulInode);
                }

                if(ret == 0)
                {
                    *pulInode = ino.ulInode;
                }
                else
                {
                    REDSTATUS ret2;

                    ret2 = RedInodeFree(&ino);
                    CRITICAL_ASSERT(ret2 == 0);
                }

                RedInodePut(&ino, 0U);
            }

            RedInodePut(&pino, (ret == 0) ? (uint8_t)(IPUT_UPDATE_MTIME | IPUT_UPDATE_CTIME) : 0U);
        }
    }

    return ret;
}
#endif /* (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) */


#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_LINK == 1)
/** @brief Create a hard link.

    This creates an additional name (link) for @p ulInode.  The new name refers
    to the same file with the same contents.  If a name is deleted, but the
    underlying file has other names, the file continues to exist.  The link
    count (accessible via RedCoreStat()) indicates the number of names that a
    file has.  All of a file's names are on equal footing: there is nothing
    special about the original name.

    If @p ulInode names a directory, the operation will fail.

    @param ulPInode The inode number of the parent directory.
    @param pszName  The null-terminated name for the new link.
    @param ulInode  The inode to create a hard link to.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EBADF          @p ulPInode is not a valid inode; or @p ulInode
                                is not a valid inode.
    @retval -RED_EEXIST         @p pszName resolves to an existing file.
    @retval -RED_EINVAL         The volume is not mounted; or @p pszName is
                                `NULL`.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_EMLINK         Creating the link would exceed the maximum link
                                count of @p ulInode.
    @retval -RED_ENAMETOOLONG   Attempting to create a link with a name that
                                exceeds the maximum name length.
    @retval -RED_ENOSPC         There is insufficient free space to expand the
                                directory that would contain the link.
    @retval -RED_ENOTDIR        @p ulPInode is not a directory.
    @retval -RED_EPERM          @p ulInode is a directory.
    @retval -RED_EROFS          The requested link requires writing in a
                                directory on a read-only file system.
*/
REDSTATUS RedCoreLink(
    uint32_t    ulPInode,
    const char *pszName,
    uint32_t    ulInode)
{
    REDSTATUS   ret;

    if(!gpRedVolume->fMounted)
    {
        ret = -RED_EINVAL;
    }
    else if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        ret = CoreLink(ulPInode, pszName, ulInode);

        if(    (ret == -RED_ENOSPC)
            && ((gpRedVolume->ulTransMask & RED_TRANSACT_VOLFULL) != 0U)
            && (gpRedCoreVol->ulAlmostFreeBlocks > 0U))
        {
            ret = RedVolTransact();

            if(ret == 0)
            {
                ret = CoreLink(ulPInode, pszName, ulInode);
            }
        }

        if((ret == 0) && ((gpRedVolume->ulTransMask & RED_TRANSACT_LINK) != 0U))
        {
            ret = RedVolTransact();
        }
    }

    return ret;
}


/** @brief Create a hard link.

    @param ulPInode The inode number of the parent directory.
    @param pszName  The null-terminated name for the new link.
    @param ulInode  The inode to create a hard link to.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EBADF          @p ulPInode is not a valid inode; or @p ulInode
                                is not a valid inode.
    @retval -RED_EEXIST         @p pszName resolves to an existing file.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_EMLINK         Creating the link would exceed the maximum link
                                count of @p ulInode.
    @retval -RED_ENAMETOOLONG   Attempting to create a link with a name that
                                exceeds the maximum name length.
    @retval -RED_ENOSPC         There is insufficient free space to expand the
                                directory that would contain the link.
    @retval -RED_ENOTDIR        @p ulPInode is not a directory.
    @retval -RED_EPERM          @p ulInode is a directory.
    @retval -RED_EROFS          The requested link requires writing in a
                                directory on a read-only file system.
*/
static REDSTATUS CoreLink(
    uint32_t    ulPInode,
    const char *pszName,
    uint32_t    ulInode)
{
    REDSTATUS   ret;

    if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        CINODE pino;

        pino.ulInode = ulPInode;
        ret = RedInodeMount(&pino, FTYPE_DIR, false);

        if(ret == 0)
        {
            CINODE ino;

            ino.ulInode = ulInode;
            ret = RedInodeMount(&ino, FTYPE_FILE, false);

            /*  POSIX specifies EPERM as the errno thrown when link() is given a
                directory.  Switch the errno returned if EISDIR was the return
                value.
            */
            if(ret == -RED_EISDIR)
            {
                ret = -RED_EPERM;
            }

            if(ret == 0)
            {
                if(ino.pInodeBuf->uNLink == UINT16_MAX)
                {
                    ret = -RED_EMLINK;
                }
                else
                {
                    ret = RedInodeBranch(&pino);
                }

                if(ret == 0)
                {
                    ret = RedInodeBranch(&ino);
                }

                if(ret == 0)
                {
                    ret = RedDirEntryCreate(&pino, pszName, ino.ulInode);
                }

                if(ret == 0)
                {
                    ino.pInodeBuf->uNLink++;
                }

                RedInodePut(&ino, (ret == 0) ? IPUT_UPDATE_CTIME : 0U);
            }

            RedInodePut(&pino, (ret == 0) ? (uint8_t)(IPUT_UPDATE_MTIME | IPUT_UPDATE_CTIME) : 0U);
        }
    }

    return ret;
}
#endif /* (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_LINK == 1) */


#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) && ((REDCONF_API_POSIX_UNLINK == 1) || (REDCONF_API_POSIX_RMDIR == 1))
/** @brief Delete a file or directory.

    The given name is deleted and the link count of the corresponding inode is
    decremented.  If the link count falls to zero (no remaining hard links),
    the inode will be deleted.

    If the path names a directory which is not empty, the unlink will fail.

    If the deletion frees data in the committed state, it will not return to
    free space until after a transaction point.  Similarly, if the inode was
    part of the committed state, the inode slot will not be available until
    after a transaction point.

    This function can fail when the disk is full.  To fix this, transact and
    try again: Reliance Edge guarantees that it is possible to delete at least
    one file or directory after a transaction point.  If disk full automatic
    transactions are enabled, this will happen automatically.

    @param ulPInode The inode number of the parent directory.
    @param pszName  The null-terminated name of the file or directory to
                    delete.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EBADF          @p ulPInode is not a valid inode.
    @retval -RED_EINVAL         The volume is not mounted; or @p pszName is
                                `NULL`.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_ENAMETOOLONG   @p pszName is too long.
    @retval -RED_ENOENT         @p pszName does not name an existing file or
                                directory.
    @retval -RED_ENOTDIR        @p ulPInode is not a directory.
    @retval -RED_ENOSPC         The file system does not have enough space to
                                modify the parent directory to perform the
                                deletion.
    @retval -RED_ENOTEMPTY      The inode refered to by @p pszName is a
                                directory which is not empty.
*/
REDSTATUS RedCoreUnlink(
    uint32_t    ulPInode,
    const char *pszName)
{
    REDSTATUS   ret;

    if(!gpRedVolume->fMounted)
    {
        ret = -RED_EINVAL;
    }
    else if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        ret = CoreUnlink(ulPInode, pszName);

        if(    (ret == -RED_ENOSPC)
            && ((gpRedVolume->ulTransMask & RED_TRANSACT_VOLFULL) != 0U)
            && (gpRedCoreVol->ulAlmostFreeBlocks > 0U))
        {
            ret = RedVolTransact();

            if(ret == 0)
            {
                ret = CoreUnlink(ulPInode, pszName);
            }
        }

        if((ret == 0) && ((gpRedVolume->ulTransMask & RED_TRANSACT_UNLINK) != 0U))
        {
            ret = RedVolTransact();
        }
    }

    return ret;
}


/** @brief Delete a file or directory.

    @param ulPInode The inode number of the parent directory.
    @param pszName  The null-terminated name of the file or directory to
                    delete.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EBADF          @p ulPInode is not a valid inode.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_ENAMETOOLONG   @p pszName is too long.
    @retval -RED_ENOENT         @p pszName does not name an existing file or
                                directory.
    @retval -RED_ENOTDIR        @p ulPInode is not a directory.
    @retval -RED_ENOSPC         The file system does not have enough space to
                                modify the parent directory to perform the
                                deletion.
    @retval -RED_ENOTEMPTY      The inode refered to by @p pszName is a
                                directory which is not empty.
*/
static REDSTATUS CoreUnlink(
    uint32_t    ulPInode,
    const char *pszName)
{
    REDSTATUS   ret;

    if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        CINODE pino;

        pino.ulInode = ulPInode;
        ret = RedInodeMount(&pino, FTYPE_DIR, false);

        if(ret == 0)
        {
            uint32_t ulDeleteIdx;
            uint32_t ulInode;

            ret = RedDirEntryLookup(&pino, pszName, &ulDeleteIdx, &ulInode);

            if(ret == 0)
            {
                ret = RedInodeBranch(&pino);
            }

            if(ret == 0)
            {
                CINODE ino;

                ino.ulInode = ulInode;
                ret = RedInodeMount(&ino, FTYPE_EITHER, false);

                if(ret == 0)
                {
                    if(ino.fDirectory && (ino.pInodeBuf->ullSize > 0U))
                    {
                        ret = -RED_ENOTEMPTY;
                    }
                    else
                    {
                      #if RESERVED_BLOCKS > 0U
                        gpRedCoreVol->fUseReservedBlocks = true;
                      #endif

                        ret = RedDirEntryDelete(&pino, ulDeleteIdx);

                      #if RESERVED_BLOCKS > 0U
                        gpRedCoreVol->fUseReservedBlocks = false;
                      #endif

                        if(ret == 0)
                        {
                            /*  If the inode is deleted, buffers are needed to
                                read all of the indirects and free the data
                                blocks.  Before doing that, to reduce the
                                minimum number of buffers needed to complete the
                                unlink, release the parent directory inode
                                buffers which are no longer needed.
                            */
                            RedInodePutCoord(&pino);

                            ret = RedInodeLinkDec(&ino);
                            CRITICAL_ASSERT(ret == 0);
                        }
                    }

                    RedInodePut(&ino, (ret == 0) ? IPUT_UPDATE_CTIME : 0U);
                }
            }

            RedInodePut(&pino, (ret == 0) ? (uint8_t)(IPUT_UPDATE_MTIME | IPUT_UPDATE_CTIME) : 0U);
        }
    }

    return ret;
}
#endif /* (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) && ((REDCONF_API_POSIX_UNLINK == 1) || (REDCONF_API_POSIX_RMDIR == 1)) */


#if REDCONF_API_POSIX == 1
/** @brief Look up the inode number of a file or directory.

    @param ulPInode The inode number of the parent directory.
    @param pszName  The null-terminated name of the file or directory to look
                    up.
    @param pulInode On successful return, populated with the inode number named
                    by @p pszName.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0               Operation was successful.
    @retval -RED_EBADF      @p ulPInode is not a valid inode.
    @retval -RED_EINVAL     The volume is not mounted; @p pszName is `NULL`; or
                            @p pulInode is `NULL`.
    @retval -RED_EIO        A disk I/O error occurred.
    @retval -RED_ENOENT     @p pszName does not name an existing file or directory.
    @retval -RED_ENOTDIR    @p ulPInode is not a directory.
*/
REDSTATUS RedCoreLookup(
    uint32_t    ulPInode,
    const char *pszName,
    uint32_t   *pulInode)
{
    REDSTATUS   ret;

    if((pulInode == NULL) || !gpRedVolume->fMounted)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        CINODE ino;

        ino.ulInode = ulPInode;
        ret = RedInodeMount(&ino, FTYPE_DIR, false);

        if(ret == 0)
        {
            ret = RedDirEntryLookup(&ino, pszName, NULL, pulInode);

            RedInodePut(&ino, 0U);
        }
    }

    return ret;
}
#endif /* REDCONF_API_POSIX == 1 */


#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_RENAME == 1)
/** @brief Rename a file or directory.

    If @p pszDstName names an existing file or directory, the behavior depends
    on the configuration.  If #REDCONF_RENAME_ATOMIC is false, and if the
    destination name exists, this function always fails with -RED_EEXIST.

    If #REDCONF_RENAME_ATOMIC is true, and if the new name exists, then in one
    atomic operation, the destination name is unlinked and the source name is
    renamed to the destination name.  Both names must be of the same type (both
    files or both directories).  As with RedCoreUnlink(), if the destination
    name is a directory, it must be empty.  The major exception to this
    behavior is that if both names are links to the same inode, then the rename
    does nothing and both names continue to exist.

    If the rename deletes the old destination, it may free data in the
    committed state, which will not return to free space until after a
    transaction point.  Similarly, if the deleted inode was part of the
    committed state, the inode slot will not be available until after a
    transaction point.

    @param ulSrcPInode  The inode number of the parent directory of the file or
                        directory to rename.
    @param pszSrcName   The name of the file or directory to rename.
    @param ulDstPInode  The new parent directory inode number of the file or
                        directory after the rename.
    @param pszNewPath   The new name of the file or directory after the rename.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EBADF          @p ulSrcPInode is not a valid inode number; or
                                @p ulDstPInode is not a valid inode number.
    @retval -RED_EEXIST         #REDCONF_RENAME_POSIX is false and the
                                destination name exists.
    @retval -RED_EINVAL         The volume is not mounted; @p pszSrcName is
                                `NULL`; or @p pszDstName is `NULL`.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_EISDIR         The destination name exists and is a directory,
                                and the source name is a non-directory.
    @retval -RED_ENAMETOOLONG   Either @p pszSrcName or @p pszDstName is longer
                                than #REDCONF_NAME_MAX.
    @retval -RED_ENOENT         The source name is not an existing entry; or
                                either @p pszSrcName or @p pszDstName point to
                                an empty string.
    @retval -RED_ENOTDIR        @p ulSrcPInode is not a directory; or
                                @p ulDstPInode is not a directory; or the source
                                name is a directory and the destination name is
                                a file.
    @retval -RED_ENOTEMPTY      The destination name is a directory which is not
                                empty.
    @retval -RED_ENOSPC         The file system does not have enough space to
                                extend the @p ulDstPInode directory.
    @retval -RED_EROFS          The directory to be removed resides on a
                                read-only file system.
*/
REDSTATUS RedCoreRename(
    uint32_t    ulSrcPInode,
    const char *pszSrcName,
    uint32_t    ulDstPInode,
    const char *pszDstName)
{
    REDSTATUS   ret;

    if(!gpRedVolume->fMounted)
    {
        ret = -RED_EINVAL;
    }
    else if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        ret = CoreRename(ulSrcPInode, pszSrcName, ulDstPInode, pszDstName);

        if(    (ret == -RED_ENOSPC)
            && ((gpRedVolume->ulTransMask & RED_TRANSACT_VOLFULL) != 0U)
            && (gpRedCoreVol->ulAlmostFreeBlocks > 0U))
        {
            ret = RedVolTransact();

            if(ret == 0)
            {
                ret = CoreRename(ulSrcPInode, pszSrcName, ulDstPInode, pszDstName);
            }
        }

        if((ret == 0) && ((gpRedVolume->ulTransMask & RED_TRANSACT_RENAME) != 0U))
        {
            ret = RedVolTransact();
        }
    }

    return ret;
}


/** @brief Rename a file or directory.

    @param ulSrcPInode  The inode number of the parent directory of the file or
                        directory to rename.
    @param pszSrcName   The name of the file or directory to rename.
    @param ulDstPInode  The new parent directory inode number of the file or
                        directory after the rename.
    @param pszNewPath   The new name of the file or directory after the rename.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EBADF          @p ulSrcPInode is not a valid inode number; or
                                @p ulDstPInode is not a valid inode number.
    @retval -RED_EEXIST         #REDCONF_RENAME_POSIX is false and the
                                destination name exists.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_EISDIR         The destination name exists and is a directory,
                                and the source name is a non-directory.
    @retval -RED_ENAMETOOLONG   Either @p pszSrcName or @p pszDstName is longer
                                than #REDCONF_NAME_MAX.
    @retval -RED_ENOENT         The source name is not an existing entry; or
                                either @p pszSrcName or @p pszDstName point to
                                an empty string.
    @retval -RED_ENOTDIR        @p ulSrcPInode is not a directory; or
                                @p ulDstPInode is not a directory; or the source
                                name is a directory and the destination name is
                                a file.
    @retval -RED_ENOTEMPTY      The destination name is a directory which is not
                                empty.
    @retval -RED_ENOSPC         The file system does not have enough space to
                                extend the @p ulDstPInode directory.
    @retval -RED_EROFS          The directory to be removed resides on a
                                read-only file system.
*/
static REDSTATUS CoreRename(
    uint32_t    ulSrcPInode,
    const char *pszSrcName,
    uint32_t    ulDstPInode,
    const char *pszDstName)
{
    REDSTATUS   ret;

    if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        bool    fUpdateTimestamps = false;
        CINODE  SrcPInode;

        SrcPInode.ulInode = ulSrcPInode;
        ret = RedInodeMount(&SrcPInode, FTYPE_DIR, true);

        if(ret == 0)
        {
            CINODE  DstPInode;
            CINODE *pDstPInode;

            if(ulSrcPInode == ulDstPInode)
            {
                pDstPInode = &SrcPInode;
            }
            else
            {
                pDstPInode = &DstPInode;
                DstPInode.ulInode = ulDstPInode;
                ret = RedInodeMount(pDstPInode, FTYPE_DIR, true);
            }

            if(ret == 0)
            {
                /*  Initialize these to zero so we can unconditionally put them,
                    even if RedDirEntryRename() fails before mounting them.
                */
                CINODE SrcInode = {0U};
                CINODE DstInode = {0U};

                ret = RedDirEntryRename(&SrcPInode, pszSrcName, &SrcInode, pDstPInode, pszDstName, &DstInode);

              #if REDCONF_RENAME_ATOMIC == 1
                if((ret == 0) && (DstInode.ulInode != INODE_INVALID) && (DstInode.ulInode != SrcInode.ulInode))
                {
                    /*  If the inode is deleted, buffers are needed to read all
                        of the indirects and free the data blocks.  Before doing
                        that, to reduce the minimum number of buffers needed to
                        complete the rename, release parent directory inode
                        buffers which are no longer needed.
                    */
                    RedInodePutCoord(&SrcPInode);
                    RedInodePutCoord(pDstPInode);

                    ret = RedInodeLinkDec(&DstInode);
                    CRITICAL_ASSERT(ret == 0);
                }

                if((ret == 0) && (DstInode.ulInode != SrcInode.ulInode))
              #else
                if(ret == 0)
              #endif
                {
                    fUpdateTimestamps = true;
                }

              #if REDCONF_RENAME_ATOMIC == 1
                RedInodePut(&DstInode, 0U);
              #endif

                /*  POSIX says updating ctime for the source inode is optional,
                    but searching around it looks like this is common for Linux
                    and other Unix file systems.
                */
                RedInodePut(&SrcInode, fUpdateTimestamps ? IPUT_UPDATE_CTIME : 0U);
                RedInodePut(pDstPInode, fUpdateTimestamps ? (uint8_t)(IPUT_UPDATE_MTIME | IPUT_UPDATE_CTIME) : 0U);
            }
        }

        RedInodePut(&SrcPInode, fUpdateTimestamps ? (uint8_t)(IPUT_UPDATE_MTIME | IPUT_UPDATE_CTIME) : 0U);
    }

    return ret;
}
#endif /* (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_RENAME == 1) */


#if REDCONF_API_POSIX == 1
/** @brief Get the status of a file or directory.

    See the ::REDSTAT type for the details of the information returned.

    @param ulInode  The inode number of the file or directory whose information
                    is to be retrieved.
    @param pStat    Pointer to a ::REDSTAT buffer to populate.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  @p ulInode is not a valid inode.
    @retval -RED_EINVAL The volume is not mounted; @p pStat is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedCoreStat(
    uint32_t    ulInode,
    REDSTAT    *pStat)
{
    REDSTATUS   ret;

    if(!gpRedVolume->fMounted || (pStat == NULL))
    {
        ret = -RED_EINVAL;
    }
    else
    {
        CINODE ino;

        ino.ulInode = ulInode;
        ret = RedInodeMount(&ino, FTYPE_EITHER, false);
        if(ret == 0)
        {
            RedMemSet(pStat, 0U, sizeof(*pStat));

            pStat->st_dev = gbRedVolNum;
            pStat->st_ino = ulInode;
            pStat->st_mode = ino.pInodeBuf->uMode;
          #if REDCONF_API_POSIX_LINK == 1
            pStat->st_nlink = ino.pInodeBuf->uNLink;
          #else
            pStat->st_nlink = 1U;
          #endif
            pStat->st_size = ino.pInodeBuf->ullSize;
          #if REDCONF_INODE_TIMESTAMPS == 1
            pStat->st_atime = ino.pInodeBuf->ulATime;
            pStat->st_mtime = ino.pInodeBuf->ulMTime;
            pStat->st_ctime = ino.pInodeBuf->ulCTime;
          #endif
          #if REDCONF_INODE_BLOCKS == 1
            pStat->st_blocks = ino.pInodeBuf->ulBlocks;
          #endif

            RedInodePut(&ino, 0U);
        }
    }

    return ret;
}
#endif /* REDCONF_API_POSIX == 1 */


#if REDCONF_API_FSE == 1
/** @brief Get the size of a file.

    @param ulInode  The inode number of the file whose size is to be retrieved.
    @param pullSize On successful exit, populated with the file size.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  @p ulInode is not a valid inode.
    @retval -RED_EINVAL The volume is not mounted; @p pullSize is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EISDIR @p ulInode is a directory inode.
*/
REDSTATUS RedCoreFileSizeGet(
    uint32_t    ulInode,
    uint64_t   *pullSize)
{
    REDSTATUS   ret;

    if(!gpRedVolume->fMounted || (pullSize == NULL))
    {
        ret = -RED_EINVAL;
    }
    else
    {
        CINODE ino;

        ino.ulInode = ulInode;
        ret = RedInodeMount(&ino, FTYPE_FILE, false);
        if(ret == 0)
        {
            *pullSize = ino.pInodeBuf->ullSize;

            RedInodePut(&ino, 0U);
        }
    }

    return ret;
}
#endif /* REDCONF_API_FSE == 1 */


/** @brief Read from a file.

    Data which has not yet been written, but which is before the end-of-file
    (sparse data), shall read as zeroes.  A short read -- where the number of
    bytes read is less than requested -- indicates that the requested read was
    partially or, if zero bytes were read, entirely beyond the end-of-file.

    If @p ullStart is at or beyond the maximum file size, it is treated like
    any other read entirely beyond the end-of-file: no data is read and
    @p pulLen is populated with zero.

    @param ulInode  The inode number of the file to read.
    @param ullStart The file offset to read from.
    @param pulLen   On entry, contains the number of bytes to read; on
                    successful exit, contains the number of bytes actually
                    read.
    @param pBuffer  The buffer to populate with the data read.  Must be big
                    enough for the read request.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  @p ulInode is not a valid inode number.
    @retval -RED_EINVAL The volume is not mounted; or @p pBuffer is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EISDIR The inode is a directory inode.
*/
REDSTATUS RedCoreFileRead(
    uint32_t    ulInode,
    uint64_t    ullStart,
    uint32_t   *pulLen,
    void       *pBuffer)
{
    REDSTATUS   ret;

    if(!gpRedVolume->fMounted || (pulLen == NULL))
    {
        ret = -RED_EINVAL;
    }
    else
    {
      #if (REDCONF_ATIME == 1) && (REDCONF_READ_ONLY == 0)
        bool    fUpdateAtime = (*pulLen > 0U) && !gpRedVolume->fReadOnly;
      #else
        bool    fUpdateAtime = false;
      #endif
        CINODE  ino;

        ino.ulInode = ulInode;
        ret = RedInodeMount(&ino, FTYPE_FILE, fUpdateAtime);
        if(ret == 0)
        {
            ret = RedInodeDataRead(&ino, ullStart, pulLen, pBuffer);

          #if (REDCONF_ATIME == 1) && (REDCONF_READ_ONLY == 0)
            RedInodePut(&ino, ((ret == 0) && fUpdateAtime) ? IPUT_UPDATE_ATIME : 0U);
          #else
            RedInodePut(&ino, 0U);
          #endif
        }
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Write to a file.

    If the write extends beyond the end-of-file, the file size will be
    increased.

    A short write -- where the number of bytes written is less than requested
    -- indicates either that the file system ran out of space but was still
    able to write some of the request; or that the request would have caused
    the file to exceed the maximum file size, but some of the data could be
    written prior to the file size limit.

    If an error is returned, either none of the data was written or a critical
    error occurred (like an I/O error) and the file system volume will be
    read-only.

    @param ulInode  The file number of the file to write.
    @param ullStart The file offset to write at.
    @param pulLen   On entry, the number of bytes to write; on successful exit,
                    the number of bytes actually written.
    @param pBuffer  The buffer containing the data to be written.  Must big
                    enough for the write request.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  @p ulInode is not a valid file number.
    @retval -RED_EFBIG  No data can be written to the given file offset since
                        the resulting file size would exceed the maximum file
                        size.
    @retval -RED_EINVAL The volume is not mounted; or @p pBuffer is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EISDIR The inode is a directory inode.
    @retval -RED_ENOSPC No data can be written because there is insufficient
                        free space.
    @retval -RED_EROFS  The file system volume is read-only.
*/
REDSTATUS RedCoreFileWrite(
    uint32_t    ulInode,
    uint64_t    ullStart,
    uint32_t   *pulLen,
    const void *pBuffer)
{
    REDSTATUS   ret;

    if(!gpRedVolume->fMounted)
    {
        ret = -RED_EINVAL;
    }
    else if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        ret = CoreFileWrite(ulInode, ullStart, pulLen, pBuffer);

        if(    (ret == -RED_ENOSPC)
            && ((gpRedVolume->ulTransMask & RED_TRANSACT_VOLFULL) != 0U)
            && (gpRedCoreVol->ulAlmostFreeBlocks > 0U))
        {
            ret = RedVolTransact();

            if(ret == 0)
            {
                ret = CoreFileWrite(ulInode, ullStart, pulLen, pBuffer);
            }
        }

        if((ret == 0) && ((gpRedVolume->ulTransMask & RED_TRANSACT_WRITE) != 0U))
        {
            ret = RedVolTransact();
        }
    }

    return ret;
}


/** @brief Write to a file.

    @param ulInode  The file number of the file to write.
    @param ullStart The file offset to write at.
    @param pulLen   On entry, the number of bytes to write; on successful exit,
                    the number of bytes actually written.
    @param pBuffer  The buffer containing the data to be written.  Must big
                    enough for the write request.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  @p ulInode is not a valid file number.
    @retval -RED_EFBIG  No data can be written to the given file offset since
                        the resulting file size would exceed the maximum file
                        size.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EISDIR The inode is a directory inode.
    @retval -RED_ENOSPC No data can be written because there is insufficient
                        free space.
    @retval -RED_EROFS  The file system volume is read-only.
*/
static REDSTATUS CoreFileWrite(
    uint32_t    ulInode,
    uint64_t    ullStart,
    uint32_t   *pulLen,
    const void *pBuffer)
{
    REDSTATUS   ret;

    if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        CINODE ino;

        ino.ulInode = ulInode;
        ret = RedInodeMount(&ino, FTYPE_FILE, true);
        if(ret == 0)
        {
            ret = RedInodeDataWrite(&ino, ullStart, pulLen, pBuffer);

            RedInodePut(&ino, (ret == 0) ? (uint8_t)(IPUT_UPDATE_MTIME | IPUT_UPDATE_CTIME) : 0U);
        }
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


#if TRUNCATE_SUPPORTED
/** @brief Set the file size.

    Allows the file size to be increased, decreased, or to remain the same.  If
    the file size is increased, the new area is sparse (will read as zeroes).
    If the file size is decreased, the data beyond the new end-of-file will
    return to free space once it is no longer part of the committed state
    (either immediately or after the next transaction point).

    @param ulInode  The inode of the file to truncate.
    @param ullSize  The new file size, in bytes.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  @p ulInode is not a valid inode number.
    @retval -RED_EFBIG  @p ullSize exceeds the maximum file size.
    @retval -RED_EINVAL The volume is not mounted.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EISDIR The inode is a directory inode.
    @retval -RED_ENOSPC Insufficient free space to perform the truncate.
    @retval -RED_EROFS  The file system volume is read-only.
*/
REDSTATUS RedCoreFileTruncate(
    uint32_t    ulInode,
    uint64_t    ullSize)
{
    REDSTATUS   ret;

    if(!gpRedVolume->fMounted)
    {
        ret = -RED_EINVAL;
    }
    else if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        ret = CoreFileTruncate(ulInode, ullSize);

        if(    (ret == -RED_ENOSPC)
            && ((gpRedVolume->ulTransMask & RED_TRANSACT_VOLFULL) != 0U)
            && (gpRedCoreVol->ulAlmostFreeBlocks > 0U))
        {
            ret = RedVolTransact();

            if(ret == 0)
            {
                ret = CoreFileTruncate(ulInode, ullSize);
            }
        }

        if((ret == 0) && ((gpRedVolume->ulTransMask & RED_TRANSACT_TRUNCATE) != 0U))
        {
            ret = RedVolTransact();
        }
    }

    return ret;
}


/** @brief Set the file size.

    @param ulInode  The inode of the file to truncate.
    @param ullSize  The new file size, in bytes.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  @p ulInode is not a valid inode number.
    @retval -RED_EFBIG  @p ullSize exceeds the maximum file size.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EISDIR The inode is a directory inode.
    @retval -RED_ENOSPC Insufficient free space to perform the truncate.
    @retval -RED_EROFS  The file system volume is read-only.
*/
static REDSTATUS CoreFileTruncate(
    uint32_t    ulInode,
    uint64_t    ullSize)
{
    REDSTATUS   ret;

    if(gpRedVolume->fReadOnly)
    {
        ret = -RED_EROFS;
    }
    else
    {
        CINODE      ino;

        ino.ulInode = ulInode;
        ret = RedInodeMount(&ino, FTYPE_FILE, true);
        if(ret == 0)
        {
          #if RESERVED_BLOCKS > 0U
            gpRedCoreVol->fUseReservedBlocks = (ullSize < ino.pInodeBuf->ullSize);
          #endif

            ret = RedInodeDataTruncate(&ino, ullSize);

          #if RESERVED_BLOCKS > 0U
            gpRedCoreVol->fUseReservedBlocks = false;
          #endif

            RedInodePut(&ino, (ret == 0) ? (uint8_t)(IPUT_UPDATE_MTIME | IPUT_UPDATE_CTIME) : 0U);
        }
    }

    return ret;
}
#endif /* TRUNCATE_SUPPORTED */


#if (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_READDIR == 1)
/** @brief Read from a directory.

    If files are added to the directory after it is opened, the new files may
    or may not be returned by this function.  If files are deleted, the deleted
    files will not be returned.

    @param ulInode  The directory inode to read from.
    @param pulPos   A token which stores the position within the directory.  To
                    read from the beginning of the directory, populate with
                    zero.
    @param pszName  Pointer to a buffer which must be big enough to store a
                    maximum size name, including a null terminator.  On
                    successful exit, populated with the name of the next
                    directory entry.
    @param pulInode On successful return, populated with the inode number of the
                    next directory entry.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0               Operation was successful.
    @retval -RED_EBADF      @p ulInode is not a valid inode number.
    @retval -RED_EINVAL     The volume is not mounted.
    @retval -RED_EIO        A disk I/O error occurred.
    @retval -RED_ENOENT     There are no more entries in the directory.
    @retval -RED_ENOTDIR    @p ulInode refers to a file.
*/
REDSTATUS RedCoreDirRead(
    uint32_t    ulInode,
    uint32_t   *pulPos,
    char       *pszName,
    uint32_t   *pulInode)
{
    REDSTATUS   ret;

    if(!gpRedVolume->fMounted)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        CINODE ino;

        ino.ulInode = ulInode;
        ret = RedInodeMount(&ino, FTYPE_DIR, false);

        if(ret == 0)
        {
            ret = RedDirEntryRead(&ino, pulPos, pszName, pulInode);

          #if (REDCONF_ATIME == 1) && (REDCONF_READ_ONLY == 0)
            if((ret == 0) && !gpRedVolume->fReadOnly)
            {
                ret = RedInodeBranch(&ino);
            }

            RedInodePut(&ino, ((ret == 0) && !gpRedVolume->fReadOnly) ? IPUT_UPDATE_ATIME : 0U);
          #else
            RedInodePut(&ino, 0U);
          #endif
        }
    }

    return ret;
}
#endif /* (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_READDIR == 1) */

