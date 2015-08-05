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
    @brief Implements directory operations.
*/
#include <redfs.h>

#if REDCONF_API_POSIX == 1

#include <redcore.h>


#define DIR_INDEX_INVALID   UINT32_MAX

#if (REDCONF_NAME_MAX % 4U) != 0U
#define DIRENT_PADDING      (4U - (REDCONF_NAME_MAX % 4U))
#else
#define DIRENT_PADDING      (0U)
#endif
#define DIRENT_SIZE         (4U + REDCONF_NAME_MAX + DIRENT_PADDING)
#define DIRENTS_PER_BLOCK   (REDCONF_BLOCK_SIZE / DIRENT_SIZE)
#define DIRENTS_MAX         (uint32_t)REDMIN(UINT32_MAX, UINT64_SUFFIX(1) * INODE_DATA_BLOCKS * DIRENTS_PER_BLOCK)


/** @brief On-disk directory entry.
*/
typedef struct
{
    /** The inode number that the directory entry points at.  If the directory
        entry is available, this holds INODE_INVALID.
    */
    uint32_t    ulInode;

    /** The name of the directory entry.  For names shorter than
        REDCONF_NAME_MAX, unused bytes in the array are zeroed.  For names of
        the maximum length, the string is not null terminated.
    */
    char        acName[REDCONF_NAME_MAX];

  #if DIRENT_PADDING > 0U
    /** Unused padding so that ulInode is always aligned on a four-byte
        boundary.
    */
    uint8_t     abPadding[DIRENT_PADDING];
  #endif
} DIRENT;


#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX_RENAME == 1)
static REDSTATUS DirCyclicRenameCheck(uint32_t ulSrcInode, const CINODE *pDstPInode);
#endif
#if REDCONF_READ_ONLY == 0
static REDSTATUS DirEntryWrite(CINODE *pPInode, uint32_t ulIdx, uint32_t ulInode, const char *pszName, uint32_t ulNameLen);
static uint64_t DirEntryIndexToOffset(uint32_t ulIdx);
#endif
static uint32_t DirOffsetToEntryIndex(uint64_t ullOffset);


#if REDCONF_READ_ONLY == 0
/** @brief Create a new entry in a directory.

    @param pPInode      A pointer to the cached inode structure of the directory
                        to which the new entry will be added.
    @param pszName      The name to be given to the new entry, terminated by a
                        null or a path separator.
    @param ulInode      The inode number the new name will point at.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_ENOSPC         There is not enough space on the volume to
                                create the new directory entry; or the directory
                                is full.
    @retval -RED_ENOTDIR        @p pPInode is not a directory.
    @retval -RED_ENAMETOOLONG   @p pszName is too long.
    @retval -RED_EEXIST         @p pszName already exists in @p ulPInode.
    @retval -RED_EINVAL         @p pPInode is not a mounted dirty cached inode
                                structure; or @p pszName is not a valid name.
*/
REDSTATUS RedDirEntryCreate(
    CINODE     *pPInode,
    const char *pszName,
    uint32_t    ulInode)
{
    REDSTATUS   ret;

    if(!CINODE_IS_DIRTY(pPInode) || (pszName == NULL) || !INODE_IS_VALID(ulInode))
    {
        ret = -RED_EINVAL;
    }
    else if(!pPInode->fDirectory)
    {
        ret = -RED_ENOTDIR;
    }
    else
    {
        uint32_t ulNameLen = RedNameLen(pszName);

        if(ulNameLen == 0U)
        {
            ret = -RED_EINVAL;
        }
        else if(ulNameLen > REDCONF_NAME_MAX)
        {
            ret = -RED_ENAMETOOLONG;
        }
        else
        {
            uint32_t ulEntryIdx;

            ret = RedDirEntryLookup(pPInode, pszName, &ulEntryIdx, NULL);
            if(ret == 0)
            {
                ret = -RED_EEXIST;
            }
            else if(ret == -RED_ENOENT)
            {
                if(ulEntryIdx == DIR_INDEX_INVALID)
                {
                    ret = -RED_ENOSPC;
                }
                else
                {
                    ret = 0;
                }
            }
            else
            {
                /*  Unexpected error, no action.
                */
            }

            if(ret == 0)
            {
                ret = DirEntryWrite(pPInode, ulEntryIdx, ulInode, pszName, ulNameLen);
            }
        }
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


#if DELETE_SUPPORTED
/** @brief Delete an existing directory entry.

    @param pPInode      A pointer to the cached inode structure of the directory
                        containing the entry to be deleted.
    @param ulDeleteIdx  Position within the directory of the entry to be
                        deleted.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0               Operation was successful.
    @retval -RED_EIO        A disk I/O error occurred.
    @retval -RED_ENOSPC     The file system does not have enough space to modify
                            the parent directory to perform the deletion.
    @retval -RED_ENOTDIR    @p pPInode is not a directory.
    @retval -RED_EINVAL     @p pPInode is not a mounted dirty cached inode
                            structure; or @p ulIdx is out of range.
*/
REDSTATUS RedDirEntryDelete(
    CINODE     *pPInode,
    uint32_t    ulDeleteIdx)
{
    REDSTATUS   ret = 0;

    if(!CINODE_IS_DIRTY(pPInode) || (ulDeleteIdx >= DIRENTS_MAX))
    {
        ret = -RED_EINVAL;
    }
    else if(!pPInode->fDirectory)
    {
        ret = -RED_ENOTDIR;
    }
    else if((DirEntryIndexToOffset(ulDeleteIdx) + DIRENT_SIZE) == pPInode->pInodeBuf->ullSize)
    {
        uint32_t ulTruncIdx = ulDeleteIdx;
        bool     fDone = false;

        /*  We are deleting the last dirent in the directory, so search
            backwards to find the last populated dirent, allowing us to truncate
            the directory to that point.
        */
        while((ret == 0) && (ulTruncIdx > 0U) && !fDone)
        {
            ret = RedInodeDataSeekAndRead(pPInode, ulTruncIdx / DIRENTS_PER_BLOCK);

            if(ret == 0)
            {
                const DIRENT *pDirents = CAST_CONST_DIRENT_PTR(pPInode->pbData);
                uint32_t      ulBlockIdx = (ulTruncIdx - 1U) % DIRENTS_PER_BLOCK;

                do
                {
                    if(pDirents[ulBlockIdx].ulInode != INODE_INVALID)
                    {
                        fDone = true;
                        break;
                    }

                    ulTruncIdx--;
                    ulBlockIdx--;
                } while(ulBlockIdx != UINT32_MAX);
            }
            else if(ret == -RED_ENODATA)
            {
                ret = 0;

                REDASSERT((ulTruncIdx % DIRENTS_PER_BLOCK) == 0U);
                ulTruncIdx -= DIRENTS_PER_BLOCK;
            }
            else
            {
                /*  Unexpected error, loop will terminate; nothing else
                    to be done.
                */
            }
        }

        /*  Truncate the directory, deleting the requested entry and any empty
            dirents at the end of the directory.
        */
        if(ret == 0)
        {
            ret = RedInodeDataTruncate(pPInode, DirEntryIndexToOffset(ulTruncIdx));
        }
    }
    else
    {
        /*  The dirent to delete is not the last entry in the directory, so just
            zero it.
        */
        ret = DirEntryWrite(pPInode, ulDeleteIdx, INODE_INVALID, "", 0U);
    }

    return ret;
}
#endif /* DELETE_SUPPORTED */


/** @brief Perform a case-sensitive search of a directory for a given name.

    If found, then position of the entry within the directory and the inode
    number it points to are returned.  As an optimization for directory entry
    creation, in the case where the requested entry does not exist, the position
    of the first available (unused) entry is returned.

    @param pPInode      A pointer to the cached inode structure of the directory
                        to search.
    @param pszName      The name of the desired entry, terminated by either a
                        null or a path separator.
    @param pulEntryIdx  On successful return, meaning that the desired entry
                        exists, populated with the position of the entry.  If
                        returning an -RED_ENOENT error, populated with the
                        position of the first available entry, or set to
                        DIR_INDEX_INVALID if the directory is full.  Optional.
    @param pulInode     On successful return, populated with the inode number
                        that the name points to.  Optional; may be `NULL`.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_ENOENT         @p pszName does not name an existing file or
                                directory.
    @retval -RED_ENOTDIR        @p pPInode is not a directory.
    @retval -RED_EINVAL         @p pPInode is not a mounted cached inode
                                structure; or @p pszName is not a valid name; or
                                @p pulEntryIdx is `NULL`.
    @retval -RED_ENAMETOOLONG   @p pszName is too long.
*/
REDSTATUS RedDirEntryLookup(
    CINODE     *pPInode,
    const char *pszName,
    uint32_t   *pulEntryIdx,
    uint32_t   *pulInode)
{
    REDSTATUS   ret = 0;

    if(!CINODE_IS_MOUNTED(pPInode) || (pszName == NULL))
    {
        ret = -RED_EINVAL;
    }
    else if(!pPInode->fDirectory)
    {
        ret = -RED_ENOTDIR;
    }
    else
    {
        uint32_t ulNameLen = RedNameLen(pszName);

        if(ulNameLen == 0U)
        {
            ret = -RED_EINVAL;
        }
        else if(ulNameLen > REDCONF_NAME_MAX)
        {
            ret = -RED_ENAMETOOLONG;
        }
        else
        {
            uint32_t    ulIdx = 0U;
            uint32_t    ulDirentCount = DirOffsetToEntryIndex(pPInode->pInodeBuf->ullSize);
            uint32_t    ulFreeIdx = DIR_INDEX_INVALID;  /* Index of first free dirent. */

            /*  Loop over the directory blocks, searching each block for a
                dirent that matches the given name.
            */
            while((ret == 0) && (ulIdx < ulDirentCount))
            {
                ret = RedInodeDataSeekAndRead(pPInode, ulIdx / DIRENTS_PER_BLOCK);

                if(ret == 0)
                {
                    const DIRENT *pDirents = CAST_CONST_DIRENT_PTR(pPInode->pbData);
                    uint32_t      ulBlockLastIdx = REDMIN(DIRENTS_PER_BLOCK, ulDirentCount - ulIdx);
                    uint32_t      ulBlockIdx;

                    for(ulBlockIdx = 0U; ulBlockIdx < ulBlockLastIdx; ulBlockIdx++)
                    {
                        const DIRENT *pDirent = &pDirents[ulBlockIdx];

                        if(pDirent->ulInode != INODE_INVALID)
                        {
                            /*  The name in the dirent will not be null
                                terminated if it is of the maximum length, so
                                use a bounded string compare and then make sure
                                there is nothing more to the name.
                            */
                            if(    (RedStrNCmp(pDirent->acName, pszName, ulNameLen) == 0)
                                && ((ulNameLen == REDCONF_NAME_MAX) || (pDirent->acName[ulNameLen] == '\0')))
                            {
                                /*  Found a matching dirent, stop and return its
                                    information.
                                */
                                if(pulInode != NULL)
                                {
                                    *pulInode = pDirent->ulInode;

                                  #ifdef REDCONF_ENDIAN_SWAP
                                    *pulInode = RedRev32(*pulInode);
                                  #endif
                                }

                                ulIdx += ulBlockIdx;
                                break;
                            }
                        }
                        else if(ulFreeIdx == DIR_INDEX_INVALID)
                        {
                            ulFreeIdx = ulIdx + ulBlockIdx;
                        }
                        else
                        {
                            /*  The directory entry is free, but we already found a free one, so there's
                                nothing to do here.
                            */
                        }
                    }

                    if(ulBlockIdx < ulBlockLastIdx)
                    {
                        /*  If we broke out of the for loop, we found a matching
                            dirent and can stop the search.
                        */
                        break;
                    }

                    ulIdx += ulBlockLastIdx;
                }
                else if(ret == -RED_ENODATA)
                {
                    if(ulFreeIdx == DIR_INDEX_INVALID)
                    {
                        ulFreeIdx = ulIdx;
                    }

                    ret = 0;
                    ulIdx += DIRENTS_PER_BLOCK;
                }
                else
                {
                    /*  Unexpected error, let the loop terminate, no action
                        here.
                    */
                }
            }

            if(ret == 0)
            {
                /*  If we made it all the way to the end of the directory
                    without stopping, then the given name does not exist in the
                    directory.
                */
                if(ulIdx == ulDirentCount)
                {
                    /*  If the directory had no sparse dirents, then the first
                        free dirent is beyond the end of the directory.  If the
                        directory is already the maximum size, then there is no
                        free dirent.
                    */
                    if((ulFreeIdx == DIR_INDEX_INVALID) && (ulDirentCount < DIRENTS_MAX))
                    {
                        ulFreeIdx = ulDirentCount;
                    }

                    ulIdx = ulFreeIdx;

                    ret = -RED_ENOENT;
                }

                if(pulEntryIdx != NULL)
                {
                    *pulEntryIdx = ulIdx;
                }
            }
        }
    }

    return ret;
}


#if (REDCONF_API_POSIX_READDIR == 1) || (REDCONF_CHECKER == 1)
/** @brief Read the next entry from a directory, given a starting index.

    @param pInode   A pointer to the cached inode structure of the directory to
                    read from.
    @param pulIdx   On entry, the directory index to start reading from.  On
                    successful return, populated with the directory index to use
                    for subsequent reads.  On -RED_ENOENT return, populated with
                    the directory index immediately following the last valid
                    one.
    @param pszName  On successful return, populated with the name of the next
                    directory entry.  Buffer must be at least
                    REDCONF_NAME_MAX + 1 in size, to store the maximum name
                    length plus a null terminator.
    @param pulInode On successful return, populated with the inode number
                    pointed at by the next directory entry.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0               Operation was successful.
    @retval -RED_EIO        A disk I/O error occurred.
    @retval -RED_ENOENT     There are no more entries in the directory.
    @retval -RED_ENOTDIR    @p pPInode is not a directory.
    @retval -RED_EINVAL     @p pPInode is not a mounted cached inode structure;
                            or @p pszName is `NULL`; or @p pulIdx is `NULL`; or
                            @p pulInode is `NULL`.
*/
REDSTATUS RedDirEntryRead(
    CINODE     *pPInode,
    uint32_t   *pulIdx,
    char       *pszName,
    uint32_t   *pulInode)
{
    REDSTATUS   ret = 0;

    if(!CINODE_IS_MOUNTED(pPInode) || (pulIdx == NULL) || (pszName == NULL) || (pulInode == NULL))
    {
        ret = -RED_EINVAL;
    }
    else if(!pPInode->fDirectory)
    {
        ret = -RED_ENOTDIR;
    }
    else
    {
        uint32_t ulIdx = *pulIdx;
        uint32_t ulDirentCount = DirOffsetToEntryIndex(pPInode->pInodeBuf->ullSize);

        /*  Starting either at the beginning of the directory or where we left
            off, loop over the directory blocks, searching each block for a
            non-sparse dirent to return as the next entry in the directory.
        */
        while((ret == 0) && (ulIdx < ulDirentCount))
        {
            uint32_t ulBlockOffset = ulIdx / DIRENTS_PER_BLOCK;

            ret = RedInodeDataSeekAndRead(pPInode, ulBlockOffset);

            if(ret == 0)
            {
                const DIRENT *pDirents = CAST_CONST_DIRENT_PTR(pPInode->pbData);
                uint32_t      ulBlockLastIdx = REDMIN(DIRENTS_PER_BLOCK, ulDirentCount - (ulBlockOffset * DIRENTS_PER_BLOCK));
                uint32_t      ulBlockIdx;

                for(ulBlockIdx = ulIdx % DIRENTS_PER_BLOCK; ulBlockIdx < ulBlockLastIdx; ulBlockIdx++)
                {
                    if(pDirents[ulBlockIdx].ulInode != INODE_INVALID)
                    {
                        *pulIdx = ulIdx + 1U;
                        RedStrNCpy(pszName, pDirents[ulBlockIdx].acName, REDCONF_NAME_MAX);
                        pszName[REDCONF_NAME_MAX] = '\0';

                        *pulInode = pDirents[ulBlockIdx].ulInode;

                      #ifdef REDCONF_ENDIAN_SWAP
                        *pulInode = RedRev32(*pulInode);
                      #endif
                        break;
                    }

                    ulIdx++;
                }

                if(ulBlockIdx < ulBlockLastIdx)
                {
                    REDASSERT(ulIdx <= ulDirentCount);
                    break;
                }
            }
            else if(ret == -RED_ENODATA)
            {
                ulIdx += DIRENTS_PER_BLOCK - (ulIdx % DIRENTS_PER_BLOCK);
                ret = 0;
            }
            else
            {
                /*  Unexpected error, loop will terminate; nothing else to do.
                */
            }

            REDASSERT(ulIdx <= ulDirentCount);
        }

        if((ret == 0) && (ulIdx >= ulDirentCount))
        {
            *pulIdx = ulDirentCount;
            ret = -RED_ENOENT;
        }
    }

    return ret;
}
#endif


#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX_RENAME == 1)
/** Rename a directory entry.

    @param pSrcPInode   The inode of the directory containing @p pszSrcName.
    @param pszSrcName   The name of the directory entry to be renamed.
    @param pSrcInode    On successful return, populated with the inode of the
                        source entry.
    @param pDstPInode   The inode of the directory in which @p pszDstName will
                        be created or replaced.
    @param pszDstName   The name of the directory entry to be created or
                        replaced.
    @param pDstInode    On successful return, if the destination previously
                        existed, populated with the inode previously pointed to
                        by the destination.  This may be the same as the source
                        inode.  If the destination did not exist, populated with
                        INODE_INVALID.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0                   Operation was successful.
    @retval -RED_EEXIST         #REDCONF_RENAME_ATOMIC is false and the
                                destination name exists.
    @retval -RED_EINVAL         @p pSrcPInode is not a mounted dirty cached
                                inode structure; or @p pSrcInode is `NULL`; or
                                @p pszSrcName is not a valid name; or
                                @p pDstPInode is not a mounted dirty cached
                                inode structure; or @p pDstInode is `NULL`; or
                                @p pszDstName is not a valid name.
    @retval -RED_EIO            A disk I/O error occurred.
    @retval -RED_EISDIR         The destination name exists and is a directory,
                                and the source name is a non-directory.
    @retval -RED_ENAMETOOLONG   Either @p pszSrcName or @p pszDstName is longer
                                than #REDCONF_NAME_MAX.
    @retval -RED_ENOENT         The source name is not an existing entry; or
                                either @p pszSrcName or @p pszDstName point to
                                an empty string.
    @retval -RED_ENOTDIR        @p pSrcPInode is not a directory; or
                                @p pDstPInode is not a directory; or the source
                                name is a directory and the destination name is
                                a file.
    @retval -RED_ENOTEMPTY      The destination name is a directory which is not
                                empty.
    @retval -RED_ENOSPC         The file system does not have enough space to
                                extend the @p ulDstPInode directory.
    @retval -RED_EROFS          The directory to be removed resides on a
                                read-only file system.
*/
REDSTATUS RedDirEntryRename(
    CINODE     *pSrcPInode,
    const char *pszSrcName,
    CINODE     *pSrcInode,
    CINODE     *pDstPInode,
    const char *pszDstName,
    CINODE     *pDstInode)
{
    REDSTATUS   ret;

    if(    !CINODE_IS_DIRTY(pSrcPInode)
        || (pszSrcName == NULL)
        || (pSrcInode == NULL)
        || !CINODE_IS_DIRTY(pDstPInode)
        || (pszDstName == NULL)
        || (pDstInode == NULL))
    {
        ret = -RED_EINVAL;
    }
    else if(!pSrcPInode->fDirectory || !pDstPInode->fDirectory)
    {
        ret = -RED_ENOTDIR;
    }
    else
    {
        uint32_t ulDstIdx = 0U; /* Init'd to quiet warnings. */
        uint32_t ulSrcIdx;

        /*  Look up the source and destination names.
        */
        ret = RedDirEntryLookup(pSrcPInode, pszSrcName, &ulSrcIdx, &pSrcInode->ulInode);

        if(ret == 0)
        {
            ret = RedDirEntryLookup(pDstPInode, pszDstName, &ulDstIdx, &pDstInode->ulInode);

            if(ret == -RED_ENOENT)
            {
                if(ulDstIdx == DIR_INDEX_INVALID)
                {
                    ret = -RED_ENOSPC;
                }
                else
                {
                  #if REDCONF_RENAME_ATOMIC == 1
                    pDstInode->ulInode = INODE_INVALID;
                  #endif
                    ret = 0;
                }
            }
          #if REDCONF_RENAME_ATOMIC == 0
            else if(ret == 0)
            {
                ret = -RED_EEXIST;
            }
            else
            {
                /*  Nothing to do here, just propagate the error.
                */
            }
          #endif
        }

      #if REDCONF_RENAME_ATOMIC == 1
        /*  If both names point to the same inode, POSIX says to do nothing to
            either name.
        */
        if((ret == 0) && (pSrcInode->ulInode != pDstInode->ulInode))
      #else
        if(ret == 0)
      #endif
        {
            ret = RedInodeMount(pSrcInode, FTYPE_EITHER, true);

          #if REDCONF_RENAME_ATOMIC == 1
            if((ret == 0) && (pDstInode->ulInode != INODE_INVALID))
            {
                /*  Source and destination must be the same type (file/dir).
                */
                ret = RedInodeMount(pDstInode, pSrcInode->fDirectory ? FTYPE_DIR : FTYPE_FILE, true);

                /*  If renaming directories, the destination must be empty.
                */
                if((ret == 0) && pDstInode->fDirectory && (pDstInode->pInodeBuf->ullSize > 0U))
                {
                    ret = -RED_ENOTEMPTY;
                }
            }
          #endif

            /*  If we are renaming a directory, make sure the rename isn't
                cyclic (e.g., renaming "foo" into "foo/bar").
            */
            if((ret == 0) && pSrcInode->fDirectory)
            {
                ret = DirCyclicRenameCheck(pSrcInode->ulInode, pDstPInode);
            }

            if(ret == 0)
            {
                ret = DirEntryWrite(pDstPInode, ulDstIdx, pSrcInode->ulInode, pszDstName, RedNameLen(pszDstName));
            }

            if(ret == 0)
            {
                ret = RedDirEntryDelete(pSrcPInode, ulSrcIdx);

                if(ret == -RED_ENOSPC)
                {
                    REDSTATUS ret2;

                    /*  If there was not enough space to branch the parent
                        directory inode and data block containin the source
                        entry, revert destination directory entry to its
                        previous state.
                    */
                  #if REDCONF_RENAME_ATOMIC == 1
                    if(pDstInode->ulInode != INODE_INVALID)
                    {
                        ret2 = DirEntryWrite(pDstPInode, ulDstIdx, pDstInode->ulInode, pszDstName, RedNameLen(pszDstName));
                    }
                    else
                  #endif
                    {
                        ret2 = RedDirEntryDelete(pDstPInode, ulDstIdx);
                    }

                    if(ret2 != 0)
                    {
                        ret = ret2;
                        CRITICAL_ERROR();
                    }
                }
            }

            if(ret == 0)
            {
                pSrcInode->pInodeBuf->ulPInode = pDstPInode->ulInode;
            }
        }
    }

    return ret;
}


/** @brief Check for a cyclic rename.

    A cyclic rename is renaming a directory into a subdirectory of itself.  For
    example, renaming "a" into "a/b/c/d" is cyclic.  These renames must not be
    allowed since they would corrupt the directory tree.

    @param ulSrcInode   The inode number of the directory being renamed.
    @param pDstPInode   A pointer to the cached inode structure of the directory
                        into which the source is being renamed.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0               Operation was successful.
    @retval -RED_EIO        A disk I/O error occurred.
    @retval -RED_EINVAL     The rename is cyclic; or invalid parameters.
    @retval -RED_ENOTDIR    @p pDstPInode is not a directory.
*/
static REDSTATUS DirCyclicRenameCheck(
    uint32_t        ulSrcInode,
    const CINODE   *pDstPInode)
{
    REDSTATUS       ret = 0;

    if(!INODE_IS_VALID(ulSrcInode) || !CINODE_IS_MOUNTED(pDstPInode))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else if(ulSrcInode == pDstPInode->ulInode)
    {
        ret = -RED_EINVAL;
    }
    else if(!pDstPInode->fDirectory)
    {
        ret = -RED_ENOTDIR;
    }
    else
    {
        CINODE NextParent;
        /*  Used to prevent infinite loop in case of corrupted directory
            structure.
        */
        uint32_t ulIteration = 0U;

        NextParent.ulInode = pDstPInode->pInodeBuf->ulPInode;

        while(     (NextParent.ulInode != ulSrcInode)
                && (NextParent.ulInode != INODE_ROOTDIR)
                && (NextParent.ulInode != INODE_INVALID)
                && (ulIteration < gpRedVolConf->ulInodeCount))
        {
            ret = RedInodeMount(&NextParent, FTYPE_DIR, false);
            if(ret != 0)
            {
                break;
            }

            NextParent.ulInode = NextParent.pInodeBuf->ulPInode;

            RedInodePut(&NextParent, 0U);

            ulIteration++;
        }

        if((ret == 0) && (ulIteration == gpRedVolConf->ulInodeCount))
        {
            CRITICAL_ERROR();
            ret = -RED_EFUBAR;
        }

        if((ret == 0) && (ulSrcInode == NextParent.ulInode))
        {
            ret = -RED_EINVAL;
        }
    }

    return ret;
}
#endif /* (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX_RENAME == 1) */


#if REDCONF_READ_ONLY == 0
/** @brief Update the contents of a directory entry.

    @param pPInode      A pointer to the cached inode structure of the directory
                        whose entry is being written.
    @param ulIdx        The index of the directory entry to write.
    @param ulInode      The inode number the directory entry is to point at.
    @param pszName      The name of the directory entry.
    @param ulNameLen    The length of @p pszName.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0               Operation was successful.
    @retval -RED_EIO        A disk I/O error occurred.
    @retval -RED_ENOSPC     There is not enough space on the volume to write the
                            directory entry.
    @retval -RED_ENOTDIR    @p pPInode is not a directory.
    @retval -RED_EINVAL     Invalid parameters.
*/
static REDSTATUS DirEntryWrite(
    CINODE     *pPInode,
    uint32_t    ulIdx,
    uint32_t    ulInode,
    const char *pszName,
    uint32_t    ulNameLen)
{
    REDSTATUS   ret;

    if(    !CINODE_IS_DIRTY(pPInode)
        || (ulIdx >= DIRENTS_MAX)
        || (!INODE_IS_VALID(ulInode) && (ulInode != INODE_INVALID))
        || (pszName == NULL)
        || (ulNameLen > REDCONF_NAME_MAX)
        || ((ulNameLen == 0U) != (ulInode == INODE_INVALID)))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else if(!pPInode->fDirectory)
    {
        ret = -RED_ENOTDIR;
    }
    else
    {
        uint64_t        ullOffset = DirEntryIndexToOffset(ulIdx);
        uint32_t        ulLen = DIRENT_SIZE;
        static DIRENT   de;

        RedMemSet(&de, 0U, sizeof(de));

        de.ulInode = ulInode;

      #ifdef REDCONF_ENDIAN_SWAP
        de.ulInode = RedRev32(de.ulInode);
      #endif

        RedStrNCpy(de.acName, pszName, ulNameLen);

        ret = RedInodeDataWrite(pPInode, ullOffset, &ulLen, &de);
    }

    return ret;
}


/** @brief Convert a directory entry index to a byte offset.

    @param ulIdx    Directory entry index.

    @return Byte offset in the directory corresponding with ulIdx.
*/
static uint64_t DirEntryIndexToOffset(
    uint32_t ulIdx)
{
    uint32_t ulBlock = ulIdx / DIRENTS_PER_BLOCK;
    uint32_t ulOffsetInBlock = ulIdx % DIRENTS_PER_BLOCK;
    uint64_t ullOffset;

    REDASSERT(ulIdx < DIRENTS_MAX);

    ullOffset = (uint64_t)ulBlock << BLOCK_SIZE_P2;
    ullOffset += (uint64_t)ulOffsetInBlock * DIRENT_SIZE;

    return ullOffset;
}
#endif /* REDCONF_READ_ONLY == 0 */


/** @brief Convert a byte offset to a directory entry index.

    @param ullOffset    Byte offset in the directory.

    @return Directory entry index corresponding with @p ullOffset.
*/
static uint32_t DirOffsetToEntryIndex(
    uint64_t ullOffset)
{
    uint32_t ulIdx;

    REDASSERT(ullOffset < INODE_SIZE_MAX);
    REDASSERT(((uint32_t)(ullOffset & (REDCONF_BLOCK_SIZE - 1U)) % DIRENT_SIZE) == 0U);

    /*  Avoid doing any 64-bit divides.
    */
    ulIdx = (uint32_t)(ullOffset >> BLOCK_SIZE_P2) * DIRENTS_PER_BLOCK;
    ulIdx += (uint32_t)(ullOffset & (REDCONF_BLOCK_SIZE - 1U)) / DIRENT_SIZE;

    return ulIdx;
}


#endif /* REDCONF_API_POSIX == 1 */

