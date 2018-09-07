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
    @brief Implements inode I/O functions.
*/
#include <redfs.h>
#include <redcore.h>


/*  This value is used to initialize the uIndirEntry and uDindirEntry members of
    the CINODE structure.  After seeking, a value of COORD_ENTRY_INVALID in
    uIndirEntry indicates that there is no indirect node in the path through the
    file metadata structure, and a value of COORD_ENTRY_INVALID in uDindirEntry
    indicates that there is no double indirect node.
*/
#define COORD_ENTRY_INVALID (UINT16_MAX)

/*  This enumeration is used by the BranchBlock() and BranchBlockCost()
    functions to determine which blocks of the file metadata structure need to
    be branched, and which to ignore.  DINDIR requires requires branching the
    double indirect only, INDIR requires branching the double indirect
    (if present) and the indirect, and FILE_DATA requires branching the indirect
    and double indirect (if present) and the file data block.
*/
typedef enum
{
    BRANCHDEPTH_DINDIR      = 0U,
    BRANCHDEPTH_INDIR       = 1U,
    BRANCHDEPTH_FILE_DATA   = 2U,
    BRANCHDEPTH_MAX         = BRANCHDEPTH_FILE_DATA
} BRANCHDEPTH;


#if REDCONF_READ_ONLY == 0
#if DELETE_SUPPORTED || TRUNCATE_SUPPORTED
static REDSTATUS Shrink(CINODE *pInode, uint64_t ullSize);
#if DINDIR_POINTERS > 0U
static REDSTATUS TruncDindir(CINODE *pInode, bool *pfFreed);
#endif
#if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
static REDSTATUS TruncIndir(CINODE *pInode, bool *pfFreed);
#endif
static REDSTATUS TruncDataBlock(const CINODE *pInode, uint32_t *pulBlock, bool fPropagate);
#endif
static REDSTATUS ExpandPrepare(CINODE *pInode);
#endif
static void SeekCoord(CINODE *pInode, uint32_t ulBlock);
static REDSTATUS ReadUnaligned(CINODE *pInode, uint64_t ullStart, uint32_t ulLen, uint8_t *pbBuffer);
static REDSTATUS ReadAligned(CINODE *pInode, uint32_t ulBlockStart, uint32_t ulBlockCount, uint8_t *pbBuffer);
#if REDCONF_READ_ONLY == 0
static REDSTATUS WriteUnaligned(CINODE *pInode, uint64_t ullStart, uint32_t ulLen, const uint8_t *pbBuffer);
static REDSTATUS WriteAligned(CINODE *pInode, uint32_t ulBlockStart, uint32_t *pulBlockCount, const uint8_t *pbBuffer);
#endif
static REDSTATUS GetExtent(CINODE *pInode, uint32_t ulBlockStart, uint32_t *pulExtentStart, uint32_t *pulExtentLen);
#if REDCONF_READ_ONLY == 0
static REDSTATUS BranchBlock(CINODE *pInode, BRANCHDEPTH depth, bool fBuffer);
static REDSTATUS BranchOneBlock(uint32_t *pulBlock, void **ppBuffer, uint16_t uBFlag);
static REDSTATUS BranchBlockCost(const CINODE *pInode, BRANCHDEPTH depth, uint32_t *pulCost);
static uint32_t FreeBlockCount(void);
#endif


/** @brief Read data from an inode.

    @param pInode   A pointer to the cached inode structure of the inode from
                    which to read.
    @param ullStart The file offset at which to read.
    @param pulLen   On input, the number of bytes to attempt to read.  On
                    successful return, populated with the number of bytes
                    actually read.
    @param pBuffer  The buffer to read into.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EINVAL @p pInode is not a mounted cached inode pointer; or
                        @p pulLen is `NULL`; or @p pBuffer is `NULL`.
*/
REDSTATUS RedInodeDataRead(
    CINODE     *pInode,
    uint64_t    ullStart,
    uint32_t   *pulLen,
    void       *pBuffer)
{
    REDSTATUS   ret = 0;

    if(!CINODE_IS_MOUNTED(pInode) || (pulLen == NULL) || (pBuffer == NULL))
    {
        ret = -RED_EINVAL;
    }
    else if(ullStart >= pInode->pInodeBuf->ullSize)
    {
        *pulLen = 0U;
    }
    else if(*pulLen == 0U)
    {
        /*  Do nothing, just return success.
        */
    }
    else
    {
        uint8_t    *pbBuffer = CAST_VOID_PTR_TO_UINT8_PTR(pBuffer);
        uint32_t    ulReadIndex = 0U;
        uint32_t    ulLen = *pulLen;
        uint32_t    ulRemaining;

        /*  Reading beyond the end of the file is not allowed.  If the requested
            read extends beyond the end of the file, truncate the read length so
            that the read stops at the end of the file.
        */
        if((pInode->pInodeBuf->ullSize - ullStart) < ulLen)
        {
            ulLen = (uint32_t)(pInode->pInodeBuf->ullSize - ullStart);
        }

        ulRemaining = ulLen;

        /*  Unaligned partial block at start.
        */
        if((ullStart & (REDCONF_BLOCK_SIZE - 1U)) != 0U)
        {
            uint32_t ulBytesInFirstBlock = REDCONF_BLOCK_SIZE - (uint32_t)(ullStart & (REDCONF_BLOCK_SIZE - 1U));
            uint32_t ulThisRead = REDMIN(ulRemaining, ulBytesInFirstBlock);

            ret = ReadUnaligned(pInode, ullStart, ulThisRead, pbBuffer);

            if(ret == 0)
            {
                ulReadIndex += ulThisRead;
                ulRemaining -= ulThisRead;
            }
        }

        /*  Whole blocks.
        */
        if((ret == 0) && (ulRemaining >= REDCONF_BLOCK_SIZE))
        {
            uint32_t ulBlockOffset = (uint32_t)((ullStart + ulReadIndex) >> BLOCK_SIZE_P2);
            uint32_t ulBlockCount = ulRemaining >> BLOCK_SIZE_P2;

            REDASSERT(((ullStart + ulReadIndex) & (REDCONF_BLOCK_SIZE - 1U)) == 0U);

            ret = ReadAligned(pInode, ulBlockOffset, ulBlockCount, &pbBuffer[ulReadIndex]);

            if(ret == 0)
            {
                ulReadIndex += ulBlockCount << BLOCK_SIZE_P2;
                ulRemaining -= ulBlockCount << BLOCK_SIZE_P2;
            }
        }

        /*  Aligned partial block at end.
        */
        if((ret == 0) && (ulRemaining > 0U))
        {
            REDASSERT(ulRemaining < REDCONF_BLOCK_SIZE);
            REDASSERT(((ullStart + ulReadIndex) & (REDCONF_BLOCK_SIZE - 1U)) == 0U);

            ret = ReadUnaligned(pInode, ullStart + ulReadIndex, ulRemaining, &pbBuffer[ulReadIndex]);
        }

        if(ret == 0)
        {
            *pulLen = ulLen;
        }
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Write to an inode.

    @param pInode   A pointer to the cached inode structure of the inode into
                    which to write.
    @param ullStart The file offset at which to write.
    @param pulLen   On input, the number of bytes to attempt to write.  On
                    successful return, populated with the number of bytes
                    actually written.
    @param pBuffer  The buffer to write from.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EFBIG  @p ullStart is greater than the maximum file size; or
                        @p ullStart is equal to the maximum file size and the
                        write length is non-zero.
    @retval -RED_EINVAL @p pInode is not a mounted cached inode pointer; or
                        @p pulLen is `NULL`; or @p pBuffer is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENOSPC No data can be written because there is insufficient
                        free space.
*/
REDSTATUS RedInodeDataWrite(
    CINODE     *pInode,
    uint64_t    ullStart,
    uint32_t   *pulLen,
    const void *pBuffer)
{
    REDSTATUS   ret = 0;

    if(!CINODE_IS_DIRTY(pInode) || (pulLen == NULL) || (pBuffer == NULL))
    {
        ret = -RED_EINVAL;
    }
    else if((ullStart > INODE_SIZE_MAX) || ((ullStart == INODE_SIZE_MAX) && (*pulLen > 0U)))
    {
        ret = -RED_EFBIG;
    }
    else if(*pulLen == 0U)
    {
        /*  Do nothing, just return success.
        */
    }
    else
    {
        const uint8_t  *pbBuffer = CAST_VOID_PTR_TO_CONST_UINT8_PTR(pBuffer);
        uint32_t        ulWriteIndex = 0U;
        uint32_t        ulLen = *pulLen;
        uint32_t        ulRemaining;

        if((INODE_SIZE_MAX - ullStart) < ulLen)
        {
            ulLen = (uint32_t)(INODE_SIZE_MAX - ullStart);
        }

        ulRemaining = ulLen;

        /*  If the write is beyond the current end of the file, and the current
            end of the file is not block-aligned, then there may be some data
            that needs to be zeroed in the last block.
        */
        if(ullStart > pInode->pInodeBuf->ullSize)
        {
            ret = ExpandPrepare(pInode);
        }

        /*  Partial block at start.
        */
        if((ret == 0) && (((ullStart & (REDCONF_BLOCK_SIZE - 1U)) != 0U) || (ulRemaining < REDCONF_BLOCK_SIZE)))
        {
            uint32_t ulBytesInFirstBlock = REDCONF_BLOCK_SIZE - (uint32_t)(ullStart & (REDCONF_BLOCK_SIZE - 1U));
            uint32_t ulThisWrite = REDMIN(ulRemaining, ulBytesInFirstBlock);

            ret = WriteUnaligned(pInode, ullStart, ulThisWrite, pbBuffer);

            if(ret == 0)
            {
                ulWriteIndex += ulThisWrite;
                ulRemaining -= ulThisWrite;
            }
        }

        /*  Whole blocks.
        */
        if((ret == 0) && (ulRemaining >= REDCONF_BLOCK_SIZE))
        {
            uint32_t ulBlockOffset = (uint32_t)((ullStart + ulWriteIndex) >> BLOCK_SIZE_P2);
            uint32_t ulBlockCount = ulRemaining >> BLOCK_SIZE_P2;
            uint32_t ulBlocksWritten = ulBlockCount;

            REDASSERT(((ullStart + ulWriteIndex) & (REDCONF_BLOCK_SIZE - 1U)) == 0U);

            ret = WriteAligned(pInode, ulBlockOffset, &ulBlocksWritten, &pbBuffer[ulWriteIndex]);

            if((ret == -RED_ENOSPC) && (ulWriteIndex > 0U))
            {
                ulBlocksWritten = 0U;
                ret = 0;
            }

            if(ret == 0)
            {
                ulWriteIndex += ulBlocksWritten << BLOCK_SIZE_P2;
                ulRemaining -= ulBlocksWritten << BLOCK_SIZE_P2;

                if(ulBlocksWritten < ulBlockCount)
                {
                    ulRemaining = 0U;
                }
            }
        }

        /*  Partial block at end.
        */
        if((ret == 0) && (ulRemaining > 0U))
        {
            REDASSERT(ulRemaining < REDCONF_BLOCK_SIZE);
            REDASSERT(((ullStart + ulWriteIndex) & (REDCONF_BLOCK_SIZE - 1U)) == 0U);
            REDASSERT(ulWriteIndex > 0U);

            ret = WriteUnaligned(pInode, ullStart + ulWriteIndex, ulRemaining, &pbBuffer[ulWriteIndex]);

            if(ret == -RED_ENOSPC)
            {
                ret = 0;
            }
            else if(ret == 0)
            {
                ulWriteIndex += ulRemaining;

                REDASSERT(ulWriteIndex == ulLen);
            }
            else
            {
                /*  Unexpected error, return it.
                */
            }
        }

        if(ret == 0)
        {
            *pulLen = ulWriteIndex;

            if((ullStart + ulWriteIndex) > pInode->pInodeBuf->ullSize)
            {
                pInode->pInodeBuf->ullSize = ullStart + ulWriteIndex;
            }
        }
    }

    return ret;
}


#if DELETE_SUPPORTED || TRUNCATE_SUPPORTED
/** @brief Change the size of an inode.

    @param pInode   A pointer to the cached inode structure.
    @praam ullSize  The new file size for the inode.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EFBIG  @p ullSize is greater than the maximum file size.
    @retval -RED_EINVAL @p pInode is not a mounted cached inode pointer.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENOSPC Insufficient free space to perform the truncate.
*/
REDSTATUS RedInodeDataTruncate(
    CINODE     *pInode,
    uint64_t    ullSize)
{
    REDSTATUS   ret = 0;

    /*  The inode does not need to be dirtied when it is being deleted, because
        the inode buffer will be discarded without ever being written to disk.
        Thus, we only check to see if it's mounted here.
    */
    if(!CINODE_IS_MOUNTED(pInode))
    {
        ret = -RED_EINVAL;
    }
    else if(ullSize > INODE_SIZE_MAX)
    {
        ret = -RED_EFBIG;
    }
    else
    {
        if(ullSize > pInode->pInodeBuf->ullSize)
        {
            ret = ExpandPrepare(pInode);
        }
        else if(ullSize < pInode->pInodeBuf->ullSize)
        {
            ret = Shrink(pInode, ullSize);
        }
        else
        {
            /*  Size is staying the same, nothing to do.
            */
        }

        if(ret == 0)
        {
            pInode->pInodeBuf->ullSize = ullSize;
        }
    }

    return ret;
}


/** @brief Free all file data beyond a specified point.

    @param pInode   A pointer to the cached inode structure.
    @param ullSize  The point beyond which to free all file data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENOSPC Insufficient free space to perform the truncate.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS Shrink(
    CINODE     *pInode,
    uint64_t    ullSize)
{
    REDSTATUS   ret = 0;

    /*  pInode->fDirty is checked explicitly here, instead of using the
        CINODE_IS_DIRTY() macro, to avoid a duplicate mount check.
    */
    if(!CINODE_IS_MOUNTED(pInode) || ((ullSize > 0U) && !pInode->fDirty))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint32_t ulTruncBlock = (uint32_t)((ullSize + REDCONF_BLOCK_SIZE - 1U) >> BLOCK_SIZE_P2);

        RedInodePutData(pInode);

      #if REDCONF_DIRECT_POINTERS > 0U
        while(ulTruncBlock < REDCONF_DIRECT_POINTERS)
        {
            ret = TruncDataBlock(pInode, &pInode->pInodeBuf->aulEntries[ulTruncBlock], true);

            if(ret != 0)
            {
                break;
            }

            ulTruncBlock++;
        }
      #endif

      #if REDCONF_INDIRECT_POINTERS > 0U
        while((ret == 0) && (ulTruncBlock < (REDCONF_DIRECT_POINTERS + INODE_INDIR_BLOCKS)))
        {
            ret = RedInodeDataSeek(pInode, ulTruncBlock);

            if((ret == 0) || (ret == -RED_ENODATA))
            {
                bool fFreed;

                ret = TruncIndir(pInode, &fFreed);

                if(ret == 0)
                {
                    if(fFreed)
                    {
                        pInode->pInodeBuf->aulEntries[pInode->uInodeEntry] = BLOCK_SPARSE;
                    }

                    /*  The next seek will go to the beginning of the next
                        indirect.
                    */
                    ulTruncBlock += (INDIR_ENTRIES - pInode->uIndirEntry);
                }
            }
        }
      #endif

      #if DINDIR_POINTERS > 0U
        while((ret == 0) && (ulTruncBlock < INODE_DATA_BLOCKS))
        {
            ret = RedInodeDataSeek(pInode, ulTruncBlock);

            if((ret == 0) || (ret == -RED_ENODATA))
            {
                bool fFreed;

                /*  TruncDindir() invokes seek as it goes along, which will
                    update the entry values (possibly all three of these);
                    make a copy so we can compute things correctly after.
                */
                uint16_t uOrigInodeEntry = pInode->uInodeEntry;
                uint16_t uOrigDindirEntry = pInode->uDindirEntry;
                uint16_t uOrigIndirEntry = pInode->uIndirEntry;

                ret = TruncDindir(pInode, &fFreed);

                if(ret == 0)
                {
                    if(fFreed)
                    {
                        pInode->pInodeBuf->aulEntries[uOrigInodeEntry] = BLOCK_SPARSE;
                    }

                    /*  The next seek will go to the beginning of the next
                        double indirect.
                    */
                    ulTruncBlock += (DINDIR_DATA_BLOCKS - (uOrigDindirEntry * INDIR_ENTRIES)) - uOrigIndirEntry;
                }
            }
        }
      #endif
    }

    return ret;
}


#if DINDIR_POINTERS > 0U
/** @brief Truncate a double indirect.

    @param pInode   A pointer to the cached inode, whose coordinates indicate
                    the truncation boundary.
    @param pfFreed  On successful return, populated with whether the double
                    indirect node was freed.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENOSPC Insufficient free space to perform the truncate.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS TruncDindir(
    CINODE     *pInode,
    bool       *pfFreed)
{
    REDSTATUS   ret = 0;

    if(!CINODE_IS_MOUNTED(pInode) || (pfFreed == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else if(pInode->pDindir == NULL)
    {
        *pfFreed = false;
    }
    else
    {
        bool        fBranch = false;
        uint16_t    uEntry;

        /*  The double indirect is definitely going to be branched (instead of
            deleted) if any of its indirect pointers which are entirely prior to
            the truncation boundary are non-sparse.
        */
        for(uEntry = 0U; !fBranch && (uEntry < pInode->uDindirEntry); uEntry++)
        {
            fBranch = pInode->pDindir->aulEntries[uEntry] != BLOCK_SPARSE;
        }

        /*  Unless we already know for a fact that the double indirect is going
            to be branched, examine the contents of the indirect pointer which
            straddles the truncation boundary.  If the indirect is going to be
            deleted, we know this indirect pointer is going away, and that might
            mean the double indirect is going to be deleted also.
        */
        if(!fBranch && (pInode->pDindir->aulEntries[pInode->uDindirEntry] != BLOCK_SPARSE))
        {
            for(uEntry = 0U; !fBranch && (uEntry < pInode->uIndirEntry); uEntry++)
            {
                fBranch = pInode->pIndir->aulEntries[uEntry] != BLOCK_SPARSE;
            }
        }

        if(fBranch)
        {
            ret = BranchBlock(pInode, BRANCHDEPTH_DINDIR, false);
        }

        if(ret == 0)
        {
            uint32_t ulBlock = pInode->ulLogicalBlock;
            uint16_t uStart = pInode->uDindirEntry; /* pInode->uDindirEntry will change. */

            for(uEntry = uStart; uEntry < INDIR_ENTRIES; uEntry++)
            {
                /*  Seek so that TruncIndir() has the correct indirect
                    buffer and indirect entry.
                */
                ret = RedInodeDataSeek(pInode, ulBlock);

                if(ret == -RED_ENODATA)
                {
                    ret = 0;
                }

                if((ret == 0) && (pInode->ulIndirBlock != BLOCK_SPARSE))
                {
                    bool fIndirFreed;

                    ret = TruncIndir(pInode, &fIndirFreed);

                    if(ret == 0)
                    {
                        /*  All of the indirects after the one which straddles
                            the truncation boundary should definitely end up
                            deleted.
                        */
                        REDASSERT((uEntry == uStart) || fIndirFreed);

                        /*  If the double indirect is being freed, all of the
                            indirects should be freed too.
                        */
                        REDASSERT(fIndirFreed || fBranch);

                        if(fBranch && fIndirFreed)
                        {
                            pInode->pDindir->aulEntries[uEntry] = BLOCK_SPARSE;
                        }
                    }
                }

                if(ret != 0)
                {
                    break;
                }

                ulBlock += (INDIR_ENTRIES - pInode->uIndirEntry);
            }

            if(ret == 0)
            {
                *pfFreed = !fBranch;

                if(!fBranch)
                {
                    RedInodePutDindir(pInode);

                    ret = RedImapBlockSet(pInode->ulDindirBlock, false);
                }
            }
        }
    }

    return ret;
}
#endif /* DINDIR_POINTERS > 0U */


#if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
/** @brief Truncate a indirect.

    @param pInode   A pointer to the cached inode, whose coordinates indicate
                    the truncation boundary.
    @param pfFreed  On successful return, populated with whether the indirect
                    node was freed.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENOSPC Insufficient free space to perform the truncate.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS TruncIndir(
    CINODE     *pInode,
    bool       *pfFreed)
{
    REDSTATUS   ret = 0;

    if(!CINODE_IS_MOUNTED(pInode) || (pfFreed == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else if(pInode->pIndir == NULL)
    {
        *pfFreed = false;
    }
    else
    {
        bool        fBranch = false;
        uint16_t    uEntry;

        /*  Scan the range of entries which are not being truncated.  If there
            is anything there, then the indirect will not be empty after the
            truncate, so it is branched and modified instead of deleted.
        */
        for(uEntry = 0U; !fBranch && (uEntry < pInode->uIndirEntry); uEntry++)
        {
            fBranch = pInode->pIndir->aulEntries[uEntry] != BLOCK_SPARSE;
        }

        if(fBranch)
        {
            ret = BranchBlock(pInode, BRANCHDEPTH_INDIR, false);
        }

        if(ret == 0)
        {
            for(uEntry = pInode->uIndirEntry; uEntry < INDIR_ENTRIES; uEntry++)
            {
                ret = TruncDataBlock(pInode, &pInode->pIndir->aulEntries[uEntry], fBranch);

                if(ret != 0)
                {
                    break;
                }
            }

            if(ret == 0)
            {
                *pfFreed = !fBranch;

                if(!fBranch)
                {
                    RedInodePutIndir(pInode);

                    ret = RedImapBlockSet(pInode->ulIndirBlock, false);
                }
            }
        }
    }

    return ret;
}
#endif /* REDCONF_DIRECT_POINTERS < INODE_ENTRIES */


/** @brief Truncate a file data block.

    @param pInode       A pointer to the cached inode structure.
    @param pulBlock     On entry, contains the block to be truncated.  On
                        successful return, if @p fPropagate is true, populated
                        with BLOCK_SPARSE, otherwise unmodified.
    @param fPropagate   Whether the parent node is being branched.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS TruncDataBlock(
    const CINODE   *pInode,
    uint32_t       *pulBlock,
    bool            fPropagate)
{
    REDSTATUS       ret = 0;

    if(!CINODE_IS_MOUNTED(pInode) || (pulBlock == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else if(*pulBlock != BLOCK_SPARSE)
    {
        ret = RedImapBlockSet(*pulBlock, false);

      #if REDCONF_INODE_BLOCKS == 1
        if(ret == 0)
        {
            if(pInode->pInodeBuf->ulBlocks == 0U)
            {
                CRITICAL_ERROR();
                ret = -RED_EFUBAR;
            }
            else
            {
                pInode->pInodeBuf->ulBlocks--;
            }
        }
      #endif

        if((ret == 0) && fPropagate)
        {
            *pulBlock = BLOCK_SPARSE;
        }
    }
    else
    {
        /*  Data block is sparse, nothing to truncate.
        */
    }

    return ret;
}
#endif /* DELETE_SUPPORTED || TRUNCATE_SUPPORTED */


/** @brief Prepare to increase the file size.

    When the inode size is increased, a sparse region is created.  It is
    possible that a prior shrink operation to an unaligned size left stale data
    beyond the end of the file in the last data block.  That data is not zeroed
    while shrinking the inode in order to transfer the disk full burden from the
    shrink operation to the expand operation.

    @param pInode   A pointer to the cached inode structure.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENOSPC Insufficient free space to perform the truncate.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS ExpandPrepare(
    CINODE     *pInode)
{
    REDSTATUS   ret = 0;

    if(!CINODE_IS_DIRTY(pInode))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint32_t ulOldSizeByteInBlock = (uint32_t)(pInode->pInodeBuf->ullSize & (REDCONF_BLOCK_SIZE - 1U));

        if(ulOldSizeByteInBlock != 0U)
        {
            ret = RedInodeDataSeek(pInode, (uint32_t)(pInode->pInodeBuf->ullSize >> BLOCK_SIZE_P2));

            if(ret == -RED_ENODATA)
            {
                ret = 0;
            }
            else if(ret == 0)
            {
                ret = BranchBlock(pInode, BRANCHDEPTH_FILE_DATA, true);

                if(ret == 0)
                {
                    RedMemSet(&pInode->pbData[ulOldSizeByteInBlock], 0U, REDCONF_BLOCK_SIZE - ulOldSizeByteInBlock);
                }
            }
            else
            {
                REDERROR();
            }
        }
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


/** @brief Seek to a given position within an inode, then buffer the data block.

    On successful return, pInode->pbData will be populated with a buffer
    corresponding to the @p ulBlock block offset.

    @param pInode   A pointer to the cached inode structure.
    @param ulBlock  The block offset to seek to and buffer.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0               Operation was successful.
    @retval -RED_ENODATA    The block offset is sparse.
    @retval -RED_EINVAL     @p ulBlock is too large.
    @retval -RED_EIO        A disk I/O error occurred.
*/
REDSTATUS RedInodeDataSeekAndRead(
    CINODE     *pInode,
    uint32_t    ulBlock)
{
    REDSTATUS   ret;

    ret = RedInodeDataSeek(pInode, ulBlock);

    if((ret == 0) && (pInode->pbData == NULL))
    {
        REDASSERT(pInode->ulDataBlock != BLOCK_SPARSE);

        ret = RedBufferGet(pInode->ulDataBlock, 0U, CAST_VOID_PTR_PTR(&pInode->pbData));
    }

    return ret;
}


/** @brief Seek to a given position within an inode.

    On successful return, pInode->ulDataBlock will be populated with the
    physical block number corresponding to the @p ulBlock block offset.

    Note: Callers of this function depend on its parameter checking.

    @param pInode   A pointer to the cached inode structure.
    @param ulBlock  The block offset to seek to.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0               Operation was successful.
    @retval -RED_ENODATA    The block offset is sparse.
    @retval -RED_EINVAL     @p ulBlock is too large; or @p pInode is not a
                            mounted cached inode pointer.
    @retval -RED_EIO        A disk I/O error occurred.
*/
REDSTATUS RedInodeDataSeek(
    CINODE     *pInode,
    uint32_t    ulBlock)
{
    REDSTATUS   ret = 0;

    if(!CINODE_IS_MOUNTED(pInode) || (ulBlock >= INODE_DATA_BLOCKS))
    {
        ret = -RED_EINVAL;
    }
    else
    {
        SeekCoord(pInode, ulBlock);

      #if DINDIR_POINTERS > 0U
        if(pInode->uDindirEntry != COORD_ENTRY_INVALID)
        {
            if(pInode->ulDindirBlock == BLOCK_SPARSE)
            {
                /*  If the double indirect is unallocated, so is the indirect.
                */
                pInode->ulIndirBlock = BLOCK_SPARSE;
            }
            else
            {
                if(pInode->pDindir == NULL)
                {
                    ret = RedBufferGet(pInode->ulDindirBlock, BFLAG_META_DINDIR, CAST_VOID_PTR_PTR(&pInode->pDindir));
                }

                if(ret == 0)
                {
                    pInode->ulIndirBlock = pInode->pDindir->aulEntries[pInode->uDindirEntry];
                }
            }
        }
      #endif

      #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
        if((ret == 0) && (pInode->uIndirEntry != COORD_ENTRY_INVALID))
        {
            if(pInode->ulIndirBlock == BLOCK_SPARSE)
            {
                /*  If the indirect is unallocated, so is the data block.
                */
                pInode->ulDataBlock = BLOCK_SPARSE;
            }
            else
            {
                if(pInode->pIndir == NULL)
                {
                    ret = RedBufferGet(pInode->ulIndirBlock, BFLAG_META_INDIR, CAST_VOID_PTR_PTR(&pInode->pIndir));
                }

                if(ret == 0)
                {
                    pInode->ulDataBlock = pInode->pIndir->aulEntries[pInode->uIndirEntry];
                }
            }
        }
      #endif

        if((ret == 0) && (pInode->ulDataBlock == BLOCK_SPARSE))
        {
            ret = -RED_ENODATA;
        }
    }

    return ret;
}


/** @brief Seek to the coordinates.

    Compute the new coordinates, and put any buffers which are not needed or are
    no longer appropriate.

    @param pInode   A pointer to the cached inode structure.
    @param ulBlock  The block offset to seek to.
*/
static void SeekCoord(
    CINODE     *pInode,
    uint32_t    ulBlock)
{
    if(!CINODE_IS_MOUNTED(pInode) || (ulBlock >= INODE_DATA_BLOCKS))
    {
        REDERROR();
    }
    else if((pInode->ulLogicalBlock != ulBlock) || !pInode->fCoordInited)
    {
        RedInodePutData(pInode);
        pInode->ulLogicalBlock = ulBlock;

      #if REDCONF_DIRECT_POINTERS > 0U
      #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
        if(ulBlock < REDCONF_DIRECT_POINTERS)
      #endif
        {
          #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
            RedInodePutCoord(pInode);
          #endif

            pInode->uInodeEntry = (uint16_t)ulBlock;
            pInode->ulDataBlock = pInode->pInodeBuf->aulEntries[pInode->uInodeEntry];

          #if DINDIR_POINTERS > 0U
            pInode->uDindirEntry = COORD_ENTRY_INVALID;
          #endif
          #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
            pInode->uIndirEntry = COORD_ENTRY_INVALID;
          #endif
        }
      #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
        else
      #endif
      #endif
      #if REDCONF_INDIRECT_POINTERS > 0U
      #if REDCONF_INDIRECT_POINTERS < INODE_ENTRIES
        if(ulBlock < (INODE_INDIR_BLOCKS + REDCONF_DIRECT_POINTERS))
      #endif
        {
            uint32_t ulIndirRangeOffset = ulBlock - REDCONF_DIRECT_POINTERS;
            uint16_t uInodeEntry = (uint16_t)((ulIndirRangeOffset / INDIR_ENTRIES) + REDCONF_DIRECT_POINTERS);
            uint16_t uIndirEntry = (uint16_t)(ulIndirRangeOffset % INDIR_ENTRIES);

          #if DINDIR_POINTERS > 0U
            RedInodePutDindir(pInode);
          #endif

            /*  If the inode entry is not changing, then the previous indirect
                is still the correct one.  Otherwise, the old indirect will be
                released and the new one will be read later.
            */
            if((pInode->uInodeEntry != uInodeEntry) || !pInode->fCoordInited)
            {
                RedInodePutIndir(pInode);

                pInode->uInodeEntry = uInodeEntry;

                pInode->ulIndirBlock = pInode->pInodeBuf->aulEntries[pInode->uInodeEntry];
            }

          #if DINDIR_POINTERS > 0U
            pInode->uDindirEntry = COORD_ENTRY_INVALID;
          #endif
            pInode->uIndirEntry = uIndirEntry;

            /*  At this point, the following pInode members are needed but not
                yet populated:

                - pIndir
                - ulDataBlock
            */
        }
      #if DINDIR_POINTERS > 0U
        else
      #endif
      #endif
      #if DINDIR_POINTERS > 0U
        {
            uint32_t ulDindirRangeOffset = (ulBlock - REDCONF_DIRECT_POINTERS) - INODE_INDIR_BLOCKS;
            uint16_t uInodeEntry = (uint16_t)((ulDindirRangeOffset / DINDIR_DATA_BLOCKS) + REDCONF_DIRECT_POINTERS + REDCONF_INDIRECT_POINTERS);
            uint32_t ulDindirNodeOffset = ulDindirRangeOffset % DINDIR_DATA_BLOCKS;
            uint16_t uDindirEntry = (uint16_t)(ulDindirNodeOffset / INDIR_ENTRIES);
            uint16_t uIndirEntry = (uint16_t)(ulDindirNodeOffset % INDIR_ENTRIES);

            /*  If the inode entry is not changing, then the previous double
                indirect is still the correct one.  Otherwise, the old double
                indirect will be released and the new one will be read later.
            */
            if((pInode->uInodeEntry != uInodeEntry) || !pInode->fCoordInited)
            {
                RedInodePutIndir(pInode);
                RedInodePutDindir(pInode);

                pInode->uInodeEntry = uInodeEntry;

                pInode->ulDindirBlock = pInode->pInodeBuf->aulEntries[pInode->uInodeEntry];
            }
            /*  If neither the inode entry nor double indirect entry are
                changing, then the previous indirect is still the correct one.
                Otherwise, it old indirect will be released and the new one will
                be read later.
            */
            else if(pInode->uDindirEntry != uDindirEntry)
            {
                RedInodePutIndir(pInode);
            }
            else
            {
                /*  Data buffer has already been put, nothing to do.
                */
            }

            pInode->uDindirEntry = uDindirEntry;
            pInode->uIndirEntry = uIndirEntry;

            /*  At this point, the following pInode members are needed but not
                yet populated:

                - pDindir
                - pIndir
                - ulIndirBlock
                - ulDataBlock
            */
        }
      #elif (REDCONF_DIRECT_POINTERS > 0U) && (REDCONF_INDIRECT_POINTERS > 0U)
        else
        {
            /*  There are no double indirects, so the block should have been in
                the direct or indirect range.
            */
            REDERROR();
        }
      #endif

        pInode->fCoordInited = true;
    }
    else
    {
        /*  Seeking to the current position, nothing to do.
        */
    }
}


/** @brief Read an unaligned portion of a block.

    @param pInode   A pointer to the cached inode structure.
    @param ullStart The file offset at which to read.
    @param ulLen    The number of bytes to read.
    @param pbBuffer The buffer to read into.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS ReadUnaligned(
    CINODE     *pInode,
    uint64_t    ullStart,
    uint32_t    ulLen,
    uint8_t    *pbBuffer)
{
    REDSTATUS   ret;

    /*  This read should not cross a block boundary.
    */
    if(    ((ullStart >> BLOCK_SIZE_P2) != (((ullStart + ulLen) - 1U) >> BLOCK_SIZE_P2))
        || (pbBuffer == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        ret = RedInodeDataSeekAndRead(pInode, (uint32_t)(ullStart >> BLOCK_SIZE_P2));

        if(ret == 0)
        {
            RedMemCpy(pbBuffer, &pInode->pbData[ullStart & (REDCONF_BLOCK_SIZE - 1U)], ulLen);
        }
        else if(ret == -RED_ENODATA)
        {
            /*  Sparse block, return zeroed data.
            */
            RedMemSet(pbBuffer, 0U, ulLen);
            ret = 0;
        }
        else
        {
            /*  No action, just return the error.
            */
        }
    }

    return ret;
}


/** @brief Read one or more whole blocks.

    @param pInode       A pointer to the cached inode structure.
    @param ulBlockStart The file block offset at which to read.
    @param ulBlockCount The number of blocks to read.
    @param pbBuffer     The buffer to read into.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS ReadAligned(
    CINODE     *pInode,
    uint32_t    ulBlockStart,
    uint32_t    ulBlockCount,
    uint8_t    *pbBuffer)
{
    REDSTATUS   ret = 0;

    if(pbBuffer == NULL)
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint32_t ulBlockIndex = 0U;

        /*  Read the data from disk one contiguous extent at a time.
        */
        while((ret == 0) && (ulBlockIndex < ulBlockCount))
        {
            uint32_t ulExtentStart;
            uint32_t ulExtentLen = ulBlockCount - ulBlockIndex;

            ret = GetExtent(pInode, ulBlockStart + ulBlockIndex, &ulExtentStart, &ulExtentLen);

            if(ret == 0)
            {
              #if REDCONF_READ_ONLY == 0
                /*  Before reading directly from disk, flush any dirty file data
                    buffers in the range to avoid reading stale data.
                */
                ret = RedBufferFlush(ulExtentStart, ulExtentLen);

                if(ret == 0)
              #endif
                {
                    ret = RedIoRead(gbRedVolNum, ulExtentStart, ulExtentLen, &pbBuffer[ulBlockIndex << BLOCK_SIZE_P2]);

                    if(ret == 0)
                    {
                        ulBlockIndex += ulExtentLen;
                    }
                }
            }
            else if(ret == -RED_ENODATA)
            {
                /*  Sparse block, return zeroed data.
                */
                RedMemSet(&pbBuffer[ulBlockIndex << BLOCK_SIZE_P2], 0U, REDCONF_BLOCK_SIZE);
                ulBlockIndex++;
                ret = 0;
            }
            else
            {
                /*  An unexpected error occurred; the loop will terminate.
                */
            }
        }
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Write an unaligned portion of a block.

    @param pInode   A pointer to the cached inode structure.
    @param ullStart The file offset at which to write.
    @param ulLen    The number of bytes to write.
    @param pbBuffer The buffer to write from.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENOSPC No data can be written because there is insufficient
                        free space.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS WriteUnaligned(
    CINODE         *pInode,
    uint64_t        ullStart,
    uint32_t        ulLen,
    const uint8_t  *pbBuffer)
{
    REDSTATUS       ret;

    /*  This write should not cross a block boundary.
    */
    if(    ((ullStart >> BLOCK_SIZE_P2) != (((ullStart + ulLen) - 1U) >> BLOCK_SIZE_P2))
        || (pbBuffer == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        ret = RedInodeDataSeek(pInode, (uint32_t)(ullStart >> BLOCK_SIZE_P2));

        if((ret == 0) || (ret == -RED_ENODATA))
        {
            ret = BranchBlock(pInode, BRANCHDEPTH_FILE_DATA, true);

            if(ret == 0)
            {
                RedMemCpy(&pInode->pbData[ullStart & (REDCONF_BLOCK_SIZE - 1U)], pbBuffer, ulLen);
            }
        }
    }

    return ret;
}


/** @brief Write one or more whole blocks.

    @param pInode           A pointer to the cached inode structure.
    @param ulBlockStart     The file block offset at which to write.
    @param pulBlockCount    On entry, the number of blocks to attempt to write.
                            On successful return, the number of blocks actually
                            written.
    @param pbBuffer         The buffer to write from.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENOSPC No data can be written because there is insufficient
                        free space.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS WriteAligned(
    CINODE         *pInode,
    uint32_t        ulBlockStart,
    uint32_t       *pulBlockCount,
    const uint8_t  *pbBuffer)
{
    REDSTATUS       ret = 0;

    if((pulBlockCount == NULL) || (pbBuffer == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        bool     fFull = false;
        uint32_t ulBlockCount = *pulBlockCount;
        uint32_t ulBlockIndex;

        /*  Branch all of the file data blocks in advance.
        */
        for(ulBlockIndex = 0U; (ulBlockIndex < ulBlockCount) && !fFull; ulBlockIndex++)
        {
            ret = RedInodeDataSeek(pInode, ulBlockStart + ulBlockIndex);

            if((ret == 0) || (ret == -RED_ENODATA))
            {
                ret = BranchBlock(pInode, BRANCHDEPTH_FILE_DATA, false);

                if(ret == -RED_ENOSPC)
                {
                    if(ulBlockIndex > 0U)
                    {
                        ret = 0;
                    }

                    fFull = true;
                }
            }

            if(ret != 0)
            {
                break;
            }
        }

        ulBlockCount = ulBlockIndex;
        ulBlockIndex = 0U;

        if(fFull)
        {
            ulBlockCount--;
        }

        /*  Write the data to disk one contiguous extent at a time.
        */
        while((ret == 0) && (ulBlockIndex < ulBlockCount))
        {
            uint32_t ulExtentStart;
            uint32_t ulExtentLen = ulBlockCount - ulBlockIndex;

            ret = GetExtent(pInode, ulBlockStart + ulBlockIndex, &ulExtentStart, &ulExtentLen);

            if(ret == 0)
            {
                ret = RedIoWrite(gbRedVolNum, ulExtentStart, ulExtentLen, &pbBuffer[ulBlockIndex << BLOCK_SIZE_P2]);

                if(ret == 0)
                {
                    /*  If there is any buffered file data for the extent we
                        just wrote, those buffers are now stale.
                    */
                    ret = RedBufferDiscardRange(ulExtentStart, ulExtentLen);
                }

                if(ret == 0)
                {
                    ulBlockIndex += ulExtentLen;
                }
            }
        }

        if(ret == 0)
        {
            *pulBlockCount = ulBlockCount;
        }
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


/** @brief Get the physical block number and count of contiguous blocks given a
           starting logical block number.

    @param pInode           A pointer to the cached inode structure.
    @param ulBlockStart     The file block offset for the start of the extent.
    @param pulExtentStart   On successful return, the starting physical block
                            number of the contiguous extent.
    @param pulExtentLen     On entry, the maximum length of the extent; on
                            successful return, the length of the contiguous
                            extent.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0               Operation was successful.
    @retval -RED_EIO        A disk I/O error occurred.
    @retval -RED_ENODATA    The block offset is sparse.
    @retval -RED_EINVAL     Invalid parameters.
*/
static REDSTATUS GetExtent(
    CINODE     *pInode,
    uint32_t    ulBlockStart,
    uint32_t   *pulExtentStart,
    uint32_t   *pulExtentLen)
{
    REDSTATUS   ret;

    if((pulExtentStart == NULL) || (pulExtentLen == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        ret = RedInodeDataSeek(pInode, ulBlockStart);

        if(ret == 0)
        {
            uint32_t ulExtentLen = *pulExtentLen;
            uint32_t ulFirstBlock = pInode->ulDataBlock;
            uint32_t ulRunLen = 1U;

            while((ret == 0) && (ulRunLen < ulExtentLen))
            {
                ret = RedInodeDataSeek(pInode, ulBlockStart + ulRunLen);

                /*  The extent ends when we find a sparse data block or when the
                    data block is not contiguous with the preceding data block.
                */
                if((ret == -RED_ENODATA) || ((ret == 0) && (pInode->ulDataBlock != (ulFirstBlock + ulRunLen))))
                {
                    ret = 0;
                    break;
                }

                ulRunLen++;
            }

            if(ret == 0)
            {
                *pulExtentStart = ulFirstBlock;
                *pulExtentLen = ulRunLen;
            }
        }
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Allocate or branch the file metadata path and data block if necessary.

    Optionally, can stop allocating/branching at a certain depth.

    @param pInode   A pointer to the cached inode structure.
    @param depth    A BRANCHDEPTH_ value indicating the lowest depth to branch.
    @param fBuffer  Whether to buffer the data block.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENOSPC No data can be written because there is insufficient
                        free space.
*/
static REDSTATUS BranchBlock(
    CINODE     *pInode,
    BRANCHDEPTH depth,
    bool        fBuffer)
{
    REDSTATUS   ret;
    uint32_t    ulCost = 0U; /* Init'd to quiet warnings. */

    ret = BranchBlockCost(pInode, depth, &ulCost);

    if((ret == 0) && (ulCost > FreeBlockCount()))
    {
        ret = -RED_ENOSPC;
    }

    if(ret == 0)
    {
      #if DINDIR_POINTERS > 0U
        if(pInode->uDindirEntry != COORD_ENTRY_INVALID)
        {
            ret = BranchOneBlock(&pInode->ulDindirBlock, CAST_VOID_PTR_PTR(&pInode->pDindir), BFLAG_META_DINDIR);

            if(ret == 0)
            {
                /*  In case we just created the double indirect.
                */
                pInode->pDindir->ulInode = pInode->ulInode;

                pInode->pInodeBuf->aulEntries[pInode->uInodeEntry] = pInode->ulDindirBlock;
            }
        }

        if(ret == 0)
      #endif
      #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
        {
            if((pInode->uIndirEntry != COORD_ENTRY_INVALID) && (depth >= BRANCHDEPTH_INDIR))
            {
                ret = BranchOneBlock(&pInode->ulIndirBlock, CAST_VOID_PTR_PTR(&pInode->pIndir), BFLAG_META_INDIR);

                if(ret == 0)
                {
                    /*  In case we just created the indirect.
                    */
                    pInode->pIndir->ulInode = pInode->ulInode;

                  #if DINDIR_POINTERS > 0U
                    if(pInode->uDindirEntry != COORD_ENTRY_INVALID)
                    {
                        pInode->pDindir->aulEntries[pInode->uDindirEntry] = pInode->ulIndirBlock;
                    }
                    else
                  #endif
                    {
                        pInode->pInodeBuf->aulEntries[pInode->uInodeEntry] = pInode->ulIndirBlock;
                    }
                }
            }
        }

        if(ret == 0)
      #endif
        {
            if(depth == BRANCHDEPTH_FILE_DATA)
            {
              #if REDCONF_INODE_BLOCKS == 1
                bool    fAllocedNew = (pInode->ulDataBlock == BLOCK_SPARSE);
              #endif
                void  **ppBufPtr = (fBuffer || (pInode->pbData != NULL)) ? CAST_VOID_PTR_PTR(&pInode->pbData) : NULL;

                ret = BranchOneBlock(&pInode->ulDataBlock, ppBufPtr, 0U);

                if(ret == 0)
                {
                  #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
                    if(pInode->uIndirEntry != COORD_ENTRY_INVALID)
                    {
                        pInode->pIndir->aulEntries[pInode->uIndirEntry] = pInode->ulDataBlock;
                    }
                    else
                  #endif
                    {
                        pInode->pInodeBuf->aulEntries[pInode->uInodeEntry] = pInode->ulDataBlock;
                    }

                  #if REDCONF_INODE_BLOCKS == 1
                    if(fAllocedNew)
                    {
                        if(pInode->pInodeBuf->ulBlocks < INODE_DATA_BLOCKS)
                        {
                            pInode->pInodeBuf->ulBlocks++;
                        }
                        else
                        {
                            CRITICAL_ERROR();
                            ret = -RED_EFUBAR;
                        }
                    }
                  #endif
                }
            }
        }

        CRITICAL_ASSERT(ret == 0);
    }

    return ret;
}


/** @brief Branch a block.

    The block can be a double indirect, indirect, or file data block.

    The caller should have already handled the disk full implications of
    branching this block.

    @param pulBlock On entry, the current block number, which may be
                    BLOCK_SPARSE if the block is to be newly allocated.  On
                    successful return, populated with the new block number,
                    which may be the same as the original block number if it
                    was not BLOCK_SPARSE and the block was already branched.
    @param ppBuffer If NULL, indicates that the caller does not want to buffer
                    the branched block.  If non-NULL, the caller does want the
                    branched block buffered, and the following is true:  On
                    entry, the current buffer for the block, if there is one, or
                    NULL if there is no buffer.  On successful exit, populated
                    with a buffer for the block, which will be dirty.  If the
                    block number is initially BLOCK_SPARSE, there should be no
                    buffer for the block.
    @param uBFlag   The buffer type flags: BFLAG_META_DINDIR, BFLAG_META_INDIR,
                    or zero for file data.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS BranchOneBlock(
    uint32_t   *pulBlock,
    void      **ppBuffer,
    uint16_t    uBFlag)
{
    REDSTATUS   ret = 0;

    if(pulBlock == NULL)
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        ALLOCSTATE  state = ALLOCSTATE_FREE;
        uint32_t    ulPrevBlock = *pulBlock;

        if(ulPrevBlock != BLOCK_SPARSE)
        {
            ret = RedImapBlockState(ulPrevBlock, &state);
        }

        if(ret == 0)
        {
            if(state == ALLOCSTATE_NEW)
            {
                /*  Block is already branched, so simply get it buffered dirty
                    if requested.
                */
                if(ppBuffer != NULL)
                {
                    if(*ppBuffer != NULL)
                    {
                        RedBufferDirty(*ppBuffer);
                    }
                    else
                    {
                        ret = RedBufferGet(ulPrevBlock, uBFlag | BFLAG_DIRTY, ppBuffer);
                    }
                }
            }
            else
            {
                /*  Block does not exist or is committed state, so allocate a
                    new block for the branch.
                */
                ret = RedImapAllocBlock(pulBlock);

                if(ret == 0)
                {
                    if(ulPrevBlock == BLOCK_SPARSE)
                    {
                        /*  Block did not exist previously, so just get it
                            buffered if requested.
                        */
                        if(ppBuffer != NULL)
                        {
                            if(*ppBuffer != NULL)
                            {
                                /*  How could there be an existing buffer when
                                    the block did not exist?
                                */
                                REDERROR();
                                ret = -RED_EINVAL;
                            }
                            else
                            {
                                ret = RedBufferGet(*pulBlock, (uint16_t)((uint32_t)uBFlag | BFLAG_NEW | BFLAG_DIRTY), ppBuffer);
                            }
                        }
                    }
                    else
                    {
                        /*  Branch the buffer for the committed state block to
                            the newly allocated location.
                        */
                        if(ppBuffer != NULL)
                        {
                            if(*ppBuffer == NULL)
                            {
                                ret = RedBufferGet(ulPrevBlock, uBFlag, ppBuffer);
                            }

                            if(ret == 0)
                            {
                                RedBufferBranch(*ppBuffer, *pulBlock);
                            }
                        }

                        /*  Mark the committed state block almost free.
                        */
                        if(ret == 0)
                        {
                            ret = RedImapBlockSet(ulPrevBlock, false);
                        }
                    }
                }
            }
        }
    }

    return ret;
}


/** @brief Compute the free space cost of branching a block.

    The caller must first use RedInodeDataSeek() to the block to be branched.

    @param pInode   A pointer to the cached inode structure, whose coordinates
                    indicate the block to be branched.
    @param depth    A BRANCHDEPTH_ value indicating how much of the file
                    metadata structure needs to be branched.
    @param pulCost  On successful return, populated with the number of blocks
                    that must be allocated from free space in order to branch
                    the given block.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS BranchBlockCost(
    const CINODE   *pInode,
    BRANCHDEPTH     depth,
    uint32_t       *pulCost)
{
    REDSTATUS       ret = 0;

    if(!CINODE_IS_MOUNTED(pInode) || !pInode->fCoordInited || (depth > BRANCHDEPTH_MAX) || (pulCost == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        ALLOCSTATE  state;

        /*  ulCost is initialized to the maximum number of blocks that could
            be branched, and decremented for every block we determine does not
            need to be branched.
        */
      #if DINDIR_POINTERS > 0U
        uint32_t    ulCost = 3U;
      #elif REDCONF_DIRECT_POINTERS < INODE_ENTRIES
        uint32_t    ulCost = 2U;
      #else
        uint32_t    ulCost = 1U;
      #endif

      #if DINDIR_POINTERS > 0U
        if(pInode->uDindirEntry != COORD_ENTRY_INVALID)
        {
            if(pInode->ulDindirBlock != BLOCK_SPARSE)
            {
                ret = RedImapBlockState(pInode->ulDindirBlock, &state);

                if((ret == 0) && (state == ALLOCSTATE_NEW))
                {
                    /*  Double indirect already branched.
                    */
                    ulCost--;
                }
            }
        }
        else
        {
            /*  At this inode offset there are no double indirects.
            */
            ulCost--;
        }

        if(ret == 0)
      #endif
      #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
        {
            if((pInode->uIndirEntry != COORD_ENTRY_INVALID) && (depth >= BRANCHDEPTH_INDIR))
            {
                if(pInode->ulIndirBlock != BLOCK_SPARSE)
                {
                    ret = RedImapBlockState(pInode->ulIndirBlock, &state);

                    if((ret == 0) && (state == ALLOCSTATE_NEW))
                    {
                        /*  Indirect already branched.
                        */
                        ulCost--;
                    }
                }
            }
            else
            {
                /*  Either not branching this deep, or at this inode offset
                    there are no indirects.
                */
                ulCost--;
            }
        }

        if(ret == 0)
      #endif
        {
            if(depth == BRANCHDEPTH_FILE_DATA)
            {
                if(pInode->ulDataBlock != BLOCK_SPARSE)
                {
                    ret = RedImapBlockState(pInode->ulDataBlock, &state);

                    if((ret == 0) && (state == ALLOCSTATE_NEW))
                    {
                        /*  File data block already branched.
                        */
                        ulCost--;

                        /*  If the file data block is branched, then its parent
                            nodes should be branched as well.
                        */
                        REDASSERT(ulCost == 0U);
                    }
                }
            }
            else
            {
                /*  Not branching this deep.
                */
                ulCost--;
            }
        }

        if(ret == 0)
        {
            *pulCost = ulCost;
        }
    }

    return ret;
}


/** @brief Yields the number of currently available free blocks.

    Accounts for reserved blocks, subtracting the number of reserved blocks if
    they are unavailable.

    @return Number of currently available free blocks.
*/
static uint32_t FreeBlockCount(void)
{
    uint32_t ulFreeBlocks = gpRedMR->ulFreeBlocks;

  #if RESERVED_BLOCKS > 0U
    if(!gpRedCoreVol->fUseReservedBlocks)
    {
        if(ulFreeBlocks >= RESERVED_BLOCKS)
        {
            ulFreeBlocks -= RESERVED_BLOCKS;
        }
        else
        {
            ulFreeBlocks = 0U;
        }
    }
  #endif

    return ulFreeBlocks;
}
#endif /* REDCONF_READ_ONLY == 0 */

