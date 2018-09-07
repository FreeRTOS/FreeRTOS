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
    @brief Implements the block device buffering system.

    This module implements the block buffer cache.  It has a number of block
    sized buffers which are used to store data from a given block (identified
    by both block number and volume number: this cache is shared among all
    volumes).  Block buffers may be either dirty or clean.  Most I/O passes
    through this module.  When a buffer is needed for a block which is not in
    the cache, a "victim" is selected via a simple LRU scheme.
*/
#include <redfs.h>
#include <redcore.h>


#if DINDIR_POINTERS > 0U
  #define INODE_META_BUFFERS 3U /* Inode, double indirect, indirect */
#elif REDCONF_INDIRECT_POINTERS > 0U
  #define INODE_META_BUFFERS 2U /* Inode, indirect */
#elif REDCONF_DIRECT_POINTERS == INODE_ENTRIES
  #define INODE_META_BUFFERS 1U /* Inode only */
#endif

#define INODE_BUFFERS (INODE_META_BUFFERS + 1U) /* Add data buffer */

#if REDCONF_IMAP_EXTERNAL == 1
  #define IMAP_BUFFERS 1U
#else
  #define IMAP_BUFFERS 0U
#endif

#if (REDCONF_READ_ONLY == 1) || (REDCONF_API_FSE == 1)
  /*  Read, write, truncate, lookup: One inode all the way down, plus imap.
  */
  #define MINIMUM_BUFFER_COUNT (INODE_BUFFERS + IMAP_BUFFERS)
#elif REDCONF_API_POSIX == 1
  #if REDCONF_API_POSIX_RENAME == 1
    #if REDCONF_RENAME_ATOMIC == 1
      /*  Two parent directories all the way down.  Source and destination inode
          buffer.  One inode buffer for cyclic rename detection.  Imap.  The
          parent inode buffers are released before deleting the destination
          inode, so that does not increase the minimum.
      */
      #define MINIMUM_BUFFER_COUNT (INODE_BUFFERS + INODE_BUFFERS + 3U + IMAP_BUFFERS)
    #else
      /*  Two parent directories all the way down.  Source inode buffer.  One
          inode buffer for cyclic rename detection.  Imap.
      */
      #define MINIMUM_BUFFER_COUNT (INODE_BUFFERS + INODE_BUFFERS + 2U + IMAP_BUFFERS)
    #endif
  #else
    /*  Link/create: Needs a parent inode all the way down, an extra inode
        buffer, and an imap buffer.

        Unlink is the same, since the parent inode buffers are released before
        the inode is deleted.
    */
    #define MINIMUM_BUFFER_COUNT (INODE_BUFFERS + 1U + IMAP_BUFFERS)
  #endif
#endif

#if REDCONF_BUFFER_COUNT < MINIMUM_BUFFER_COUNT
#error "REDCONF_BUFFER_COUNT is too low for the configuration"
#endif


/*  A note on the typecasts in the below macros: Operands to bitwise operators
    are subject to the "usual arithmetic conversions".  This means that the
    flags, which have uint16_t values, are promoted to int.  MISRA-C:2012 R10.1
    forbids using signed integers in bitwise operations, so we cast to uint32_t
    to avoid the integer promotion, then back to uint16_t to reflect the actual
    type.
*/
#define BFLAG_META_MASK (uint16_t)((uint32_t)BFLAG_META_MASTER | BFLAG_META_IMAP | BFLAG_META_INODE | BFLAG_META_INDIR | BFLAG_META_DINDIR)
#define BFLAG_MASK (uint16_t)((uint32_t)BFLAG_DIRTY | BFLAG_NEW | BFLAG_META_MASK)


/*  An invalid block number.  Used to indicate buffers which are not currently
    in use.
*/
#define BBLK_INVALID UINT32_MAX


/** @brief Metadata stored for each block buffer.

    To make better use of CPU caching when searching the BUFFERHEAD array, this
    structure should be kept small.
*/
typedef struct
{
    uint32_t    ulBlock;    /**< Block number the buffer is associated with; BBLK_INVALID if unused. */
    uint8_t     bVolNum;    /**< Volume the block resides on. */
    uint8_t     bRefCount;  /**< Number of references. */
    uint16_t    uFlags;     /**< Buffer flags: mask of BFLAG_* values. */
} BUFFERHEAD;


/** @brief State information for the block buffer module.
*/
typedef struct
{
    /** Number of buffers which are referenced (have a bRefCount > 0).
    */
    uint16_t    uNumUsed;

    /** MRU array.  Each element of the array stores a buffer index; each buffer
        index appears in the array once and only once.  The first element of the
        array is the most-recently-used (MRU) buffer, followed by the next most
        recently used, and so on, till the last element, which is the least-
        recently-used (LRU) buffer.
    */
    uint8_t     abMRU[REDCONF_BUFFER_COUNT];

    /** Buffer heads, storing metadata for each buffer.
    */
    BUFFERHEAD  aHead[REDCONF_BUFFER_COUNT];

    /** Array of memory for the block buffers themselves.

        Force 64-bit alignment of the aabBuffer array to ensure that it is safe
        to cast buffer pointers to node structure pointers.
    */
    ALIGNED_2D_BYTE_ARRAY(b, aabBuffer, REDCONF_BUFFER_COUNT, REDCONF_BLOCK_SIZE);
} BUFFERCTX;


static bool BufferIsValid(const uint8_t  *pbBuffer, uint16_t uFlags);
static bool BufferToIdx(const void *pBuffer, uint8_t *pbIdx);
#if REDCONF_READ_ONLY == 0
static REDSTATUS BufferWrite(uint8_t bIdx);
static REDSTATUS BufferFinalize(uint8_t *pbBuffer, uint16_t uFlags);
#endif
static void BufferMakeLRU(uint8_t bIdx);
static void BufferMakeMRU(uint8_t bIdx);
static bool BufferFind(uint32_t ulBlock, uint8_t *pbIdx);

#ifdef REDCONF_ENDIAN_SWAP
static void BufferEndianSwap(const void *pBuffer, uint16_t uFlags);
static void BufferEndianSwapHeader(NODEHEADER *pHeader);
static void BufferEndianSwapMaster(MASTERBLOCK *pMaster);
static void BufferEndianSwapMetaRoot(METAROOT *pMetaRoot);
static void BufferEndianSwapInode(INODE *pInode);
static void BufferEndianSwapIndir(INDIR *pIndir);
#endif


static BUFFERCTX gBufCtx;


/** @brief Initialize the buffers.
*/
void RedBufferInit(void)
{
    uint8_t bIdx;

    RedMemSet(&gBufCtx, 0U, sizeof(gBufCtx));

    for(bIdx = 0U; bIdx < REDCONF_BUFFER_COUNT; bIdx++)
    {
        /*  When the buffers have been freshly initialized, acquire the buffers
            in the order in which they appear in the array.
        */
        gBufCtx.abMRU[bIdx] = (uint8_t)((REDCONF_BUFFER_COUNT - bIdx) - 1U);
        gBufCtx.aHead[bIdx].ulBlock = BBLK_INVALID;
    }
}


/** @brief Acquire a buffer.

    @param ulBlock  Block number to acquire.
    @param uFlags   BFLAG_ values for the operation.
    @param ppBuffer On success, populated with the acquired buffer.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EINVAL Invalid parameters.
    @retval -RED_EBUSY  All buffers are referenced.
*/
REDSTATUS RedBufferGet(
    uint32_t    ulBlock,
    uint16_t    uFlags,
    void      **ppBuffer)
{
    REDSTATUS   ret = 0;
    uint8_t     bIdx;

    if((ulBlock >= gpRedVolume->ulBlockCount) || ((uFlags & BFLAG_MASK) != uFlags) || (ppBuffer == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        if(BufferFind(ulBlock, &bIdx))
        {
            /*  Error if the buffer exists and BFLAG_NEW was specified, since
                the new flag is used when a block is newly allocated/created, so
                the block was previously free and and there should never be an
                existing buffer for a free block.

                Error if the buffer exists but does not have the same type as
                was requested.
            */
            if(    ((uFlags & BFLAG_NEW) != 0U)
                || ((uFlags & BFLAG_META_MASK) != (gBufCtx.aHead[bIdx].uFlags & BFLAG_META_MASK)))
            {
                CRITICAL_ERROR();
                ret = -RED_EFUBAR;
            }
        }
        else if(gBufCtx.uNumUsed == REDCONF_BUFFER_COUNT)
        {
            /*  The MINIMUM_BUFFER_COUNT is supposed to ensure that no operation
                ever runs out of buffers, so this should never happen.
            */
            CRITICAL_ERROR();
            ret = -RED_EBUSY;
        }
        else
        {
            BUFFERHEAD *pHead;

            /*  Search for the least recently used buffer which is not
                referenced.
            */
            for(bIdx = (uint8_t)(REDCONF_BUFFER_COUNT - 1U); bIdx > 0U; bIdx--)
            {
                if(gBufCtx.aHead[gBufCtx.abMRU[bIdx]].bRefCount == 0U)
                {
                    break;
                }
            }

            bIdx = gBufCtx.abMRU[bIdx];
            pHead = &gBufCtx.aHead[bIdx];

            if(pHead->bRefCount == 0U)
            {
                /*  If the LRU buffer is valid and dirty, write it out before
                    repurposing it.
                */
                if(((pHead->uFlags & BFLAG_DIRTY) != 0U) && (pHead->ulBlock != BBLK_INVALID))
                {
                  #if REDCONF_READ_ONLY == 1
                    CRITICAL_ERROR();
                    ret = -RED_EFUBAR;
                  #else
                    ret = BufferWrite(bIdx);
                  #endif
                }
            }
            else
            {
                /*  All the buffers are used, which should have been caught by
                    checking gBufCtx.uNumUsed.
                */
                CRITICAL_ERROR();
                ret = -RED_EBUSY;
            }

            if(ret == 0)
            {
                if((uFlags & BFLAG_NEW) == 0U)
                {
                    /*  Invalidate the LRU buffer.  If the read fails, we do not
                        want the buffer head to continue to refer to the old
                        block number, since the read, even if it fails, may have
                        partially overwritten the buffer data (consider the case
                        where block size exceeds sector size, and some but not
                        all of the sectors are read successfully), and if the
                        buffer were to be used subsequently with its partially
                        erroneous contents, bad things could happen.
                    */
                    pHead->ulBlock = BBLK_INVALID;

                    ret = RedIoRead(gbRedVolNum, ulBlock, 1U, gBufCtx.b.aabBuffer[bIdx]);

                    if((ret == 0) && ((uFlags & BFLAG_META) != 0U))
                    {
                        if(!BufferIsValid(gBufCtx.b.aabBuffer[bIdx], uFlags))
                        {
                            /*  A corrupt metadata node is usually a critical
                                error.  The master block is an exception since
                                it might be invalid because the volume is not
                                mounted; that condition is expected and should
                                not result in an assertion.
                            */
                            CRITICAL_ASSERT((uFlags & BFLAG_META_MASTER) == BFLAG_META_MASTER);
                            ret = -RED_EIO;
                        }
                    }

                  #ifdef REDCONF_ENDIAN_SWAP
                    if(ret == 0)
                    {
                        BufferEndianSwap(gBufCtx.b.aabBuffer[bIdx], uFlags);
                    }
                  #endif
                }
                else
                {
                    RedMemSet(gBufCtx.b.aabBuffer[bIdx], 0U, REDCONF_BLOCK_SIZE);
                }
            }

            if(ret == 0)
            {
                pHead->bVolNum = gbRedVolNum;
                pHead->ulBlock = ulBlock;
                pHead->uFlags = 0U;
            }
        }

        /*  Reference the buffer, update its flags, and promote it to MRU.  This
            happens both when BufferFind() found an existing buffer for the
            block and when the LRU buffer was repurposed to create a buffer for
            the block.
        */
        if(ret == 0)
        {
            BUFFERHEAD *pHead = &gBufCtx.aHead[bIdx];

            pHead->bRefCount++;

            if(pHead->bRefCount == 1U)
            {
                gBufCtx.uNumUsed++;
            }

            /*  BFLAG_NEW tells this function to zero the buffer instead of
                reading it from disk; it has no meaning later on, and thus is
                not saved.
            */
            pHead->uFlags |= (uFlags & (~BFLAG_NEW));

            BufferMakeMRU(bIdx);

            *ppBuffer = gBufCtx.b.aabBuffer[bIdx];
        }
    }

    return ret;
}


/** @brief Release a buffer.

    @param pBuffer  The buffer to release.
 */
void RedBufferPut(
    const void *pBuffer)
{
    uint8_t     bIdx;

    if(!BufferToIdx(pBuffer, &bIdx))
    {
        REDERROR();
    }
    else
    {
        REDASSERT(gBufCtx.aHead[bIdx].bRefCount > 0U);
        gBufCtx.aHead[bIdx].bRefCount--;

        if(gBufCtx.aHead[bIdx].bRefCount == 0U)
        {
            REDASSERT(gBufCtx.uNumUsed > 0U);
            gBufCtx.uNumUsed--;
        }
    }
}


#if REDCONF_READ_ONLY == 0
/** @brief Flush all buffers for the active volume in the given range of blocks.

    @param ulBlockStart Starting block number to flush.
    @param ulBlockCount Count of blocks, starting at @p ulBlockStart, to flush.
                        Must not be zero.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EINVAL Invalid parameters.
*/
REDSTATUS RedBufferFlush(
    uint32_t    ulBlockStart,
    uint32_t    ulBlockCount)
{
    REDSTATUS   ret = 0;

    if(    (ulBlockStart >= gpRedVolume->ulBlockCount)
        || ((gpRedVolume->ulBlockCount - ulBlockStart) < ulBlockCount)
        || (ulBlockCount == 0U))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint8_t bIdx;

        for(bIdx = 0U; bIdx < REDCONF_BUFFER_COUNT; bIdx++)
        {
            BUFFERHEAD *pHead = &gBufCtx.aHead[bIdx];

            if(    (pHead->bVolNum == gbRedVolNum)
                && (pHead->ulBlock != BBLK_INVALID)
                && ((pHead->uFlags & BFLAG_DIRTY) != 0U)
                && (pHead->ulBlock >= ulBlockStart)
                && (pHead->ulBlock < (ulBlockStart + ulBlockCount)))
            {
                ret = BufferWrite(bIdx);

                if(ret == 0)
                {
                    pHead->uFlags &= (~BFLAG_DIRTY);
                }
                else
                {
                    break;
                }
            }
        }
    }

    return ret;
}


/** @brief Mark a buffer dirty

    @param pBuffer  The buffer to mark dirty.
*/
void RedBufferDirty(
    const void *pBuffer)
{
    uint8_t     bIdx;

    if(!BufferToIdx(pBuffer, &bIdx))
    {
        REDERROR();
    }
    else
    {
        REDASSERT(gBufCtx.aHead[bIdx].bRefCount > 0U);

        gBufCtx.aHead[bIdx].uFlags |= BFLAG_DIRTY;
    }
}


/** @brief Branch a buffer, marking it dirty and assigning a new block number.

    @param pBuffer      The buffer to branch.
    @param ulBlockNew   The new block number for the buffer.
*/
void RedBufferBranch(
    const void *pBuffer,
    uint32_t    ulBlockNew)
{
    uint8_t     bIdx;

    if(    !BufferToIdx(pBuffer, &bIdx)
        || (ulBlockNew >= gpRedVolume->ulBlockCount))
    {
        REDERROR();
    }
    else
    {
        BUFFERHEAD *pHead = &gBufCtx.aHead[bIdx];

        REDASSERT(pHead->bRefCount > 0U);
        REDASSERT((pHead->uFlags & BFLAG_DIRTY) == 0U);

        pHead->uFlags |= BFLAG_DIRTY;
        pHead->ulBlock = ulBlockNew;
    }
}


#if (REDCONF_API_POSIX == 1) || FORMAT_SUPPORTED
/** @brief Discard a buffer, releasing it and marking it invalid.

    @param pBuffer  The buffer to discard.
*/
void RedBufferDiscard(
    const void *pBuffer)
{
    uint8_t     bIdx;

    if(!BufferToIdx(pBuffer, &bIdx))
    {
        REDERROR();
    }
    else
    {
        REDASSERT(gBufCtx.aHead[bIdx].bRefCount == 1U);
        REDASSERT(gBufCtx.uNumUsed > 0U);

        gBufCtx.aHead[bIdx].bRefCount = 0U;
        gBufCtx.aHead[bIdx].ulBlock = BBLK_INVALID;

        gBufCtx.uNumUsed--;

        BufferMakeLRU(bIdx);
    }
}
#endif
#endif /* REDCONF_READ_ONLY == 0 */


/** @brief Discard a range of buffers, marking them invalid.

    @param ulBlockStart The starting block number to discard
    @param ulBlockCount The number of blocks, starting at @p ulBlockStart, to
                        discard.  Must not be zero.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL Invalid parameters.
    @retval -RED_EBUSY  A block in the desired range is referenced.
*/
REDSTATUS RedBufferDiscardRange(
    uint32_t    ulBlockStart,
    uint32_t    ulBlockCount)
{
    REDSTATUS   ret = 0;

    if(    (ulBlockStart >= gpRedVolume->ulBlockCount)
        || ((gpRedVolume->ulBlockCount - ulBlockStart) < ulBlockCount)
        || (ulBlockCount == 0U))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint8_t bIdx;

        for(bIdx = 0U; bIdx < REDCONF_BUFFER_COUNT; bIdx++)
        {
            BUFFERHEAD *pHead = &gBufCtx.aHead[bIdx];

            if(    (pHead->bVolNum == gbRedVolNum)
                && (pHead->ulBlock != BBLK_INVALID)
                && (pHead->ulBlock >= ulBlockStart)
                && (pHead->ulBlock < (ulBlockStart + ulBlockCount)))
            {
                if(pHead->bRefCount == 0U)
                {
                    pHead->ulBlock = BBLK_INVALID;

                    BufferMakeLRU(bIdx);
                }
                else
                {
                    /*  This should never happen.  There are three general cases
                        when this function is used:

                        1) Discarding every block, as happens during unmount
                           and at the end of format.  There should no longer be
                           any referenced buffers at those points.
                        2) Discarding a block which has become free.  All
                           buffers for such blocks should be put or branched
                           beforehand.
                        3) Discarding of blocks that were just written straight
                           to disk, leaving stale data in the buffer.  The write
                           code should never reference buffers for these blocks,
                           since they would not be needed or used.
                    */
                    CRITICAL_ERROR();
                    ret = -RED_EBUSY;
                    break;
                }
            }
        }
    }

    return ret;
}


/** Determine whether a metadata buffer is valid.

    This includes checking its signature, CRC, and sequence number.

    @param pbBuffer Pointer to the metadata buffer to validate.
    @param uFlags   The buffer flags provided by the caller.  Used to determine
                    the expected signature.

    @return Whether the metadata buffer is valid.

    @retval true    The metadata buffer is valid.
    @retval false   The metadata buffer is invalid.
*/
static bool BufferIsValid(
    const uint8_t  *pbBuffer,
    uint16_t        uFlags)
{
    bool            fValid;

    if((pbBuffer == NULL) || ((uFlags & BFLAG_MASK) != uFlags))
    {
        REDERROR();
        fValid = false;
    }
    else
    {
        NODEHEADER  buf;
        uint16_t    uMetaFlags = uFlags & BFLAG_META_MASK;

        /*  Casting pbBuffer to (NODEHEADER *) would run afoul MISRA-C:2012
            R11.3, so instead copy the fields out.
        */
        RedMemCpy(&buf.ulSignature, &pbBuffer[NODEHEADER_OFFSET_SIG], sizeof(buf.ulSignature));
        RedMemCpy(&buf.ulCRC,       &pbBuffer[NODEHEADER_OFFSET_CRC], sizeof(buf.ulCRC));
        RedMemCpy(&buf.ullSequence, &pbBuffer[NODEHEADER_OFFSET_SEQ], sizeof(buf.ullSequence));

      #ifdef REDCONF_ENDIAN_SWAP
        buf.ulCRC = RedRev32(buf.ulCRC);
        buf.ulSignature = RedRev32(buf.ulSignature);
        buf.ullSequence = RedRev64(buf.ullSequence);
      #endif

        /*  Make sure the signature is correct for the type of metadata block
            requested by the caller.
        */
        switch(buf.ulSignature)
        {
            case META_SIG_MASTER:
                fValid = (uMetaFlags == BFLAG_META_MASTER);
                break;
          #if REDCONF_IMAP_EXTERNAL == 1
            case META_SIG_IMAP:
                fValid = (uMetaFlags == BFLAG_META_IMAP);
                break;
          #endif
            case META_SIG_INODE:
                fValid = (uMetaFlags == BFLAG_META_INODE);
                break;
          #if DINDIR_POINTERS > 0U
            case META_SIG_DINDIR:
                fValid = (uMetaFlags == BFLAG_META_DINDIR);
                break;
          #endif
          #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
            case META_SIG_INDIR:
                fValid = (uMetaFlags == BFLAG_META_INDIR);
                break;
          #endif
            default:
                fValid = false;
                break;
        }

        if(fValid)
        {
            uint32_t ulComputedCrc;

            /*  Check for disk corruption by comparing the stored CRC with one
                computed from the data.

                Also check the sequence number: if it is greater than the
                current sequence number, the block is from a previous format
                or the disk is writing blocks out of order.  During mount,
                before the metaroots have been read, the sequence number will
                be unknown, and the check is skipped.
            */
            ulComputedCrc = RedCrcNode(pbBuffer);
            if(buf.ulCRC != ulComputedCrc)
            {
                fValid = false;
            }
            else if(gpRedVolume->fMounted && (buf.ullSequence >= gpRedVolume->ullSequence))
            {
                fValid = false;
            }
            else
            {
                /*  Buffer is valid.  No action, fValid is already true.
                */
            }
        }
    }

    return fValid;
}


/** @brief Derive the index of the buffer.

    @param pBuffer  The buffer to derive the index of.
    @param pbIdx    On success, populated with the index of the buffer.

    @return Boolean indicating result.

    @retval true    Success.
    @retval false   Failure.  @p pBuffer is not a valid buffer pointer.
*/
static bool BufferToIdx(
    const void *pBuffer,
    uint8_t    *pbIdx)
{
    bool        fRet = false;

    if((pBuffer != NULL) && (pbIdx != NULL))
    {
        uint8_t bIdx;

        /*  pBuffer should be a pointer to one of the block buffers.

            A good compiler should optimize this loop into a bounds check and an
            alignment check, although GCC has been observed to not do so; if the
            number of buffers is small, it should not make much difference.  The
            alternative is to use pointer comparisons, but this both deviates
            from MISRA-C:2012 and involves undefined behavior.
        */
        for(bIdx = 0U; bIdx < REDCONF_BUFFER_COUNT; bIdx++)
        {
            if(pBuffer == &gBufCtx.b.aabBuffer[bIdx][0U])
            {
                break;
            }
        }

        if(    (bIdx < REDCONF_BUFFER_COUNT)
            && (gBufCtx.aHead[bIdx].ulBlock != BBLK_INVALID)
            && (gBufCtx.aHead[bIdx].bVolNum == gbRedVolNum))
        {
            *pbIdx = bIdx;
            fRet = true;
        }
    }

    return fRet;
}


#if REDCONF_READ_ONLY == 0
/** @brief Write out a dirty buffer.

    @param bIdx The index of the buffer to write.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EINVAL Invalid parameters.
*/
static REDSTATUS BufferWrite(
    uint8_t     bIdx)
{
    REDSTATUS   ret = 0;

    if(bIdx < REDCONF_BUFFER_COUNT)
    {
        const BUFFERHEAD *pHead = &gBufCtx.aHead[bIdx];

        REDASSERT((pHead->uFlags & BFLAG_DIRTY) != 0U);

        if((pHead->uFlags & BFLAG_META) != 0U)
        {
            ret = BufferFinalize(gBufCtx.b.aabBuffer[bIdx], pHead->uFlags);
        }

        if(ret == 0)
        {
            ret = RedIoWrite(pHead->bVolNum, pHead->ulBlock, 1U, gBufCtx.b.aabBuffer[bIdx]);

          #ifdef REDCONF_ENDIAN_SWAP
            BufferEndianSwap(gBufCtx.b.aabBuffer[bIdx], pHead->uFlags);
          #endif
        }
    }
    else
    {
        REDERROR();
        ret = -RED_EINVAL;
    }

    return ret;
}


/** @brief Finalize a metadata buffer.

    This updates the CRC and the sequence number.  It also sets the signature,
    though this is only truly needed if the buffer is new.

    @param pbBuffer Pointer to the metadata buffer to finalize.
    @param uFlags   The associated buffer flags.  Used to determine the expected
                    signature.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL Invalid parameter; or maximum sequence number reached.
*/
static REDSTATUS BufferFinalize(
    uint8_t    *pbBuffer,
    uint16_t    uFlags)
{
    REDSTATUS   ret = 0;

    if((pbBuffer == NULL) || ((uFlags & BFLAG_MASK) != uFlags))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint32_t ulSignature;

        switch(uFlags & BFLAG_META_MASK)
        {
            case BFLAG_META_MASTER:
                ulSignature = META_SIG_MASTER;
                break;
          #if REDCONF_IMAP_EXTERNAL == 1
            case BFLAG_META_IMAP:
                ulSignature = META_SIG_IMAP;
                break;
          #endif
            case BFLAG_META_INODE:
                ulSignature = META_SIG_INODE;
                break;
          #if DINDIR_POINTERS > 0U
            case BFLAG_META_DINDIR:
                ulSignature = META_SIG_DINDIR;
                break;
          #endif
          #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
            case BFLAG_META_INDIR:
                ulSignature = META_SIG_INDIR;
                break;
          #endif
            default:
                ulSignature = 0U;
                break;
        }

        if(ulSignature == 0U)
        {
            REDERROR();
            ret = -RED_EINVAL;
        }
        else
        {
            uint64_t ullSeqNum = gpRedVolume->ullSequence;

            ret = RedVolSeqNumIncrement();
            if(ret == 0)
            {
                uint32_t ulCrc;

                RedMemCpy(&pbBuffer[NODEHEADER_OFFSET_SIG], &ulSignature, sizeof(ulSignature));
                RedMemCpy(&pbBuffer[NODEHEADER_OFFSET_SEQ], &ullSeqNum, sizeof(ullSeqNum));

              #ifdef REDCONF_ENDIAN_SWAP
                BufferEndianSwap(pbBuffer, uFlags);
              #endif

                ulCrc = RedCrcNode(pbBuffer);
              #ifdef REDCONF_ENDIAN_SWAP
                ulCrc = RedRev32(ulCrc);
              #endif
                RedMemCpy(&pbBuffer[NODEHEADER_OFFSET_CRC], &ulCrc, sizeof(ulCrc));
            }
        }
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


#ifdef REDCONF_ENDIAN_SWAP
/** @brief Swap the byte order of a metadata buffer

    Does nothing if the buffer is not a metadata node.  Also does nothing for
    meta roots, which don't go through the buffers anyways.

    @param pBuffer  Pointer to the metadata buffer to swap
    @param uFlags   The associated buffer flags.  Used to determin the type of
                    metadata node.
*/
static void BufferEndianSwap(
    void       *pBuffer,
    uint16_t    uFlags)
{
    if((pBuffer == NULL) || ((uFlags & BFLAG_MASK) != uFlags))
    {
        REDERROR();
    }
    else if((uFlags & BFLAG_META_MASK) != 0)
    {
        BufferEndianSwapHeader(pBuffer);

        switch(uFlags & BFLAG_META_MASK)
        {
            case BFLAG_META_MASTER:
                BufferEndianSwapMaster(pBuffer);
                break;
            case BFLAG_META_INODE:
                BufferEndianSwapInode(pBuffer);
                break;
          #if DINDIR_POINTERS > 0U
            case BFLAG_META_DINDIR:
                BufferEndianSwapIndir(pBuffer);
                break;
          #endif
          #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
            case BFLAG_META_INDIR:
                BufferEndianSwapIndir(pBuffer);
                break;
          #endif
            default:
                break;
        }
    }
    else
    {
        /*  File data buffers do not need to be swapped.
        */
    }
}


/** @brief Swap the byte order of a metadata node header

    @param pHeader  Pointer to the metadata node header to swap
*/
static void BufferEndianSwapHeader(
    NODEHEADER *pHeader)
{
    if(pHeader == NULL)
    {
        REDERROR();
    }
    else
    {
        pHeader->ulSignature = RedRev32(pHeader->ulSignature);
        pHeader->ulCRC = RedRev32(pHeader->ulCRC);
        pHeader->ullSequence = RedRev64(pHeader->ullSequence);
    }
}


/** @brief Swap the byte order of a master block

    @param pMaster  Pointer to the master block to swap
*/
static void BufferEndianSwapMaster(
    MASTERBLOCK *pMaster)
{
    if(pMaster == NULL)
    {
        REDERROR();
    }
    else
    {
        pMaster->ulVersion = RedRev32(pMaster->ulVersion);
        pMaster->ulFormatTime = RedRev32(pMaster->ulFormatTime);
        pMaster->ulInodeCount = RedRev32(pMaster->ulInodeCount);
        pMaster->ulBlockCount = RedRev32(pMaster->ulBlockCount);
        pMaster->uMaxNameLen = RedRev16(pMaster->uMaxNameLen);
        pMaster->uDirectPointers = RedRev16(pMaster->uDirectPointers);
        pMaster->uIndirectPointers = RedRev16(pMaster->uIndirectPointers);
    }
}


/** @brief Swap the byte order of an inode

    @param pInode   Pointer to the inode to swap
*/
static void BufferEndianSwapInode(
    INODE  *pInode)
{
    if(pInode == NULL)
    {
        REDERROR();
    }
    else
    {
        uint32_t ulIdx;

        pInode->ullSize = RedRev64(pInode->ullSize);

      #if REDCONF_INODE_BLOCKS == 1
        pInode->ulBlocks = RedRev32(pInode->ulBlocks);
      #endif

      #if REDCONF_INODE_TIMESTAMPS == 1
        pInode->ulATime = RedRev32(pInode->ulATime);
        pInode->ulMTime = RedRev32(pInode->ulMTime);
        pInode->ulCTime = RedRev32(pInode->ulCTime);
      #endif

        pInode->uMode = RedRev16(pInode->uMode);

      #if (REDCONF_API_POSIX == 1) && (REDCONF_API_POSIX_LINK == 1)
        pInode->uNLink = RedRev16(pInode->uNLink);
      #endif

      #if REDCONF_API_POSIX == 1
        pInode->ulPInode = RedRev32(pInode->ulPInode);
      #endif

        for(ulIdx = 0; ulIdx < INODE_ENTRIES; ulIdx++)
        {
            pInode->aulEntries[ulIdx] = RedRev32(pInode->aulEntries[ulIdx]);
        }
    }
}


#if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
/** @brief Swap the byte order of an indirect or double indirect node

    @param pIndir   Pointer to the node to swap
*/
static void BufferEndianSwapIndir(
    INDIR  *pIndir)
{
    if(pIndir == NULL)
    {
        REDERROR();
    }
    else
    {
        uint32_t ulIdx;

        pIndir->ulInode = RedRev32(pIndir->ulInode);

        for(ulIdx = 0; ulIdx < INDIR_ENTRIES; ulIdx++)
        {
            pIndir->aulEntries[ulIdx] = RedRev32(pIndir->aulEntries[ulIdx]);
        }
    }
}

#endif /* REDCONF_DIRECT_POINTERS < INODE_ENTRIES */
#endif /* #ifdef REDCONF_ENDIAN_SWAP */


/** @brief Mark a buffer as least recently used.

    @param bIdx The index of the buffer to make LRU.
*/
static void BufferMakeLRU(
    uint8_t bIdx)
{
    if(bIdx >= REDCONF_BUFFER_COUNT)
    {
        REDERROR();
    }
    else if(bIdx != gBufCtx.abMRU[REDCONF_BUFFER_COUNT - 1U])
    {
        uint8_t bMruIdx;

        /*  Find the current position of the buffer in the MRU array.  We do not
            need to check the last slot, since we already know from the above
            check that the index is not there.
        */
        for(bMruIdx = 0U; bMruIdx < (REDCONF_BUFFER_COUNT - 1U); bMruIdx++)
        {
            if(bIdx == gBufCtx.abMRU[bMruIdx])
            {
                break;
            }
        }

        if(bMruIdx < (REDCONF_BUFFER_COUNT - 1U))
        {
            /*  Move the buffer index to the back of the MRU array, making it
                the LRU buffer.
            */
            RedMemMove(&gBufCtx.abMRU[bMruIdx], &gBufCtx.abMRU[bMruIdx + 1U], REDCONF_BUFFER_COUNT - ((uint32_t)bMruIdx + 1U));
            gBufCtx.abMRU[REDCONF_BUFFER_COUNT - 1U] = bIdx;
        }
        else
        {
            REDERROR();
        }
    }
    else
    {
        /*  Buffer already LRU, nothing to do.
        */
    }
}


/** @brief Mark a buffer as most recently used.

    @param bIdx The index of the buffer to make MRU.
*/
static void BufferMakeMRU(
    uint8_t bIdx)
{
    if(bIdx >= REDCONF_BUFFER_COUNT)
    {
        REDERROR();
    }
    else if(bIdx != gBufCtx.abMRU[0U])
    {
        uint8_t bMruIdx;

        /*  Find the current position of the buffer in the MRU array.  We do not
            need to check the first slot, since we already know from the above
            check that the index is not there.
        */
        for(bMruIdx = 1U; bMruIdx < REDCONF_BUFFER_COUNT; bMruIdx++)
        {
            if(bIdx == gBufCtx.abMRU[bMruIdx])
            {
                break;
            }
        }

        if(bMruIdx < REDCONF_BUFFER_COUNT)
        {
            /*  Move the buffer index to the front of the MRU array, making it
                the MRU buffer.
            */
            RedMemMove(&gBufCtx.abMRU[1U], &gBufCtx.abMRU[0U], bMruIdx);
            gBufCtx.abMRU[0U] = bIdx;
        }
        else
        {
            REDERROR();
        }
    }
    else
    {
        /*  Buffer already MRU, nothing to do.
        */
    }
}


/** @brief Find a block in the buffers.

    @param ulBlock  The block number to find.
    @param pbIdx    If the block is buffered (true is returned), populated with
                    the index of the buffer.

    @return Boolean indicating whether or not the block is buffered.

    @retval true    @p ulBlock is buffered, and its index has been stored in
                    @p pbIdx.
    @retval false   @p ulBlock is not buffered.
*/
static bool BufferFind(
    uint32_t ulBlock,
    uint8_t *pbIdx)
{
    bool     ret = false;

    if((ulBlock >= gpRedVolume->ulBlockCount) || (pbIdx == NULL))
    {
        REDERROR();
    }
    else
    {
        uint8_t bIdx;

        for(bIdx = 0U; bIdx < REDCONF_BUFFER_COUNT; bIdx++)
        {
            const BUFFERHEAD *pHead = &gBufCtx.aHead[bIdx];

            if((pHead->bVolNum == gbRedVolNum) && (pHead->ulBlock == ulBlock))
            {
                *pbIdx = bIdx;
                ret = true;
                break;
            }
        }
    }

    return ret;
}

