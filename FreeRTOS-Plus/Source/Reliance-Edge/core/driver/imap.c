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
    @brief Implements allocation routines.

    This module implements routines for working with the imap, a bitmap which
    tracks which blocks are allocated or free.  Some of the functionality is
    delegated to imapinline.c and imapextern.c.
*/
#include <redfs.h>
#include <redcore.h>


/** @brief Get the allocation bit of a block from either metaroot.

    Will pass the call down either to the inline imap or to the external imap
    implementation, whichever is appropriate for the current volume.

    @param bMR          The metaroot index: either 0 or 1.
    @param ulBlock      The block number to query.
    @param pfAllocated  On successful return, populated with the allocation bit
                        of the block.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p bMR is out of range; or @p ulBlock is out of range;
                        or @p pfAllocated is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedImapBlockGet(
    uint8_t     bMR,
    uint32_t    ulBlock,
    bool       *pfAllocated)
{
    REDSTATUS   ret;

    if(    (bMR > 1U)
        || (ulBlock < gpRedCoreVol->ulInodeTableStartBN)
        || (ulBlock >= gpRedVolume->ulBlockCount)
        || (pfAllocated == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
      #if (REDCONF_IMAP_INLINE == 1) && (REDCONF_IMAP_EXTERNAL == 1)
        if(gpRedCoreVol->fImapInline)
        {
            ret = RedImapIBlockGet(bMR, ulBlock, pfAllocated);
        }
        else
        {
            ret = RedImapEBlockGet(bMR, ulBlock, pfAllocated);
        }
      #elif REDCONF_IMAP_INLINE == 1
        ret = RedImapIBlockGet(bMR, ulBlock, pfAllocated);
      #else
        ret = RedImapEBlockGet(bMR, ulBlock, pfAllocated);
      #endif
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Set the allocation bit of a block in the working metaroot.

    Will pass the call down either to the inline imap or to the external imap
    implementation, whichever is appropriate for the current volume.

    @param ulBlock      The block number to allocate or free.
    @param fAllocated   Whether to allocate the block (true) or free it (false).

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p ulBlock is out of range; or @p ulBlock is allocable
                        and @p fAllocated is 1.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedImapBlockSet(
    uint32_t    ulBlock,
    bool        fAllocated)
{
    REDSTATUS   ret;

    if(    (ulBlock < gpRedCoreVol->ulInodeTableStartBN)
        || (ulBlock >= gpRedVolume->ulBlockCount))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else if(    (ulBlock >= gpRedCoreVol->ulFirstAllocableBN)
             && (    (fAllocated && (gpRedMR->ulFreeBlocks == 0U))
                  || ((!fAllocated) && (gpRedMR->ulFreeBlocks >= gpRedVolume->ulBlocksAllocable))))
    {
        /*  Attempting either to free more blocks than are allocable, or
            allocate a block when there are none available.  This could indicate
            metadata corruption.
        */
        CRITICAL_ERROR();
        ret = -RED_EFUBAR;
    }
    else
    {
      #if (REDCONF_IMAP_INLINE == 1) && (REDCONF_IMAP_EXTERNAL == 1)
        if(gpRedCoreVol->fImapInline)
        {
            ret = RedImapIBlockSet(ulBlock, fAllocated);
        }
        else
        {
            ret = RedImapEBlockSet(ulBlock, fAllocated);
        }
      #elif REDCONF_IMAP_INLINE == 1
        ret = RedImapIBlockSet(ulBlock, fAllocated);
      #else
        ret = RedImapEBlockSet(ulBlock, fAllocated);
      #endif

        /*  Any change to the allocation state of a block indicates that the
            volume is now branched.
        */
        gpRedCoreVol->fBranched = true;
    }

    /*  If a block was marked as no longer in use, discard it from the buffers.
    */
    if((ret == 0) && (!fAllocated))
    {
        ret = RedBufferDiscardRange(ulBlock, 1U);
        CRITICAL_ASSERT(ret == 0);
    }

    /*  Adjust the free/almost free block count if the block was allocable.
    */
    if((ret == 0) && (ulBlock >= gpRedCoreVol->ulFirstAllocableBN))
    {
        if(fAllocated)
        {
            gpRedMR->ulFreeBlocks--;
        }
        else
        {
            bool fWasAllocated;

            /*  Whether the block became free or almost free depends on its
                previous allocation state.  If it was used, then it is now
                almost free.  Otherwise, it was new and is now free.
            */
            ret = RedImapBlockGet(1U - gpRedCoreVol->bCurMR, ulBlock, &fWasAllocated);
            CRITICAL_ASSERT(ret == 0);

            if(ret == 0)
            {
                if(fWasAllocated)
                {
                    gpRedCoreVol->ulAlmostFreeBlocks++;
                }
                else
                {
                    gpRedMR->ulFreeBlocks++;
                }
            }
        }
    }

    return ret;
}


/** @brief Allocate one block.

    @param pulBlock On successful return, populated with the allocated block
                    number.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p pulBlock is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENOSPC Insufficient free space to perform the allocation.
*/
REDSTATUS RedImapAllocBlock(
    uint32_t   *pulBlock)
{
    REDSTATUS   ret;

    if(pulBlock == NULL)
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else if(gpRedMR->ulFreeBlocks == 0U)
    {
        ret = -RED_ENOSPC;
    }
    else
    {
        uint32_t ulStopBlock = gpRedMR->ulAllocNextBlock;
        bool     fAllocated = false;

        do
        {
            ALLOCSTATE state;

            ret = RedImapBlockState(gpRedMR->ulAllocNextBlock, &state);
            CRITICAL_ASSERT(ret == 0);

            if(ret == 0)
            {
                if(state == ALLOCSTATE_FREE)
                {
                    ret = RedImapBlockSet(gpRedMR->ulAllocNextBlock, true);
                    CRITICAL_ASSERT(ret == 0);

                    *pulBlock = gpRedMR->ulAllocNextBlock;
                    fAllocated = true;
                }

                /*  Increment the next block number, wrapping it when the end of
                    the volume is reached.
                */
                gpRedMR->ulAllocNextBlock++;
                if(gpRedMR->ulAllocNextBlock == gpRedVolume->ulBlockCount)
                {
                    gpRedMR->ulAllocNextBlock = gpRedCoreVol->ulFirstAllocableBN;
                }
            }
        }
        while((ret == 0) && !fAllocated && (gpRedMR->ulAllocNextBlock != ulStopBlock));

        if((ret == 0) && !fAllocated)
        {
            /*  The free block count was already determined to be non-zero, no
                error occurred while looking for free blocks, but no free blocks
                were found.  This indicates metadata corruption.
            */
            CRITICAL_ERROR();
            ret = -RED_EFUBAR;
        }
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


/** @brief Get the allocation state of a block.

    Takes into account the allocation bits from both metaroots, and returns one
    of four possible allocation state values:

    - ::ALLOCSTATE_FREE Free and may be allocated; writeable.
    - ::ALLOCSTATE_USED In-use and transacted; not writeable.
    - ::ALLOCSTATE_NEW In-use but not transacted; writeable.
    - ::ALLOCSTATE_AFREE Will become free after a transaction; not writeable.

    @param ulBlock  The block number to query.
    @param pState   On successful return, populated with the state of the block.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p ulBlock is out of range; or @p pState is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedImapBlockState(
    uint32_t    ulBlock,
    ALLOCSTATE *pState)
{
    REDSTATUS   ret;

    if(    (ulBlock < gpRedCoreVol->ulInodeTableStartBN)
        || (ulBlock >= gpRedVolume->ulBlockCount)
        || (pState == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        bool fBitCurrent;

        ret = RedImapBlockGet(gpRedCoreVol->bCurMR, ulBlock, &fBitCurrent);

        if(ret == 0)
        {
            bool fBitOld;

            ret = RedImapBlockGet(1U - gpRedCoreVol->bCurMR, ulBlock, &fBitOld);

            if(ret == 0)
            {
                if(fBitCurrent)
                {
                    if(fBitOld)
                    {
                        *pState = ALLOCSTATE_USED;
                    }
                    else
                    {
                        *pState = ALLOCSTATE_NEW;
                    }
                }
                else
                {
                    if(fBitOld)
                    {
                        *pState = ALLOCSTATE_AFREE;
                    }
                    else
                    {
                        *pState = ALLOCSTATE_FREE;
                    }
                }
            }
        }
    }

    return ret;
}

