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
    @brief Implements routines for the external imap.

    The external imap is used on volumes that are too big for the imap bitmap
    to be stored entirely in the metaroot, so instead the bitmap is stored in
    imap nodes on disk, and the metaroot bitmap is used to toggle between imap
    nodes.
*/
#include <redfs.h>

#if REDCONF_IMAP_EXTERNAL == 1

#include <redcore.h>


#if REDCONF_READ_ONLY == 0
static REDSTATUS ImapNodeBranch(uint32_t ulImapNode, IMAPNODE **ppImap);
static bool ImapNodeIsBranched(uint32_t ulImapNode);
#endif


/** @brief Get the allocation bit of a block from the imap as it exists in
           either metaroot.

    @param bMR          The metaroot index: either 0 or 1.
    @param ulBlock      The block number to query.
    @param pfAllocated  On successful exit, populated with the allocation bit
                        of the block.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p bMR is out of range; or @p ulBlock is out of range;
                        or @p pfAllocated is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedImapEBlockGet(
    uint8_t     bMR,
    uint32_t    ulBlock,
    bool       *pfAllocated)
{
    REDSTATUS   ret;

    if(    gpRedCoreVol->fImapInline
        || (bMR > 1U)
        || (ulBlock < gpRedCoreVol->ulInodeTableStartBN)
        || (ulBlock >= gpRedVolume->ulBlockCount)
        || (pfAllocated == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint32_t    ulOffset = ulBlock - gpRedCoreVol->ulInodeTableStartBN;
        uint32_t    ulImapNode = ulOffset / IMAPNODE_ENTRIES;
        uint8_t     bMRToRead = bMR;
        IMAPNODE   *pImap;

      #if REDCONF_READ_ONLY == 0
        /*  If the imap node is not branched, then both copies of the imap are
            identical.  If the old metaroot copy is requested, use the current
            copy instead, since it is more likely to be buffered.
        */
        if(bMR == (1U - gpRedCoreVol->bCurMR))
        {
            if(!ImapNodeIsBranched(ulImapNode))
            {
                bMRToRead = 1U - bMR;
            }
        }
      #endif

        ret = RedBufferGet(RedImapNodeBlock(bMRToRead, ulImapNode), BFLAG_META_IMAP, CAST_VOID_PTR_PTR(&pImap));

        if(ret == 0)
        {
            *pfAllocated = RedBitGet(pImap->abEntries, ulOffset % IMAPNODE_ENTRIES);

            RedBufferPut(pImap);
        }
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Set the allocation bit of a block in the working-state imap.

    @param ulBlock      The block number to allocate or free.
    @param fAllocated   Whether to allocate the block (true) or free it (false).

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p ulBlock is out of range.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedImapEBlockSet(
    uint32_t    ulBlock,
    bool        fAllocated)
{
    REDSTATUS   ret;

    if(    gpRedCoreVol->fImapInline
        || (ulBlock < gpRedCoreVol->ulInodeTableStartBN)
        || (ulBlock >= gpRedVolume->ulBlockCount))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint32_t    ulOffset = ulBlock - gpRedCoreVol->ulInodeTableStartBN;
        uint32_t    ulImapNode = ulOffset / IMAPNODE_ENTRIES;
        IMAPNODE   *pImap;

        ret = ImapNodeBranch(ulImapNode, &pImap);

        if(ret == 0)
        {
            uint32_t ulImapEntry = ulOffset % IMAPNODE_ENTRIES;

            if(RedBitGet(pImap->abEntries, ulImapEntry) == fAllocated)
            {
                /*  The driver shouldn't ever set a bit in the imap to its
                    current value.  That shouldn't ever be needed, and it
                    indicates that the driver is doing unnecessary I/O, or
                    that the imap is corrupt.
                */
                CRITICAL_ERROR();
                ret = -RED_EFUBAR;
            }
            else if(fAllocated)
            {
                RedBitSet(pImap->abEntries, ulImapEntry);
            }
            else
            {
                RedBitClear(pImap->abEntries, ulImapEntry);
            }

            RedBufferPut(pImap);
        }
    }

    return ret;
}


/** @brief Branch an imap node and get a buffer for it.

    If the imap node is already branched, it can be overwritten in its current
    location, and this function just gets it buffered dirty.  If the node is not
    already branched, the metaroot must be updated to toggle the imap node to
    its alternate location, thereby preserving the committed state copy of the
    imap node.

    @param ulImapNode   The imap node to branch and buffer.
    @param ppImap       On successful return, populated with the imap node
                        buffer, which will be marked dirty.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p ulImapNode is out of range; or @p ppImap is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS ImapNodeBranch(
    uint32_t    ulImapNode,
    IMAPNODE  **ppImap)
{
    REDSTATUS   ret;

    if((ulImapNode >= gpRedCoreVol->ulImapNodeCount) || (ppImap == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else if(ImapNodeIsBranched(ulImapNode))
    {
        /*  Imap node is already branched, so just get it buffered dirty.
        */
        ret = RedBufferGet(RedImapNodeBlock(gpRedCoreVol->bCurMR, ulImapNode), BFLAG_META_IMAP | BFLAG_DIRTY, CAST_VOID_PTR_PTR(ppImap));
    }
    else
    {
        uint32_t    ulBlockCurrent;
        uint32_t    ulBlockOld;

        /*  The metaroot currently points to the committed state imap node.
            Toggle the metaroot to point at the alternate, writeable location.
        */
        if(RedBitGet(gpRedMR->abEntries, ulImapNode))
        {
            RedBitClear(gpRedMR->abEntries, ulImapNode);
        }
        else
        {
            RedBitSet(gpRedMR->abEntries, ulImapNode);
        }

        ulBlockCurrent = RedImapNodeBlock(gpRedCoreVol->bCurMR, ulImapNode);
        ulBlockOld     = RedImapNodeBlock(1U - gpRedCoreVol->bCurMR, ulImapNode);

        ret = RedBufferDiscardRange(ulBlockCurrent, 1U);

        /*  Buffer the committed copy then reassign the block number to the
            writeable location.  This also dirties the buffer.
        */
        if(ret == 0)
        {
            ret = RedBufferGet(ulBlockOld, BFLAG_META_IMAP, CAST_VOID_PTR_PTR(ppImap));

            if(ret == 0)
            {
                RedBufferBranch(*ppImap, ulBlockCurrent);
            }
        }
    }

    return ret;
}


/** @brief Determine whether an imap node is branched.

    If the imap node is branched, it can be overwritten in its current location.

    @param ulImapNode   The imap node to examine.

    @return Whether the imap node is branched.
*/
static bool ImapNodeIsBranched(
    uint32_t    ulImapNode)
{
    bool        fNodeBitSetInMetaroot0 = RedBitGet(gpRedCoreVol->aMR[0U].abEntries, ulImapNode);
    bool        fNodeBitSetInMetaroot1 = RedBitGet(gpRedCoreVol->aMR[1U].abEntries, ulImapNode);

    /*  If the imap node is not branched, both metaroots will point to the same
        copy of the node.
    */
    return fNodeBitSetInMetaroot0 != fNodeBitSetInMetaroot1;
}
#endif /* REDCONF_READ_ONLY == 0 */


/** @brief Calculate the block number of the imap node location indicated by the
           given metaroot.

    An imap node has two locations on disk.  A bit in the metaroot bitmap
    indicates which location is the valid one, according to that metaroot.  This
    function returns the block number of the imap node which is valid in the
    given metaroot.

    @param bMR          Which metaroot to examine.
    @param ulImapNode   The imap node for which to calculate the block number.

    @return Block number of the imap node, as indicated by the given metaroot.
*/
uint32_t RedImapNodeBlock(
    uint8_t     bMR,
    uint32_t    ulImapNode)
{
    uint32_t    ulBlock;

    REDASSERT(ulImapNode < gpRedCoreVol->ulImapNodeCount);

    ulBlock = gpRedCoreVol->ulImapStartBN + (ulImapNode * 2U);

    if(bMR > 1U)
    {
        REDERROR();
    }
    else if(RedBitGet(gpRedCoreVol->aMR[bMR].abEntries, ulImapNode))
    {
        /*  Bit is set, so point ulBlock at the second copy of the node.
        */
        ulBlock++;
    }
    else
    {
        /*  ulBlock already points at the first copy of the node.
        */
    }

    return ulBlock;
}

#endif /* REDCONF_IMAP_EXTERNAL == 1 */

