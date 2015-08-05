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
    @brief Implements inode functions.
*/
#include <redfs.h>
#include <redcore.h>


#if REDCONF_READ_ONLY == 0
static REDSTATUS InodeIsBranched(uint32_t ulInode, bool *pfIsBranched);
#endif
#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1)
static REDSTATUS InodeFindFree(uint32_t *pulInode);
#endif
#if REDCONF_READ_ONLY == 0
static REDSTATUS InodeGetWriteableCopy(uint32_t ulInode, uint8_t *pbWhich);
#endif
static REDSTATUS InodeGetCurrentCopy(uint32_t ulInode, uint8_t *pbWhich);
#if REDCONF_READ_ONLY == 0
static REDSTATUS InodeBitSet(uint32_t ulInode, uint8_t bWhich, bool fAllocated);
#endif
static uint32_t InodeBlock(uint32_t ulInode, uint8_t bWhich);


/** @brief Mount an existing inode.

    Will populate all fields of the cached inode structure, except those which
    are populated during seek.

    @param pInode   A pointer to the cached inode structure.  The
                    pInode->ulInode field must already be initialized with the
                    inode number to mount.  All other fields will be discarded.
    @param type     The expected inode type.
    @param fBranch  Whether to branch the inode.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0               Operation was successful.
    @retval -RED_EINVAL     Invalid parameters.
    @retval -RED_EROFS      @p fBranch is true but the driver is read-only.
    @retval -RED_EIO        A disk I/O error occurred.
    @retval -RED_EBADF      The inode number is free; or the inode number is not
                            valid.
    @retval -RED_EISDIR     @p type is ::FTYPE_FILE and the inode is a directory.
    @retval -RED_ENOTDIR    @p type is ::FTYPE_DIR and the inode is a file.
*/
REDSTATUS RedInodeMount(
    CINODE     *pInode,
    FTYPE       type,
    bool        fBranch)
{
    REDSTATUS   ret = 0;

    if(pInode == NULL)
    {
        ret = -RED_EINVAL;
    }
    else if(!INODE_IS_VALID(pInode->ulInode))
    {
        ret = -RED_EBADF;
    }
  #if REDCONF_API_FSE == 1
    else if(type == FTYPE_DIR)
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
  #endif
  #if REDCONF_READ_ONLY == 1
    else if(fBranch)
    {
        REDERROR();
        ret = -RED_EROFS;
    }
  #endif
    else
    {
        uint32_t ulInode = pInode->ulInode;
        uint8_t  bWhich = 0U; /* Init'd to quiet warnings. */

        RedMemSet(pInode, 0U, sizeof(*pInode));
        pInode->ulInode = ulInode;

        ret = InodeGetCurrentCopy(pInode->ulInode, &bWhich);

        if(ret == 0)
        {
            ret = RedBufferGet(InodeBlock(pInode->ulInode, bWhich), BFLAG_META_INODE, CAST_VOID_PTR_PTR(&pInode->pInodeBuf));
        }

      #if REDCONF_READ_ONLY == 0
        if(ret == 0)
        {
            ret = InodeIsBranched(pInode->ulInode, &pInode->fBranched);
        }
      #endif

        if(ret == 0)
        {
            if(RED_S_ISREG(pInode->pInodeBuf->uMode))
            {
              #if REDCONF_API_POSIX == 1
                pInode->fDirectory = false;

                if(type == FTYPE_DIR)
                {
                    ret = -RED_ENOTDIR;
                }
              #endif
            }
          #if REDCONF_API_POSIX == 1
            else if(RED_S_ISDIR(pInode->pInodeBuf->uMode))
            {
                pInode->fDirectory = true;

                if(type == FTYPE_FILE)
                {
                    ret = -RED_EISDIR;
                }
            }
          #endif
            else
            {
                /*  Missing or unsupported inode type.
                */
                CRITICAL_ERROR();
                ret = -RED_EFUBAR;
            }
        }

      #if REDCONF_READ_ONLY == 0
        if((ret == 0) && fBranch)
        {
            ret = RedInodeBranch(pInode);
        }
      #endif

        if(ret != 0)
        {
            RedInodePut(pInode, 0U);
        }
    }

    return ret;
}


#if (REDCONF_READ_ONLY == 0) && ((REDCONF_API_POSIX == 1) || FORMAT_SUPPORTED)
/** @brief Create an inode.

    @param pInode   Pointer to the cached inode structure.  If pInode->ulInode
                    is #INODE_INVALID, a free inode will be found; otherwise,
                    pInode->ulInode will be the inode number (an error will be
                    returned if it is not free).
    @param ulPInode The parent inode number.
    @param uMode    The inode mode.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  pInode->ulInode is an invalid inode number other than
                        #INODE_INVALID.
    @retval -RED_EINVAL Invalid parameters.
    @retval -RED_EEXIST Tried to create an inode with an inode number that is
                        already in use.
    @retval -RED_ENFILE All inode slots are already in use.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedInodeCreate(
    CINODE     *pInode,
    uint32_t    ulPInode,
    uint16_t    uMode)
{
    REDSTATUS   ret;

  #if REDCONF_API_POSIX == 1
    /*  ulPInode must be a valid inode number, unless we are creating the root
        directory, in which case ulPInode must be INODE_INVALID (the root
        directory has no parent).
    */
    if(    (pInode == NULL)
        || (!INODE_IS_VALID(ulPInode) && ((ulPInode != INODE_INVALID) || (pInode->ulInode != INODE_ROOTDIR))))
  #else
    if(pInode == NULL)
  #endif
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint32_t ulInode = pInode->ulInode;

        RedMemSet(pInode, 0U, sizeof(*pInode));

      #if REDCONF_API_POSIX == 1
        if(ulInode == INODE_INVALID)
        {
            /*  Caller requested that an inode number be allocated.  Search for
                an unused inode number, error if there isn't one.
            */
            ret = InodeFindFree(&pInode->ulInode);
        }
        else
      #endif
        {
            /*  Caller requested creation of a specific inode number.  Make sure
                it's valid and doesn't already exist.
            */
            if(INODE_IS_VALID(ulInode))
            {
                bool fFree;

                ret = RedInodeIsFree(ulInode, &fFree);
                if(ret == 0)
                {
                    if(fFree)
                    {
                        pInode->ulInode = ulInode;
                    }
                    else
                    {
                        ret = -RED_EEXIST;
                    }
                }
            }
            else
            {
                ret = -RED_EBADF;
            }
        }

        if(ret == 0)
        {
            uint8_t bWriteableWhich;

            ret = InodeGetWriteableCopy(pInode->ulInode, &bWriteableWhich);

            if(ret == 0)
            {
                ret = RedBufferGet(InodeBlock(pInode->ulInode, bWriteableWhich),
                    (uint16_t)((uint32_t)BFLAG_META_INODE | BFLAG_DIRTY | BFLAG_NEW), CAST_VOID_PTR_PTR(&pInode->pInodeBuf));

                if(ret == 0)
                {
                    /*  Mark the inode block as allocated.
                    */
                    ret = InodeBitSet(pInode->ulInode, bWriteableWhich, true);

                    if(ret != 0)
                    {
                        RedBufferPut(pInode->pInodeBuf);
                    }
                }
            }
        }

        if(ret == 0)
        {
          #if REDCONF_INODE_TIMESTAMPS == 1
            uint32_t ulNow = RedOsClockGetTime();

            pInode->pInodeBuf->ulATime = ulNow;
            pInode->pInodeBuf->ulMTime = ulNow;
            pInode->pInodeBuf->ulCTime = ulNow;
          #endif

            pInode->pInodeBuf->uMode = uMode;

          #if REDCONF_API_POSIX == 1
          #if REDCONF_API_POSIX_LINK == 1
            pInode->pInodeBuf->uNLink = 1U;
          #endif
            pInode->pInodeBuf->ulPInode = ulPInode;
          #else
            (void)ulPInode;
          #endif

            pInode->fBranched = true;
            pInode->fDirty = true;

          #if REDCONF_API_POSIX == 1
            gpRedMR->ulFreeInodes--;
          #endif
        }
    }

    return ret;
}
#endif /* (REDCONF_READ_ONLY == 0) && ((REDCONF_API_POSIX == 1) || FORMAT_SUPPORTED) */


#if DELETE_SUPPORTED
/** @brief Delete an inode.

    @param pInode   Pointer to the cached inode structure.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  The inode is free.
    @retval -RED_EINVAL @p pInode is `NULL`; or pInode->pBuffer is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedInodeDelete(
    CINODE     *pInode)
{
    REDSTATUS   ret = 0;

    if(!CINODE_IS_MOUNTED(pInode))
    {
        ret = -RED_EINVAL;
    }
    else
    {
        if(pInode->pInodeBuf->ullSize != 0U)
        {
            ret = RedInodeDataTruncate(pInode, UINT64_SUFFIX(0));
        }

        if(ret == 0)
        {
            ret = RedInodeFree(pInode);
        }
    }

    return ret;
}


/** @brief Decrement an inode link count and delete the inode if the link count
           falls to zero.

    @param pInode   A pointer to the cached inode structure.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p pInode is not a mounted cachde inode.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedInodeLinkDec(
    CINODE     *pInode)
{
    REDSTATUS   ret;

    if(!CINODE_IS_MOUNTED(pInode))
    {
        ret = -RED_EINVAL;
    }
  #if REDCONF_API_POSIX_LINK == 1
    else if(pInode->pInodeBuf->uNLink > 1U)
    {
        ret = RedInodeBranch(pInode);

        if(ret == 0)
        {
            pInode->pInodeBuf->uNLink--;
        }
    }
  #endif
    else
    {
        ret = RedInodeDelete(pInode);
    }

    return ret;
}
#endif /* DELETE_SUPPORTED */


#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1)
/** @brief Free an inode.

    @param pInode   Pointer to the cached inode structure.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  The inode is free.
    @retval -RED_EINVAL @p pInode is `NULL`; or pInode->pBuffer is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedInodeFree(
    CINODE     *pInode)
{
    REDSTATUS   ret;

    if(!CINODE_IS_MOUNTED(pInode))
    {
        ret = -RED_EINVAL;
    }
    else
    {
        bool fSlot0Allocated;

        RedBufferDiscard(pInode->pInodeBuf);
        pInode->pInodeBuf = NULL;

        /*  Determine which of the two slots for the inode is currently
            allocated, and free that slot.
        */
        ret = RedInodeBitGet(gpRedCoreVol->bCurMR, pInode->ulInode, 0U, &fSlot0Allocated);

        if(ret == 0)
        {
            bool fSlot1Allocated;

            ret = RedInodeBitGet(gpRedCoreVol->bCurMR, pInode->ulInode, 1U, &fSlot1Allocated);

            if(ret == 0)
            {
                if(fSlot0Allocated)
                {
                    if(fSlot1Allocated)
                    {
                        /*  Both inode slots should never be allocated at
                            the same time.
                        */
                        CRITICAL_ERROR();
                        ret = -RED_EFUBAR;
                    }
                    else
                    {
                        ret = InodeBitSet(pInode->ulInode, 0U, false);
                    }
                }
                else
                {
                    if(!fSlot1Allocated)
                    {
                        /*  The inode in unallocated, which should have been
                            caught when it was mounted.
                        */
                        CRITICAL_ERROR();
                        ret = -RED_EBADF;
                    }
                    else
                    {
                        ret = InodeBitSet(pInode->ulInode, 1U, false);
                    }
                }
            }
        }

        pInode->ulInode = INODE_INVALID;

        if(ret == 0)
        {
            if(gpRedMR->ulFreeInodes >= gpRedVolConf->ulInodeCount)
            {
                CRITICAL_ERROR();
                ret = -RED_EFUBAR;
            }
            else
            {
                gpRedMR->ulFreeInodes++;
            }
        }
    }

    return ret;
}
#endif /* (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1) */


/** @brief Put the cached inode structure.

    This puts all of the buffers in the ::CINODE structure.  Also updates inode
    timestamp fields if requested.

    @param pInode       The cached inode structure.
    @param bTimeFields  The inode timestamp fields to update.
*/
void RedInodePut(
    CINODE  *pInode,
    uint8_t  bTimeFields)
{
    if(pInode == NULL)
    {
        REDERROR();
    }
    else
    {
        RedInodePutCoord(pInode);

        if(pInode->pInodeBuf != NULL)
        {
          #if (REDCONF_READ_ONLY == 0) && (REDCONF_INODE_TIMESTAMPS == 1)
            if((bTimeFields & IPUT_UPDATE_MASK) != 0U)
            {
                if(!pInode->fBranched || !pInode->fDirty)
                {
                    REDERROR();
                }
                else
                {
                    uint32_t ulNow = RedOsClockGetTime();

                  #if REDCONF_ATIME == 1
                    if((bTimeFields & IPUT_UPDATE_ATIME) != 0U)
                    {
                        pInode->pInodeBuf->ulATime = ulNow;
                    }
                  #endif

                    if((bTimeFields & IPUT_UPDATE_MTIME) != 0U)
                    {
                        pInode->pInodeBuf->ulMTime = ulNow;
                    }

                    if((bTimeFields & IPUT_UPDATE_CTIME) != 0U)
                    {
                        pInode->pInodeBuf->ulCTime = ulNow;
                    }
                }
            }
          #else
            (void)bTimeFields;
          #endif

            RedBufferPut(pInode->pInodeBuf);
            pInode->pInodeBuf = NULL;
        }
    }
}


/** @brief Put all buffers in the cached inode structure except for the inode
           node buffer.

    @param pInode   A pointer to the cached inode structure.
*/
void RedInodePutCoord(
    CINODE *pInode)
{
    if(pInode == NULL)
    {
        REDERROR();
    }
    else
    {
        RedInodePutData(pInode);
      #if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
        RedInodePutIndir(pInode);
      #endif
      #if DINDIR_POINTERS > 0U
        RedInodePutDindir(pInode);
      #endif
    }
}


#if DINDIR_POINTERS > 0U
/** @brief Put the double indirect buffer.

    @param pInode   A pointer to the cached inode structure.
*/
void RedInodePutDindir(
    CINODE *pInode)
{
    if(pInode == NULL)
    {
        REDERROR();
    }
    else if(pInode->pDindir != NULL)
    {
        RedBufferPut(pInode->pDindir);
        pInode->pDindir = NULL;
    }
    else
    {
        /*  No double indirect buffer, nothing to put.
        */
    }
}
#endif


#if REDCONF_DIRECT_POINTERS < INODE_ENTRIES
/** @brief Put the indirect buffer.

    @param pInode   A pointer to the cached inode structure.
*/
void RedInodePutIndir(
    CINODE *pInode)
{
    if(pInode == NULL)
    {
        REDERROR();
    }
    else if(pInode->pIndir != NULL)
    {
        RedBufferPut(pInode->pIndir);
        pInode->pIndir = NULL;
    }
    else
    {
        /*  No indirect buffer, nothing to put.
        */
    }
}
#endif


/** @brief Put the inode data buffer.

    @param pInode   A pointer to the cached inode structure.
*/
void RedInodePutData(
    CINODE *pInode)
{
    if(pInode == NULL)
    {
        REDERROR();
    }
    else if(pInode->pbData != NULL)
    {
        RedBufferPut(pInode->pbData);
        pInode->pbData = NULL;
    }
    else
    {
        /*  No data buffer, nothing to put.
        */
    }
}


#if REDCONF_READ_ONLY == 0
/** @brief Determine if an inode is branched.

    @param ulInode      The inode number to examine.
    @param pfIsBranched On successful return, populated with whether the inode
                        is branched.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p pInode is `NULL`; or @p ulInode is not a valid inode
                        number.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS InodeIsBranched(
    uint32_t    ulInode,
    bool       *pfIsBranched)
{
    REDSTATUS   ret;

    if(!INODE_IS_VALID(ulInode) || (pfIsBranched == NULL))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        ALLOCSTATE state;

        ret = RedImapBlockState(InodeBlock(ulInode, 0U), &state);

        if(ret == 0)
        {
            if(state == ALLOCSTATE_NEW)
            {
                *pfIsBranched = true;
            }
            else
            {
                ret = RedImapBlockState(InodeBlock(ulInode, 1U), &state);

                if(ret == 0)
                {
                    if(state == ALLOCSTATE_NEW)
                    {
                        *pfIsBranched = true;
                    }
                    else
                    {
                        *pfIsBranched = false;
                    }
                }
            }
        }
    }

    return ret;
}


/** @brief Branch an inode.

    A branched inode is one in which the allocation state for one copy is free
    or almost free, and the other copy is in the new state.  The copy which is
    in the new state is the writeable copy, which is also buffered and dirty.

    @param pInode   Pointer to the cached inode structure which has already been
                    mounted.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL Invalid parameters.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedInodeBranch(
    CINODE *pInode)
{
    REDSTATUS ret;

    if(!CINODE_IS_MOUNTED(pInode))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else if(!pInode->fBranched)
    {
        uint8_t bWhich;

        ret = InodeGetWriteableCopy(pInode->ulInode, &bWhich);

        if(ret == 0)
        {
            RedBufferBranch(pInode->pInodeBuf, InodeBlock(pInode->ulInode, bWhich));
            pInode->fBranched = true;
            pInode->fDirty = true;
        }

        /*  Toggle the inode slots: the old slot block becomes almost free
            (still used by the committed state) and the new slot block becomes
            new.
        */
        if(ret == 0)
        {
            ret = InodeBitSet(pInode->ulInode, 1U - bWhich, false);
        }

        if(ret == 0)
        {
            ret = InodeBitSet(pInode->ulInode, bWhich, true);
        }

        CRITICAL_ASSERT(ret == 0);
    }
    else
    {
        RedBufferDirty(pInode->pInodeBuf);
        pInode->fDirty = true;
        ret = 0;
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


#if (REDCONF_READ_ONLY == 0) && (REDCONF_API_POSIX == 1)
/** @brief Find a free inode number.

    @param pulInode On successful return, populated with a free inode number.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p pulInode is `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_ENFILE No available inode numbers.
*/
static REDSTATUS InodeFindFree(
    uint32_t   *pulInode)
{
    REDSTATUS   ret;

    if(pulInode == NULL)
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else if(gpRedMR->ulFreeInodes == 0U)
    {
        ret = -RED_ENFILE;
    }
    else
    {
        uint32_t ulInode;

        ret = 0;

        for(ulInode = INODE_FIRST_FREE; ulInode < (INODE_FIRST_VALID + gpRedVolConf->ulInodeCount); ulInode++)
        {
            bool fFree;

            ret = RedInodeIsFree(ulInode, &fFree);

            if((ret != 0) || fFree)
            {
                break;
            }
        }

        if(ret == 0)
        {
            if(ulInode < (INODE_FIRST_VALID + gpRedVolConf->ulInodeCount))
            {
                *pulInode = ulInode;
            }
            else
            {
                /*  If gpRedMR->ulFreeInodes > 0, we should have found an inode.
                */
                CRITICAL_ERROR();
                ret = -RED_ENFILE;
            }
        }
    }

    return ret;
}
#endif


#if ((REDCONF_READ_ONLY == 0) && ((REDCONF_API_POSIX == 1) || FORMAT_SUPPORTED)) || (REDCONF_CHECKER == 1)
/** @brief Determine whether an inode number is available.

    @param ulInode  The node number to examine.
    @param pfFree   On successful return, populated with whether the inode
                    number is available (true) or in use (false).

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p pfFree is `NULL`; or @p ulInode is not a valid inode
                        number.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedInodeIsFree(
    uint32_t    ulInode,
    bool       *pfFree)
{
    REDSTATUS   ret;

    if(pfFree == NULL)
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        bool fSlot0Allocated;

        *pfFree = false;

        ret = RedInodeBitGet(gpRedCoreVol->bCurMR, ulInode, 0U, &fSlot0Allocated);
        if((ret == 0) && !fSlot0Allocated)
        {
            bool fSlot1Allocated;

            ret = RedInodeBitGet(gpRedCoreVol->bCurMR, ulInode, 1U, &fSlot1Allocated);
            if((ret == 0) && !fSlot1Allocated)
            {
                *pfFree = true;
            }
        }
    }

    return ret;
}
#endif


#if REDCONF_READ_ONLY == 0
/** @brief Determine which copy of the inode is currently writeable.

    @param ulInode  The inode number to examine.
    @param pbWhich  On successful return, populated with which copy of the inode
                    (either 0 or 1) is writeable.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p pbWhich is `NULL`; or ulInode is not a valid inode
                        number.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS InodeGetWriteableCopy(
    uint32_t    ulInode,
    uint8_t    *pbWhich)
{
    REDSTATUS   ret;

    if(pbWhich == NULL)
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        bool fSlot0Allocated;

        /*  The writeable inode slot is the one which is free in the committed
            state, so query the committed state metaroot.
        */
        ret = RedInodeBitGet(1U - gpRedCoreVol->bCurMR, ulInode, 0U, &fSlot0Allocated);

        if(ret == 0)
        {
            if(!fSlot0Allocated)
            {
                *pbWhich = 0U;
            }
            else
            {
                bool fSlot1Allocated;

                ret = RedInodeBitGet(1U - gpRedCoreVol->bCurMR, ulInode, 1U, &fSlot1Allocated);

                if(ret == 0)
                {
                    if(!fSlot1Allocated)
                    {
                        *pbWhich = 1U;
                    }
                    else
                    {
                        /*  Both inode slots were allocated, which should never
                            happen.
                        */
                        CRITICAL_ERROR();
                        ret = -RED_EFUBAR;
                    }
                }
            }
        }
    }

    return ret;
}
#endif


/** @brief Determine which copy of the inode is current.

    @param ulInode  The inode number to examine.
    @param pbWhich  On successful return, populated with which copy of the inode
                    (either 0 or 1) is current.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EBADF  @p ulInode is an unallocated inode number.
    @retval -RED_EINVAL @p pbWhich is `NULL`; or ulInode is not a valid inode
                        number.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS InodeGetCurrentCopy(
    uint32_t    ulInode,
    uint8_t    *pbWhich)
{
    REDSTATUS   ret;

    if(pbWhich == NULL)
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        bool fSlot0Allocated;

        /*  The current inode slot is the one which is allocated in the working
            state metaroot.
        */
        ret = RedInodeBitGet(gpRedCoreVol->bCurMR, ulInode, 0U, &fSlot0Allocated);
        if(ret == 0)
        {
            if(fSlot0Allocated)
            {
                *pbWhich = 0U;
            }
            else
            {
                bool fSlot1Allocated;

                ret = RedInodeBitGet(gpRedCoreVol->bCurMR, ulInode, 1U, &fSlot1Allocated);
                if(ret == 0)
                {
                    if(fSlot1Allocated)
                    {
                        *pbWhich = 1U;
                    }
                    else
                    {
                        /*  Neither slot for this inode was allocated, so the
                            inode is actually free.
                        */
                        ret = -RED_EBADF;
                    }
                }
            }
        }
    }

    return ret;
}


/** @brief Get whether a copy of an inode is allocated.

    @param bMR          The metaroot index: either 0 or 1.
    @param ulInode      The inode number.
    @param bWhich       Which copy of the inode to get.
    @param pfAllocated  On successful return, populated with whether the given
                        copy of the inode is allocated.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p bMR is not 1 or 0; @p ulInode is not a valid inode
                        number; or @p bWhich is not 1 or 0; or @p pfAllocated is
                        `NULL`.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedInodeBitGet(
    uint8_t     bMR,
    uint32_t    ulInode,
    uint8_t     bWhich,
    bool       *pfAllocated)
{
    REDSTATUS   ret;

    if(!INODE_IS_VALID(ulInode) || (bWhich > 1U))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        ret = RedImapBlockGet(bMR, InodeBlock(ulInode, bWhich), pfAllocated);
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Set whether a copy of an inode is allocated.

    @param ulInode      The inode number.
    @param bWhich       Which copy of the inode to set.
    @param fAllocated   If true, the inode is set to allocated; if false, the
                        inode is set to free.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p ulInode is not a valid inode number; or @p bWhich is
                        not 1 or 0.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS InodeBitSet(
    uint32_t    ulInode,
    uint8_t     bWhich,
    bool        fAllocated)
{
    REDSTATUS   ret;

    if(!INODE_IS_VALID(ulInode) || (bWhich > 1U))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        ret = RedImapBlockSet(InodeBlock(ulInode, bWhich), fAllocated);
    }

    return ret;
}
#endif


/** @brief Determine the block number of an inode.

    @param ulInode  The inode number.
    @param bWhich   Which copy of the inode.

    @return The block number of the inode.
*/
static uint32_t InodeBlock(
    uint32_t    ulInode,
    uint8_t     bWhich)
{
    REDASSERT(INODE_IS_VALID(ulInode));
    REDASSERT(bWhich <= 1U);

    return gpRedCoreVol->ulInodeTableStartBN + ((ulInode - INODE_FIRST_VALID) * 2U) + bWhich;
}

