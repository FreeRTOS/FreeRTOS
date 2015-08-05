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
    @brief Implements routines for the inline imap.

    The inline imap is used on volumes that are small enough for the imap bitmap
    to be entirely contained within the metaroot.
*/
#include <redfs.h>

#if REDCONF_IMAP_INLINE == 1

#include <redcore.h>


/** @brief Get the allocation bit of a block from either metaroot.

    @param bMR          The metaroot index: either 0 or 1.
    @param ulBlock      The block number to query.
    @param pfAllocated  On successful return, populated with the allocation bit
                        of the block.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p bMR is out of range; or @p ulBlock is out of range;
                        @p pfAllocated is `NULL`; or the current volume does not
                        use the inline imap.
*/
REDSTATUS RedImapIBlockGet(
    uint8_t     bMR,
    uint32_t    ulBlock,
    bool       *pfAllocated)
{
    REDSTATUS   ret;

    if(    (!gpRedCoreVol->fImapInline)
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
        *pfAllocated = RedBitGet(gpRedCoreVol->aMR[bMR].abEntries, ulBlock - gpRedCoreVol->ulInodeTableStartBN);
        ret = 0;
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Set the allocation bit of a block in the working metaroot.

    @param ulBlock      The block number to allocate or free.
    @param fAllocated   Whether to allocate the block (true) or free it (false).

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p ulBlock is out of range; or the current volume does
                        not use the inline imap.
*/
REDSTATUS RedImapIBlockSet(
    uint32_t    ulBlock,
    bool        fAllocated)
{
    REDSTATUS   ret;

    if(    (!gpRedCoreVol->fImapInline)
        || (ulBlock < gpRedCoreVol->ulInodeTableStartBN)
        || (ulBlock >= gpRedVolume->ulBlockCount))
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint32_t ulOffset = ulBlock - gpRedCoreVol->ulInodeTableStartBN;

        if(RedBitGet(gpRedMR->abEntries, ulOffset) == fAllocated)
        {
            /*  The driver shouldn't ever set a bit in the imap to its current
                value.  This is more of a problem with the external imap, but it
                is checked here for consistency.
            */
            CRITICAL_ERROR();
            ret = -RED_EFUBAR;
        }
        else if(fAllocated)
        {
            RedBitSet(gpRedMR->abEntries, ulOffset);
            ret = 0;
        }
        else
        {
            RedBitClear(gpRedMR->abEntries, ulOffset);
            ret = 0;
        }
    }

    return ret;
}
#endif

#endif /* REDCONF_IMAP_INLINE == 1 */

