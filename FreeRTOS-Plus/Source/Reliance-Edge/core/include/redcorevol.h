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
#ifndef REDCOREVOL_H
#define REDCOREVOL_H


/** @brief Per-volume run-time data specific to the core.
 */
typedef struct
{
    /** Whether this volume uses the inline imap (true) or external imap
     *  (false).  Computed at initialization time based on the block count.
     */
    bool fImapInline;

    #if REDCONF_IMAP_EXTERNAL == 1

        /** First block number of the on-disk imap.  Valid only when fImapInline
         *  is false.
         */
        uint32_t ulImapStartBN;

        /** The number of double-allocated imap nodes that make up the imap.
         */
        uint32_t ulImapNodeCount;
    #endif

    /** Block number where the inode table starts.
     */
    uint32_t ulInodeTableStartBN;

    /** First block number that can be allocated.
     */
    uint32_t ulFirstAllocableBN;

    /** The two metaroot structures, committed and working state.
     */
    METAROOT aMR[ 2U ];

    /** The index of the current metaroot; must be 0 or 1.
     */
    uint8_t bCurMR;

    /** Whether the volume has been branched or not.
     */
    bool fBranched;

    /** The number of blocks which will become free after the next transaction.
     */
    uint32_t ulAlmostFreeBlocks;

    #if RESERVED_BLOCKS > 0U

        /** Whether to use the blocks reserved for operations that create free
         *  space.
         */
        bool fUseReservedBlocks;
    #endif
} COREVOLUME;

/*  Pointer to the core volume currently being accessed; populated during
 *  RedCoreVolSetCurrent().
 */
extern COREVOLUME * CONST_IF_ONE_VOLUME gpRedCoreVol;

/*  Pointer to the metaroot currently being accessed; populated during
 *  RedCoreVolSetCurrent() and RedCoreVolTransact().
 */
extern METAROOT * gpRedMR;


#endif /* ifndef REDCOREVOL_H */
