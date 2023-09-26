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
 *  @brief Implements the Reliance Edge file system formatter.
 */
#include <redfs.h>
#include <redcoreapi.h>
#include <redcore.h>

#if FORMAT_SUPPORTED


/** @brief Format a file system volume.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EBUSY  Volume is mounted.
 *  @retval -RED_EIO    A disk I/O error occurred.
 */
    REDSTATUS RedVolFormat( void )
    {
        REDSTATUS ret;

        if( gpRedVolume->fMounted )
        {
            ret = -RED_EBUSY;
        }
        else
        {
            ret = RedOsBDevOpen( gbRedVolNum, BDEV_O_RDWR );
        }

        if( ret == 0 )
        {
            MASTERBLOCK * pMB;
            REDSTATUS ret2;

            /*  Overwrite the master block with zeroes, so that if formatting is
             *  interrupted, the volume will not be mountable.
             */
            ret = RedBufferGet( BLOCK_NUM_MASTER, BFLAG_NEW | BFLAG_DIRTY, CAST_VOID_PTR_PTR( &pMB ) );

            if( ret == 0 )
            {
                ret = RedBufferFlush( BLOCK_NUM_MASTER, 1U );

                RedBufferDiscard( pMB );
            }

            if( ret == 0 )
            {
                ret = RedIoFlush( gbRedVolNum );
            }

            #if REDCONF_IMAP_EXTERNAL == 1
                if( ( ret == 0 ) && !gpRedCoreVol->fImapInline )
                {
                    uint32_t ulImapBlock;
                    uint32_t ulImapBlockLimit = gpRedCoreVol->ulImapStartBN + ( gpRedCoreVol->ulImapNodeCount * 2U );
                    uint16_t uImapFlags = ( uint16_t ) ( ( uint32_t ) BFLAG_META_IMAP | BFLAG_NEW | BFLAG_DIRTY );

                    /*  Technically it is only necessary to create one copy of each imap
                     *  node (the copy the metaroot points at), but creating them both
                     *  avoids headaches during disk image analysis from stale imaps
                     *  left over from previous formats.
                     */
                    for( ulImapBlock = gpRedCoreVol->ulImapStartBN; ulImapBlock < ulImapBlockLimit; ulImapBlock++ )
                    {
                        IMAPNODE * pImap;

                        ret = RedBufferGet( ulImapBlock, uImapFlags, CAST_VOID_PTR_PTR( &pImap ) );

                        if( ret != 0 )
                        {
                            break;
                        }

                        RedBufferPut( pImap );
                    }
                }
            #endif /* if REDCONF_IMAP_EXTERNAL == 1 */

            /*  Write the first metaroot.
             */
            if( ret == 0 )
            {
                RedMemSet( gpRedMR, 0U, sizeof( *gpRedMR ) );

                gpRedMR->ulFreeBlocks = gpRedVolume->ulBlocksAllocable;
                #if REDCONF_API_POSIX == 1
                    gpRedMR->ulFreeInodes = gpRedVolConf->ulInodeCount;
                #endif
                gpRedMR->ulAllocNextBlock = gpRedCoreVol->ulFirstAllocableBN;

                /*  The branched flag is typically set automatically when bits in
                 *  the imap change.  It is set here explicitly because the imap has
                 *  only been initialized, not changed.
                 */
                gpRedCoreVol->fBranched = true;

                ret = RedVolTransact();
            }

            #if REDCONF_API_POSIX == 1

                /*  Create the root directory.
                 */
                if( ret == 0 )
                {
                    CINODE rootdir;

                    rootdir.ulInode = INODE_ROOTDIR;
                    ret = RedInodeCreate( &rootdir, INODE_INVALID, RED_S_IFDIR );

                    if( ret == 0 )
                    {
                        RedInodePut( &rootdir, 0U );
                    }
                }
            #endif /* if REDCONF_API_POSIX == 1 */

            #if REDCONF_API_FSE == 1

                /*  The FSE API does not support creating or deletes files, so all the
                 *  inodes are created during setup.
                 */
                if( ret == 0 )
                {
                    uint32_t ulInodeIdx;

                    for( ulInodeIdx = 0U; ulInodeIdx < gpRedVolConf->ulInodeCount; ulInodeIdx++ )
                    {
                        CINODE ino;

                        ino.ulInode = INODE_FIRST_FREE + ulInodeIdx;
                        ret = RedInodeCreate( &ino, INODE_INVALID, RED_S_IFREG );

                        if( ret == 0 )
                        {
                            RedInodePut( &ino, 0U );
                        }
                    }
                }
            #endif /* if REDCONF_API_FSE == 1 */

            /*  Write the second metaroot.
             */
            if( ret == 0 )
            {
                ret = RedVolTransact();
            }

            /*  Populate and write out the master block.
             */
            if( ret == 0 )
            {
                ret = RedBufferGet( BLOCK_NUM_MASTER, ( uint16_t ) ( ( uint32_t ) BFLAG_META_MASTER | BFLAG_NEW | BFLAG_DIRTY ), CAST_VOID_PTR_PTR( &pMB ) );
            }

            if( ret == 0 )
            {
                pMB->ulVersion = RED_DISK_LAYOUT_VERSION;
                RedStrNCpy( pMB->acBuildNum, RED_BUILD_NUMBER, sizeof( pMB->acBuildNum ) );
                pMB->ulFormatTime = RedOsClockGetTime();
                pMB->ulInodeCount = gpRedVolConf->ulInodeCount;
                pMB->ulBlockCount = gpRedVolume->ulBlockCount;
                pMB->uMaxNameLen = REDCONF_NAME_MAX;
                pMB->uDirectPointers = REDCONF_DIRECT_POINTERS;
                pMB->uIndirectPointers = REDCONF_INDIRECT_POINTERS;
                pMB->bBlockSizeP2 = BLOCK_SIZE_P2;

                #if REDCONF_API_POSIX == 1
                    pMB->bFlags |= MBFLAG_API_POSIX;
                #endif
                #if REDCONF_INODE_TIMESTAMPS == 1
                    pMB->bFlags |= MBFLAG_INODE_TIMESTAMPS;
                #endif
                #if REDCONF_INODE_BLOCKS == 1
                    pMB->bFlags |= MBFLAG_INODE_BLOCKS;
                #endif
                #if ( REDCONF_API_POSIX == 1 ) && ( REDCONF_API_POSIX_LINK == 1 )
                    pMB->bFlags |= MBFLAG_INODE_NLINK;
                #endif

                ret = RedBufferFlush( BLOCK_NUM_MASTER, 1U );

                RedBufferPut( pMB );
            }

            if( ret == 0 )
            {
                ret = RedIoFlush( gbRedVolNum );
            }

            ret2 = RedOsBDevClose( gbRedVolNum );

            if( ret == 0 )
            {
                ret = ret2;
            }
        }

        /*  Discard the buffers so a subsequent format will not run into blocks it
         *  does not expect.
         */
        if( ret == 0 )
        {
            ret = RedBufferDiscardRange( 0U, gpRedVolume->ulBlockCount );
        }

        return ret;
    }


#endif /* FORMAT_SUPPORTED */
