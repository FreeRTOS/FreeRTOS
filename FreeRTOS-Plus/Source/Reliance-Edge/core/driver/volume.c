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
 *  @brief Implements core volume operations.
 */
#include <redfs.h>
#include <redcore.h>


static bool MetarootIsValid( METAROOT * pMR,
                             bool * pfSectorCRCIsValid );
#ifdef REDCONF_ENDIAN_SWAP
    static void MetaRootEndianSwap( METAROOT * pMetaRoot );
#endif


/** @brief Mount a file system volume.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EIO    Volume not formatted, improperly formatted, or corrupt.
 */
REDSTATUS RedVolMount( void )
{
    REDSTATUS ret;

    #if REDCONF_READ_ONLY == 0
        ret = RedOsBDevOpen( gbRedVolNum, BDEV_O_RDWR );
    #else
        ret = RedOsBDevOpen( gbRedVolNum, BDEV_O_RDONLY );
    #endif

    if( ret == 0 )
    {
        ret = RedVolMountMaster();

        if( ret == 0 )
        {
            ret = RedVolMountMetaroot();
        }

        if( ret != 0 )
        {
            /*  If we fail to mount, invalidate the buffers to prevent any
             *  confusion that could be caused by stale or corrupt metadata.
             */
            ( void ) RedBufferDiscardRange( 0U, gpRedVolume->ulBlockCount );
            ( void ) RedOsBDevClose( gbRedVolNum );
        }
    }

    return ret;
}


/** @brief Mount the master block.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EIO    Master block missing, corrupt, or inconsistent with the
 *                      compile-time driver settings.
 */
REDSTATUS RedVolMountMaster( void )
{
    REDSTATUS ret;
    MASTERBLOCK * pMB;

    /*  Read the master block, to ensure that the disk was formatted with
     *  Reliance Edge.
     */
    ret = RedBufferGet( BLOCK_NUM_MASTER, BFLAG_META_MASTER, CAST_VOID_PTR_PTR( &pMB ) );

    if( ret == 0 )
    {
        /*  Verify that the driver was compiled with the same settings that
         *  the disk was formatted with.  If not, the user has made a
         *  mistake: either the driver settings are wrong, or the disk needs
         *  to be reformatted.
         */
        if( ( pMB->ulVersion != RED_DISK_LAYOUT_VERSION ) ||
            ( pMB->ulInodeCount != gpRedVolConf->ulInodeCount ) ||
            ( pMB->ulBlockCount != gpRedVolume->ulBlockCount ) ||
            ( pMB->uMaxNameLen != REDCONF_NAME_MAX ) ||
            ( pMB->uDirectPointers != REDCONF_DIRECT_POINTERS ) ||
            ( pMB->uIndirectPointers != REDCONF_INDIRECT_POINTERS ) ||
            ( pMB->bBlockSizeP2 != BLOCK_SIZE_P2 ) ||
            ( ( ( pMB->bFlags & MBFLAG_API_POSIX ) != 0U ) != ( REDCONF_API_POSIX == 1 ) ) ||
            ( ( ( pMB->bFlags & MBFLAG_INODE_TIMESTAMPS ) != 0U ) != ( REDCONF_INODE_TIMESTAMPS == 1 ) ) ||
            ( ( ( pMB->bFlags & MBFLAG_INODE_BLOCKS ) != 0U ) != ( REDCONF_INODE_BLOCKS == 1 ) ) )
        {
            ret = -RED_EIO;
        }

        #if REDCONF_API_POSIX == 1
            else if( ( ( pMB->bFlags & MBFLAG_INODE_NLINK ) != 0U ) != ( REDCONF_API_POSIX_LINK == 1 ) )
            {
                ret = -RED_EIO;
            }
        #else
            else if( ( pMB->bFlags & MBFLAG_INODE_NLINK ) != 0U )
            {
                ret = -RED_EIO;
            }
        #endif
        else
        {
            /*  Master block configuration is valid.
             *
             *  Save the sequence number of the master block in the volume,
             *  since we need it later (see RedVolMountMetaroot()) and we do
             *  not want to re-buffer the master block.
             */
            gpRedVolume->ullSequence = pMB->hdr.ullSequence;
        }

        RedBufferPut( pMB );
    }

    return ret;
}


/** @brief Mount the latest metaroot.
 *
 *  This function also populates the volume contexts.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EIO    Both metaroots are missing or corrupt.
 */
REDSTATUS RedVolMountMetaroot( void )
{
    REDSTATUS ret;

    ret = RedIoRead( gbRedVolNum, BLOCK_NUM_FIRST_METAROOT, 1U, &gpRedCoreVol->aMR[ 0U ] );

    if( ret == 0 )
    {
        ret = RedIoRead( gbRedVolNum, BLOCK_NUM_FIRST_METAROOT + 1U, 1U, &gpRedCoreVol->aMR[ 1U ] );
    }

    /*  Determine which metaroot is the most recent copy that was written
     *  completely.
     */
    if( ret == 0 )
    {
        uint8_t bMR = UINT8_MAX;
        bool fSectorCRCIsValid;

        if( MetarootIsValid( &gpRedCoreVol->aMR[ 0U ], &fSectorCRCIsValid ) )
        {
            bMR = 0U;

            #ifdef REDCONF_ENDIAN_SWAP
                MetaRootEndianSwap( &gpRedCoreVol->aMR[ 0U ] );
            #endif
        }
        else if( gpRedVolConf->fAtomicSectorWrite && !fSectorCRCIsValid )
        {
            ret = -RED_EIO;
        }
        else
        {
            /*  Metaroot is not valid, so it is ignored and there's nothing
             *  to do here.
             */
        }

        if( ret == 0 )
        {
            if( MetarootIsValid( &gpRedCoreVol->aMR[ 1U ], &fSectorCRCIsValid ) )
            {
                #ifdef REDCONF_ENDIAN_SWAP
                    MetaRootEndianSwap( &gpRedCoreVol->aMR[ 1U ] );
                #endif

                if( ( bMR != 0U ) || ( gpRedCoreVol->aMR[ 1U ].hdr.ullSequence > gpRedCoreVol->aMR[ 0U ].hdr.ullSequence ) )
                {
                    bMR = 1U;
                }
            }
            else if( gpRedVolConf->fAtomicSectorWrite && !fSectorCRCIsValid )
            {
                ret = -RED_EIO;
            }
            else
            {
                /*  Metaroot is not valid, so it is ignored and there's nothing
                 *  to do here.
                 */
            }
        }

        if( ret == 0 )
        {
            if( bMR == UINT8_MAX )
            {
                /*  Neither metaroot was valid.
                 */
                ret = -RED_EIO;
            }
            else
            {
                gpRedCoreVol->bCurMR = bMR;
                gpRedMR = &gpRedCoreVol->aMR[ bMR ];
            }
        }
    }

    if( ret == 0 )
    {
        /*  Normally the metaroot contains the highest sequence number, but the
         *  master block is the last block written during format, so on a
         *  freshly formatted volume the master block sequence number (stored in
         *  gpRedVolume->ullSequence) will be higher than that in the metaroot.
         */
        if( gpRedMR->hdr.ullSequence > gpRedVolume->ullSequence )
        {
            gpRedVolume->ullSequence = gpRedMR->hdr.ullSequence;
        }

        /*  gpRedVolume->ullSequence stores the *next* sequence number; to avoid
         *  giving the next node written to disk the same sequence number as the
         *  metaroot, increment it here.
         */
        ret = RedVolSeqNumIncrement();
    }

    if( ret == 0 )
    {
        gpRedVolume->fMounted = true;
        #if REDCONF_READ_ONLY == 0
            gpRedVolume->fReadOnly = false;
        #endif

        #if RESERVED_BLOCKS > 0U
            gpRedCoreVol->fUseReservedBlocks = false;
        #endif
        gpRedCoreVol->ulAlmostFreeBlocks = 0U;

        gpRedCoreVol->aMR[ 1U - gpRedCoreVol->bCurMR ] = *gpRedMR;
        gpRedCoreVol->bCurMR = 1U - gpRedCoreVol->bCurMR;
        gpRedMR = &gpRedCoreVol->aMR[ gpRedCoreVol->bCurMR ];
    }

    return ret;
}


/** @brief Determine whether the metaroot is valid.
 *
 *  @param pMR                  The metaroot buffer.
 *  @param pfSectorCRCIsValid   Populated with whether the first sector of the
 *                              metaroot buffer is valid.
 *
 *  @return Whether the metaroot is valid.
 *
 *  @retval true    The metaroot buffer is valid.
 *  @retval false   The metaroot buffer is invalid.
 */
static bool MetarootIsValid( METAROOT * pMR,
                             bool * pfSectorCRCIsValid )
{
    bool fRet = false;

    if( pfSectorCRCIsValid == NULL )
    {
        REDERROR();
    }
    else if( pMR == NULL )
    {
        REDERROR();
        *pfSectorCRCIsValid = false;
    }

    #ifdef REDCONF_ENDIAN_SWAP
        else if( RedRev32( pMR->hdr.ulSignature ) != META_SIG_METAROOT )
    #else
        else if( pMR->hdr.ulSignature != META_SIG_METAROOT )
    #endif
    {
        *pfSectorCRCIsValid = false;
    }
    else
    {
        const uint8_t * pbMR = CAST_VOID_PTR_TO_CONST_UINT8_PTR( pMR );
        uint32_t ulSectorCRC = pMR->ulSectorCRC;
        uint32_t ulCRC;

        #ifdef REDCONF_ENDIAN_SWAP
            ulSectorCRC = RedRev32( ulSectorCRC );
        #endif

        /*  The sector CRC was zero when the CRC was computed during the
         *  transaction, so it must be zero here.
         */
        pMR->ulSectorCRC = 0U;

        ulCRC = RedCrc32Update( 0U, &pbMR[ 8U ], gpRedVolConf->ulSectorSize - 8U );

        fRet = ulCRC == ulSectorCRC;
        *pfSectorCRCIsValid = fRet;

        if( fRet )
        {
            if( gpRedVolConf->ulSectorSize < REDCONF_BLOCK_SIZE )
            {
                ulCRC = RedCrc32Update( ulCRC, &pbMR[ gpRedVolConf->ulSectorSize ], REDCONF_BLOCK_SIZE - gpRedVolConf->ulSectorSize );
            }

            #ifdef REDCONF_ENDIAN_SWAP
                ulCRC = RedRev32( ulCRC );
            #endif

            fRet = ulCRC == pMR->hdr.ulCRC;
        }
    }

    return fRet;
}


#if REDCONF_READ_ONLY == 0

/** @brief Commit a transaction point.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EIO    A disk I/O error occurred.
 */
    REDSTATUS RedVolTransact( void )
    {
        REDSTATUS ret = 0;

        REDASSERT( !gpRedVolume->fReadOnly ); /* Should be checked by caller. */

        if( gpRedCoreVol->fBranched )
        {
            gpRedMR->ulFreeBlocks += gpRedCoreVol->ulAlmostFreeBlocks;
            gpRedCoreVol->ulAlmostFreeBlocks = 0U;

            ret = RedBufferFlush( 0U, gpRedVolume->ulBlockCount );

            if( ret == 0 )
            {
                gpRedMR->hdr.ulSignature = META_SIG_METAROOT;
                gpRedMR->hdr.ullSequence = gpRedVolume->ullSequence;

                ret = RedVolSeqNumIncrement();
            }

            if( ret == 0 )
            {
                const uint8_t * pbMR = CAST_VOID_PTR_TO_CONST_UINT8_PTR( gpRedMR );
                uint32_t ulSectorCRC;

                #ifdef REDCONF_ENDIAN_SWAP
                    MetaRootEndianSwap( gpRedMR );
                #endif

                gpRedMR->ulSectorCRC = 0U;

                ulSectorCRC = RedCrc32Update( 0U, &pbMR[ 8U ], gpRedVolConf->ulSectorSize - 8U );

                if( gpRedVolConf->ulSectorSize < REDCONF_BLOCK_SIZE )
                {
                    gpRedMR->hdr.ulCRC = RedCrc32Update( ulSectorCRC, &pbMR[ gpRedVolConf->ulSectorSize ], REDCONF_BLOCK_SIZE - gpRedVolConf->ulSectorSize );
                }
                else
                {
                    gpRedMR->hdr.ulCRC = ulSectorCRC;
                }

                gpRedMR->ulSectorCRC = ulSectorCRC;

                #ifdef REDCONF_ENDIAN_SWAP
                    gpRedMR->hdr.ulCRC = RedRev32( gpRedMR->hdr.ulCRC );
                    gpRedMR->ulSectorCRC = RedRev32( gpRedMR->ulSectorCRC );
                #endif

                /*  Flush the block device before writing the metaroot, so that all
                 *  previously written blocks are guaranteed to be on the media before
                 *  the metaroot is written.  Otherwise, if the block device reorders
                 *  the writes, the metaroot could reach the media before metadata it
                 *  points at, creating a window for disk corruption if power is lost.
                 */
                ret = RedIoFlush( gbRedVolNum );
            }

            if( ret == 0 )
            {
                ret = RedIoWrite( gbRedVolNum, BLOCK_NUM_FIRST_METAROOT + gpRedCoreVol->bCurMR, 1U, gpRedMR );

                #ifdef REDCONF_ENDIAN_SWAP
                    MetaRootEndianSwap( gpRedMR );
                #endif
            }

            /*  Flush the block device to force the metaroot write to the media.  This
             *  guarantees the transaction point is really complete before we return.
             */
            if( ret == 0 )
            {
                ret = RedIoFlush( gbRedVolNum );
            }

            /*  Toggle to the other metaroot buffer.  The working state and committed
             *  state metaroot buffers exchange places.
             */
            if( ret == 0 )
            {
                uint8_t bNextMR = 1U - gpRedCoreVol->bCurMR;

                gpRedCoreVol->aMR[ bNextMR ] = *gpRedMR;
                gpRedCoreVol->bCurMR = bNextMR;

                gpRedMR = &gpRedCoreVol->aMR[ gpRedCoreVol->bCurMR ];

                gpRedCoreVol->fBranched = false;
            }

            CRITICAL_ASSERT( ret == 0 );
        }

        return ret;
    }
#endif /* if REDCONF_READ_ONLY == 0 */


#ifdef REDCONF_ENDIAN_SWAP
    static void MetaRootEndianSwap( METAROOT * pMetaRoot )
    {
        if( pMetaRoot == NULL )
        {
            REDERROR();
        }
        else
        {
            pMetaRoot->ulSectorCRC = RedRev32( pMetaRoot->ulSectorCRC );
            pMetaRoot->ulFreeBlocks = RedRev32( pMetaRoot->ulFreeBlocks );
            #if REDCONF_API_POSIX == 1
                pMetaRoot->ulFreeInodes = RedRev32( pMetaRoot->ulFreeInodes );
            #endif
            pMetaRoot->ulAllocNextBlock = RedRev32( pMetaRoot->ulAllocNextBlock );
        }
    }
#endif /* ifdef REDCONF_ENDIAN_SWAP */


/** @brief Process a critical file system error.
 *
 *  @param pszFileName  The file in which the error occurred.
 *  @param ulLineNum    The line number at which the error occurred.
 */
void RedVolCriticalError( const char * pszFileName,
                          uint32_t ulLineNum )
{
    #if REDCONF_OUTPUT == 1
        #if REDCONF_READ_ONLY == 0
            if( !gpRedVolume->fReadOnly )
            {
                RedOsOutputString( "Critical file system error in Reliance Edge, setting volume to READONLY\n" );
            }
            else
        #endif
        {
            RedOsOutputString( "Critical file system error in Reliance Edge (volume already READONLY)\n" );
        }
    #endif /* if REDCONF_OUTPUT == 1 */

    #if REDCONF_READ_ONLY == 0
        gpRedVolume->fReadOnly = true;
    #endif

    #if REDCONF_ASSERTS == 1
        RedOsAssertFail( pszFileName, ulLineNum );
    #else
        ( void ) pszFileName;
        ( void ) ulLineNum;
    #endif
}


/** @brief Increment the sequence number.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EINVAL Cannot increment sequence number: maximum value reached.
 *                      This should not ever happen.
 */
REDSTATUS RedVolSeqNumIncrement( void )
{
    REDSTATUS ret;

    if( gpRedVolume->ullSequence == UINT64_MAX )
    {
        /*  In practice this should never, ever happen; to get here, there would
         *  need to be UINT64_MAX disk writes, which would take eons: longer
         *  than the lifetime of any product or storage media.  If this assert
         *  fires and the current year is still written with four digits,
         *  suspect memory corruption.
         */
        CRITICAL_ERROR();
        ret = -RED_EFUBAR;
    }
    else
    {
        gpRedVolume->ullSequence++;
        ret = 0;
    }

    return ret;
}
