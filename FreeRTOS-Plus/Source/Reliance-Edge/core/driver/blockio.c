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
 *  @brief Implements block device I/O using logical blocks as the units.
 *
 *  The OS block device implementations operate on sectors.  The core does I/O
 *  in terms of logical blocks: this module translates from logical blocks to
 *  sectors.
 *
 *  If bBlockIoRetries is greater than 0 for the current volume, then this
 *  module will retry block device calls on failure up to the configured number
 *  of times.  This behavior caters to the type of unreliable hardware and
 *  drivers that are sometimes found in the IoT world, where one operation may
 *  fail but the next may still succeed.
 */
#include <redfs.h>
#include <redcore.h>


/** @brief Read a range of logical blocks.
 *
 *  @param bVolNum      The volume whose block device is being read from.
 *  @param ulBlockStart The first block to read.
 *  @param ulBlockCount The number of blocks to read.
 *  @param pBuffer      The buffer to populate with the data read.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EIO    A disk I/O error occurred.
 *  @retval -RED_EINVAL Invalid parameters.
 */
REDSTATUS RedIoRead( uint8_t bVolNum,
                     uint32_t ulBlockStart,
                     uint32_t ulBlockCount,
                     void * pBuffer )
{
    REDSTATUS ret = 0;

    if( ( bVolNum >= REDCONF_VOLUME_COUNT ) ||
        ( ulBlockStart >= gaRedVolume[ bVolNum ].ulBlockCount ) ||
        ( ( gaRedVolume[ bVolNum ].ulBlockCount - ulBlockStart ) < ulBlockCount ) ||
        ( ulBlockCount == 0U ) ||
        ( pBuffer == NULL ) )
    {
        REDERROR();
        ret = -RED_EINVAL;
    }
    else
    {
        uint8_t bSectorShift = gaRedVolume[ bVolNum ].bBlockSectorShift;
        uint64_t ullSectorStart = ( uint64_t ) ulBlockStart << bSectorShift;
        uint32_t ulSectorCount = ulBlockCount << bSectorShift;
        uint8_t bRetryIdx;

        REDASSERT( bSectorShift < 32U );
        REDASSERT( ( ulSectorCount >> bSectorShift ) == ulBlockCount );

        for( bRetryIdx = 0U; bRetryIdx <= gpRedVolConf->bBlockIoRetries; bRetryIdx++ )
        {
            ret = RedOsBDevRead( bVolNum, ullSectorStart, ulSectorCount, pBuffer );

            if( ret == 0 )
            {
                break;
            }
        }
    }

    CRITICAL_ASSERT( ret == 0 );

    return ret;
}


#if REDCONF_READ_ONLY == 0

/** @brief Write a range of logical blocks.
 *
 *  @param bVolNum      The volume whose block device is being written to.
 *  @param ulBlockStart The first block to write.
 *  @param ulBlockCount The number of blocks to write.
 *  @param pBuffer      The buffer containing the data to write.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EIO    A disk I/O error occurred.
 *  @retval -RED_EINVAL Invalid parameters.
 */
    REDSTATUS RedIoWrite( uint8_t bVolNum,
                          uint32_t ulBlockStart,
                          uint32_t ulBlockCount,
                          const void * pBuffer )
    {
        REDSTATUS ret = 0;

        if( ( bVolNum >= REDCONF_VOLUME_COUNT ) ||
            ( ulBlockStart >= gaRedVolume[ bVolNum ].ulBlockCount ) ||
            ( ( gaRedVolume[ bVolNum ].ulBlockCount - ulBlockStart ) < ulBlockCount ) ||
            ( ulBlockCount == 0U ) ||
            ( pBuffer == NULL ) )
        {
            REDERROR();
            ret = -RED_EINVAL;
        }
        else
        {
            uint8_t bSectorShift = gaRedVolume[ bVolNum ].bBlockSectorShift;
            uint64_t ullSectorStart = ( uint64_t ) ulBlockStart << bSectorShift;
            uint32_t ulSectorCount = ulBlockCount << bSectorShift;
            uint8_t bRetryIdx;

            REDASSERT( bSectorShift < 32U );
            REDASSERT( ( ulSectorCount >> bSectorShift ) == ulBlockCount );

            for( bRetryIdx = 0U; bRetryIdx <= gpRedVolConf->bBlockIoRetries; bRetryIdx++ )
            {
                ret = RedOsBDevWrite( bVolNum, ullSectorStart, ulSectorCount, pBuffer );

                if( ret == 0 )
                {
                    break;
                }
            }
        }

        CRITICAL_ASSERT( ret == 0 );

        return ret;
    }


/** @brief Flush any caches beneath the file system.
 *
 *  @param bVolNum  The volume number of the volume whose block device is being
 *                  flushed.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number.
 *  @retval -RED_EIO    A disk I/O error occurred.
 */
    REDSTATUS RedIoFlush( uint8_t bVolNum )
    {
        REDSTATUS ret = 0;

        if( bVolNum >= REDCONF_VOLUME_COUNT )
        {
            REDERROR();
            ret = -RED_EINVAL;
        }
        else
        {
            uint8_t bRetryIdx;

            for( bRetryIdx = 0U; bRetryIdx <= gpRedVolConf->bBlockIoRetries; bRetryIdx++ )
            {
                ret = RedOsBDevFlush( bVolNum );

                if( ret == 0 )
                {
                    break;
                }
            }
        }

        CRITICAL_ASSERT( ret == 0 );

        return ret;
    }
#endif /* REDCONF_READ_ONLY == 0 */
