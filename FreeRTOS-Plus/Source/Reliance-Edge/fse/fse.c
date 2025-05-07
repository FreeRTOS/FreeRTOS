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
 *  @brief Implementation of the Reliance Edge FSE API.
 */
#include <redfs.h>

#if REDCONF_API_FSE == 1

/** @defgroup red_group_fse The File System Essentials Interface
 *  @{
 */

    #include <redvolume.h>
    #include <redcoreapi.h>
    #include <redfse.h>


    static REDSTATUS FseEnter( uint8_t bVolNum );
    static void FseLeave( void );


    static bool gfFseInited; /* Whether driver is initialized. */


/** @brief Initialize the Reliance Edge file system driver.
 *
 *  Prepares the Reliance Edge file system driver to be used.  Must be the first
 *  Reliance Edge function to be invoked: no volumes can be mounted until the
 *  driver has been initialized.
 *
 *  If this function is called when the Reliance Edge driver is already
 *  initialized, it does nothing and returns success.
 *
 *  This function is not thread safe: attempting to initialize from multiple
 *  threads could leave things in a bad state.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0   Operation was successful.
 */
    REDSTATUS RedFseInit( void )
    {
        REDSTATUS ret;

        if( gfFseInited )
        {
            ret = 0;
        }
        else
        {
            ret = RedCoreInit();

            if( ret == 0 )
            {
                gfFseInited = true;
            }
        }

        return ret;
    }


/** @brief Uninitialize the Reliance Edge file system driver.
 *
 *  Tears down the Reliance Edge file system driver.  Cannot be used until all
 *  Reliance Edge volumes are unmounted.  A subsequent call to RedFseInit()
 *  will initialize the driver again.
 *
 *  If this function is called when the Reliance Edge driver is already
 *  uninitialized, it does nothing and returns success.
 *
 *  This function is not thread safe: attempting to uninitialize from multiple
 *  threads could leave things in a bad state.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EBUSY  At least one volume is still mounted.
 */
    REDSTATUS RedFseUninit( void )
    {
        REDSTATUS ret = 0;

        if( !gfFseInited )
        {
            ret = 0;
        }
        else
        {
            uint8_t bVolNum;

            #if REDCONF_TASK_COUNT > 1U
                RedOsMutexAcquire();
            #endif

            for( bVolNum = 0U; bVolNum < REDCONF_VOLUME_COUNT; bVolNum++ )
            {
                if( gaRedVolume[ bVolNum ].fMounted )
                {
                    ret = -RED_EBUSY;
                    break;
                }
            }

            if( ret == 0 )
            {
                gfFseInited = false;
            }

            #if REDCONF_TASK_COUNT > 1U
                RedOsMutexRelease();
            #endif

            if( ret == 0 )
            {
                ret = RedCoreUninit();
            }
        }

        return ret;
    }


/** @brief Mount a file system volume.
 *
 *  Prepares the file system volume to be accessed.  Mount will fail if the
 *  volume has never been formatted, or if the on-disk format is inconsistent
 *  with the compile-time configuration.
 *
 *  If the volume is already mounted, this function does nothing and returns
 *  success.
 *
 *  @param bVolNum  The volume number of the volume to be mounted.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number; or the driver is
 *                      uninitialized.
 *  @retval -RED_EIO    Volume not formatted, improperly formatted, or corrupt.
 */
    REDSTATUS RedFseMount( uint8_t bVolNum )
    {
        REDSTATUS ret;

        ret = FseEnter( bVolNum );

        if( ret == 0 )
        {
            if( !gpRedVolume->fMounted )
            {
                ret = RedCoreVolMount();
            }

            FseLeave();
        }

        return ret;
    }


/** @brief Unmount a file system volume.
 *
 *  This function discards the in-memory state for the file system and marks it
 *  as unmounted.  Subsequent attempts to access the volume will fail until the
 *  volume is mounted again.
 *
 *  If unmount automatic transaction points are enabled, this function will
 *  commit a transaction point prior to unmounting.  If unmount automatic
 *  transaction points are disabled, this function will unmount without
 *  transacting, effectively discarding the working state.
 *
 *  Before unmounting, this function will wait for any active file system
 *  thread to complete by acquiring the FS mutex.  The volume will be marked as
 *  unmounted before the FS mutex is released, so subsequent FS threads will
 *  possibly block and then see an error when attempting to access a volume
 *  which is unmounting or unmounted.
 *
 *  If the volume is already unmounted, this function does nothing and returns
 *  success.
 *
 *  @param bVolNum  The volume number of the volume to be unmounted.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number; or the driver is
 *                      uninitialized.
 *  @retval -RED_EIO    I/O error during unmount automatic transaction point.
 */
    REDSTATUS RedFseUnmount( uint8_t bVolNum )
    {
        REDSTATUS ret;

        ret = FseEnter( bVolNum );

        if( ret == 0 )
        {
            if( gpRedVolume->fMounted )
            {
                ret = RedCoreVolUnmount();
            }

            FseLeave();
        }

        return ret;
    }


    #if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_FSE_FORMAT == 1 )

/** @brief Format a file system volume.
 *
 *  Uses the statically defined volume configuration.  After calling this
 *  function, the volume needs to be mounted -- see RedFseMount().
 *
 *  An error is returned if the volume is mounted.
 *
 *  @param bVolNum  The volume number of the volume to be formatted.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EBUSY  The volume is mounted.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number; or the driver is
 *                      uninitialized.
 *  @retval -RED_EIO    I/O error formatting the volume.
 */
        REDSTATUS RedFseFormat( uint8_t bVolNum )
        {
            REDSTATUS ret;

            ret = FseEnter( bVolNum );

            if( ret == 0 )
            {
                ret = RedCoreVolFormat();

                FseLeave();
            }

            return ret;
        }
    #endif /* if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_FSE_FORMAT == 1 ) */


/** @brief Read from a file.
 *
 *  Data which has not yet been written, but which is before the end-of-file
 *  (sparse data), shall read as zeroes.  A short read -- where the number of
 *  bytes read is less than requested -- indicates that the requested read was
 *  partially or, if zero bytes were read, entirely beyond the end-of-file.
 *
 *  If @p ullFileOffset is at or beyond the maximum file size, it is treated
 *  like any other read entirely beyond the end-of-file: no data is read and
 *  zero is returned.
 *
 *  @param bVolNum          The volume number of the file to read.
 *  @param ulFileNum        The file number of the file to read.
 *  @param ullFileOffset    The file offset to read from.
 *  @param ulLength         The number of bytes to read.
 *  @param pBuffer          The buffer to populate with the data read.  Must be
 *                          at least ulLength bytes in size.
 *
 *  @return The number of bytes read (nonnegative) or a negated ::REDSTATUS
 *          code indicating the operation result (negative).
 *
 *  @retval >=0         The number of bytes read from the file.
 *  @retval -RED_EBADF  @p ulFileNum is not a valid file number.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number or not mounted;
 *                      or @p pBuffer is `NULL`; or @p ulLength exceeds
 *                      INT32_MAX and cannot be returned properly.
 *  @retval -RED_EIO    A disk I/O error occurred.
 */
    int32_t RedFseRead( uint8_t bVolNum,
                        uint32_t ulFileNum,
                        uint64_t ullFileOffset,
                        uint32_t ulLength,
                        void * pBuffer )
    {
        int32_t ret;

        if( ulLength > ( uint32_t ) INT32_MAX )
        {
            ret = -RED_EINVAL;
        }
        else
        {
            ret = FseEnter( bVolNum );
        }

        if( ret == 0 )
        {
            uint32_t ulReadLen = ulLength;

            ret = RedCoreFileRead( ulFileNum, ullFileOffset, &ulReadLen, pBuffer );

            FseLeave();

            if( ret == 0 )
            {
                ret = ( int32_t ) ulReadLen;
            }
        }

        return ret;
    }


    #if REDCONF_READ_ONLY == 0

/** @brief Write to a file.
 *
 *  If the write extends beyond the end-of-file, the file size will be
 *  increased.
 *
 *  A short write -- where the number of bytes written is less than requested
 *  -- indicates either that the file system ran out of space but was still
 *  able to write some of the request; or that the request would have caused
 *  the file to exceed the maximum file size, but some of the data could be
 *  written prior to the file size limit.
 *
 *  If an error is returned (negative return), either none of the data was
 *  written or a critical error occurred (like an I/O error) and the file
 *  system volume will be read-only.
 *
 *  @param bVolNum          The volume number of the file to write.
 *  @param ulFileNum        The file number of the file to write.
 *  @param ullFileOffset    The file offset to write at.
 *  @param ulLength         The number of bytes to write.
 *  @param pBuffer          The buffer containing the data to be written.  Must
 *                          be at least ulLength bytes in size.
 *
 *  @return The number of bytes written (nonnegative) or a negated ::REDSTATUS
 *          code indicating the operation result (negative).
 *
 *  @retval >0          The number of bytes written to the file.
 *  @retval -RED_EBADF  @p ulFileNum is not a valid file number.
 *  @retval -RED_EFBIG  No data can be written to the given file offset since
 *                      the resulting file size would exceed the maximum file
 *                      size.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number or not mounted;
 *                      or @p pBuffer is `NULL`; or @p ulLength exceeds
 *                      INT32_MAX and cannot be returned properly.
 *  @retval -RED_EIO    A disk I/O error occurred.
 *  @retval -RED_ENOSPC No data can be written because there is insufficient
 *                      free space.
 *  @retval -RED_EROFS  The file system volume is read-only.
 */
        int32_t RedFseWrite( uint8_t bVolNum,
                             uint32_t ulFileNum,
                             uint64_t ullFileOffset,
                             uint32_t ulLength,
                             const void * pBuffer )
        {
            int32_t ret;

            if( ulLength > ( uint32_t ) INT32_MAX )
            {
                ret = -RED_EINVAL;
            }
            else
            {
                ret = FseEnter( bVolNum );
            }

            if( ret == 0 )
            {
                uint32_t ulWriteLen = ulLength;

                ret = RedCoreFileWrite( ulFileNum, ullFileOffset, &ulWriteLen, pBuffer );

                FseLeave();

                if( ret == 0 )
                {
                    ret = ( int32_t ) ulWriteLen;
                }
            }

            return ret;
        }
    #endif /* if REDCONF_READ_ONLY == 0 */


    #if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_FSE_TRUNCATE == 1 )

/** @brief Truncate a file (set the file size).
 *
 *  Allows the file size to be increased, decreased, or to remain the same.  If
 *  the file size is increased, the new area is sparse (will read as zeroes).
 *  If the file size is decreased, the data beyond the new end-of-file will
 *  return to free space once it is no longer part of the committed state
 *  (either immediately or after the next transaction point).
 *
 *  This function can fail when the disk is full if @p ullNewFileSize is
 *  non-zero.  If decreasing the file size, this can be fixed by transacting and
 *  trying again: Reliance Edge guarantees that it is possible to perform a
 *  truncate of at least one file that decreases the file size after a
 *  transaction point.  If disk full transactions are enabled, this will happen
 *  automatically.
 *
 *  @param bVolNum          The volume number of the file to truncate.
 *  @param ulFileNum        The file number of the file to truncate.
 *  @param ullNewFileSize   The new file size, in bytes.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EBADF  @p ulFileNum is not a valid file number.
 *  @retval -RED_EFBIG  @p ullNewFileSize exceeds the maximum file size.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number or not mounted.
 *  @retval -RED_EIO    A disk I/O error occurred.
 *  @retval -RED_ENOSPC Insufficient free space to perform the truncate.
 *  @retval -RED_EROFS  The file system volume is read-only.
 */
        REDSTATUS RedFseTruncate( uint8_t bVolNum,
                                  uint32_t ulFileNum,
                                  uint64_t ullNewFileSize )
        {
            REDSTATUS ret;

            ret = FseEnter( bVolNum );

            if( ret == 0 )
            {
                ret = RedCoreFileTruncate( ulFileNum, ullNewFileSize );

                FseLeave();
            }

            return ret;
        }
    #endif /* if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_FSE_TRUNCATE == 1 ) */


/** @brief Retrieve the size of a file.
 *
 *  @param bVolNum      The volume number of the file whose size is being read.
 *  @param ulFileNum    The file number of the file whose size is being read.
 *
 *  @return The size of the file (nonnegative) or a negated ::REDSTATUS code
 *          indicating the operation result (negative).
 *
 *  @retval >=0         The size of the file.
 *  @retval -RED_EBADF  @p ulFileNum is not a valid file number.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number or not mounted.
 *  @retval -RED_EIO    A disk I/O error occurred.
 */
    int64_t RedFseSizeGet( uint8_t bVolNum,
                           uint32_t ulFileNum )
    {
        int64_t ret;

        ret = FseEnter( bVolNum );

        if( ret == 0 )
        {
            uint64_t ullSize;

            ret = RedCoreFileSizeGet( ulFileNum, &ullSize );

            FseLeave();

            if( ret == 0 )
            {
                /*  Unless there is an on-disk format change, the maximum file size
                 *  is guaranteed to be less than INT64_MAX, and so it can be safely
                 *  returned in an int64_t.
                 */
                REDASSERT( ullSize < ( uint64_t ) INT64_MAX );

                ret = ( int64_t ) ullSize;
            }
        }

        return ret;
    }


    #if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_FSE_TRANSMASKSET == 1 )

/** @brief Update the transaction mask.
 *
 *  The following events are available:
 *
 *  - #RED_TRANSACT_UMOUNT
 *  - #RED_TRANSACT_WRITE
 *  - #RED_TRANSACT_TRUNCATE
 *  - #RED_TRANSACT_VOLFULL
 *
 *  The #RED_TRANSACT_MANUAL macro (by itself) may be used to disable all
 *  automatic transaction events.  The #RED_TRANSACT_MASK macro is a bitmask of
 *  all transaction flags, excluding those representing excluded functionality.
 *
 *  Attempting to enable events for excluded functionality will result in an
 *  error.
 *
 *  @param bVolNum      The volume number of the volume whose transaction mask
 *                      is being changed.
 *  @param ulEventMask  A bitwise-OR'd mask of automatic transaction events to
 *                      be set as the current transaction mode.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number or not mounted;
 *                      or @p ulEventMask contains invalid bits.
 *  @retval -RED_EROFS  The file system volume is read-only.
 */
        REDSTATUS RedFseTransMaskSet( uint8_t bVolNum,
                                      uint32_t ulEventMask )
        {
            REDSTATUS ret;

            ret = FseEnter( bVolNum );

            if( ret == 0 )
            {
                ret = RedCoreTransMaskSet( ulEventMask );

                FseLeave();
            }

            return ret;
        }
    #endif /* if ( REDCONF_READ_ONLY == 0 ) && ( REDCONF_API_FSE_TRANSMASKSET == 1 ) */


    #if REDCONF_API_FSE_TRANSMASKGET == 1

/** @brief Read the transaction mask.
 *
 *  If the volume is read-only, the returned event mask is always zero.
 *
 *  @param bVolNum      The volume number of the volume whose transaction mask
 *                      is being retrieved.
 *  @param pulEventMask Populated with a bitwise-OR'd mask of automatic
 *                      transaction events which represent the current
 *                      transaction mode for the volume.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number or not mounted;
 *                      or @p pulEventMask is `NULL`.
 */
        REDSTATUS RedFseTransMaskGet( uint8_t bVolNum,
                                      uint32_t * pulEventMask )
        {
            REDSTATUS ret;

            ret = FseEnter( bVolNum );

            if( ret == 0 )
            {
                ret = RedCoreTransMaskGet( pulEventMask );

                FseLeave();
            }

            return ret;
        }
    #endif /* if REDCONF_API_FSE_TRANSMASKGET == 1 */


    #if REDCONF_READ_ONLY == 0

/** @brief Commit a transaction point.
 *
 *  Reliance Edge is a transactional file system.  All modifications, of both
 *  metadata and filedata, are initially working state.  A transaction point
 *  is a process whereby the working state atomically becomes the committed
 *  state, replacing the previous committed state.  Whenever Reliance Edge is
 *  mounted, including after power loss, the state of the file system after
 *  mount is the most recent committed state.  Nothing from the committed
 *  state is ever missing, and nothing from the working state is ever included.
 *
 *  @param bVolNum  The volume number of the volume to transact.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EINVAL @p bVolNum is an invalid volume number or not mounted.
 *  @retval -RED_EIO    A disk I/O error occurred.
 *  @retval -RED_EROFS  The file system volume is read-only.
 */
        REDSTATUS RedFseTransact( uint8_t bVolNum )
        {
            REDSTATUS ret;

            ret = FseEnter( bVolNum );

            if( ret == 0 )
            {
                ret = RedCoreVolTransact();

                FseLeave();
            }

            return ret;
        }
    #endif /* if REDCONF_READ_ONLY == 0 */

/** @} */

/** @brief Enter the file system driver.
 *
 *  @param bVolNum  The volume to be accessed.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0           Operation was successful.
 *  @retval -RED_EINVAL The file system driver is uninitialized; or @p bVolNum
 *                      is not a valid volume number.
 */
    static REDSTATUS FseEnter( uint8_t bVolNum )
    {
        REDSTATUS ret;

        if( gfFseInited )
        {
            #if REDCONF_TASK_COUNT > 1U
                RedOsMutexAcquire();
            #endif

            /*  This also serves to range-check the volume number (even in single
             *  volume configurations).
             */
            ret = RedCoreVolSetCurrent( bVolNum );

            #if REDCONF_TASK_COUNT > 1U
                if( ret != 0 )
                {
                    RedOsMutexRelease();
                }
            #endif
        }
        else
        {
            ret = -RED_EINVAL;
        }

        return ret;
    }


/** @brief Leave the file system driver.
 */
    static void FseLeave( void )
    {
        REDASSERT( gfFseInited );

        #if REDCONF_TASK_COUNT > 1U
            RedOsMutexRelease();
        #endif
    }


#endif /* REDCONF_API_FSE == 1 */
