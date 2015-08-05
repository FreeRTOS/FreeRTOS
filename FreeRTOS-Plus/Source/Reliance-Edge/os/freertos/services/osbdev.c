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
    @brief Implements block device I/O.
*/
#include <FreeRTOS.h>

#include <redfs.h>
#include <redvolume.h>
#include <redosdeviations.h>


/*------------------------------------------------------------------------------
    Porting Note:

    Several example implementations of this module for FreeRTOS are available.
    If you are lucky, you can use one of these implementations; otherwise, these
    can serve as examples of how to implement this service.
------------------------------------------------------------------------------*/

/** @brief The F_DRIVER example implementation.

    This implementation is designed to reuse an existing block device driver
    that was written for FreeRTOS+FAT SL.  If you have such a driver, with
    little work it can be "dropped in" and used for Reliance Edge.  The only
    customization required is that gpfnRedOsBDevInit needs to be defined and
    pointed at the F_DRIVERINIT function.  This can be done in this module or in
    another C file.

    The disadantage of using the FreeRTOS F_DRIVER functions is that they only
    support single-sector reads and writes.  Reliance Edge will issue
    multi-sector requests, and servicing these one sector at a time will
    significantly slow down the file system.
*/
#define BDEV_F_DRIVER       0U

/** @brief The FatFs example implementation.

    This implementation is designed to reuse an existing block device driver
    that was written for FatFs.  If you have such a driver, it can be linked
    in and used immediately.  The FatFs `diskio.h` header must be in the include
    directory path.
*/
#define BDEV_FATFS          1U

/** @brief The Atmel Studio Framework SD/MMC driver example implementation.

    This implementation uses a modified version of the open source SD/MMC driver
    included in the Atmel Studio Framework (ASF) and will work as-is for many
    varieties of Atmel hardware.  This example assumes relatively minor
    modifications to the ASF SD/MMC driver to make it support multi-sector read
    and write requests, which greatly improves performance.  The modified driver
    is distributed with Reliance Edge and is included in FreeRTOS Atmel projects
    (such as in projects/freertos/atmel/sam4e-ek/src/ASF).

    This example can easily be modified to work with an unmodified version of
    the ASF SD/MMC driver.  Simply replace sd_mmc_mem_2_ram_multi() and
    sd_mmc_ram_2_mem_multi() with sd_mmc_mem_2_ram() and sd_mmc_ram_2_mem()
    respectively, and add a for loop to loop over each sector in the request.
    However, as described in the manual, there are considerable performance
    advantages to issuing real multi-sector requests, so using the modified
    driver is recommended.
*/
#define BDEV_ATMEL_SDMMC    2U

/** @brief The RAM disk example implementation.

    This implementation uses a RAM disk.  It will allow you to compile and test
    Reliance Edge even if your storage driver is not yet ready.  On typical
    target hardware, the amount of spare RAM will be limited so generally only
    very small disks will be available.
*/
#define BDEV_RAM_DISK       3U

/** @brief Pick which example implementation is compiled.

    Must be one of:
    - #BDEV_F_DRIVER
    - #BDEV_FATFS
    - #BDEV_ATMEL_SDMMC
    - #BDEV_RAM_DISK
*/
#define BDEV_EXAMPLE_IMPLEMENTATION BDEV_RAM_DISK


static REDSTATUS DiskOpen(uint8_t bVolNum, BDEVOPENMODE mode);
static REDSTATUS DiskClose(uint8_t bVolNum);
static REDSTATUS DiskRead(uint8_t bVolNum, uint64_t ullSectorStart, uint32_t ulSectorCount, void *pBuffer);
#if REDCONF_READ_ONLY == 0
static REDSTATUS DiskWrite(uint8_t bVolNum, uint64_t ullSectorStart, uint32_t ulSectorCount, const void *pBuffer);
static REDSTATUS DiskFlush(uint8_t bVolNum);
#endif


/** @brief Initialize a block device.

    This function is called when the file system needs access to a block
    device.

    Upon successful return, the block device should be fully initialized and
    ready to service read/write/flush/close requests.

    The behavior of calling this function on a block device which is already
    open is undefined.

    @param bVolNum  The volume number of the volume whose block device is being
                    initialized.
    @param mode     The open mode, indicating the type of access required.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p bVolNum is an invalid volume number.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedOsBDevOpen(
    uint8_t         bVolNum,
    BDEVOPENMODE    mode)
{
    REDSTATUS       ret;

    if(bVolNum >= REDCONF_VOLUME_COUNT)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        ret = DiskOpen(bVolNum, mode);
    }

    return ret;
}


/** @brief Uninitialize a block device.

    This function is called when the file system no longer needs access to a
    block device.  If any resource were allocated by RedOsBDevOpen() to service
    block device requests, they should be freed at this time.

    Upon successful return, the block device must be in such a state that it
    can be opened again.

    The behavior of calling this function on a block device which is already
    closed is undefined.

    @param bVolNum  The volume number of the volume whose block device is being
                    uninitialized.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p bVolNum is an invalid volume number.
*/
REDSTATUS RedOsBDevClose(
    uint8_t     bVolNum)
{
    REDSTATUS   ret;

    if(bVolNum >= REDCONF_VOLUME_COUNT)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        ret = DiskClose(bVolNum);
    }

    return ret;
}


/** @brief Read sectors from a physical block device.

    The behavior of calling this function is undefined if the block device is
    closed or if it was opened with ::BDEV_O_WRONLY.

    @param bVolNum          The volume number of the volume whose block device
                            is being read from.
    @param ullSectorStart   The starting sector number.
    @param ulSectorCount    The number of sectors to read.
    @param pBuffer          The buffer into which to read the sector data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p bVolNum is an invalid volume number, @p pBuffer is
                        `NULL`, or @p ullStartSector and/or @p ulSectorCount
                        refer to an invalid range of sectors.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedOsBDevRead(
    uint8_t     bVolNum,
    uint64_t    ullSectorStart,
    uint32_t    ulSectorCount,
    void       *pBuffer)
{
    REDSTATUS   ret = 0;

    if(    (bVolNum >= REDCONF_VOLUME_COUNT)
        || (ullSectorStart >= gaRedVolConf[bVolNum].ullSectorCount)
        || ((gaRedVolConf[bVolNum].ullSectorCount - ullSectorStart) < ulSectorCount)
        || (pBuffer == NULL))
    {
        ret = -RED_EINVAL;
    }
    else
    {
        ret = DiskRead(bVolNum, ullSectorStart, ulSectorCount, pBuffer);
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Write sectors to a physical block device.

    The behavior of calling this function is undefined if the block device is
    closed or if it was opened with ::BDEV_O_RDONLY.

    @param bVolNum          The volume number of the volume whose block device
                            is being written to.
    @param ullSectorStart   The starting sector number.
    @param ulSectorCount    The number of sectors to write.
    @param pBuffer          The buffer from which to write the sector data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p bVolNum is an invalid volume number, @p pBuffer is
                        `NULL`, or @p ullStartSector and/or @p ulSectorCount
                        refer to an invalid range of sectors.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedOsBDevWrite(
    uint8_t     bVolNum,
    uint64_t    ullSectorStart,
    uint32_t    ulSectorCount,
    const void *pBuffer)
{
    REDSTATUS   ret = 0;

    if(    (bVolNum >= REDCONF_VOLUME_COUNT)
        || (ullSectorStart >= gaRedVolConf[bVolNum].ullSectorCount)
        || ((gaRedVolConf[bVolNum].ullSectorCount - ullSectorStart) < ulSectorCount)
        || (pBuffer == NULL))
    {
        ret = -RED_EINVAL;
    }
    else
    {
        ret = DiskWrite(bVolNum, ullSectorStart, ulSectorCount, pBuffer);
    }

    return ret;
}


/** @brief Flush any caches beneath the file system.

    This function must synchronously flush all software and hardware caches
    beneath the file system, ensuring that all sectors written previously are
    committed to permanent storage.

    If the environment has no caching beneath the file system, the
    implementation of this function can do nothing and return success.

    The behavior of calling this function is undefined if the block device is
    closed or if it was opened with ::BDEV_O_RDONLY.

    @param bVolNum  The volume number of the volume whose block device is being
                    flushed.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL @p bVolNum is an invalid volume number.
    @retval -RED_EIO    A disk I/O error occurred.
*/
REDSTATUS RedOsBDevFlush(
    uint8_t     bVolNum)
{
    REDSTATUS   ret;

    if(bVolNum >= REDCONF_VOLUME_COUNT)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        ret = DiskFlush(bVolNum);
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


#if BDEV_EXAMPLE_IMPLEMENTATION == BDEV_F_DRIVER

#include <api_mdriver.h>


/*  This must be declared and initialized elsewere (e.g., in project code) to
    point at the initialization function for the F_DRIVER block device.
*/
extern const F_DRIVERINIT gpfnRedOsBDevInit;

static F_DRIVER *gapFDriver[REDCONF_VOLUME_COUNT];


/** @brief Initialize a disk.

    @param bVolNum  The volume number of the volume whose block device is being
                    initialized.
    @param mode     The open mode, indicating the type of access required.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS DiskOpen(
    uint8_t         bVolNum,
    BDEVOPENMODE    mode)
{
    REDSTATUS       ret;

    (void)mode;

    if((gpfnRedOsBDevInit == NULL) || (gapFDriver[bVolNum] != NULL))
    {
        ret = -RED_EINVAL;
    }
    else
    {
        F_DRIVER *pDriver;

        pDriver = gpfnRedOsBDevInit(bVolNum);
        if(pDriver != NULL)
        {
            F_PHY   geom;
            int     iErr;

            /*  Validate that the geometry is consistent with the volume
                configuration.
            */
            iErr = pDriver->getphy(pDriver, &geom);
            if(iErr == 0)
            {
                if(    (geom.bytes_per_sector != gaRedVolConf[bVolNum].ulSectorSize)
                    || (geom.number_of_sectors < gaRedVolConf[bVolNum].ullSectorCount))
                {
                    ret = -RED_EINVAL;
                }
                else
                {
                    gapFDriver[bVolNum] = pDriver;
                    ret = 0;
                }
            }
            else
            {
                ret = -RED_EIO;
            }

            if(ret != 0)
            {
                pDriver->release(pDriver);
            }
        }
        else
        {
            ret = -RED_EIO;
        }
    }

    return ret;
}


/** @brief Uninitialize a disk.

    @param bVolNum  The volume number of the volume whose block device is being
                    uninitialized.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskClose(
    uint8_t     bVolNum)
{
    REDSTATUS   ret;

    if(gapFDriver[bVolNum] == NULL)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        gapFDriver[bVolNum]->release(gapFDriver[bVolNum]);
        gapFDriver[bVolNum] = NULL;

        ret = 0;
    }

    return ret;
}


/** @brief Read sectors from a disk.

    @param bVolNum          The volume number of the volume whose block device
                            is being read from.
    @param ullSectorStart   The starting sector number.
    @param ulSectorCount    The number of sectors to read.
    @param pBuffer          The buffer into which to read the sector data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS DiskRead(
    uint8_t     bVolNum,
    uint64_t    ullSectorStart,
    uint32_t    ulSectorCount,
    void       *pBuffer)
{
    REDSTATUS   ret = 0;
    F_DRIVER   *pDriver = gapFDriver[bVolNum];

    if(pDriver == NULL)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        uint8_t    *pbBuffer = CAST_VOID_PTR_TO_UINT8_PTR(pBuffer);
        uint32_t    ulSectorSize = gaRedVolConf[bVolNum].ulSectorSize;
        uint32_t    ulSectorIdx;
        int         iErr;

        for(ulSectorIdx = 0U; ulSectorIdx < ulSectorCount; ulSectorIdx++)
        {
            iErr = pDriver->readsector(pDriver, &pbBuffer[ulSectorIdx * ulSectorSize],
                                       CAST_ULONG(ullSectorStart + ulSectorCount));
            if(iErr != 0)
            {
                ret = -RED_EIO;
                break;
            }
        }
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Write sectors to a disk.

    @param bVolNum          The volume number of the volume whose block device
                            is being written to.
    @param ullSectorStart   The starting sector number.
    @param ulSectorCount    The number of sectors to write.
    @param pBuffer          The buffer from which to write the sector data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EINVAL The block device is not open.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS DiskWrite(
    uint8_t     bVolNum,
    uint64_t    ullSectorStart,
    uint32_t    ulSectorCount,
    const void *pBuffer)
{
    REDSTATUS   ret = 0;
    F_DRIVER   *pDriver = gapFDriver[bVolNum];

    if(pDriver == NULL)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        const uint8_t  *pbBuffer = CAST_VOID_PTR_TO_CONST_UINT8_PTR(pBuffer);
        uint32_t        ulSectorSize = gaRedVolConf[bVolNum].ulSectorSize;
        uint32_t        ulSectorIdx;
        int             iErr;

        for(ulSectorIdx = 0U; ulSectorIdx < ulSectorCount; ulSectorIdx++)
        {
            /*  We have to cast pbBuffer to non-const since the writesector
                prototype is flawed, using a non-const pointer for the buffer.
            */
            iErr = pDriver->writesector(pDriver, CAST_AWAY_CONST(uint8_t, &pbBuffer[ulSectorIdx * ulSectorSize]),
                                        CAST_ULONG(ullSectorStart + ulSectorCount));
            if(iErr != 0)
            {
                ret = -RED_EIO;
                break;
            }
        }
    }

    return ret;
}


/** @brief Flush any caches beneath the file system.

    @param bVolNum  The volume number of the volume whose block device is being
                    flushed.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskFlush(
    uint8_t     bVolNum)
{
    REDSTATUS   ret;

    if(gapFDriver[bVolNum] == NULL)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        /*  The F_DRIVER interface does not include a flush function, so to be
            reliable the F_DRIVER implementation must use synchronous writes.
        */
        ret = 0;
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


#elif BDEV_EXAMPLE_IMPLEMENTATION == BDEV_FATFS

#include <task.h>
#include <diskio.h>

/*  disk_read() and disk_write() use an unsigned 8-bit value to specify the
    sector count, so no transfer can be larger than 255 sectors.
*/
#define MAX_SECTOR_TRANSFER UINT8_MAX


/** @brief Initialize a disk.

    @param bVolNum  The volume number of the volume whose block device is being
                    initialized.
    @param mode     The open mode, indicating the type of access required.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS DiskOpen(
    uint8_t         bVolNum,
    BDEVOPENMODE    mode)
{
    DSTATUS         status;
    uint32_t        ulTries;
    REDSTATUS       ret = 0;

    /*  With some implementations of disk_initialize(), such as the one
        implemented by Atmel for the ASF, the first time the disk is opened, the
        SD card can take a while to get ready, in which time disk_initialize()
        returns an error.  Try numerous times, waiting half a second after each
        failure.  Empirically, this has been observed to succeed on the second
        try, so trying 10x more than that provides a margin of error.
    */
    for(ulTries = 0U; ulTries < 20U; ulTries++)
    {
        /*  Assuming that the volume number is also the correct drive number.
            If this is not the case in your environment, a static constant array
            can be declared to map volume numbers to the correct driver number.
        */
        status = disk_initialize(bVolNum);
        if(status == 0)
        {
            break;
        }

        vTaskDelay(500U / portTICK_PERIOD_MS);
    }

    if(status != 0)
    {
        ret = -RED_EIO;
    }

    /*  Retrieve the sector size and sector count to ensure they are compatible
        with our compile-time geometry.
    */
    if(ret == 0)
    {
        WORD    wSectorSize;
        DWORD   dwSectorCount;
        DRESULT result;

        result = disk_ioctl(bVolNum, GET_SECTOR_SIZE, &wSectorSize);
        if(result == RES_OK)
        {
            result = disk_ioctl(bVolNum, GET_SECTOR_COUNT, &dwSectorCount);
            if(result == RES_OK)
            {
                if(    (wSectorSize != gaRedVolConf[bVolNum].ulSectorSize)
                    || (dwSectorCount < gaRedVolConf[bVolNum].ullSectorCount))
                {
                    ret = -RED_EINVAL;
                }
            }
            else
            {
                ret = -RED_EIO;
            }
        }
        else
        {
            ret = -RED_EIO;
        }
    }

    return ret;
}


/** @brief Uninitialize a disk.

    @param bVolNum  The volume number of the volume whose block device is being
                    uninitialized.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskClose(
    uint8_t     bVolNum)
{
    (void)bVolNum;
    return 0;
}


/** @brief Read sectors from a disk.

    @param bVolNum          The volume number of the volume whose block device
                            is being read from.
    @param ullSectorStart   The starting sector number.
    @param ulSectorCount    The number of sectors to read.
    @param pBuffer          The buffer into which to read the sector data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS DiskRead(
    uint8_t     bVolNum,
    uint64_t    ullSectorStart,
    uint32_t    ulSectorCount,
    void       *pBuffer)
{
    REDSTATUS   ret = 0;
    uint32_t    ulSectorIdx = 0U;
    uint32_t    ulSectorSize = gaRedVolConf[bVolNum].ulSectorSize;
    uint8_t    *pbBuffer = CAST_VOID_PTR_TO_UINT8_PTR(pBuffer);

    while(ulSectorIdx < ulSectorCount)
    {
        uint32_t    ulTransfer = REDMIN(ulSectorCount - ulSectorIdx, MAX_SECTOR_TRANSFER);
        DRESULT     result;

        result = disk_read(bVolNum, &pbBuffer[ulSectorIdx * ulSectorSize], (DWORD)(ullSectorStart + ulSectorIdx), (BYTE)ulTransfer);
        if(result != RES_OK)
        {
            ret = -RED_EIO;
            break;
        }

        ulSectorIdx += ulTransfer;
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Write sectors to a disk.

    @param bVolNum          The volume number of the volume whose block device
                            is being written to.
    @param ullSectorStart   The starting sector number.
    @param ulSectorCount    The number of sectors to write.
    @param pBuffer          The buffer from which to write the sector data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS DiskWrite(
    uint8_t         bVolNum,
    uint64_t        ullSectorStart,
    uint32_t        ulSectorCount,
    const void     *pBuffer)
{
    REDSTATUS       ret = 0;
    uint32_t        ulSectorIdx = 0U;
    uint32_t        ulSectorSize = gaRedVolConf[bVolNum].ulSectorSize;
    const uint8_t  *pbBuffer = CAST_VOID_PTR_TO_CONST_UINT8_PTR(pBuffer);

    while(ulSectorIdx < ulSectorCount)
    {
        uint32_t    ulTransfer = REDMIN(ulSectorCount - ulSectorIdx, MAX_SECTOR_TRANSFER);
        DRESULT     result;

        result = disk_write(bVolNum, &pbBuffer[ulSectorIdx * ulSectorSize], (DWORD)(ullSectorStart + ulSectorIdx), (BYTE)ulTransfer);
        if(result != RES_OK)
        {
            ret = -RED_EIO;
            break;
        }

        ulSectorIdx += ulTransfer;
    }

    return ret;
}


/** @brief Flush any caches beneath the file system.

    @param bVolNum  The volume number of the volume whose block device is being
                    flushed.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskFlush(
    uint8_t     bVolNum)
{
    REDSTATUS   ret;
    DRESULT     result;

    result = disk_ioctl(bVolNum, CTRL_SYNC, NULL);
    if(result == RES_OK)
    {
        ret = 0;
    }
    else
    {
        ret = -RED_EIO;
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


#elif BDEV_EXAMPLE_IMPLEMENTATION == BDEV_ATMEL_SDMMC

#include <task.h>

#include <conf_sd_mmc.h>
#include <sd_mmc.h>
#include <sd_mmc_mem.h>
#include <ctrl_access.h>

/*  sd_mmc_mem_2_ram_multi() and sd_mmc_ram_2_mem_multi() use an unsigned
    16-bit value to specify the sector count, so no transfer can be larger
    than UINT16_MAX sectors.
*/
#define MAX_SECTOR_TRANSFER UINT16_MAX


/** @brief Initialize a disk.

    @param bVolNum  The volume number of the volume whose block device is being
                    initialized.
    @param mode     The open mode, indicating the type of access required.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
    @retval -RED_EROFS  The device is read-only media and write access was
                        requested.
*/
static REDSTATUS DiskOpen(
    uint8_t         bVolNum,
    BDEVOPENMODE    mode)
{
    REDSTATUS       ret = 0;
    uint32_t        ulTries;
    Ctrl_status     cs;

    /*  Note: Assuming the volume number is the same as the SD card slot.  The
        ASF SD/MMC driver supports two SD slots.  This implementation will need
        to be modified if multiple volumes share a single SD card.
    */

    /*  The first time the disk is opened, the SD card can take a while to get
        ready, in which time sd_mmc_test_unit_ready() returns either CTRL_BUSY
        or CTRL_NO_PRESENT.  Try numerous times, waiting half a second after
        each failure.  Empirically, this has been observed to succeed on the
        second try, so trying 10x more than that provides a margin of error.
    */
    for(ulTries = 0U; ulTries < 20U; ulTries++)
    {
        cs = sd_mmc_test_unit_ready(bVolNum);
        if((cs != CTRL_NO_PRESENT) && (cs != CTRL_BUSY))
        {
            break;
        }

        vTaskDelay(500U / portTICK_PERIOD_MS);
    }

    if(cs == CTRL_GOOD)
    {
      #if REDCONF_READ_ONLY == 0
        if(mode != BDEV_O_RDONLY)
        {
            if(sd_mmc_wr_protect(bVolNum))
            {
                ret = -RED_EROFS;
            }
        }

        if(ret == 0)
      #endif
        {
            uint32_t ulSectorLast;

            (void)sd_mmc_read_capacity(bVolNum, &ulSectorLast);

            /*  The ASF SD/MMC driver only supports 512-byte sectors.
            */
            if(    (gaRedVolConf[bVolNum].ulSectorSize != 512U)
                || (((uint64_t)ulSectorLast + 1U) < gaRedVolConf[bVolNum].ullSectorCount))
            {
                ret = -RED_EINVAL;
            }
        }
    }
    else
    {
        ret = -RED_EIO;
    }

    return ret;
}


/** @brief Uninitialize a disk.

    @param bVolNum  The volume number of the volume whose block device is being
                    uninitialized.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskClose(
    uint8_t     bVolNum)
{
    (void)bVolNum;
    return 0;
}


/** @brief Read sectors from a disk.

    @param bVolNum          The volume number of the volume whose block device
                            is being read from.
    @param ullSectorStart   The starting sector number.
    @param ulSectorCount    The number of sectors to read.
    @param pBuffer          The buffer into which to read the sector data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskRead(
    uint8_t     bVolNum,
    uint64_t    ullSectorStart,
    uint32_t    ulSectorCount,
    void       *pBuffer)
{
    REDSTATUS   ret = 0;
    uint32_t    ulSectorIdx = 0U;
    uint32_t    ulSectorSize = gaRedVolConf[bVolNum].ulSectorSize;
    uint8_t    *pbBuffer = CAST_VOID_PTR_TO_UINT8_PTR(pBuffer);

    while(ulSectorIdx < ulSectorCount)
    {
        uint32_t    ulTransfer = REDMIN(ulSectorCount - ulSectorIdx, MAX_SECTOR_TRANSFER);
        Ctrl_status cs;

        cs = sd_mmc_mem_2_ram_multi(bVolNum, (uint32_t)(ullSectorStart + ulSectorIdx),
                                    (uint16_t)ulTransfer, &pbBuffer[ulSectorIdx * ulSectorSize]);
        if(cs != CTRL_GOOD)
        {
            ret = -RED_EIO;
            break;
        }

        ulSectorIdx += ulTransfer;
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Write sectors to a disk.

    @param bVolNum          The volume number of the volume whose block device
                            is being written to.
    @param ullSectorStart   The starting sector number.
    @param ulSectorCount    The number of sectors to write.
    @param pBuffer          The buffer from which to write the sector data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskWrite(
    uint8_t         bVolNum,
    uint64_t        ullSectorStart,
    uint32_t        ulSectorCount,
    const void     *pBuffer)
{
    REDSTATUS       ret = 0;
    uint32_t        ulSectorIdx = 0U;
    uint32_t        ulSectorSize = gaRedVolConf[bVolNum].ulSectorSize;
    const uint8_t  *pbBuffer = CAST_VOID_PTR_TO_CONST_UINT8_PTR(pBuffer);

    while(ulSectorIdx < ulSectorCount)
    {
        uint32_t    ulTransfer = REDMIN(ulSectorCount - ulSectorIdx, MAX_SECTOR_TRANSFER);
        Ctrl_status cs;

        cs = sd_mmc_ram_2_mem_multi(bVolNum, (uint32_t)(ullSectorStart + ulSectorIdx),
                                    (uint16_t)ulTransfer, &pbBuffer[ulSectorIdx * ulSectorSize]);
        if(cs != CTRL_GOOD)
        {
            ret = -RED_EIO;
            break;
        }

        ulSectorIdx += ulTransfer;
    }

    return ret;
}


/** @brief Flush any caches beneath the file system.

    @param bVolNum  The volume number of the volume whose block device is being
                    flushed.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskFlush(
    uint8_t     bVolNum)
{
    REDSTATUS   ret;
    Ctrl_status cs;

    /*  The ASF SD/MMC driver appears to write sectors synchronously, so it
        should be fine to do nothing and return success.  However, Atmel's
        implementation of the FatFs diskio.c file does the equivalent of the
        below when the disk is flushed.  Just in case this is important for some
        non-obvious reason, do the same.
    */
    cs = sd_mmc_test_unit_ready(bVolNum);
    if(cs == CTRL_GOOD)
    {
        ret = 0;
    }
    else
    {
        ret = -RED_EIO;
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


#elif BDEV_EXAMPLE_IMPLEMENTATION == BDEV_RAM_DISK

#include <stdlib.h> /* For ALLOCATE_CLEARED_MEMORY(), which expands to calloc(). */


static uint8_t *gapbRamDisk[REDCONF_VOLUME_COUNT];


/** @brief Initialize a disk.

    @param bVolNum  The volume number of the volume whose block device is being
                    initialized.
    @param mode     The open mode, indicating the type of access required.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0           Operation was successful.
    @retval -RED_EIO    A disk I/O error occurred.
*/
static REDSTATUS DiskOpen(
    uint8_t         bVolNum,
    BDEVOPENMODE    mode)
{
    REDSTATUS       ret = 0;

    (void)mode;

    if(gapbRamDisk[bVolNum] == NULL)
    {
        gapbRamDisk[bVolNum] = ALLOCATE_CLEARED_MEMORY(gaRedVolume[bVolNum].ulBlockCount, REDCONF_BLOCK_SIZE);
        if(gapbRamDisk[bVolNum] == NULL)
        {
            ret = -RED_EIO;
        }
    }

    return ret;
}


/** @brief Uninitialize a disk.

    @param bVolNum  The volume number of the volume whose block device is being
                    uninitialized.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskClose(
    uint8_t     bVolNum)
{
    REDSTATUS   ret;

    if(gapbRamDisk[bVolNum] == NULL)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        /*  This implementation uses dynamically allocated memory, but must
            retain previously written data after the block device is closed, and
            thus the memory cannot be freed and will remain allocated until
            reboot.
        */
        ret = 0;
    }

    return ret;
}


/** @brief Read sectors from a disk.

    @param bVolNum          The volume number of the volume whose block device
                            is being read from.
    @param ullSectorStart   The starting sector number.
    @param ulSectorCount    The number of sectors to read.
    @param pBuffer          The buffer into which to read the sector data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskRead(
    uint8_t     bVolNum,
    uint64_t    ullSectorStart,
    uint32_t    ulSectorCount,
    void       *pBuffer)
{
    REDSTATUS   ret;

    if(gapbRamDisk[bVolNum] == NULL)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        uint64_t ullByteOffset = ullSectorStart * gaRedVolConf[bVolNum].ulSectorSize;
        uint32_t ulByteCount = ulSectorCount * gaRedVolConf[bVolNum].ulSectorSize;

        RedMemCpy(pBuffer, &gapbRamDisk[bVolNum][ullByteOffset], ulByteCount);

        ret = 0;
    }

    return ret;
}


#if REDCONF_READ_ONLY == 0
/** @brief Write sectors to a disk.

    @param bVolNum          The volume number of the volume whose block device
                            is being written to.
    @param ullSectorStart   The starting sector number.
    @param ulSectorCount    The number of sectors to write.
    @param pBuffer          The buffer from which to write the sector data.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskWrite(
    uint8_t     bVolNum,
    uint64_t    ullSectorStart,
    uint32_t    ulSectorCount,
    const void *pBuffer)
{
    REDSTATUS   ret;

    if(gapbRamDisk[bVolNum] == NULL)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        uint64_t ullByteOffset = ullSectorStart * gaRedVolConf[bVolNum].ulSectorSize;
        uint32_t ulByteCount = ulSectorCount * gaRedVolConf[bVolNum].ulSectorSize;

        RedMemCpy(&gapbRamDisk[bVolNum][ullByteOffset], pBuffer, ulByteCount);

        ret = 0;
    }

    return ret;
}


/** @brief Flush any caches beneath the file system.

    @param bVolNum  The volume number of the volume whose block device is being
                    flushed.

    @return A negated ::REDSTATUS code indicating the operation result.

    @retval 0   Operation was successful.
*/
static REDSTATUS DiskFlush(
    uint8_t     bVolNum)
{
    REDSTATUS   ret;

    if(gapbRamDisk[bVolNum] == NULL)
    {
        ret = -RED_EINVAL;
    }
    else
    {
        ret = 0;
    }

    return ret;
}
#endif /* REDCONF_READ_ONLY == 0 */


#else

#error "Invalid BDEV_EXAMPLE_IMPLEMENTATION value"

#endif /* BDEV_EXAMPLE_IMPLEMENTATION == ... */

