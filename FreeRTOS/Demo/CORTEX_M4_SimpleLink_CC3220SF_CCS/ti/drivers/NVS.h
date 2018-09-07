/*
 * Copyright (c) 2015-2016, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
/** ==========================================================================
 *  @file       NVS.h
 *
 *  @brief      <b>PRELIMINARY</b> Non-Volatile Storage Driver.
 *
 *  <b>WARNING</b> These APIs are <b>PRELIMINARY</b>, and subject to
 *  change in the next few months.
 *
 *  The NVS header file should be included in an application as follows:
 *  @code
 *  #include <ti/drivers/NVS.h>
 *  @endcode
 *
 *  # Operation #
 *
 *  The NVS module allows you to manage non-volatile memory.  Using the
 *  NVS APIs, you can read and write data to persistant storage.  Each NVS
 *  object manages a 'block' of non-volatile memory of a size specified in
 *  the NVS object's hardware attributes.  A 'page' will refer to the
 *  smallest unit of non-volatile storage that can be erased at one time,
 *  and the page size is the size of this unit.  This is hardware specific
 *  and may be meaningless for some persistant storage systems.  However,
 *  in the case of flash memory, page size should be taken into account
 *  when deciding the block size for NVS to manage.  For example on
 *  TM4C129x devices, a page size is 16KB.
 *
 *  When page size is relevant (e.g. for flash memory), the size of an
 *  NVS block size must be less than or equal to the page size.  The block
 *  size can be less than the page size, however, care must be taken not
 *  to use the area in the page outside of the block.  When the block is
 *  erased, the entire page will be erased, clearing anything in the page
 *  that was written outside of the block.
 *
 *  See the device specific NVS header file for configuration details.
 *
 *  ==========================================================================
 */

#ifndef ti_drivers_NVS__include
#define ti_drivers_NVS__include

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#if defined (__cplusplus)
extern "C" {
#endif

/**
 *  @defgroup NVS_CONTROL NVS_control command and status codes
 *  These NVS macros are reservations for NVS.h
 *  @{
 */

/*!
 * Common NVS_control command code reservation offset.
 * NVS driver implementations should offset command codes with NVS_CMD_RESERVED
 * growing positively
 *
 * Example implementation specific command codes:
 * @code
 * #define NVSXYZ_CMD_COMMAND0     NVS_CMD_RESERVED + 0
 * #define NVSXYZ_CMD_COMMAND1     NVS_CMD_RESERVED + 1
 * @endcode
 */
#define NVS_CMD_RESERVED            32

/*!
 * Common NVS_control status code reservation offset.
 * NVS driver implementations should offset status codes with
 * NVS_STATUS_RESERVED growing negatively.
 *
 * Example implementation specific status codes:
 * @code
 * #define NVSXYZ_STATUS_ERROR0    NVS_STATUS_RESERVED - 0
 * #define NVSXYZ_STATUS_ERROR1    NVS_STATUS_RESERVED - 1
 * #define NVSXYZ_STATUS_ERROR2    NVS_STATUS_RESERVED - 2
 * @endcode
 */
#define NVS_STATUS_RESERVED        -32

/**
 *  @defgroup NVS_STATUS Status Codes
 *  NVS_STATUS_* macros are general status codes returned by NVS_control()
 *  @{
 *  @ingroup NVS_CONTROL
 */

/*!
 * @brief   Successful status code returned by NVS_control().
 *
 * NVS_control() returns NVS_STATUS_SUCCESS if the control code was executed
 * successfully.
 */
#define NVS_STATUS_SUCCESS         0

/*!
 * @brief   Generic error status code returned by NVS_control().
 *
 * NVS_control() returns NVS_STATUS_ERROR if the control code was not executed
 * successfully.
 */
#define NVS_STATUS_ERROR          -1

/*!
 * @brief   An error status code returned by NVS_control() for undefined
 * command codes.
 *
 * NVS_control() returns NVS_STATUS_UNDEFINEDCMD if the control code is not
 * recognized by the driver implementation.
 */
#define NVS_STATUS_UNDEFINEDCMD   -2
/** @}*/

/**
 *  @defgroup NVS_CMD Command Codes
 *  NVS_CMD_* macros are general command codes for NVS_control(). Not all NVS
 *  driver implementations support these command codes.
 *  @{
 *  @ingroup NVS_CONTROL
 */

/* Add NVS_CMD_<commands> here */

/** @}*/

/** @}*/

/*!
 *  @brief Success return code
 */
#define NVS_SOK (0)

/*!
 *  @brief General failure return code
 */
#define NVS_EFAIL               (-1)
#define NVS_EOFFSET             (-3)
#define NVS_EALIGN              (-4)
#define NVS_ENOTENOUGHBYTES     (-5)
#define NVS_EALREADYWRITTEN     (-6)
#define NVS_ECOPYBLOCK          (-7)

/*!
 *  @brief NVS write flags
 *
 *  The following flags can be or'd together and passed as a bit mask
 *  to NVS_write.
 */

/*!
 *  @brief Exclusive write flag
 *
 *  Only write if the area has not already been written to since the last
 *  erase.  In the case of flash memory on some devices, once data is written
 *  to a location, that location cannot be written to again without first
 *  erasing the entire flash page.  If the NVS_WRITE_EXCLUSIVE flag is
 *  set in the flags passed to NVS_write(), the location where the data
 *  will be written to is first checked if it has been modified since the
 *  last time the NVS block was erarsed.  If that is the case, NVS_write()
 *  will return an error.
 */
#define NVS_WRITE_EXCLUSIVE           (0x1)

/*!
 *  @brief Erase write flag.
 *
 *  If NVS_WRITE_ERASE is set in the flags passed to NVS_write(), the entire
 *  NVS block will be erased before being written to.
 */
#define NVS_WRITE_ERASE               (0x2)

/*!
 *  @brief Validate write flag.
 *
 *  If NVS_WRITE_VALIDATE is set in the flags passed to NVS_write(), the region
 *  in the NVS block that was written to will be validated (i.e., compared
 *  against the data buffer passed to NVS_write()).
 */
#define NVS_WRITE_VALIDATE            (0x4)

/*!
 *  @brief    NVS Parameters
 *
 *  NVS parameters are used with the NVS_open() call. Default values for
 *  these parameters are set using NVS_Params_init().
 *
 *  @sa       NVS_Params_init()
 */
typedef struct NVS_Params {
    bool    eraseOnOpen;    /*!< Erase block on open */
} NVS_Params;

/*!
 *  @brief      NVS attributes
 *
 *  The address of an NVS_Attrs structure can be passed to NVS_getAttrs()
 *  to fill in the fields.
 *
 *  pageSize is the size of the smallest erase page.  This is hardware
 *  specific.  For example, all TM4C123x devices use 1KB pages, but
 *  TM4C129x devices use 16KB pages. Please consult the device datasheet
 *  to determine the pageSize to use.
 *
 *  blockSize is the actual size of the NVS storage block that the
 *  application chooses to manage.
 *  If pageSize is greater than blockSize, care should be taken not to
 *  use the storage on the page that is outside of the block, since it
 *  may be erased when writing to the block.  The block size must not be
 *  greater than the page size.
 *
 *  @sa     NVS_getAttrs()
 */
typedef struct NVS_Attrs {
    size_t  pageSize;    /*! Hardware page size */
    size_t  blockSize;   /*! Size of the NVS block to manage */
} NVS_Attrs;

/*!
 *  @brief      A handle that is returned from the NVS_open() call.
 */
typedef struct NVS_Config      *NVS_Handle;

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              NVS_close().
 */
typedef void        (*NVS_CloseFxn)    (NVS_Handle handle);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              NVS_control().
 */
typedef int         (*NVS_ControlFxn)  (NVS_Handle handle, unsigned int cmd,
                                        uintptr_t arg);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              NVS_exit().
 */
typedef void        (*NVS_ExitFxn)     (NVS_Handle handle);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              NVS_getAttrs().
 */
typedef int         (*NVS_GetAttrsFxn) (NVS_Handle handle, NVS_Attrs *attrs);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              NVS_init().
 */
typedef void        (*NVS_InitFxn)     (NVS_Handle handle);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              NVS_open().
 */
typedef NVS_Handle  (*NVS_OpenFxn)     (NVS_Handle handle, NVS_Params *params);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              NVS_read().
 */
typedef int         (*NVS_ReadFxn)     (NVS_Handle handle, size_t offset,
                                        void *buffer, size_t bufferSize);

/*!
 *  @brief      A function pointer to a driver specific implementation of
 *              NVS_write().
 */
typedef int         (*NVS_WriteFxn)    (NVS_Handle handle, size_t offset,
                                        void *buffer, size_t bufferSize,
                                        unsigned int flags);

/*!
 *  @brief      The definition of an NVS function table that contains the
 *              required set of functions to control a specific NVS driver
 *              implementation.
 */
typedef struct NVS_FxnTable {
    /*! Function to close the specified NVS block */
    NVS_CloseFxn        closeFxn;

    /*! Function to apply control command to the specified NVS block */
    NVS_ControlFxn      controlFxn;

    /*! Function to de-initialize the NVS module */
    NVS_ExitFxn         exitFxn;

    /*! Function to get the NVS device-specific attributes */
    NVS_GetAttrsFxn     getAttrsFxn;

    /*! Function to initialize the NVS module */
    NVS_InitFxn         initFxn;

    /*! Function to open an NVS block */
    NVS_OpenFxn         openFxn;

    /*! Function to read from the specified NVS block */
    NVS_ReadFxn         readFxn;

    /*! Function to write to the specified NVS block */
    NVS_WriteFxn        writeFxn;
} NVS_FxnTable;

/*!
 *  @brief  NVS Global configuration
 *
 *  The NVS_Config structure contains a set of pointers used to characterize
 *  the NVS driver implementation.
 *
 *  This structure needs to be defined before calling NVS_init() and it must
 *  not be changed thereafter.
 *
 *  @sa     NVS_init()
 */
typedef struct NVS_Config {
    /*! Pointer to a table of driver-specific implementations of NVS APIs */
    NVS_FxnTable const *fxnTablePtr;

    /*! Pointer to a driver specific data object */
    void               *object;

    /*! Pointer to a driver specific hardware attributes structure */
    void         const *hwAttrs;
} NVS_Config;

/*!
 *  @brief  Function to close an NVS handle
 *
 *  @param  handle      A handle returned from NVS_open()
 *
 *  @sa     NVS_open()
 */
extern void NVS_close(NVS_Handle handle);

/*!
 *  @brief  Function performs implementation specific features on a given
 *          NVS_Handle.
 *
 *  @pre    NVS_open() must be called first.
 *
 *  @param  handle      An NVS handle returned from NVS_open()
 *
 *  @param  cmd         A command value defined by the driver specific
 *                      implementation
 *
 *  @param  arg         An optional R/W (read/write) argument that is
 *                      accompanied with cmd
 *
 *  @return Implementation specific return codes. Negative values indicate
 *          unsuccessful operations.
 *
 *  @sa     NVS_open()
 */
extern int NVS_control(NVS_Handle handle, unsigned int cmd, uintptr_t arg);

/*!
 *  @brief  Erase the block of storage reference by an NVS handle
 *
 *  @param  handle      A handle returned from NVS_open()
 *
 *  @return  NVS_SOK    Success.
 *  @return  NVS_EFAIL  An error occurred erasing the flash.
 */
extern int NVS_erase(NVS_Handle handle);

/*!
 *  @brief  Function to de-initialize the NVS module
 *
 *  @pre    NVS_init() was called.
 */
extern void NVS_exit(void);

/*!
 *  @brief  Function to get the NVS attributes
 *
 *  @param  handle      A handle returned from NVS_open()
 *
 *  @param  attrs       Location to store attributes.
 */
extern int NVS_getAttrs(NVS_Handle handle, NVS_Attrs *attrs);

/*!
 *  @brief  Function to initialize the NVS module
 *
 *  @pre    The NVS_config structure must exist and be persistent before this
 *          function can be called. This function must also be called before
 *          any other NVS APIs.
 */
extern void NVS_init(void);

/*!
 *  @brief  Get an NVS block for reading and writing.
 *
 *  @pre    NVS_init() was called.
 *
 *  @param  index         Index in the NVS_config table of the block
 *                        to manage.
 *
 *  @param  params        Pointer to a parameter block.  If NULL, default
 *                        parameter values will be used.
 */
extern NVS_Handle NVS_open(int index, NVS_Params *params);

/*!
 *  @brief   Read data from an NVS block.
 *
 *  @param   handle     A handle returned from NVS_open()
 *
 *  @param   offset     The byte offset into the NVS block to start
 *                      reading from.
 *
 *  @param   buffer     A buffer to copy the data to.
 *
 *  @param   bufferSize The size of the buffer (number of bytes to read).
 *
 *  @return  NVS_SOK      Success.
 *  @return  NVS_EOFFSET  The location and size to read from does not
 *                        lie completely within the NVS block.
 *
 *  @remark  This call may block to ensure atomic access to the block.
 */
extern int NVS_read(NVS_Handle handle, size_t offset, void *buffer,
                    size_t bufferSize);

/*!
 *  @brief   Write data to an NVS block.
 *
 *  @param   handle     A handle returned from NVS_open()
 *
 *  @param   offset     The byte offset into the NVS block to start
 *                      writing.  offset must be 4-byte aligned.
 *
 *  @param   buffer     A buffer conntaining data to write to
 *                      the NVS block.  If buffer is NULL, the block
 *                      will be erased.  A non-NULL buffer must be
 *                      aligned on a 4-byte boundary.
 *
 *  @param   bufferSize The size of the buffer (number of bytes to write).
 *                      bufferSize must be a multiple of 4 bytes.
 *
 *  @param   flags      Write flags (NVS_WRITE_EXCLUSIVE, NVS_WRITE_ERASE,
 *                      NVS_WRITE_VALIDATE).
 *
 *  @return  NVS_SOK      Success.
 *  @return  NVS_EOFFSET  The location and size to write to does not
 *                        lie completely within the NVS block.
 *  @return  NVS_EALIGN   The offset or bufferSize is not 4-byte aligned.
 *  @return  NVS_ALREADYWRITTEN
 *                        The region to write to (the bufferSize region
 *                        starting at offset into the block) has already
 *                        been written to since the last erase, and
 *                        NVS_WRITE_EXCLUSIVE is set in the flags parameter.
 *
 *  @remark  This call may block to ensure atomic access to the block.
 */
extern int NVS_write(NVS_Handle handle, size_t offset, void *buffer,
                     size_t bufferSize, unsigned int flags);

#if defined (__cplusplus)
}
#endif /* defined (__cplusplus) */

/*@}*/
#endif /* ti_drivers_NVS__include */
