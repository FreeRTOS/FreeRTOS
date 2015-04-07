/******************************************************************************
*
* Copyright 2013 Altera Corporation. All Rights Reserved.
* 
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
* 
* 1. Redistributions of source code must retain the above copyright notice,
* this list of conditions and the following disclaimer.
* 
* 2. Redistributions in binary form must reproduce the above copyright notice,
* this list of conditions and the following disclaimer in the documentation
* and/or other materials provided with the distribution.
* 
* 3. The name of the author may not be used to endorse or promote products
* derived from this software without specific prior written permission.
* 
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
* OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
* IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
* OF SUCH DAMAGE.
* 
******************************************************************************/

/*! \file
 *  Altera - NAND Flash Controller Module
 */

#ifndef __ALT_NAND_FLASH_H__
#define __ALT_NAND_FLASH_H__

#include "hwlib.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/******************************************************************************/
/*! \addtogroup ALT_NAND_FLASH NAND Flash Controller
 *
 * This module defines an API for configuration and management of access to NAND
 * flash memory devices through the HPS NAND flash controller.
 *
 * This API supports the following features:
 * * Support for ONFI 1.0 devices or legacy devices that can be identified by
 *   the NAND flash controller.
 * * Automatic initialization and discovery of supported NAND flash devices.
 * * ECC protection in hardware.
 * * Erase by block.
 * * Read/Write by (whole) pages.
 * * DMA read/write transfers.
 *
 * This API provides basic I/O operations to unmanaged NAND flash memory with
 * optional hardware assisted ECC protection. This module does not provide higher
 * level flash I/O features such as a flash file system or capabilities for bad
 * block life cycle management or wear leveling.

 * Support of certain operational features may be device dependent and therefore
 * it is important to consult the data sheet for the specific NAND flash device
 * that the NAND flash controller will interface to.
 *
 * The comments in this module use the following NAND flash terminology:
 * * \b Plane - A collection of blocks typically on a single die of a multi-die
 *              device.
 * * \b Block - The basic unit of NAND flash memory. Blocks are the smallest unit
 *              that can be erased. Blocks contain pages.
 * * \b Page - A subdivision of a block. It contains the data payload and spare
 *             data areas used to store ECC and bad block information.
 * * \b Sector - A subdivision of a page. It contains the data payload protected
 *               by ECC.
 * * \b Spare - The area of a page used to store ECC and bad block information.
 *
 * The NAND flash controller uses indexed addressing to operate on flash device
 * blocks or pages. The NAND flash 32-bit address is organized as follows:
 *
 *  Bits      | Description                                                             
 * :----------|:-------------------------------------------------------------------------
 *  [31:24]   | <em>Reserved - Unused</em>
 *  [23:\e m] | Specifies the block address portion of the address.
 *  [\e m:0]  | Specifies the page address portion of the address.
 *
 * where \e m depends on the number of pages per block for the flash device.
 *
 * For functions expecting \e block_addr parameters, only the bits 23 : \e m are
 * relevant in a 32-bit address argument value. All other bits should be zero or a
 * ALT_E_BAD_ARG is returned.
 *
 * For functions expecting \e page_addr parameters, both the bits \e m : 0
 * specifying the page as well as the bits 23 : \e m specifying the block
 * containing the page are relevant in a 32-bit address argument. All other bits
 * should be zero or a ALT_E_BAD_ARG is returned.
 *
 * \internal
 * General Implementation Notes:
 * * Command data and control paths that bypass HW ECC or require SW ECC are not
 *   used in this implementation or supported by the API. This does not imply that
 *   a user must elect to enable ECC in order to use flash memory but if the user
 *   so chooses then this module API only employs HW assisted ECC protection in
 *   its implementation.
 * * Whether to use ECC protection or not should be decided from the first used of
 *   the NAND flash device and then used consistently thereafter. Once ECC
 *   protection is enabled then the flash memory locations must be initialized
 *   before ever reading from them. Flash memory is initialized by erasing and
 *   then writing to the flash memory while ECC is enabled.
 * * The ECC program mode of "Main Area Transfer Mode" operation is used and
 *   maintained throughout the implementation of this API. No API is provided for
 *   switching ECC program modes in order to simplify the implementation and user
 *   programming model.
 * \endinternal
 *
 * @{
 */

/*!
 * Type definition for a callback function prototype used by NAND flash controller
 * API functions to notify users of asynchronous operation completion or
 * operational error status.
 *
 * \param       status
 *              The final status of the asynchronous operation success or failure.
 *
 * \param       completion_arg
 *              A pointer for passing user defined data. The content of this
 *              parameter is user defined and is passed when the asynchronous
 *              operation is initiated.
 */
typedef void (*alt_nand_callback_t)(ALT_STATUS_CODE status, void *callback_arg);

/*!
 * Type definition for a user defined custom flash device initialization
 * function. This function should be provided for flash devices that do not
 * support automatic device discovery and parameter configuration or devices
 * where customized settings are desired.
 *
 * This function is invoked by the alt_nand_flash_init() routine at the proper
 * point during the NAND flash controller initialization process.
 *
 * Returning any status code other than ALT_E_SUCCESS from this custom
 * initialization function will cause the alt_nand_flash_init() function to fail
 * as well.
 *
 * \param       user_arg
 *              A pointer for optionally passing user defined data. The content of
 *              this parameter is user defined and its value may be NULL if
 *              unused.
 *
 * \retval      ALT_E_SUCCESS   Custom flash device initialization was successful.
 * \retval      ALT_E_ERROR     Custom flash device initialization failed.
 */
typedef ALT_STATUS_CODE (*alt_nand_flash_custom_init_t)(void *user_arg);

/*!
 * This function initializes the NAND flash controller and attached flash device by:
 * * Taking the NAND flash controller out of reset.
 * * Performing automatic NAND flash device discovery and parameter configuration
 *   for supported devices.
 * * Optionally loading block 0, page 0 of the device and configuring direct read
 *   access (preloader use case only).
 * * And assuming the device discovery and parameter configuration (automatic or
 *   custom) process is successful, then scans the device for blocks marked as
 *   defective at manufacture time and builds a bad block table. The bad block
 *   table is used at runtime to avoid erasing or programming any block marked as
 *   defective.
 *
 * \param       load_block0_page0
 *              If \b true then load block 0, page 0 from the flash device and
 *              configure the NAND flash controller for direct read access. This
 *              option is typically used by custom preloaders and should be set to 
 *              \b false by most users.
 *
 * \param       page_size_512
 *              If \b true the flash device has a 512 byte page size. This type of
 *              device typically does not support automatic discovery and
 *              therefore requires custom flash device initialization via the \e
 *              custom_init function.
 *
 * \param       custom_init
 *              A pointer to a user defined function to perform customized flash
 *              device initialization. The function must program the applicable
 *              NAND flash controller registers in the config group based on
 *              specific device features and operational performance
 *              parameters. The NAND flash controller registers are accessible via
 *              the NAND flash controller SoCAL header file "socal/alt_nand.h".  A
 *              NULL value for this parameter allows the NAND flash controller to
 *              do automatic device discovery and parameter configuration. A NULL
 *              value should normally be passed for ONFI and supported legacy
 *              flash devices.
 *
 * \param       user_arg
 *              A user defined argument that is passed to the custom
 *              initialization function when invoked.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * See:
 * * Cadence DB
 *   - Section 4.4 Initialization Protocol
 *   - Section 11.2 Device Initialization Sequence
 *   - Section 11.3 Device Operation Control (Maybe?)
 * * CV Device Handbook
 *   - Discovery and Initialization
 *   - Bootstrap Interface
 *   - Configuration by Host (Provide SW hook)
 *   - Clocks
 *   - Resets
 *   - Device Initialization Sequence
 * * Open NAND Flash Interface Specification Revision 1.0
 *   - Section 3.2. Factory Defect Mapping for bad block table construction.
 *
 * 1) Discovery and Initialization section of HPS TRM
 * 2) Bootstrap Interface section of HPS TRM
 * 3) Configuration by Host section of HPS TRM
 *
 * Checks:
 * - nand_x_clk and nand_clk
 *
 * ONFI - Use ONFI discovery protocol to identify device and read its feature properties.
 *
 * Legacy - Use the Read Electronic Signature command to identify device.
 *
 * Others - Generally 512 byte page size devices.
 *
 * Unless bootstrap_inhibit_b0p0_load (sysmgr.nandgrp.bootstrap.noloadb0p0) signal
 * is asserted, the NAND flash controller will page load block 0/page 0 to
 * allow for booting.
 *
 * If bootstrap_inhibit_init () is asserted the NAND flash controller do not
 * perform initialization and just issues a RESET command to the device.
 *
 * \endinternal
 */
ALT_STATUS_CODE alt_nand_flash_init(const bool load_block0_page0,
                                    const bool page_size_512,
                                    alt_nand_flash_custom_init_t custom_init,
                                    void *user_arg);

/*!
 * Uninitialize the NAND flash controller.
 *
 * Uninitialize the NAND flash controller by putting the flash controller into
 * reset.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_nand_flash_uninit(void);

/*!
 * Defines an value to represent an invalid or bad flash device address.
 */
#define ALT_NAND_INVALID_FLASH_ADDR     0xffffffff

/*!
 * Returns the block number of the specified block or page address. The returned
 * block address is right shift aligned to bit 0.
 *
 * This function may be used after a successful call to alt_nand_flash_init().
 *
 * \param       addr
 *              A block or page address value.
 *
 * \returns     The bit 0 right aligned block address portion of the \e addr
 *              argument.
 */
uint32_t alt_nand_block_address_get(const uint32_t addr);

/*!
 * Returns the page number of the specified block or page address. The returned
 * page address is right shift aligned to bit 0.
 *
 * This function may be used after a successful call to alt_nand_flash_init().
 *
 * \param       addr
 *              A block or page address value.
 *
 * \returns     The bit 0 right aligned page address portion of the \e addr
 *              argument.
 */
uint32_t alt_nand_page_address_get(const uint32_t addr);

/*!
 * Returns a valid block or page address for a flash device with the given block
 * and page argument values.
 *
 * This function may be used after a successful call to alt_nand_flash_init().
 *
 * \param       block_num
 *              The flash device block number to use in composing the final flash
 *              device address.
 *
 * \param       page_num
 *              The flash device page number within the block to use in composing
 *              the final flash device address.
 *
 * \returns     A valid block or page address for the flash
 *              device. ALT_NAND_INVALID_FLASH_ADDR is returned if either of the \e
 *              block_num or \e page_num arguments is invalid for the device.
 */
uint32_t alt_nand_flash_addr_compose(const uint32_t block_num, 
                                     const uint32_t page_num);

/*!
 * Erases the designated flash device block.
 *
 * Erases the flash device block designated by \e block_addr. The erase operation
 * proceeds asynchronously with a user callback notification upon completion or
 * error.
 * 
 * Flash memory must be erased before being written. Erasing sets all bits in a
 * given block of flash memory to '1' which is the erased state.
 *
 * \param       block_addr
 *              The block address to erase.
 *
 * \param       completion_callback
 *              A user defined callback function that is called when the operation
 *              completes or an error occurs.
 *
 * \param       completion_arg
 *              A user defined argument that is passed to the callback function
 *              when the operation completes or an error occurs.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 * \retval      ALT_E_BAD_BLK   One or more device block(s) are marked defective 
 *                              and hence the operation was ignored.
 *
 * \internal
 * See:
 * * CV Device Handbook
 *   - Flash-Related Special Function Operations - Erase Operations
 *     + Single Block Erase
 *     + Multi-Plane Erase
 *
 * Command to erase a single block (section 5.2.3.1 of Cadence DB).
 * \endinternal
 */
ALT_STATUS_CODE alt_nand_flash_block_erase(const uint32_t block_addr,
                                           alt_nand_callback_t completion_callback,
                                           void *completion_arg);

/*!
 * Read one or more pages from the flash device.
 *
 * Reads \e num_pages from the flash device beginning at \e page_addr. Whole pages
 * are read from flash memory. The pages are copied into the \e dest location.
 * 
 * If ECC is enabled then the NAND flash controller performs ECC correction and
 * detection on the fly as data is read from the device and before being
 * transferred out of the controller.
 *
 * \param       page_addr
 *              The beginning page address to read.
 *
 * \param       num_pages
 *              The number of pages to read.
 *
 * \param       dest
 *              The address of the destination buffer.
 *
 * \param       dest_size
 *              The size of the destination buffer in bytes.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 * \retval      ALT_E_BAD_BLK   The device block is marked defective and hence the 
 *                              operation was ignored.
 * \retval      ALT_E_BUF_OVF   The destination buffer does not contain enough space 
 *                              for the operation. 
 * \retval      ALT_E_ECC_UNCOR An uncorrected ECC error occurred.
 *
 * \internal
 * See:
 * * CV Device Handbook
 *   - Indexed Addressing
 *   - MAP01 Commands
 *   - MAP10 Commands
 *   - Data DMA (ignore Burst DMA)
 * * Pipeline Read-Ahead and Write-Ahead Operations
 *
 * Map01 Commands (section 5.2.2 of Cadence DB).

 * Pipeline read-ahead operations (sections 5.2.3.6 and 5.2.3.6.1 of Cadence DB).
 *
 * Do not use Map00 in this implementation. ECC correction is not performed while
 * doing such operations and is not recommended in MLC devices.
 *
 * Entire page(s) are read.
 *
 * Use Map01 for single page reads.
 *
 * Use pipeline read-ahead technique to optimize multi-page reads.
 * \endinternal
 */
ALT_STATUS_CODE alt_nand_flash_page_read(const uint32_t page_addr, 
                                         const uint32_t num_pages,
                                         void *dest,
                                         const uint32_t dest_size);

/*!
 * Write one or more pages to the flash device.
 *
 * Writes \e num_pages to the flash device beginning at \e page_addr. Whole pages
 * are written to flash memory. The block(s) containing the pages must have been
 * previously erased.
 * 
 * \param       page_addr
 *              The beginning page address to write.
 *
 * \param       num_pages
 *              The number of pages to write.
 *
 * \param       src
 *              The address of the source buffer containing th data to be written
 *              to the flash device.
 *
 * \param       src_size
 *              The size of the source buffer in bytes.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 * \retval      ALT_E_BAD_BLK   The device block is marked defective and hence the 
 *                              operation was ignored.
 * \retval      ALT_E_BUF_OVF   The source buffer is larger than the flash device 
 *                              page(s) destination.
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_nand_flash_page_write(const uint32_t page_addr, 
                                          const uint32_t num_pages,
                                          const void *src,
                                          const uint32_t src_size);

/*!
 * Read one or more pages from the flash device using the NAND flash controller's
 * internal DMA. The read operation proceeds asynchronously with a user callback
 * notification upon completion or error.
 *
 * Reads \e num_pages from the flash device beginning at \e page_addr. Whole pages
 * are read from flash memory. The pages are copied into the \e dest location.
 * 
 * If ECC is enabled then the NAND flash controller performs ECC correction and
 * detection on the fly as data is read from the device and before being
 * transferred out of the controller.
 *
 * \param       page_addr
 *              The beginning page address to read.
 *
 * \param       num_pages
 *              The number of pages to read.
 *
 * \param       dest
 *              The address of the destination buffer.
 *
 * \param       dest_size
 *              The size of the destination buffer in bytes.
 *
 * \param       completion_callback
 *              A user defined callback function that is called when the operation
 *              completes or an error occurs.
 *
 * \param       completion_arg
 *              A user defined argument that is passed to the callback function
 *              when the operation completes or an error occurs.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 * \retval      ALT_E_BAD_BLK   The device block is marked defective and hence the 
 *                              operation was ignored.
 * \retval      ALT_E_BUF_OVF   The destination buffer does not contain enough space 
 *                              for the operation. 
 *
 * \internal
 * See:
 * * CV Device Handbook
 *   - Data DMA
 *   - Multitransaction DMA Command
 *   - Interrupt and DMA Enabling
 * * Pipeline Read-Ahead and Write-Ahead Operations
 * \endinternal
 */
ALT_STATUS_CODE alt_nand_flash_page_dma_read(const uint32_t page_addr, 
                                             const uint32_t num_pages,
                                             void *dest,
                                             const uint32_t dest_size,
                                             alt_nand_callback_t completion_callback,
                                             void *completion_arg);
/*!
 * Write one or more pages to the flash device using the NAND flash controller's
 * internal DMA. The write operation proceeds asynchronously with a user callback
 * notification upon completion or error.
 *
 * Writes \e num_pages to the flash device beginning at \e page_addr. Whole pages
 * are written to flash memory. The block(s) containing the pages must have been
 * previously erased.
 * 
 * \param       page_addr
 *              The beginning page address to write.
 *
 * \param       num_pages
 *              The number of pages to write.
 *
 * \param       src
 *              The address of the source buffer containing th data to be written
 *              to the flash device.
 *
 * \param       src_size
 *              The size of the source buffer in bytes.
 *
 * \param       completion_callback
 *              A user defined callback function that is called when the operation
 *              completes or an error occurs.
 *
 * \param       completion_arg
 *              A user defined argument that is passed to the callback function
 *              when the operation completes or an error occurs.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 * \retval      ALT_E_BAD_BLK   The device block is marked defective and hence the 
 *                              operation was ignored.
 * \retval      ALT_E_BUF_OVF   The destination buffer does not contain enough space 
 *                              for the operation. 
 *
 * \internal
 * See:
 * * CV Device Handbook
 *   - Data DMA
 *   - Multitransaction DMA Command
 *   - Interrupt and DMA Enabling
 * * Pipeline Read-Ahead and Write-Ahead Operations
 * \endinternal
 */
ALT_STATUS_CODE alt_nand_flash_page_dma_write(const uint32_t page_addr, 
                                              const uint32_t num_pages,
                                              const void *src,
                                              const uint32_t src_size,
                                              alt_nand_callback_t completion_callback,
                                              void *completion_arg);

/*!
 * This type definition enumerates the possible ECC correction code bit encodings
 * and their applicability to sector size.
 */
typedef enum ALT_NAND_ECC_CORRECTION_e
{
    ALT_NAND_ECC_4_BIT_CORRECTION      = 4,    /*!< Performs 4 bit correction over a 512 byte sector */ 
    ALT_NAND_ECC_8_BIT_CORRECTION      = 8,    /*!< Performs 8 bit correction over a 512 byte sector */
    ALT_NAND_ECC_16_BIT_CORRECTION     = 16,   /*!< Performs 16 bit correction over a 512 byte sector */
    ALT_NAND_ECC_24_BIT_CORRECTION     = 24    /*!< Performs 24 bit correction over a 1024 byte sector */
} ALT_NAND_ECC_CORRECTION_t;

/*!
 * Enable hardware ECC protection for the flash device.
 *
 * \param       ecc_correction
 *              The desired ECC correction code bit encoding.
 *
 * \retval      ALT_E_SUCCESS       Indicates successful completion.
 * \retval      ALT_E_ERROR         Indicates an error occurred.
 * \retval      ALT_E_INV_OPTION    The specified ECC correction value is not 
 *                                  appropriate for the device page size and 
 *                                  spare area available.
 *
 * \internal
 * See: Cadence DB - Section 11.4 ECC Enabling
 * \endinternal
 */
ALT_STATUS_CODE alt_nand_flash_ecc_enable(const ALT_NAND_ECC_CORRECTION_t ecc_correction);

/*!
 * Disable hardware ECC protection for the flash device.
 *
 * \retval      ALT_E_SUCCESS       Indicates successful completion.
 * \retval      ALT_E_ERROR         Indicates an error occurred.
 *
 * \internal
 * See: Cadence DB - Section 11.4 ECC Enabling
 * \endinternal
 */
ALT_STATUS_CODE alt_nand_flash_ecc_disable(void);


/*!
 * This type defines a structure for accessing the ECC error correction
 * information for the last transaction completed by the NAND flash controller.
 */
typedef struct ALT_NAND_FLASH_ECC_STATUS_s
{
    uint32_t    corrected_errors[4];    /*!< Maximum of number of errors corrected
                                         *   per sector in a bank. This field is
                                         *   not valid for uncorrectable errors. A
                                         *   value of zero indicates that no ECC
                                         *   error occurred in last completed
                                         *   transaction. Index \e n corressponds
                                         *   to bank \e n.
                                         */
    bool        uncorrected_error[4];   /*!< \b true if an uncorrectable error
                                         *   occurred while reading pages for last
                                         *   transaction in a bank.  Uncorrectable
                                         *   errors also generate
                                         *   ALT_NAND_INT_STATUS_ECC_UNCOR_ERR
                                         *   interrupt status conditions.  Index
                                         *   \e n corressponds to bank \e n.
                                         */
} ALT_NAND_FLASH_ECC_STATUS_t;

/*!
 * Gets the ECC error correction information for the last transaction completed by
 * the NAND flash controller.
 *
 * \param       ecc_status
 *              [out] Pointer to a \ref ALT_NAND_FLASH_ECC_STATUS_t structure
 *              containing the ECC status for the last completed transaction.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 *
 * \internal
 * nandregs.ecc.ECCCorInfo_b01
 * nandregs.ecc.ECCCorInfo_b23
 * \endinternal
 */
ALT_STATUS_CODE alt_nand_flash_ecc_status_get(ALT_NAND_FLASH_ECC_STATUS_t *ecc_status);

/*!
 * This type definition enumerates the interrupt status conditions for the NAND
 * flash controller.
 *
 * The enumerations serve as masks for the NAND flash controller events that can
 * be set when the designated conditions occur and the corresponding event is
 * enabled.  When any of these event source conditions are true, the \b
 * ALT_INT_INTERRUPT_NAND_IRQ interrupt output is asserted high.
 *
 * Interrupt sources are cleared when software calls alt_nand_int_clear(). The
 * interrupt sources are individually maskable using alt_nand_int_disable() and
 * alt_nand_int_enable().
 *
 * The NAND flash controller has a single active high interrupt output
 * (nand_int). This interrupt is the logical "OR" of all of the interrupt bits
 * within the flash controller that are enabled and set. There is also a global
 * interrupt enable in the flash controller block that must be set to enable
 * interrupts. Each interrupt source within the IP has an active high enable bit
 * and a sticky bit. The sticky bit is an active high "write one to clear" status
 * bit. There are four sets of identical interrupt bits, one for each of the four
 * banks. The following conditions can trigger an interrupt:
 * - Page transfer
 * - Pipeline command sequence violation
 * - Rest/initialization complete
 * - Ready/Busy pin low to high transition
 * - Unsupported command
 * - Locked block command failure
 * - Pipeline command or copyback command complete
 * - Erase complete
 * - Program complete
 * - Load complete
 * - Erase fail
 * - Program fail
 * - Timeout
 * - DMA command complete
 * - Uncorrectable ECC error
 */
typedef enum ALT_NAND_INT_STATUS_e
{
    ALT_NAND_INT_STATUS_PAGE_XFER_INC           = (1 << 15),
                                                /*!< For every page of data
                                                 *   transfer to or from the
                                                 *   device, this status will be
                                                 *   set.
                                                 */
    ALT_NAND_INT_STATUS_PIPE_CMD_ERR            = (1 << 14),
                                                /*!< A pipeline command sequence
                                                 *   has been violated. This
                                                 *   occurs when MAP01 page
                                                 *   read/write address does not
                                                 *   match the corresponding
                                                 *   expected address from the
                                                 *   pipeline commands issued
                                                 *   earlier.
                                                 */
    ALT_NAND_INT_STATUS_RST_COMP                = (1 << 13),
                                                /*!< The NAND flash controller
                                                 *   has finished reset and
                                                 *   initialization process.
                                                 */
    ALT_NAND_INT_STATUS_INT_ACT                 = (1 << 12),
                                                /*!< R/B pin of device
                                                 *   transitioned from low to
                                                 *   high.
                                                 */
    ALT_NAND_INT_STATUS_UNSUP_CMD               = (1 << 11),
                                                /*!< An unsupported command was
                                                 *   received. This interrupt is
                                                 *   set when an invalid command
                                                 *   is received, or when a
                                                 *   command sequence is broken.
                                                 */
    ALT_NAND_INT_STATUS_LOCKED_BLK              = (1 << 10),
                                                /*!< The address to program or
                                                 *   erase operation is to a
                                                 *   locked block and the
                                                 *   operation failed due to this
                                                 *   reason.
                                                 */
    ALT_NAND_INT_STATUS_PIPE_CPYBCK_CMD_COMP    = (1 << 9),
                                                /*!< A pipeline command or a
                                                 *   copyback bank command has
                                                 *   completed on this particular
                                                 *   bank.
                                                 */
    ALT_NAND_INT_STATUS_ERASE_COMP              = (1 << 8),
                                                /*!< Device erase operation
                                                 *   complete.
                                                 */
    ALT_NAND_INT_STATUS_PROGRAM_COMP            = (1 << 7),
                                                /*!< Device finished the last
                                                 *   issued program command.
                                                 */
    ALT_NAND_INT_STATUS_LOAD_COMP               = (1 << 6),
                                                /*!< Device finished the last
                                                 *   issued load command.
                                                 */
    ALT_NAND_INT_STATUS_ERASE_FAIL              = (1 << 5),
                                                /*!< Erase failure occurred in the
                                                 *   device on issuance of a erase
                                                 *   command. err_block_addr and
                                                 *   err_page_addr contain the
                                                 *   block address and page
                                                 *   address that failed erase
                                                 *   operation.
                                                 */
    ALT_NAND_INT_STATUS_PROGRAM_FAIL            = (1 << 4),
                                                /*!< Program failure occurred in
                                                 *   the device on issuance of a
                                                 *   program
                                                 *   command. err_block_addr and
                                                 *   err_page_addr contain the
                                                 *   block address and page
                                                 *   address that failed program
                                                 *   operation.
                                                 */
    ALT_NAND_INT_STATUS_TIME_OUT                = (1 << 3),
                                                /*!< Watchdog timer has triggered
                                                 *   in the controller due to one
                                                 *   of the reasons like device
                                                 *   not responding or controller
                                                 *   state machine did not get
                                                 *   back to idle.
                                                 */
    ALT_NAND_INT_STATUS_DMA_CMD_COMP            = (1 << 2),
                                                /*!< A data DMA command has
                                                 *   completed on this bank.
                                                 */
    ALT_NAND_INT_STATUS_ECC_UNCOR_ERR           = (1 << 0)
                                                /*!< ECC logic detected
                                                 *   uncorrectable error while
                                                 *   reading data from flash
                                                 *   device.
                                                 */
} ALT_NAND_INT_STATUS_t;

/*!
 * Returns the NAND flash controller interrupt status register value.
 *
 * This function returns the current value of the NAND flash controller interrupt
 * status register value which reflects the current NAND flash controller status
 * conditions.
 *
 * \returns The current value of the NAND flash controller interrupt status
 *              register value which reflects the current NAND flash controller
 *              status conditions as defined by the \ref ALT_NAND_INT_STATUS_t
 *              mask.  If the corresponding bit is set then the condition is
 *              asserted.
 */
uint32_t alt_nand_int_status_get(void);

/*!
 * Clears the specified NAND flash controller interrupt status conditions
 * identified in the mask.
 *
 * This function clears one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_NAND_IRQ interrupt signal state.
 *
 * \param       mask
 *              Specifies the QSPI interrupt status conditions to clear.  \e mask
 *              is a mask of logically OR'ed \ref ALT_NAND_INT_STATUS_t values
 *              that designate the status conditions to clear.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_nand_int_clear(const uint32_t mask);

/*!
 * Disable the specified NAND flash controller interrupt status conditions
 * identified in the mask.
 *
 * This function disables one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_NAND_IRQ interrupt signal state.
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have
 * the effect of enabling it as a contributor to the \b ALT_INT_INTERRUPT_NAND_IRQ
 * interrupt signal state. The function alt_nand_int_enable() is used to enable
 * status source conditions.
 *
 * \param       mask
 *              Specifies the status conditions to disable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed \ref
 *              ALT_NAND_INT_STATUS_t values that designate the status conditions
 *              to disable.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_nand_int_disable(const uint32_t mask);

/*!
 * Enable the specified NAND flash controller interrupt status conditions
 * identified in the mask.
 *
 * This function enables one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_NAND_IRQ interrupt signal state.
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have
 * the effect of disabling it as a contributor to the \b ALT_INT_INTERRUPT_NAND_IRQ 
 * interrupt signal state. The function alt_nand_int_disable() is used to disable 
 * status source conditions.
 *
 * \param       mask
 *              Specifies the status conditions to enable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed \ref
 *              ALT_NAND_INT_STATUS_t values that designate the status conditions
 *              to enable.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_nand_int_enable(const uint32_t mask);

/*!
 * Returns the number of planes in the flash memory device.
 *
 * Returns the number of planes as read from the device during discovery and
 * parameter configuration. For 512 byte devices this information typically has to
 * be manually programmed by software.
 *
 * \returns     The number of planes contained in the device.
 *
 * \internal
 * nandregs.config.number_of_planes
 * \endinternal
 */
uint32_t alt_nand_num_planes_get(void);

/*!
 * Returns the number of blocks in the flash memory device.
 *
 * Returns the number of blocks as read from the device during discovery and
 * parameter configuration. For 512 byte devices this information typically has to
 * be manually programmed by software.
 *
 * \returns     The number of blocks contained in the device.
 *
 * \internal
 * ???
 * \endinternal
 */
uint32_t alt_nand_num_blocks_get(void);

/*!
 * Returnes the number of pages per device block.
 *
 * Returns the number of pages per block as read from the device during discovery
 * and parameter configuration. For 512 byte devices this information typically
 * has to be manually programmed by software.
 *
 * \returns     The number of pages per device block.
 *
 * \internal
 * nandregs.config.pages_per_block
 * \endinternal
 */
uint32_t alt_nand_num_pages_per_block_get(void);

/*!
 * Returns the size of a page sector in bytes.
 *
 * Returns the size of a page sector in bytes as read from the device during
 * discovery and parameter configuration. For 512 byte devices this information
 * typically has to be manually programmed by software.
 *
 * \returns     Returns the size of a page sector in bytes.
 *
 * \internal
 * nandregs.config.device_main_area_size
 * \endinternal
 */
uint32_t alt_nand_sector_size_get(void);

/*!
 * Returns the size of a page spare area in bytes.
 *
 * Returns the size of a page spare area in bytes as read from the device during
 * discovery and parameter configuration. For 512 byte devices this information
 * typically has to be manually programmed by software.
 *
 * \returns     Returns the size of a page spare area in bytes.
 *
 * \internal
 * nandregs.config.device_spare_area_size
 * \endinternal
 */
uint32_t alt_nand_spare_size_get(void);

/*!
 * Returns \b true if the specified device block is bad otherwise returns \b
 * false.
 *
 * Returns \b true if the specified device block is marked defective
 * (i.e. bad) and should not be used. Otherwise the device block is assumed usable
 * and \b true is returned.
 *
 * \param       block_addr
 *              The block address to check.
 *
 * \returns     \b true if the specified device block is bad otherwise returns
 *              \b false.
 *
 * \internal
 * Uses the bad block table constructed by alt_nand_flash_init().
 * \endinternal
 */
bool alt_nand_block_is_bad(const uint32_t block_addr);

/*!
 * The ONFI Factory Defect Mapping defined value used by manufacturers to mark a
 * block as defective. A manufacturer marks defective blocks by setting at least
 * one byte in the spare area of the first or last page of the defective block to
 * a value of 0.
 */
#define ALT_NAND_BAD_BLOCK_MARKER               0

/*!
 * This type defines the data structure used to hold the bad block table.
 *
 * The table is an array composed of uint32_t elements. Each array element
 * contains the bad block status for 32 consecutive blocks on the flash
 * device. The array is of length <em>ceil( alt_nand_num_blocks_get() / 32 )</em>
 * elements.
 *
 * Each bit holds the defect status of a block in the device. The LSB bit position
 * of the first element of the array corressponds to the defect status of Block
 * 0. The MSB of the first element of the array corressponds to the defect status
 * of Block 31. The second element of the array contains the defect status of the
 * next 32 consecutive blocks of the device (Blocks 32-63) and so on.
 *
 * The following code fragment illustrates how the bad block table is used to
 * determine whether a particular block is bad or not:
 *
 * \code
 * #define ALT_NAND_GOOD_BLOCK_FLAG     0
 * #define ALT_NAND_BAD_BLOCK_FLAG      1
 *
 * block_is_bad = false;
 * block_table_index = block_number / 32;
 * block_bit_position = block_number % 32;
 * if ((( bad_block_table[block_table_index] >> block_bit_position) & 0x1) == ALT_NAND_BAD_BLOCK_FLAG)
 *     block_is_bad = true;
 * \endcode
 */
typedef uint32_t * alt_nand_bad_block_table_t;

/*!
 * Get a copy of the bad block table for the device.
 *
 * Returns a copy of the bad block table for the device in a user specified
 * buffer. The size and organization of the bad block table are described in \ref
 * alt_nand_bad_block_table_t.
 *
 * \param       bad_block_table
 *              [out] Pointer to a buffer of type alt_nand_bad_block_table_t to
 *              return a copy of the bad block table in.
 *
 * \param       bad_block_table_len
 *              The length of the \e bad_block_table parameter in number of
 *              elements.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 * \retval      ALT_E_BAD_ARG   The \e bad_block_table_len specifies a bad_block_table
 *                              length that is not large enough to hold a copy of
 *                              the bad block table for the device.
 *                              
 */
ALT_STATUS_CODE alt_nand_bad_block_table_get(alt_nand_bad_block_table_t bad_block_table,
                                             const uint32_t bad_block_table_len);




/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_NAND_FLASH_H__ */
