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

#ifndef __ALT_FPGA_MGR_H__
#define __ALT_FPGA_MGR_H__

#include "hwlib.h"
#include "alt_dma.h"
#include <stdio.h>

#ifdef __cplusplus
extern "C"
{
#endif /* __cplusplus */

/*!
 * \addtogroup FPGA_MGR The FPGA Manager
 *
 * This module defines the FPGA Manager API for accessing, configuring, and
 * controlling the FPGA fabric and the FPGA/HPS interface.
 *
 * @{
 */


/*!
 * This preprocessor definition determines if DMA support for FPGA programming
 * is enabled or not. Enabling DMA support enables the following API:
 *  * alt_fpga_configure_dma()
 *  * alt_fpga_istream_configure_dma()
 *
 * To enable DMA support, define ALT_FPGA_ENABLE_DMA_SUPPORT=1 in the Makefile.
 */
#ifndef ALT_FPGA_ENABLE_DMA_SUPPORT
#define ALT_FPGA_ENABLE_DMA_SUPPORT (0)
#endif

/*!
 * Initializes the FPGA manager. This should be the first API called when using
 * the FPGA manager API.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_fpga_init(void);

/*!
 * Uninitializes the FPGA manager
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_fpga_uninit(void);

/*!
 * \addtogroup FPGA_MGR_STATUS FPGA Manager Status and Control
 *
 * This group provides functions for controlling and determining status of the
 * FPGA Manager.
 *
 * @{
 */

/*!
 * Instructs the CPU core to acquire control of the FPGA control block. This
 * must API must be called before any other API is issued.
 *
 * \retval      ALT_E_SUCCESS       Successful status.
 * \retval      ALT_E_ERROR         Error acquiring control of the FPGA control
 *                                  block. This is likely due to another device
 *                                  on the system controlling the FPGA control
 *                                  block or a repeat call to this API without
 *                                  first being released.
 */
ALT_STATUS_CODE alt_fpga_control_enable(void);

/*!
 * Instructs the CPU core to release control of the FPGA control block. This
 * API should be called after all FPGA related operations are completed. This
 * will allow another device on the system to configure the FPGA.
 *
 * \retval      ALT_E_SUCCESS       Successful status.
 * \retval      ALT_E_ERROR         Failure status.
 */
ALT_STATUS_CODE alt_fpga_control_disable(void);

/*!
 * Returns \b true if the HPS currently has control of the FPGA control block
 * and \b false otherwise.
 *
 * \retval      true                HPS has control of the FPGA control block.
 * \retval      false               HPS does not have control of the FPGA
 *                                  control block.
 */
bool alt_fpga_control_is_enabled(void);

/*!
 * This type definition enumerates the possible states the FPGA can be in at
 * any one time.
 */
typedef enum ALT_FPGA_STATE_e
{
    /*!
     * FPGA in Power Up Phase. This is the state of the FPGA just after
     * powering up.
     *
     * \internal
     * Register documentation calls it "PWR_OFF" which is really a misnomer as
     * the FPGA is powered as evident from alt_fpga_mon_status_get() and
     * looking at the ALT_FPGA_MON_FPGA_POWER_ON bit.
     * \endinternal
     */
    ALT_FPGA_STATE_POWER_UP = 0x0,

    /*!
     * FPGA in Reset Phase. In this phase, the FPGA resets, clears the FPGA
     * configuration RAM bits, tri-states all FPGA user I/O pins, pulls the
     * nSTATUS and CONF_DONE pins low, and determines the configuration mode
     * by reading the value of the MSEL pins.
     */
    ALT_FPGA_STATE_RESET = 0x1,

    /*!
     * FPGA in Configuration Phase. This state represents the phase when the
     * configuration bitstream is loaded into the FPGA fabric. The
     * configuration phase is complete after the FPGA has received all the
     * configuration data.
     */
    ALT_FPGA_STATE_CFG = 0x2,

    /*!
     * FPGA in Initialization Phase. In this state the FPGA prepares to enter
     * User Mode. In Configuration via PCI Express (CVP), this state indicates
     * I/O configuration has completed.
     */
    ALT_FPGA_STATE_INIT = 0x3,

    /*!
     * FPGA in User Mode. In this state, the FPGA performs the function loaded
     * during the configuration phase. The FPGA user I/O are functional as
     * determined at design time.
     */
    ALT_FPGA_STATE_USER_MODE = 0x4,

    /*!
     * FPGA state has not yet been determined. This only occurs briefly after
     * reset.
     */
    ALT_FPGA_STATE_UNKNOWN = 0x5,

    /*!
     * FPGA is powered off.
     *
     * \internal
     * This is a software only state which is determined by
     * alt_fpga_mon_status_get() and looking at the ALT_FPGA_MON_FPGA_POWER_ON
     * bit. The hardware register sourced for ALT_FPGA_STATE_t is only 3 bits
     * wide so this will never occur in hardware.
     * \endinternal
     */
    ALT_FPGA_STATE_POWER_OFF = 0xF

} ALT_FPGA_STATE_t;

/*!
 * Returns the current operational state of the FPGA fabric.
 *
 * \returns     The current operational state of the FPGA.
 */
ALT_FPGA_STATE_t alt_fpga_state_get(void);

/*!
 * This type definition enumerates the monitored status conditions for the FPGA
 * Control Block (CB).
 */
typedef enum ALT_FPGA_MON_STATUS_e
{
    /*!
     * 0 if the FPGA is in Reset Phase or if the FPGA detected an error during
     * the Configuration Phase.
     */
    ALT_FPGA_MON_nSTATUS = 0x0001,

    /*!
     * 0 during the FPGA Reset Phase and 1 when the FPGA Configuration Phase is
     * done.
     */
    ALT_FPGA_MON_CONF_DONE = 0x0002,

    /*!
     * 0 during the FPGA Configuration Phase and 1 when the FPGA Initialization
     * Phase is done.
     */
    ALT_FPGA_MON_INIT_DONE = 0x0004,

    /*!
     * CRC error indicator. A 1 indicates that the FPGA detected a CRC error
     * while in User Mode.
     */
    ALT_FPGA_MON_CRC_ERROR = 0x0008,

    /*!
     * Configuration via PCIe (CVP) Done indicator. A 1 indicates that CVP is
     * done.
     */
    ALT_FPGA_MON_CVP_CONF_DONE = 0x0010,

    /*!
     * Partial Reconfiguration ready indicator. A 1 indicates that the FPGA is
     * ready to receive partial reconfiguration or external scrubbing data.
     */
    ALT_FPGA_MON_PR_READY = 0x0020,

    /*!
     * Partial Reconfiguration error indicator. A 1 indicates that the FPGA
     * detected an error during partial reconfiguration or external scrubbing.
     */
    ALT_FPGA_MON_PR_ERROR = 0x0040,

    /*!
     * Partial Reconfiguration done indicator. A 1 indicates partial
     * reconfiguration or external scrubbing is done.
     */
    ALT_FPGA_MON_PR_DONE = 0x0080,

    /*!
     * Value of the nCONFIG pin. This can be pulled-down by the FPGA in this
     * device or logic external to this device connected to the nCONFIG pin.
     * See the description of the nCONFIG field in this register to understand
     * when the FPGA in this device pulls-down the nCONFIG pin. Logic external
     * to this device pulls-down the nCONFIG pin to put the FPGA into the Reset
     * Phase.
     */
    ALT_FPGA_MON_nCONFIG_PIN = 0x0100,

    /*!
     * Value of the nSTATUS pin. This can be pulled-down by the FPGA in this
     * device or logic external to this device connected to the nSTATUS pin.
     * See the description of the nSTATUS field in this register to understand
     * when the FPGA in this device pulls-down the nSTATUS pin. Logic external
     * to this device pulls-down the nSTATUS pin during Configuration Phase or
     * Initialization Phase if it detected an error.
     */
    ALT_FPGA_MON_nSTATUS_PIN = 0x0200,

    /*!
     * Value of the CONF_DONE pin. This can be pulled-down by the FPGA in this
     * device or logic external to this device connected to the CONF_DONE pin.
     * See the description of the CONF_DONE field in this register to
     * understand when the FPGA in this device pulls-down the CONF_DONE pin.
     * See FPGA documentation to determine how logic external to this device
     * drives CONF_DONE.
     */
    ALT_FPGA_MON_CONF_DONE_PIN = 0x0400,

    /*!
     * FPGA powered on indicator.
     */
    ALT_FPGA_MON_FPGA_POWER_ON = 0x0800,

} ALT_FPGA_MON_STATUS_t;

/*!
 * Returns the FPGA Control Block monitor status conditions.
 *
 * This function returns the current value of the FPGA Control Block monitor
 * status conditions.
 *
 * \returns     The current values of the FPGA Control Block monitor status
 *              conditions as defined by the \ref ALT_FPGA_MON_STATUS_t mask
 *              bits. If the corresponding bit is set then the condition is
 *              asserted.
 *
 * \internal
 * Use the Raw Interrupt Status Register \b hps::fpgamgrregs::mon::gpio_ext_porta
 * to retrieve the monitor status conditions.
 * \endinternal
 */
uint32_t alt_fpga_mon_status_get(void);

/*!
 * Assert and hold the FPGA in reset.
 *
 * This function asserts and holds the FPGA in reset. Any FPGA configuration is
 * cleared. The FPGA must be reconfigured to resume operation.
 * 
 * The FPGA is reset by the assertion of the nCONFIG signal. The signal remains
 * asserted until alt_fgpa_reset_deassert() is called.
 *
 * \retval      ALT_E_SUCCESS           Successful status.
 * \retval      ALT_E_FPGA_PWR_OFF      FPGA is not powered on.
 * \retval      ALT_E_FPGA_NO_SOC_CTRL  SoC software is not in control of the
 *                                      FPGA. Use alt_fpga_control_enable() to
 *                                      gain control.
 */
ALT_STATUS_CODE alt_fgpa_reset_assert(void);

/*!
 * Deassert and release the FPGA from reset.
 *
 * This function deasserts the FPGA from reset. The FPGA must be reconfigured to
 * resume operation.
 * 
 * The FPGA is reset by the deassertion of the nCONFIG signal. 
 *
 * \retval      ALT_E_SUCCESS           Successful status.
 * \retval      ALT_E_FPGA_PWR_OFF      FPGA is not powered on.
 * \retval      ALT_E_FPGA_NO_SOC_CTRL  SoC software is not in control of the
 *                                      FPGA. Use alt_fpga_control_enable() to
 *                                      gain control.
 */
ALT_STATUS_CODE alt_fgpa_reset_deassert(void);

/*!
 * @}
 */

/*!
 * \addtogroup FPGA_MGR_CFG FPGA Configuration
 *
 * This functional group provides the following services:
 *  * Determination of the FPGA configuration mode.
 *  * Software control for full configuration of the FPGA.
 *  * Software control for partial reconfiguration of the FPGA \e (Future).
 *
 * @{
 */

/*!
 * This type definition enumerates the available modes for configuring the
 * FPGA.
 */
typedef enum ALT_FPGA_CFG_MODE_e
{
    /*!
     * 16-bit Passive Parallel with Fast Power on Reset Delay; No AES
     * Encryption; No Data Compression. CDRATIO must be programmed to x1.
     */
    ALT_FPGA_CFG_MODE_PP16_FAST_NOAES_NODC = 0x0,

    /*!
     * 16-bit Passive Parallel with Fast Power on Reset Delay; With AES
     * Encryption; No Data Compression. CDRATIO must be programmed to x4.
     */
    ALT_FPGA_CFG_MODE_PP16_FAST_AES_NODC = 0x1,

    /*!
     * 16-bit Passive Parallel with Fast Power on Reset Delay; AES Optional;
     * With Data Compression. CDRATIO must be programmed to x8.
     */
    ALT_FPGA_CFG_MODE_PP16_FAST_AESOPT_DC = 0x2,

    /*!
     * 16-bit Passive Parallel with Slow Power on Reset Delay; No AES
     * Encryption; No Data Compression. CDRATIO must be programmed to x1.
     */
    ALT_FPGA_CFG_MODE_PP16_SLOW_NOAES_NODC = 0x4,

    /*!
     * 16-bit Passive Parallel with Slow Power on Reset Delay; With AES
     * Encryption; No Data Compression. CDRATIO must be programmed to x4.
     */
    ALT_FPGA_CFG_MODE_PP16_SLOW_AES_NODC = 0x5,

    /*!
     * 16-bit Passive Parallel with Slow Power on Reset Delay; AES Optional;
     * With Data Compression. CDRATIO must be programmed to x8.
     */
    ALT_FPGA_CFG_MODE_PP16_SLOW_AESOPT_DC = 0x6,

    /*!
     * 32-bit Passive Parallel with Fast Power on Reset Delay; No AES
     * Encryption; No Data Compression. CDRATIO must be programmed to x1.
     */
    ALT_FPGA_CFG_MODE_PP32_FAST_NOAES_NODC = 0x8,

    /*!
     * 32-bit Passive Parallel with Fast Power on Reset Delay; With AES
     * Encryption; No Data Compression. CDRATIO must be programmed to x4.
     */
    ALT_FPGA_CFG_MODE_PP32_FAST_AES_NODC = 0x9,

    /*!
     * 32-bit Passive Parallel with Fast Power on Reset Delay; AES Optional;
     * With Data Compression. CDRATIO must be programmed to x8.
     */
    ALT_FPGA_CFG_MODE_PP32_FAST_AESOPT_DC = 0xa,

    /*!
     * 32-bit Passive Parallel with Slow Power on Reset Delay; No AES
     * Encryption; No Data Compression. CDRATIO must be programmed to x1.
         */
    ALT_FPGA_CFG_MODE_PP32_SLOW_NOAES_NODC = 0xc,

    /*!
     * 32-bit Passive Parallel with Slow Power on Reset Delay; With AES
     * Encryption; No Data Compression. CDRATIO must be programmed to x4.
     */
    ALT_FPGA_CFG_MODE_PP32_SLOW_AES_NODC = 0xd,

    /*!
     * 32-bit Passive Parallel with Slow Power on Reset Delay; AES Optional;
     * With Data Compression. CDRATIO must be programmed to x8.
     */
    ALT_FPGA_CFG_MODE_PP32_SLOW_AESOPT_DC = 0xe,

    /*!
     * Unknown FPGA Configuration Mode.
     */
    ALT_FPGA_CFG_MODE_UNKNOWN = 0x20,

} ALT_FPGA_CFG_MODE_t;

/*!
 * Gets the FPGA configuration mode currently in effect.
 *
 * Presently, the FPGA configuration mode is statically set by the external MSEL
 * pin values and cannot be programmatically overridden by HPS software.
 *
 * \returns     The current FPGA configuration mode as determined by the MSEL
 *              pin values.
 */
ALT_FPGA_CFG_MODE_t alt_fpga_cfg_mode_get(void);

/*!
 * Sets the FPGA configuration mode.
 *
 * Presently, the FPGA configuration mode is statically set by the external
 * MSEL pin values and cannot be programmatically overridden by HPS software.
 * This function should always return ALT_E_ERROR at least for Hammerhead-P.
 * This may change with future SoCFPGA devices.
 *
 * \param       cfg_mode
 *              The desired FPGA configuration mode.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Failed to set the FPGA configuration mode.
 *
 * \internal
 * This should set the fpgamgrregs::stat::msel. The full configuration reads
 * this to program the fpgamgrregs::ctrl with the appropriate parameters
 * decoded from msel.
 * \endinternal
 */
ALT_STATUS_CODE alt_fpga_cfg_mode_set(ALT_FPGA_CFG_MODE_t cfg_mode);

/*!
 * Type definition for the callback function prototype used by the FPGA Manager
 * to read configuration bitstream data from a user defined input source
 * stream.
 *
 * The purpose of this callback function declaration is to provide a prototype
 * for a user defined method of sequentially reading FPGA configuration
 * bitstream data from an arbitrary input source. Example input sources include
 * a file resident on a file system, a network stream socket, or a fixed
 * address block in flash memory. The only requirement on the input source is
 * that it is capable of supplying consecutive blocks of data of the requested
 * size from the FPGA configuration bitstream as demanded by the FPGA Manager.
 *
 * During FPGA configuration, the FPGA Manager periodically calls the user
 * defined callback function to fetch the next \e buf_len consecutive
 * configuration data bytes from the user defined input stream. The callback
 * function fills the FPGA Manager supplied buffer \e buf with up to the next
 * \e buf_len bytes of configuration bitsteam data as read from the input
 * source stream. The callback function returns the number of configuration
 * bytes read into \e buf or 0 upon reaching the end of the configuration
 * bitstream data.
 *
 * If an error occurs on the configuration bitstream input source, then the
 * callback function should return an error code value less than 0.
 *
 * \param       buf
 *              A pointer to a buffer to fill with FPGA configuration bitstream
 *              data bytes.
 *
 * \param       buf_len
 *              The length of the input buffer \e buf in bytes. The number of
 *              FPGA configuration bitstream data bytes copied into \e buf
 *              should not exceed \e buf_len.
 *
 * \param       user_data
 *              A 32-bit data word for passing user defined data. The content
 *              of this parameter is user defined. The FPGA Manager merely
 *              forwards the \e user_data value when it invokes the callback.
 * 
 * \retval      >0      The number of bytes returned in buf.
 * \retval      =0      The end of the input stream has been reached.
 * \retval      <0      An error occurred on the input stream.
 */
typedef int32_t (*alt_fpga_istream_t)(void* buf, size_t buf_len, void* user_data);

/*!
 * \addtogroup FPGA_MGR_CFG_FULL FPGA Full Configuration
 *
 * These functions manage full configuration of the FPGA fabric from HPS
 * software.
 *
 * @{
 */

/*!
 * Perform a full configuration of the FPGA from the specified configuration
 * bitstream located in addressable memory.
 *
 * Due to the nature of FPGA configuration, there may be intermittent and
 * recoverable errors during the process. When the API returns ALT_E_FPGA_CFG,
 * it is advisable to retry configuration up to 5 times. If the error still
 * persists, there may be an unrecoverable configuration error or a problem
 * with configuration image bitstream data.
 *
 * \internal
 * Source: FPGA Manager NPP, section 4.2.1.3 "Error handling and corrupted
 * configuration file"
 * \endinternal
 *
 * \param       cfg_buf
 *              A pointer to a buffer containing FPGA configuration bitstream
 *              data.
 *
 * \param       cfg_buf_len
 *              The length of the configuration bitstream data in bytes.
 *
 * \retval      ALT_E_SUCCESS           FPGA configuration was successful.
 * \retval      ALT_E_FPGA_CFG          FPGA configuration error detected.
 * \retval      ALT_E_FPGA_CRC          FPGA CRC error detected.
 * \retval      ALT_E_FPGA_PWR_OFF      FPGA is not powered on.
 * \retval      ALT_E_FPGA_NO_SOC_CTRL  SoC software is not in control of the
 *                                      FPGA. Use alt_fpga_control_enable() to
 *                                      gain control.
 */
ALT_STATUS_CODE alt_fpga_configure(const void* cfg_buf,
                                   size_t cfg_buf_len);

#if ALT_FPGA_ENABLE_DMA_SUPPORT

/*!
 * Perform a full configuration of the FPGA from the specified configuration
 * bitstream located in addressable memory using the DMA engine. Using DMA can
 * have a large performance benefit in FPGA programming time.
 *
 * Due to the nature of FPGA configuration, there may be intermittent and
 * recoverable errors during the process. When the API returns ALT_E_FPGA_CFG,
 * it is advisable to retry configuration up to 5 times. If the error still
 * persists, there may be an unrecoverable configuration error or a problem
 * with configuration image bitstream data.
 *
 * \internal
 * Source: FPGA Manager NPP, section 4.2.1.3 "Error handling and corrupted
 * configuration file"
 * \endinternal
 *
 * \param       cfg_buf
 *              A pointer to a buffer containing FPGA configuration bitstream
 *              data.
 *
 * \param       cfg_buf_len
 *              The length of the configuration bitstream data in bytes.
 *
 * \retval      ALT_E_SUCCESS           FPGA configuration was successful.
 * \retval      ALT_E_FPGA_CFG          FPGA configuration error detected.
 * \retval      ALT_E_FPGA_CRC          FPGA CRC error detected.
 * \retval      ALT_E_FPGA_PWR_OFF      FPGA is not powered on.
 * \retval      ALT_E_FPGA_NO_SOC_CTRL  SoC software is not in control of the
 *                                      FPGA. Use alt_fpga_control_enable() to
 *                                      gain control.
 * \retval      ALT_E_BAD_ARG           The user provided buffer is unaligned
 *                                      to the 32-bit boundary.
 */

ALT_STATUS_CODE alt_fpga_configure_dma(const void* cfg_buf,
                                       size_t cfg_buf_len,
                                       ALT_DMA_CHANNEL_t dma_channel);

#endif

/*!
 * Perform a full configuration of the FPGA from the user defined configuration
 * bitstream input source.
 *
 * Due to the nature of FPGA configuration, there may be intermittent and
 * recoverable errors during the process. When the API returns ALT_E_FPGA_CFG,
 * it is advisable to retry configuration up to 5 times. If the error still
 * persists, there may be an unrecoverable configuration error or a problem
 * with configuration image bitstream data.
 *
 * \internal
 * Source: FPGA Manager NPP, section 4.2.1.3 "Error handling and corrupted
 * configuration file"
 * \endinternal
 *
 * \param       cfg_stream
 *              A pointer to a callback function used to consecutively read
 *              configuration bitstream data from a user defined input stream.
 * 
 * \param       user_data
 *              A 32-bit user defined data word. The content of this parameter
 *              is user defined. The FPGA Manager merely forwards the \e
 *              user_data value when it invokes the \e cfg_stream callback.
 *
 * \retval      ALT_E_SUCCESS           FPGA configuration FPGA was successful.
 * \retval      ALT_E_FPGA_CFG          FPGA configuration error detected.
 * \retval      ALT_E_FPGA_CRC          FPGA CRC error detected.
 * \retval      ALT_E_FPGA_CFG_STM      An error occurred on the FPGA
 *                                      configuration bitstream input source.
 * \retval      ALT_E_FPGA_PWR_OFF      FPGA is not powered on.
 * \retval      ALT_E_FPGA_NO_SOC_CTRL  SoC software is not in control of the
 *                                      FPGA. Use alt_fpga_control_enable() to
 *                                      gain control.
 */
ALT_STATUS_CODE alt_fpga_istream_configure(alt_fpga_istream_t cfg_stream,
                                           void * user_data);

#if ALT_FPGA_ENABLE_DMA_SUPPORT

/*!
 * Perform a full configuration of the FPGA from the user defined configuration
 * bitstream input source using the DMA engine. Using DMA can have a large
 * performance benefit in FPGA programming time.
 *
 * Due to the nature of FPGA configuration, there may be intermittent and
 * recoverable errors during the process. When the API returns ALT_E_FPGA_CFG,
 * it is advisable to retry configuration up to 5 times. If the error still
 * persists, there may be an unrecoverable configuration error or a problem
 * with configuration image bitstream data.
 *
 * \internal
 * Source: FPGA Manager NPP, section 4.2.1.3 "Error handling and corrupted
 * configuration file"
 * \endinternal
 *
 * \param       cfg_stream
 *              A pointer to a callback function used to consecutively read
 *              configuration bitstream data from a user defined input stream.
 * 
 * \param       user_data
 *              A 32-bit user defined data word. The content of this parameter
 *              is user defined. The FPGA Manager merely forwards the \e
 *              user_data value when it invokes the \e cfg_stream callback.
 *
 * \retval      ALT_E_SUCCESS           FPGA configuration FPGA was successful.
 * \retval      ALT_E_FPGA_CFG          FPGA configuration error detected.
 * \retval      ALT_E_FPGA_CRC          FPGA CRC error detected.
 * \retval      ALT_E_FPGA_CFG_STM      An error occurred on the FPGA
 *                                      configuration bitstream input source.
 * \retval      ALT_E_FPGA_PWR_OFF      FPGA is not powered on.
 * \retval      ALT_E_FPGA_NO_SOC_CTRL  SoC software is not in control of the
 *                                      FPGA. Use alt_fpga_control_enable() to
 *                                      gain control.
 * \retval      ALT_E_BAD_ARG           The user provided buffer is unaligned
 *                                      to the 32-bit boundary.
 */
ALT_STATUS_CODE alt_fpga_istream_configure_dma(alt_fpga_istream_t cfg_stream,
                                               void * user_data,
                                               ALT_DMA_CHANNEL_t dma_channel);

#endif

/*!
 * @}
 */

/*!
 * @}
 */

/*!
 * \addtogroup FPGA_MGR_INT FPGA Manager Interrupt Control
 *
 * The functions in this group provide management of interrupts originating
 * from the FPGA Manager.
 *
 * The following interrupt request (IRQ) signal is sourced from the FPGA
 * Manager:
 *
 * * \b fpga_man_IRQ - FPGA Manager control block interrupt output. Provides
 *                     monitoring of the configuration and operational status
 *                     of the FPGA.  The interrupt signal assertion value is
 *                     the logical \e OR of twelve sources that monitor the
 *                     status of the FPGA control block (CB).  The twelve FPGA
 *                     CB interrupt sources are enumerated and described by the
 *                     type \ref ALT_FPGA_MON_STATUS_t.
 *
 *                     Each FPGA monitor status condition may be individually
 *                     disabled/enabled as a contributor to the determination
 *                     of the \b fpga_man_IRQ assertion status.
 *
 *                     The \b fpga_man_IRQ and its contributing FPGA monitor
 *                     status conditions are treated as a level sensitive
 *                     interrupt. As as consequence, there are no explicit
 *                     functions to explicitly clear an asserted FPGA monitor
 *                     status conditions.
 *
 * @{
 */

/*!
 * Disable the \b fpga_man_IRQ interrupt signal source monitor status
 * condition(s).
 *
 * This function disables one or more of the monitor status conditions as
 * contributors to the \b fpga_man_IRQ interrupt signal state.
 *
 * NOTE: A set bit for a monitor status condition in the mask value does not
 * have the effect of enabling it as a contributor to the \b fpga_man_IRQ
 * interrupt signal state. The function alt_fpga_man_irq_enable() is used to
 * enable monitor status source condition(s).
 *
 * \param       mon_stat_mask
 *              Specifies the monitor status conditions to disable as interrupt
 *              source contributors. \e mon_stat_mask is a mask of logically
 *              OR'ed ALT_FPGA_MON_STATUS_t values that designate the monitor
 *              status conditions to disable.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_BAD_ARG   The \e mon_stat_mask argument contains an
 *                              unknown monitor status value.
 */
ALT_STATUS_CODE alt_fpga_man_irq_disable(ALT_FPGA_MON_STATUS_t mon_stat_mask);

/*!
 * Enable the \b fpga_man_IRQ interrupt signal source monitor status
 * condition(s).
 *
 * This function enables one or more of the monitor status conditions as
 * contributors to the \b fpga_man_IRQ interrupt signal state.
 *
 * NOTE: A cleared bit for any monitor status condition in the mask value does
 * not have the effect of disabling it as a contributor to the \b fpga_man_IRQ
 * interrupt signal state. The function alt_fpga_man_irq_disable() is used to
 * disable monitor status source condition(s).
 *
 * \param       mon_stat_mask
 *              Specifies the monitor status conditions to enable as interrupt
 *              source contributors. \e mon_stat_mask is a mask of logically
 *              OR'ed ALT_FPGA_MON_STATUS_t values that designate the monitor
 *              conditions to enable.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_BAD_ARG   The \e mon_stat_mask argument contains an
 *                              unknown monitor status value.
 */
ALT_STATUS_CODE alt_fpga_man_irq_enable(ALT_FPGA_MON_STATUS_t mon_stat_mask);

/*!
 * @}
 */

/*!
 * \addtogroup FPGA_MGR_GPIO SoC to FPGA General Purpose I/O Signals
 *
 * These functions provide a simple, low-latency, low-performance signal
 * interface between the SoC and the FPGA.  There is a General Purpose Output
 * (GPO) register that provides a path to drive up to 32 signals from the SoC
 * to the FPGA.  There is a General Purpose Input (GPI) register that provides
 * a path to read up to 32 signals driven from the FPGA to the SoC.
 *
 * @{
 */

/*!
 * This type definition enumerates the signal mask selections for the General
 * Purpose Input (GPI) signals driven from the FPGA to the SoC.
 */
typedef enum ALT_FPGA_GPI_e
{
    /*! Signal driven from the FPGA fabric on f2s_gp[0] */
    ALT_FPGA_GPI_0  = (int32_t)(1UL <<  0),

    /*! Signal driven from the FPGA fabric on f2s_gp[1] */
    ALT_FPGA_GPI_1  = (int32_t)(1UL <<  1),

    /*! Signal driven from the FPGA fabric on f2s_gp[2] */
    ALT_FPGA_GPI_2  = (int32_t)(1UL <<  2),

    /*! Signal driven from the FPGA fabric on f2s_gp[3] */
    ALT_FPGA_GPI_3  = (int32_t)(1UL <<  3),

    /*! Signal driven from the FPGA fabric on f2s_gp[4] */
    ALT_FPGA_GPI_4  = (int32_t)(1UL <<  4),

    /*! Signal driven from the FPGA fabric on f2s_gp[5] */
    ALT_FPGA_GPI_5  = (int32_t)(1UL <<  5),

    /*! Signal driven from the FPGA fabric on f2s_gp[6] */
    ALT_FPGA_GPI_6  = (int32_t)(1UL <<  6),

    /*! Signal driven from the FPGA fabric on f2s_gp[7] */
    ALT_FPGA_GPI_7  = (int32_t)(1UL <<  7),

    /*! Signal driven from the FPGA fabric on f2s_gp[8] */
    ALT_FPGA_GPI_8  = (int32_t)(1UL <<  8),

    /*! Signal driven from the FPGA fabric on f2s_gp[9] */
    ALT_FPGA_GPI_9  = (int32_t)(1UL <<  9),

    /*! Signal driven from the FPGA fabric on f2s_gp[10] */
    ALT_FPGA_GPI_10 = (int32_t)(1UL << 10),

    /*! Signal driven from the FPGA fabric on f2s_gp[11] */
    ALT_FPGA_GPI_11 = (int32_t)(1UL << 11),

    /*! Signal driven from the FPGA fabric on f2s_gp[12] */
    ALT_FPGA_GPI_12 = (int32_t)(1UL << 12),

    /*! Signal driven from the FPGA fabric on f2s_gp[13] */
    ALT_FPGA_GPI_13 = (int32_t)(1UL << 13),

    /*! Signal driven from the FPGA fabric on f2s_gp[14] */
    ALT_FPGA_GPI_14 = (int32_t)(1UL << 14),

    /*! Signal driven from the FPGA fabric on f2s_gp[15] */
    ALT_FPGA_GPI_15 = (int32_t)(1UL << 15),

    /*! Signal driven from the FPGA fabric on f2s_gp[16] */
    ALT_FPGA_GPI_16 = (int32_t)(1UL << 16),

    /*! Signal driven from the FPGA fabric on f2s_gp[17] */
    ALT_FPGA_GPI_17 = (int32_t)(1UL << 17),

    /*! Signal driven from the FPGA fabric on f2s_gp[18] */
    ALT_FPGA_GPI_18 = (int32_t)(1UL << 18),

    /*! Signal driven from the FPGA fabric on f2s_gp[19] */
    ALT_FPGA_GPI_19 = (int32_t)(1UL << 19),

    /*! Signal driven from the FPGA fabric on f2s_gp[20] */
    ALT_FPGA_GPI_20 = (int32_t)(1UL << 20),

    /*! Signal driven from the FPGA fabric on f2s_gp[21] */
    ALT_FPGA_GPI_21 = (int32_t)(1UL << 21),

    /*! Signal driven from the FPGA fabric on f2s_gp[22] */
    ALT_FPGA_GPI_22 = (int32_t)(1UL << 22),

    /*! Signal driven from the FPGA fabric on f2s_gp[23] */
    ALT_FPGA_GPI_23 = (int32_t)(1UL << 23),

    /*! Signal driven from the FPGA fabric on f2s_gp[24] */
    ALT_FPGA_GPI_24 = (int32_t)(1UL << 24),

    /*! Signal driven from the FPGA fabric on f2s_gp[25] */
    ALT_FPGA_GPI_25 = (int32_t)(1UL << 25),

    /*! Signal driven from the FPGA fabric on f2s_gp[26] */
    ALT_FPGA_GPI_26 = (int32_t)(1UL << 26),

    /*! Signal driven from the FPGA fabric on f2s_gp[27] */
    ALT_FPGA_GPI_27 = (int32_t)(1UL << 27),

    /*! Signal driven from the FPGA fabric on f2s_gp[28] */
    ALT_FPGA_GPI_28 = (int32_t)(1UL << 28),

    /*! Signal driven from the FPGA fabric on f2s_gp[29] */
    ALT_FPGA_GPI_29 = (int32_t)(1UL << 29),

    /*! Signal driven from the FPGA fabric on f2s_gp[30] */
    ALT_FPGA_GPI_30 = (int32_t)(1UL << 30),

    /*! Signal driven from the FPGA fabric on f2s_gp[31] */
    ALT_FPGA_GPI_31 = (int32_t)(1UL << 31)

} ALT_FPGA_GPI_t;

/*!
 * Reads the General Purpose Input (GPI) register value.
 *
 * Returns the GPI register value that is the masked selection of the 32 \b
 * f2s_gp signal values driven by the FPGA. The \e mask may be defined by the
 * logical OR of \ref ALT_FPGA_GPI_t values.
 *
 * NOTE: If the FPGA is not in User Mode then the value of this register
 *       undefined.
 *
 * \param       mask
 *              The set of signals (where mask bits equal one) to read.  Other
 *              signals values (where mask bits equal zero) are returned as 0.
 *
 * \returns     Returns the GPI register value that is the masked selection of
 *              the 32 \b f2s_gp signals from the FPGA.
 */
uint32_t alt_fpga_gpi_read(uint32_t mask);

/*!
 * This type definition enumerates the signal mask selections for the General
 * Purpose Output (GPO) signals driven from the SoC to the FPGA.
 */
typedef enum ALT_FPGA_GPO_e
{
    /*! Signal driven from the FPGA fabric on s2f_gp[0] */
    ALT_FPGA_GPO_0  = (int32_t)(1UL <<  0),

    /*! Signal driven from the FPGA fabric on s2f_gp[1] */
    ALT_FPGA_GPO_1  = (int32_t)(1UL <<  1),

    /*! Signal driven from the FPGA fabric on s2f_gp[2] */
    ALT_FPGA_GPO_2  = (int32_t)(1UL <<  2),

    /*! Signal driven from the FPGA fabric on s2f_gp[3] */
    ALT_FPGA_GPO_3  = (int32_t)(1UL <<  3),

    /*! Signal driven from the FPGA fabric on s2f_gp[4] */
    ALT_FPGA_GPO_4  = (int32_t)(1UL <<  4),

    /*! Signal driven from the FPGA fabric on s2f_gp[5] */
    ALT_FPGA_GPO_5  = (int32_t)(1UL <<  5),

    /*! Signal driven from the FPGA fabric on s2f_gp[6] */
    ALT_FPGA_GPO_6  = (int32_t)(1UL <<  6),

    /*! Signal driven from the FPGA fabric on s2f_gp[7] */
    ALT_FPGA_GPO_7  = (int32_t)(1UL <<  7),

    /*! Signal driven from the FPGA fabric on s2f_gp[8] */
    ALT_FPGA_GPO_8  = (int32_t)(1UL <<  8),

    /*! Signal driven from the FPGA fabric on s2f_gp[9] */
    ALT_FPGA_GPO_9  = (int32_t)(1UL <<  9),

    /*! Signal driven from the FPGA fabric on s2f_gp[10] */
    ALT_FPGA_GPO_10 = (int32_t)(1UL << 10),

    /*! Signal driven from the FPGA fabric on s2f_gp[11] */
    ALT_FPGA_GPO_11 = (int32_t)(1UL << 11),

    /*! Signal driven from the FPGA fabric on s2f_gp[12] */
    ALT_FPGA_GPO_12 = (int32_t)(1UL << 12),

    /*! Signal driven from the FPGA fabric on s2f_gp[13] */
    ALT_FPGA_GPO_13 = (int32_t)(1UL << 13),

    /*! Signal driven from the FPGA fabric on s2f_gp[14] */
    ALT_FPGA_GPO_14 = (int32_t)(1UL << 14),

    /*! Signal driven from the FPGA fabric on s2f_gp[15] */
    ALT_FPGA_GPO_15 = (int32_t)(1UL << 15),

    /*! Signal driven from the FPGA fabric on s2f_gp[16] */
    ALT_FPGA_GPO_16 = (int32_t)(1UL << 16),

    /*! Signal driven from the FPGA fabric on s2f_gp[17] */
    ALT_FPGA_GPO_17 = (int32_t)(1UL << 17),

    /*! Signal driven from the FPGA fabric on s2f_gp[18] */
    ALT_FPGA_GPO_18 = (int32_t)(1UL << 18),

    /*! Signal driven from the FPGA fabric on s2f_gp[19] */
    ALT_FPGA_GPO_19 = (int32_t)(1UL << 19),

    /*! Signal driven from the FPGA fabric on s2f_gp[20] */
    ALT_FPGA_GPO_20 = (int32_t)(1UL << 20),

    /*! Signal driven from the FPGA fabric on s2f_gp[21] */
    ALT_FPGA_GPO_21 = (int32_t)(1UL << 21),

    /*! Signal driven from the FPGA fabric on s2f_gp[22] */
    ALT_FPGA_GPO_22 = (int32_t)(1UL << 22),

    /*! Signal driven from the FPGA fabric on s2f_gp[23] */
    ALT_FPGA_GPO_23 = (int32_t)(1UL << 23),

    /*! Signal driven from the FPGA fabric on s2f_gp[24] */
    ALT_FPGA_GPO_24 = (int32_t)(1UL << 24),

    /*! Signal driven from the FPGA fabric on s2f_gp[25] */
    ALT_FPGA_GPO_25 = (int32_t)(1UL << 25),

    /*! Signal driven from the FPGA fabric on s2f_gp[26] */
    ALT_FPGA_GPO_26 = (int32_t)(1UL << 26),

    /*! Signal driven from the FPGA fabric on s2f_gp[27] */
    ALT_FPGA_GPO_27 = (int32_t)(1UL << 27),

    /*! Signal driven from the FPGA fabric on s2f_gp[28] */
    ALT_FPGA_GPO_28 = (int32_t)(1UL << 28),

    /*! Signal driven from the FPGA fabric on s2f_gp[29] */
    ALT_FPGA_GPO_29 = (int32_t)(1UL << 29),

    /*! Signal driven from the FPGA fabric on s2f_gp[30] */
    ALT_FPGA_GPO_30 = (int32_t)(1UL << 30),

    /*! Signal driven from the FPGA fabric on s2f_gp[31] */
    ALT_FPGA_GPO_31 = (int32_t)(1UL << 31)

} ALT_FPGA_GPO_t;

/*!
 * Writes the General Purpose Output (GPO) register value.
 *
 * Writes the GPO data outputs with the specified values. The GPO drives the 32
 * \b s2f_gp signal values to the FPGA. Output signals are only written if
 * their corresponding mask bits are set.
 *
 * NOTE: If the FPGA is not in User Mode then the effect of this operation is 
 *       undefined.
 *
 * \param       mask
 *              The set of signals (where mask bits equal one) to write.  Other
 *              signals (where mask bits equal zero) are not changed. The \e
 *              mask may be defined by the logical OR of \ref ALT_FPGA_GPO_t
 *              values.
 *
 * \param       value
 *              The 32-bit aggregate GPO register value. Values for the
 *              corressponding signal bits specified in the \e mask are written
 *              to the FPGA signals.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     The write failed.
 */
ALT_STATUS_CODE alt_fpga_gpo_write(uint32_t mask, uint32_t value);

/*!
 * @}
 */

/*!
 * @}
 */

#ifdef __cplusplus
}
#endif  /* __cplusplus */

#endif  /* __ALT_FPGA_MGR_H__ */
