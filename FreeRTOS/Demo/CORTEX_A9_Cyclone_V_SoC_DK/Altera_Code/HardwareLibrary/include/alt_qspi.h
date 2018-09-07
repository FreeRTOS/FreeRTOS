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

/******************************************************************************
* 
* !!!! Customer Be Aware, Exception!!!
*
* 1. Qspi Direct Access Mode is not working!
*
*    This is because the qspi flash memory installed on our DevKit board, Micro 
*    part N25Q00xx, 8 Gb, is not completely compatible with our embedded Synopsis 
*    QSPI controller IP. Therefore there is no viable direct access code offered
*    in the lib.  All the memory rea/write functionality is offered with indirect
*    access only.   
*
*    Should you install a different flash memory part in your custom board, and 
*    wondering wether direct access mode works, please contact with us.
* 
******************************************************************************/

/*! \file
 *  Altera - QSPI Flash Controller Module
 */

#ifndef __ALT_QSPI_H__
#define __ALT_QSPI_H__

#include "hwlib.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/******************************************************************************/
/*! \addtogroup ALT_QSPI QSPI Flash Controller Module
 *
 * This module defines a low level driver API for the hardware processor system
 * (HPS) quad serial peripheral interface (QSPI) flash controller for access to
 * serial NOR flash devices. The quad SPI flash controller supports standard SPI
 * flash devices as well as high-performance dual and quad SPI flash
 * devices.
 *
 * @{
 */

/******************************************************************************/
/*! \addtogroup ALT_QSPI_CSR General Control and Status Functions
 *
 * The declarations and functions in this group provide general purpose control
 * and status functions for the QSPI Flash Controller.
 *
 * @{
 */

/******************************************************************************/
/*!
 * Initialize the QSPI flash controller for use.
 *
 * \internal
 * Implementation Notes:
 *  * The QSPI Controller has been designed to wake up in a state that is
 *    suitable for performing basic reads and writes using the direct access
 *    controller.
 *  * Bring out of reset
 *  * QSPI reference clock validation
 *  * See Programmer's Guide, Configuring the QSPI Controller for use after
 *    reset, in QSPI_FLASH_CTRL for full initialization details.
 * \endinternal
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_init(void);

/******************************************************************************/
/*!
 * Uninitialize the QSPI flash controller.
 *
 * Uninitialize the QSPI flash controller by cancelling any indirect transfers
 * in progress and putting the QSPI controller into reset.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_uninit(void);

/******************************************************************************/
/*!
 * Disable the QSPI Controller.
 *
 * Disable the QSPI once the current transfer of the data word (FF_W) is
 * complete. All output enables are inactive and all pins are set to input 
 * mode.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_disable(void);

/******************************************************************************/
/*!
 * Enable the QSPI Controller.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_enable(void);

/******************************************************************************/
/*!
 * This type definition enumerates the interrupt status conditions for the QSPI
 * controller.
 *
 * The enumerations serve as masks for the QSPI controller events that can be
 * set when the designated conditions occur and the corresponding event is
 * enabled.  When any of these event source conditions are true, the \b
 * ALT_INT_INTERRUPT_QSPI_IRQ interrupt output is asserted high.
 *
 * Interrupt sources are cleared when software calls alt_qspi_int_clear(). The
 * interrupt sources are individually maskable using alt_qspi_int_disable() and
 * alt_qspi_int_enable().
 */
typedef enum ALT_QSPI_INT_STATUS_e
{
    /*!
     * Mode fail M - indicates the voltage on pin n_ss_in is inconsistent with
     * the SPI mode. Set = 1 if n_ss_in is low in master mode (multi-master
     * contention). These conditions will clear the spi_enable bit and disable
     * the SPI.
     *  * 0 = no mode fault has been detected.
     *  * 1 = a mode fault has occurred.
     */
    ALT_QSPI_INT_STATUS_MODE_FAIL         = (0x1 << 0),

    /*!
     * Underflow Detected.
     *  * 0 = no underflow has been detected.
     *  * 1 = underflow is detected and an attempt to transfer data is made
     *        when the small TX FIFO is empty. This may occur when AHB write
     *        data is being supplied too slowly to keep up with the requested
     *        write operation.
     */
    ALT_QSPI_INT_STATUS_UFL               = (0x1 << 1),

    /*!
     * Controller has completed last triggered indirect operation.
     */
    ALT_QSPI_INT_STATUS_IDAC_OP_COMPLETE  = (0x1 << 2),

    /*!
     * Indirect operation was requested but could not be accepted. Two indirect
     * operations already in storage.
     */
    ALT_QSPI_INT_STATUS_IDAC_OP_REJECT    = (0x1 << 3),

    /*!
     * Write to protected area was attempted and rejected.
     */
    ALT_QSPI_INT_STATUS_WR_PROT_VIOL      = (0x1 << 4),

    /*!
     * Illegal AHB Access Detected. AHB write wrapping bursts and the use of
     * SPLIT/RETRY accesses will cause this interrupt to trigger.
     */
    ALT_QSPI_INT_STATUS_ILL_AHB_ACCESS    = (0x1 << 5),

    /*!
     * Indirect Transfer Watermark Level Breached.
     */
    ALT_QSPI_INT_STATUS_IDAC_WTRMK_TRIG   = (0x1 << 6),

    /*!
     * Receive Overflow. This should only occur in Legacy SPI mode.
     *
     * Set if an attempt is made to push the RX FIFO when it is full. This bit
     * is reset only by a system reset and cleared only when this register is
     * read. If a new push to the RX FIFO occurs coincident with a register read
     * this flag will remain set.
     *  * 0 = no overflow has been detected.
     *  * 1 = an overflow has occurred.
     */
    ALT_QSPI_INT_STATUS_RX_OVF            = (0x1 << 7),

    /*!
     * Small TX FIFO not full (current FIFO status). Can be ignored in non-SPI
     * legacy mode.
     *  * 0 = FIFO has >= THRESHOLD entries.
     *  * 1 = FIFO has < THRESHOLD entries.
     */
    ALT_QSPI_INT_STATUS_TX_FIFO_NOT_FULL  = (0x1 << 8),

    /*!
     * Small TX FIFO full (current FIFO status). Can be ignored in non-SPI
     * legacy mode.
     *  * 0 = FIFO is not full.
     *  * 1 = FIFO is full.
     */
    ALT_QSPI_INT_STATUS_TX_FIFO_FULL      = (0x1 << 9),

    /*!
     * Small RX FIFO not empty (current FIFO status). Can be ignored in non-SPI
     * legacy mode.
     *  * 0 = FIFO has < RX THRESHOLD entries.
     *  * 1 = FIFO has >= THRESHOLD entries.
     */
    ALT_QSPI_INT_STATUS_RX_FIFO_NOT_EMPTY = (0x1 << 10),

    /*!
     * Small RX FIFO full (current FIFO status). Can be ignored in non-SPI
     * legacy mode.
     *  * 0 = FIFO is not full.
     *  * 1 = FIFO is full.
     */
    ALT_QSPI_INT_STATUS_RX_FIFO_FULL      = (0x1 << 11),

    /*!
     * Indirect Read partition of SRAM is full and unable to immediately
     * complete indirect operation.
     */
    ALT_QSPI_INT_STATUS_IDAC_RD_FULL      = (0x1 << 12)

} ALT_QSPI_INT_STATUS_t;

/******************************************************************************/
/*!
 * Returns the QSPI controller interrupt status register value.
 *
 * This function returns the current value of the QSPI controller interrupt
 * status register value which reflects the current QSPI controller status
 * conditions.
 *
 * \returns     The current value of the QSPI controller interrupt status
 *              register value which reflects the current QSPI controller status
 *              conditions as defined by the \ref ALT_QSPI_INT_STATUS_t mask.
 *              If the corresponding bit is set then the condition is asserted.
 */
uint32_t alt_qspi_int_status_get(void);

/******************************************************************************/
/*!
 * Clears the specified QSPI controller interrupt status conditions identified
 * in the mask.
 *
 * This function clears one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_QSPI_IRQ interrupt signal state.
 *
 * \param       mask
 *              Specifies the QSPI interrupt status conditions to clear.  \e
 *              mask is a mask of logically OR'ed \ref ALT_QSPI_INT_STATUS_t
 *              values that designate the status conditions to clear.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_int_clear(const uint32_t mask);

/******************************************************************************/
/*!
 * Disable the specified QSPI controller interrupt status conditions identified
 * in the mask.
 *
 * This function disables one or more of the status conditions as contributors
 * to the \b ALT_INT_INTERRUPT_QSPI_IRQ interrupt signal state.
 *
 * This API requires that the QSPI controller be idle, as determined by
 * alt_qspi_is_idle().
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have
 * the effect of enabling it as a contributor to the \b
 * ALT_INT_INTERRUPT_QSPI_IRQ interrupt signal state. The function
 * alt_qspi_int_enable() is used to enable status source conditions.
 *
 * \param       mask
 *              Specifies the status conditions to disable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed
 *              \ref ALT_QSPI_INT_STATUS_t values that designate the status
 *              conditions to disable.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_int_disable(const uint32_t mask);

/******************************************************************************/
/*!
 * Enable the specified QSPI controller interrupt status conditions identified
 * in the mask.
 *
 * This function enables one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_QSPI_IRQ interrupt signal state.
 *
 * This API requires that the QSPI controller be idle, as determined by
 * alt_qspi_is_idle().
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have
 * the effect of disabling it as a contributor to the \b
 * ALT_INT_INTERRUPT_QSPI_IRQ interrupt signal state. The function
 * alt_qspi_int_disable() is used to disable status source conditions.
 *
 * \param       mask
 *              Specifies the status conditions to enable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed
 *              \ref ALT_QSPI_INT_STATUS_t values that designate the status
 *              conditions to enable.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_int_enable(const uint32_t mask);

/******************************************************************************/
/*!
 * Returns true the serial interface and QSPI pipeline is IDLE.
 *
 * \returns     Returns true the serial interface and QSPI pipeline is IDLE.
 */
bool alt_qspi_is_idle(void);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_QSPI_GP_BLKIO General Purpose Block I/O
 *
 * The functions in this group provide general purpose block read and
 * write flash functions.
 *
 * \internal
 * These functions use Indirect Read/Write transfers to read and write block
 * data to the flash device. An outline of the operational flow for these
 * operations can be found in:
 * //depot/soc/hhp_sw/baremetal_fw/drivers/qspi/qspi.c
 * 
 * The general flow for an indirect block read is to call
 * qspi_configure_mode_indirect_read_start() to initiate the read transfer from
 * the flash device into the SRAM buffer and follow with a call to either
 * qpsi_write_sram_fifo_poll() or qspi_read_sram_fifo_irq() to copy the data
 * from SRAM into the user's buffer.
 * 
 * The general flow for an indirect block write is to call
 * qspi_configure_mode_indirect_write_start() to initiate the write transfer
 * from the SRAM buffer to the flash device and follow with a call to either
 * qpsi_write_sram_fifo_poll() or qspi_write_sram_fifo_irq() to fill the SRAM
 * buffer with the user's data as space becomes available.
 * \endinternal
 *
 * @{
 */

/******************************************************************************/
/*!
 * Read a block of data from the specified flash address.
 *
 * Reads a block of \e n data bytes from the flash \e src address into the user
 * supplied \e dest buffer. The memory address, flash address, and size must be
 * word aligned.
 *
 * \param       dest
 *              The address of a caller supplied destination buffer large enough
 *              to contain the requested block of flash data.
 *
 * \param       src
 *              The flash device address to start reading data from.
 *
 * \param       size
 *              The requested number of data bytes to read from the flash device.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_read(void * dest, uint32_t src, size_t size);

/******************************************************************************/
/*!
 * Write a block of data to the specified flash address.
 *
 * Writes a block of \e n data bytes to the flash \e dest address from the
 * designated \e src buffer. The applicable destination flash address range
 * should have been erased prior to calling this function. The flash address,
 * memory address, and size must be word aligned.
 *
 * \param       dest
 *              The destination flash address to begin writing data to.
 *
 * \param       src
 *              The source address to start writing data from.
 *
 * \param       size
 *              The requested number of data bytes to write to the flash device.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_write(uint32_t dest, const void * src, size_t size);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_QSPI_DEV_CFG Flash Device Configuration
 *
 * The declarations and functions in this group are used to configure the QSPI
 * controller interface to external flash devices.
 *
 * The following steps describe how to initialize and configure the
 * QSPI controller to operate with a flash device.
 *
 * * Wait until any pending QSPI operations have completed.
 * * Disable the QSPI controller using alt_qspi_disable().
 * * Configure the device for optimal read transaction performance using
 *   alt_qspi_device_read_config_set().
 * * Configure the device for optimal write transaction performance using
 *   alt_qspi_device_write_config_set().
 * * Enable (alt_qspi_mode_bit_disable()) or disable
 *   (alt_qspi_mode_bit_disable()) the mode bits per the device
 *   requirements. If mode bits are enabled, then configure the mode
 *   bit values using alt_qspi_mode_bit_config_set().
 * * Configure the device size and write protection information using
 *   alt_qspi_device_size_config_set().
 * * Configure the QSPI device delay and timing settings using
 *   alt_qspi_device_write_config_set().
 * * Configure the baud divisor setting to define the required clock frequency
 *   to the device using alt_qspi_baud_rate_div_set().
 * * Enable the QSPI controller using alt_qspi_enable().
 *
 * @{
 */

/******************************************************************************/
/*!
 * This type enumerates the operational modes the QSPI controller can be
 * configured for. It may apply to instruction, address, and/or data width
 * interactions between the QSPI controller and the flash device.
 */
typedef enum ALT_QSPI_MODE_e
{
  ALT_QSPI_MODE_SINGLE = 0,     /*!< Use Standard Single SPI (SIO-SPI) mode (bits 
                                 *   always transferred into the device on DQ0 
                                 *   only). Supported by all SPI flash devices.
                                 */
  ALT_QSPI_MODE_DUAL   = 1,     /*!< Use Dual SPI (DIO-SPI) SPI mode where bits are
                                 *   transferred on DQ0 and DQ1.
                                 */
  ALT_QSPI_MODE_QUAD   = 2      /*!< Use Dual SPI (QIO-SPI) SPI mode where bits are
                                 *   transferred on DQ0, DQ1, DQ3, and DQ3.
                                 */
} ALT_QSPI_MODE_t;

/******************************************************************************/
/*!
 * This type enumerates the mode configurations available for driving the
 * ss_n[3:0] device chip selects.  The chip selects may be controlled as either
 * in a '1 of 4' or '4 to 16 decode' mode.
 */
typedef enum ALT_QSPI_CS_MODE_e
{
  ALT_QSPI_CS_MODE_SINGLE_SELECT = 0,   /*!< Select 1 of 4 chip select ss_n[3:0]
                                         */
  ALT_QSPI_CS_MODE_DECODE        = 1    /*!< Select external 4 to 16 decode of
                                         *   ss_n[3:0].
                                         */
} ALT_QSPI_CS_MODE_t;

/******************************************************************************/
/*!
 * This type enumerates the QSPI controller master baud rate divisor selections.
 */
typedef enum ALT_QSPI_BAUD_DIV_e
{
  ALT_QSPI_BAUD_DIV_2            = 0x0, /*!< Divide by 2 */
  ALT_QSPI_BAUD_DIV_4            = 0x1, /*!< Divide by 4 */
  ALT_QSPI_BAUD_DIV_6            = 0x2, /*!< Divide by 6 */
  ALT_QSPI_BAUD_DIV_8            = 0x3, /*!< Divide by 8 */
  ALT_QSPI_BAUD_DIV_10           = 0x4, /*!< Divide by 10 */
  ALT_QSPI_BAUD_DIV_12           = 0x5, /*!< Divide by 12 */
  ALT_QSPI_BAUD_DIV_14           = 0x6, /*!< Divide by 14 */
  ALT_QSPI_BAUD_DIV_16           = 0x7, /*!< Divide by 16 */
  ALT_QSPI_BAUD_DIV_18           = 0x8, /*!< Divide by 18 */
  ALT_QSPI_BAUD_DIV_20           = 0x9, /*!< Divide by 20 */
  ALT_QSPI_BAUD_DIV_22           = 0xA, /*!< Divide by 22 */
  ALT_QSPI_BAUD_DIV_24           = 0xB, /*!< Divide by 24 */
  ALT_QSPI_BAUD_DIV_26           = 0xC, /*!< Divide by 26 */
  ALT_QSPI_BAUD_DIV_28           = 0xD, /*!< Divide by 28 */
  ALT_QSPI_BAUD_DIV_30           = 0xE, /*!< Divide by 30 */
  ALT_QSPI_BAUD_DIV_32           = 0xF  /*!< Divide by 32 */
} ALT_QSPI_BAUD_DIV_t;

/******************************************************************************/
/*!
 * Device Size Configuration
 *
 * This type defines the structure used to specify flash device size and write
 * protect regions.
 */
typedef struct ALT_QSPI_DEV_SIZE_CONFIG_s
{
  uint32_t      block_size;         /*!< Number of bytes per device block. The
                                     *   number is specified as a power of 2.
                                     *   That is 0 = 1 byte, 1 = 2 bytes, ...
                                     *   16 = 65535 bytes, etc.
                                     */
  uint32_t      page_size;          /*!< Number of bytes per device page.  This
                                     *   is required by the controller for
                                     *   performing flash writes up to and
                                     *   across page boundaries.
                                     */
  uint32_t      addr_size;          /*!< Number of bytes used for the flash
                                     *   address. The value is \e n + 1
                                     *   based. That is 0 = 1 byte, 1 = 2 bytes,
                                     *   2 = 3 bytes, 3 = 4 bytes.
                                     */
  uint32_t      lower_wrprot_block; /*!< The block number that defines the lower
                                     *   block in the range of blocks that is
                                     *   protected from writing. This field
                                     *   is ignored it write protection is 
                                     *   disabled.
                                     */
  uint32_t      upper_wrprot_block; /*!< The block number that defines the upper
                                     *   block in the range of blocks that is
                                     *   protected from writing. This field
                                     *   is ignored it write protection is 
                                     *   disabled.
                                     */
  bool          wrprot_enable;      /*!< The write region enable value. A value
                                     *   of \b true enables write protection
                                     *   on the region specified by the
                                     *   \e lower_wrprot_block and
                                     *   \e upper_wrprot_block range.
                                     */
} ALT_QSPI_DEV_SIZE_CONFIG_t;

/******************************************************************************/
/*!
 * This type enumerates the QSPI clock phase activity options outside the SPI
 * word.
 */
typedef enum ALT_QSPI_CLK_PHASE_e
{
  ALT_QSPI_CLK_PHASE_ACTIVE     = 0,    /*!< The SPI clock is active outside the
                                         *   word
                                         */
  ALT_QSPI_CLK_PHASE_INACTIVE   = 1     /*!< The SPI clock is inactive outside the
                                         *   word
                                         */
} ALT_QSPI_CLK_PHASE_t;

/******************************************************************************/
/*!
 * This type enumerates the QSPI clock polarity options outside the SPI word.
 */
typedef enum ALT_QSPI_CLK_POLARITY_e
{
  ALT_QSPI_CLK_POLARITY_LOW     = 0,    /*!< SPI clock is quiescent low outside the
                                         *   word.
                                         */
  ALT_QSPI_CLK_POLARITY_HIGH    = 1     /*!< SPI clock is quiescent high outside the
                                         *   word.
                                         */
} ALT_QSPI_CLK_POLARITY_t;

/******************************************************************************/
/*!
 * QSPI Controller Timing Configuration
 *
 * This type defines the structure used to configure timing paramaters used by
 * the QSPI controller to communicate with a target flash device.
 *
 * All timing values are defined in cycles of the SPI master ref clock.
 */
typedef struct ALT_QSPI_TIMING_CONFIG_s
{
  ALT_QSPI_CLK_PHASE_t      clk_phase;  /*!< Selects whether the clock is in an
                                         *   active or inactive phase outside the
                                         *   SPI word.
                                         */

  ALT_QSPI_CLK_POLARITY_t   clk_pol;    /*!< Selects whether the clock is quiescent
                                         *   low or high outside the SPI word.
                                         */

  uint32_t                  cs_da;      /*!< Chip Select De-Assert. Added delay in
                                         *   master reference clocks for the length
                                         *   that the master mode chip select
                                         *   outputs are de-asserted between
                                         *   transactions. If CSDA = \e X, then the
                                         *   chip select de-assert time will be: 1
                                         *   sclk_out + 1 ref_clk + \e X ref_clks.
                                         */
  uint32_t                  cs_dads;    /*!< Chip Select De-Assert Different
                                         *   Slaves. Delay in master reference
                                         *   clocks between one chip select being
                                         *   de-activated and the activation of
                                         *   another. This is used to ensure a quiet
                                         *   period between the selection of two
                                         *   different slaves.  CSDADS is only
                                         *   relevant when switching between 2
                                         *   different external flash devices. If
                                         *   CSDADS = \e X, then the delay will be:
                                         *   1 sclk_out + 3 ref_clks + \e X
                                         *   ref_clks.
                                         */
  uint32_t                  cs_eot;     /*!< Chip Select End Of Transfer. Delay in
                                         *   master reference clocks between last
                                         *   bit of current transaction and
                                         *   de-asserting the device chip select
                                         *   (n_ss_out). By default (when CSEOT=0),
                                         *   the chip select will be de-asserted on
                                         *   the last falling edge of sclk_out at
                                         *   the completion of the current
                                         *   transaction. If CSEOT = \e X, then chip
                                         *   selected will de-assert \e X ref_clks
                                         *   after the last falling edge of
                                         *   sclk_out.
                                         */
  uint32_t                  cs_sot;     /*!< Chip Select Start Of Transfer. Delay in
                                         *   master reference clocks between setting
                                         *   n_ss_out low and first bit transfer. By
                                         *   default (CSSOT=0), chip select will be
                                         *   asserted half a SCLK period before the
                                         *   first rising edge of sclk_out. If CSSOT
                                         *   = \e X, chip select will be asserted
                                         *   half an sclk_out period before the
                                         *   first rising edge of sclk_out + \e X
                                         *   ref_clks.
                                         */

  uint32_t                  rd_datacap; /*!< The additional number of read data
                                         *   capture cycles (ref_clk) that should be
                                         *   applied to the internal read data
                                         *   capture circuit.  The large
                                         *   clock-to-out delay of the flash memory
                                         *   together with trace delays as well as
                                         *   other device delays may impose a
                                         *   maximum flash clock frequency which is
                                         *   less than the flash memory device
                                         *   itself can operate at. To compensate,
                                         *   software should set this register to a
                                         *   value that guarantees robust data
                                         *   captures.
                                         */
} ALT_QSPI_TIMING_CONFIG_t;

/******************************************************************************/
/*!
 * Device Instruction Configuration
 *
 * This type defines a structure for specifying the optimal instruction set
 * configuration to use with a target flash device.
 */
typedef struct ALT_QSPI_DEV_INST_CONFIG_s
{
  uint32_t              op_code;            /*!< The read or write op code to use
                                             *   for the device transaction.
                                             */
  ALT_QSPI_MODE_t       inst_type;          /*!< Instruction mode type for the
                                             *   controller to use with the
                                             *   device. The instruction type
                                             *   applies to all instructions
                                             *   (reads and writes) issued from
                                             *   either the Direct Access
                                             *   Controller or the Indirect
                                             *   Acces Controller.
                                             */
  ALT_QSPI_MODE_t       addr_xfer_type;     /*!< Address transfer mode type. The
                                             *   value of this field is ignored
                                             *   if the \e inst_type data member
                                             *   is set to anything other than
                                             *   ALT_QSPI_MODE_SINGLE. In that
                                             *   case, the addr_xfer_type
                                             *   assumes the same mode as the \e
                                             *   inst_type.
                                             */
  ALT_QSPI_MODE_t       data_xfer_type;     /*!< Data transfer mode type. The
                                             *   value of this field is ignored
                                             *   if the \e inst_type data member
                                             *   is set to anything other than
                                             *   ALT_QSPI_MODE_SINGLE. In that
                                             *   case, the data_xfer_type
                                             *   assumes the same mode as the \e
                                             *   inst_type.
                                             */
  uint32_t              dummy_cycles;       /*!< Number of dummy clock cycles
                                             *   required by device for a read
                                             *   or write instruction.
                                             */

} ALT_QSPI_DEV_INST_CONFIG_t;

/******************************************************************************/
/*!
 * Get the current value of the QSPI master baud rate divisor.
 *
 * \returns     The value of the QSPI master baud rate divisor.
 */
ALT_QSPI_BAUD_DIV_t alt_qspi_baud_rate_div_get(void);

/******************************************************************************/
/*!
 * Set the current value of the QSPI master baud rate divisor.
 *
 * Sets the value of the QSPI master baud rate divisor.
 *
 * \param       baud_rate_div
 *              The master baud rate divisor. Valid range includes
 *              even values 2 to 32.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_baud_rate_div_set(const ALT_QSPI_BAUD_DIV_t baud_rate_div);

/******************************************************************************/
/*!
 * Get the current QSPI device peripheral chip select output and decode function
 * configuration values.
 *
 * \param       cs
 *              [out] The chip select line output values.
 *
 * \param       cs_mode
 *              [out] The decode mode to use for the chip selects.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_chip_select_config_get(uint32_t* cs, ALT_QSPI_CS_MODE_t* cs_mode);

/******************************************************************************/
/*!
 * Set the QSPI device peripheral chip select outputs and decode function
 * configuration.
 *
 * The chip select lines output values operate according to the selected chip
 * select decode mode. If \e cs_mode is ALT_QSPI_CS_MODE_SINGLE_SELECT then
 * cs[3:0] are output thus:
 *
 *  cs[3:0]  | n_ss_out[3:0]
 * :---------|:----------------------------
 *  xxx0     | 1110
 *  xx01     | 1101
 *  x011     | 1011
 *  0111     | 0111
 *  1111     | 1111 (no peripheral selected)
 *
 * Otherwise if \e cs_mode is ALT_QSPI_CS_MODE_DECODE then cs[3:0] directly
 * drives n_ss_out[3:0].
 *
 * \param       cs
 *              The chip select line output values.
 *
 * \param       cs_mode
 *              The decode mode to use for the chip selects.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_chip_select_config_set(const uint32_t cs,
                                                const ALT_QSPI_CS_MODE_t cs_mode);

/******************************************************************************/
/*!
 * Disable the mode bits from being sent after the address bytes.
 *
 * Prevent the mode bits defined in the Mode Bit Configuration register from
 * being sent following the address bytes.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_mode_bit_disable(void);

/******************************************************************************/
/*!
 * Enable the mode bits to be sent after the address bytes.
 *
 * Ensure the mode bits defined in the Mode Bit Configuration register to
 * be sent following the address bytes.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_mode_bit_enable(void);

/******************************************************************************/
/*!
 * Get the current value of the Mode Bit Configuration register.
 *
 * \returns     The 8 bit value that is sent to the device following the address
 *              bytes when the mode bit is enabled (see: alt_qspi_mode_bit_enable())
 */
uint32_t alt_qspi_mode_bit_config_get(void);

/******************************************************************************/
/*!
 * Set the value of the Mode Bit Configuration register.
 *
 * Set the value of the 8 bits that are sent to the device following the address
 * bytes when the mode bit is enabled (see: alt_qspi_mode_bit_enable())
 *
 * This API requires that the QSPI controller be idle, as determined by
 * alt_qspi_is_idle().
 *
 * \param       mode_bits
 *              The 8 bit value sent to the device following the address bytes.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_mode_bit_config_set(const uint32_t mode_bits);

/******************************************************************************/
/*!
 * Get the current flash device size and write protection configuration.
 *
 * \param       cfg
 *              [out] Pointer to a ALT_QSPI_DEV_SIZE_CONFIG_t structure to
 *              contain the returned flash device size and write protection
 *              configuration.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_device_size_config_get(ALT_QSPI_DEV_SIZE_CONFIG_t * cfg);

/******************************************************************************/
/*!
 * Set the flash device size and write protection configuration.
 *
 * \param       cfg
 *              Pointer to a ALT_QSPI_DEV_SIZE_CONFIG_t structure containing the
 *              flash device size and write protection configuration.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_device_size_config_set(const ALT_QSPI_DEV_SIZE_CONFIG_t * cfg);

/******************************************************************************/
/*!
 * Get the current QSPI device read instruction configuration.
 *
 * \param       cfg
 *              [out] Pointer to a ALT_QSPI_DEV_INST_CONFIG_t structure to
 *              contain the returned QSPI controller instruction configuration
 *              used when performing read transactions with the device.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_device_read_config_get(ALT_QSPI_DEV_INST_CONFIG_t * cfg);

/******************************************************************************/
/*!
 * Set the QSPI device read instruction configuration.
 *
 * This API requires that the QSPI controller be idle, as determined by
 * alt_qspi_is_idle().
 *
 * \param       cfg
 *              Pointer to a ALT_QSPI_DEV_INST_CONFIG_t structure specifying the
 *              desired op code, transfer widths, and dummy cycles for the QSPI
 *              controller to use when performing read transactions with the
 *              device.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_device_read_config_set(const ALT_QSPI_DEV_INST_CONFIG_t * cfg);

/******************************************************************************/
/*!
 * Get the current QSPI device write instruction configuration.
 *
 * \param       cfg
 *              [out] Pointer to a ALT_QSPI_DEV_INST_CONFIG_t structure to
 *              contain the returned QSPI controller instruction configuration
 *              used when performing write transactions with the device.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_device_write_config_get(ALT_QSPI_DEV_INST_CONFIG_t * cfg);

/******************************************************************************/
/*!
 * Set the QSPI device write instruction configuration.
 *
 * This API requires that the QSPI controller be idle, as determined by
 * alt_qspi_is_idle().
 *
 * \param       cfg
 *              Pointer to a ALT_QSPI_DEV_INST_CONFIG_t structure specifying the
 *              desired op code, transfer widths, and dummy cycles for the QSPI
 *              controller to use when performing write transactions with the
 *              device.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_device_write_config_set(const ALT_QSPI_DEV_INST_CONFIG_t * cfg);

/******************************************************************************/
/*!
 * Get the QSPI device delay and timing configuration parameters.
 *
 * This function returns the settings of the chip select delay and timing
 * configurations.
 *
 * \param       cfg
 *              [out] Pointer to a ALT_QSPI_TIMING_CONFIG_t structure to return
 *              the device timing and delay settings.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_timing_config_get(ALT_QSPI_TIMING_CONFIG_t * cfg);

/******************************************************************************/
/*!
 * Set the QSPI device delay and timing configuration parameters.
 *
 * This function allows the user to configure how the chip select is driven
 * after each flash access. This is required as each device may have different
 * timing requirements.  As the serial clock frequency is increased, these
 * timing parameters become more important and can be adjusted to meet the
 * requirements of a specific flash device.  All timings are defined in cycles
 * of the SPI master ref clock.
 *
 * This API requires that the QSPI controller be idle, as determined by
 * alt_qspi_is_idle().
 *
 * \param       cfg
 *              Pointer to a ALT_QSPI_TIMING_CONFIG_t structure specifying the
 *              desired timing and delay settings.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_timing_config_set(const ALT_QSPI_TIMING_CONFIG_t * cfg);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_QSPI_DAC Direct Access Mode
 *
 * In direct access mode, an access to the AHB data slave triggers a read or
 * write command to the flash memory. To use the direct access mode, enable the
 * direct access controller with the alt_qspi_direct_enable() function. An
 * external master, for example a processor, triggers the direct access
 * controller with a read or write operation to the AHB data slave
 * interface. The data slave exposes a 1MB window into the flash device. You can
 * remap this window to any 1MB location within the flash device address range.
 *
 * To remap the AHB data slave to access other 1MB regions of the flash device,
 * enable address remapping by calling alt_qspi_ahb_address_remap_enable(). All
 * incoming data slave accesses remap to the offset specified in the remap
 * address register which is configured by alt_qspi_ahb_remap_address_set().
 *
 * The 20 LSBs of incoming addresses are used for accessing the 1MB region and
 * the higher bits are ignored.
 *
 * The quad SPI controller does not issue any error status for accesses that lie
 * outside the connected flash memory space.
 *
 * @{
 */

/******************************************************************************/
/*!
 * Disable the QSPI Direct Access Controller.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_direct_disable(void);

/******************************************************************************/
/*!
 * Enable the QSPI Direct Access Controller.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_direct_enable(void);

/******************************************************************************/
/*!
 * Get the current AHB address remap value.
 *
 * Returns the current value of the AHB remap address register.
 *
 * \returns     The value used to remap an incoming AHB address to a
 *              different address used by the flash device.
 */
uint32_t alt_qspi_ahb_remap_address_get(void);

/******************************************************************************/
/*!
 * Set the AHB address remap value.
 *
 * Sets the value of the AHB remap address register.
 *
 * This API requires that the QSPI controller be idle, as determined by
 * alt_qspi_is_idle().
 *
 * \param       ahb_remap_addr
 *              The value used to remap an incoming AHB address to a different
 *              address used by the flash device.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_ahb_remap_address_set(const uint32_t ahb_remap_addr);

/******************************************************************************/
/*!
 * Disable AHB address remapping.
 *
 * Disables remapping of incoming AHB addresses so they are sent unmodified to
 * the flash device. The incoming AHB address maps directly to the address
 * serially sent to the flash device.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_ahb_address_remap_disable(void);

/******************************************************************************/
/*!
 * Enable AHB address remapping.
 *
 * Enables remapping of incoming AHB addresses so they are modified to 
 * \<address\> + \e N, where \e N is the configured remap address value. 
 *
 * See: alt_qspi_ahb_remap_address_set().
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_ahb_address_remap_enable(void);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_QSPI_INDAC Indirect Access Mode
 *
 * In indirect access mode, flash data is temporarily buffered in the QSPI
 * controller's SRAM. Software controls and triggers indirect accesses through
 * the APB register slave interface. The controller transfers data through the
 * AHB data slave interface.
 *
 * An indirect read operation reads data from the flash memory, places the data
 * into the SRAM, and transfers the data to an external master through the AHB
 * data slave interface.
 *
 * An indirect write operation programs data from the SRAM to the flash memory.
 *
 * @{
 */

/******************************************************************************/
/*!
 * Starts an indirect read transfer.
 *
 * Initiates an indirect read transfer of the requested number of bytes from the
 * designated flash address.
 *
 * After calling this function, flash data may be read from the QSPI SRAM buffer
 * as it becomes available via one of the following methods:
 *  * Directly from the AHB data slave interface at the configured AHB trigger
 *    address. If the requested data is not immediately available in the SRAM
 *    buffer then AHB wait states will be applied until the data has been read
 *    from flash into the SRAM buffer. Alternatively, data may be read from the
 *    AHB data slave as the SRAM is filled. The availability of data in the SRAM
 *    buffer may be determined by an SRAM watermark interrupt notification or by
 *    polling the SRAM fill level.
 *  * Configuring and enabling the QSPI DMA peripheral controller.
 *
 * The following is a list of restrictions:
 *  * flash_addr must be word aligned.
 *  * num_bytes must be word aligned.
 *  * The transfer must not cross the 3-byte addressing boundary. This
 *    restriction may be device specific and may be lifted in the future.
 *
 * \param       flash_addr
 *              The flash source address to read data from.
 *
 * \param       num_bytes
 *              The number of bytes to read from the flash source address.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_indirect_read_start(const uint32_t flash_addr,
                                             const size_t num_bytes);

/******************************************************************************/
/*!
 * Finish the indirect read operation that was completed or canceled. This
 * function should be called before another indirect read is started.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_indirect_read_finish(void);

/******************************************************************************/
/*!
 * Cancel all indirect read transfers in progress.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_indirect_read_cancel(void);

/******************************************************************************/
/*!
 * Get the current indirect read SRAM fill level value.
 *
 * Returns the SRAM fill level for the indirect read partition in units of SRAM
 * words (4 bytes).
 *
 * \returns     The SRAM fill level for the indirect read partition in units of 
 *              SRAM words (4 bytes).
 */
uint32_t alt_qspi_indirect_read_fill_level(void);

/******************************************************************************/
/*!
 * Get the current indirect read watermark value.
 *
 * The watermark value (in bytes) represents the minimum fill level of the SRAM
 * before a DMA peripheral access is permitted. When the SRAM fill level passes
 * the watermark, an interrupt source is also generated. This can be disabled by
 * writing a value of all zeroes.
 *
 * \returns     The current indirect read watermark value.
 */
uint32_t alt_qspi_indirect_read_watermark_get(void);

/******************************************************************************/
/*!
 * Set the indirect read watermark value.
 *
 * The watermark value (in bytes) represents the minimum fill level of the SRAM
 * before a DMA peripheral access is permitted. When the SRAM fill level passes
 * the watermark, an interrupt source is also generated. This can be disabled by
 * writing a value of all zeroes. The watermark can only be set when no indirect
 * read is in progress.
 *
 * \param       watermark
 *              The watermark value (in bytes).
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_indirect_read_watermark_set(const uint32_t watermark);

/******************************************************************************/
/*!
 * Returns true when an indirect read has completed otherwise false.
 *
 * \internal
 * Returns Indirect Read Transfer Control Register bit 5 "Indirect Completion Status".
 * \endinternal
 *
 * \returns     Returns true when an indirect read has completed otherwise false.
 */
bool alt_qspi_indirect_read_is_complete(void);

/******************************************************************************/
/*!
 * Starts an indirect write transfer.
 *
 * Initiates an indirect write transfer of the requested number of bytes to the
 * designated flash address.
 *
 * After calling this function, flash data may be written to the QSPI SRAM
 * buffer there is space via one of the following methods:
 *  * Directly from the AHB data slave interface at the configured AHB trigger
 *    address. If the requested space is not immediately available in the SRAM
 *    buffer then AHB wait states will be applied until the space becomes
 *    available. Alternatively, the data may be written to the AHB data slave
 *    as the SRAM is drained. The space in the SRAM buffer may be determined by
 *    an SRAM watermark interrupt notification or by polling the SRAM fill
 *    level and subtracting that value from the SRAM space devoted to writes.
 *  * Configuring and enabling the QSPI DMA peripheral controller.
 *
 * The following is a list of restrictions:
 *  * flash_addr must be word aligned.
 *  * num_bytes must be word aligned.
 *  * num_bytes must be 256 or below. This is due to a device specific
 *    limitation and may be lifted in the future.
 *  * The transfer must not cross the page (256 byte) addressing boundary. This
 *    restriction may be device specific and may be lifted in the future.
 *
 * \param       flash_addr
 *              The flash destination address to write data to.
 *
 * \param       num_bytes
 *              The number of bytes to write to the flash.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_indirect_write_start(const uint32_t flash_addr,
                                              const size_t num_bytes);

/******************************************************************************/
/*!
 * Finish the indirect write operation that was completed or canceled. This
 * function should be called before another indirect write is started.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_indirect_write_finish(void);

/******************************************************************************/
/*!
 * Cancel all indirect write transfers in progress.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_indirect_write_cancel(void);

/******************************************************************************/
/*!
 * Get the current indirect write SRAM fill level value.
 *
 * Returns the SRAM fill level for the indirect write partition in units of SRAM
 * words (4 bytes).
 *
 * \returns     The SRAM fill level for the indirect write partition in units of 
 *              SRAM words (4 bytes).
 */
uint32_t alt_qspi_indirect_write_fill_level(void);

/******************************************************************************/
/*!
 * Get the current indirect write watermark value.
 *
 * The watermark value (in bytes) represents the maximum fill level of the SRAM
 * before a DMA peripheral access is permitted.  When the SRAM fill level falls
 * below the watermark, an interrupt is also generated. This can be disabled by
 * writing a value of all ones.
 *
 * \returns     The current indirect write watermark value.
 */
uint32_t alt_qspi_indirect_write_watermark_get(void);

/******************************************************************************/
/*!
 * Set the indirect write watermark value.
 *
 * The watermark value (in bytes) represents the maximum fill level of the SRAM
 * before a DMA peripheral access is permitted.  When the SRAM fill level falls
 * below the watermark, an interrupt is also generated. This can be disabled by
 * writing a value of all ones. The watermark can only be set when no indirect
 * write is in progress.
 *
 * \param       watermark
 *              The watermark value (in bytes).
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_indirect_write_watermark_set(const uint32_t watermark);

/******************************************************************************/
/*!
 * Returns true when an indirect write has completed otherwise false.
 *
 * \internal
 * Returns Indirect Write Transfer Control Register bit 5 "Indirect Completion
 * Status".
 * \endinternal
 *
 * \returns     Returns true when an indirect write has completed otherwise
 *              false.
 */
bool alt_qspi_indirect_write_is_complete(void);

/******************************************************************************/
/*! \addtogroup ALT_QSPI_CFG_SRAM SRAM Partition
 *
 * The SRAM local memory buffer is a 128 by 32-bit (512 total bytes) memory. The
 * SRAM has two partitions, with the lower partition reserved for indirect read
 * operations and the upper partition for indirect write operations. The size of
 * the partitions is specified in the SRAM partition register, based on 32-bit
 * word sizes. For example, to specify four bytes of storage, write the value 1.
 * The value written to the indirect read partition size field ( addr ) defines
 * the number of entries reserved for indirect read operations. For example, write
 * the value 32 (0x20) to partition the 128-entry SRAM to 32 entries (25%) for
 * read usage and 96 entries (75%) for write usage.
 *
 * The functions in this section provide accces to configure the SRAM read
 * partition allocation.
 *
 * @{
 */

/*!
 * The size of the onboard SRAM in bytes.
 */
#define ALT_QSPI_SRAM_FIFO_SIZE           (512)

/*
 * The size of the onboard SRAM in entries. Each entry is word (32-bit) sized.
 */
#define ALT_QSPI_SRAM_FIFO_ENTRY_COUNT    (512 / sizeof(uint32_t))

/******************************************************************************/
/*!
 * Get the entry count (words) of the indirect read partition in the QSPI
 * controller SRAM.
 *
 * There is an additional word of read memory not in the SRAM but used to
 * buffer the SRAM and the AHB. As such, the total on board memory buffer for
 * indirect read is 1 more than the value reported by this function.
 *
 * \returns     The count of 32-bit words of the indirect read partition in the
 *              QSPI controller SRAM.
 *
 * \internal
 * The documentation states that the number of locations allocated to indirect
 * read = SRAM_PARTITION_REG + 1. Cadence clarified that the +1 comes from an
 * additional register slice for read's, implemented in FLOPs, which was done
 * to avoid connection the SRAM directly to the AHB interface. This was done
 * for performance / timing reasons. The +1 will not be included in the return
 * value but documented as an additional entry.
 * \endinternal
 */
uint32_t alt_qspi_sram_partition_get(void);

/******************************************************************************/
/*!
 * Set the entry count (words) of the indirect read partition in the QSPI
 * controller SRAM.
 *
 * Note: It is recommended that setting SRAM partition to 0 or 127 should be
 * avoided although it is not prohibited.
 *
 * \param       read_part_size
 *              The count of 32-bit words to allocate to the indirect read
 *              partition in the QSPI controller SRAM.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_sram_partition_set(const uint32_t read_part_size);

/*! @} */

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_QSPI_ERASE Flash Erase
 *
 * The functions in this group are used to erase selected portions of a flash
 * device.
 * @{
 */

/******************************************************************************/
/*!
 * This function erases the designated flash device subsector.
 *
 * This function erases the flash device subsector containing the designated
 * flash address. Any address within the subsector is valid.
 *
 * \param       addr
 *              A flash address contained within the the subsector to be erased.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_erase_subsector(const uint32_t addr);

/******************************************************************************/
/*!
 * This function erases the designated flash device sector.
 *
 * This function erases the flash device sector containing the designated flash
 * address. Any address within the sector is valid.
 *
 * \param       addr
 *              A flash address contained within the the sector to be erased.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_erase_sector(const uint32_t addr);

/******************************************************************************/
/*!
 * This function erases the entire flash device.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_erase_chip(void);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_QSPI_DMA DMA Peripheral Interface
 *
 * The DMA peripheral request controller is only used for the indirect mode of
 * operation where data is temporarily stored in the SRAM. The QSPI flash
 * controller uses the DMA peripheral request interface to trigger the external
 * DMA into performing data transfers between memory and the QSPI
 * controller.
 *
 * There are two DMA peripheral request interfaces, one for indirect reads and
 * one for indirect writes. The DMA peripheral request controller can issue two
 * types of DMA requests, single or burst, to the external DMA. The number of
 * bytes for each single or burst request is specified using the
 * alt_qspi_dma_config_set(). The DMA peripheral request controller splits the
 * total amount of data to be transferred into a number of DMA burst and single
 * requests by dividing the total number of bytes by the number of bytes
 * specified in the burst request, and then dividing the remainder by the number
 * of bytes in a single request.
 *
 * When programming the DMA controller, the burst request size must match the
 * burst request size set in the quad SPI controller to avoid quickly reaching
 * an overflow or underflow condition.
 * @{
 */

/******************************************************************************/
/*!
 * Disable the QSPI DMA peripheral interface.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_dma_disable(void);

/******************************************************************************/
/*!
 * Enable the QSPI DMA peripheral interface.
 *
 * Enable the QSPI DMA handshaking logic. When enabled the QSPI will trigger DMA
 * transfer requests via the DMA peripheral interface.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_dma_enable(void);

/******************************************************************************/
/*!
 * Get the current DMA peripheral configuration.
 *
 * This function returns the QSPI DMA peripheral interface single and burst type
 * transfer size configurations.
 *
 * \param       single_type_sz
 *              [out] The number of bytes for each DMA single type
 *              request. Value must be a power of 2 between 1 and 32728.
 *
 * \param       burst_type_sz
 *              [out] The number of bytes for each DMA burst type request. Value
 *              must be a power of 2 between 1 and 32728.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_dma_config_get(uint32_t * single_type_sz,
                                        uint32_t * burst_type_sz);

/******************************************************************************/
/*!
 * Set the DMA peripheral configuration.
 *
 * This function configures the QSPI DMA peripheral interface single and burst
 * type transfer sizes.  The DMA configruation should be setup while the
 * controller is idle. Because all transfers are required to be word aligned,
 * the smallest DMA request is 4 bytes. 
 *
 * This API requires that the QSPI controller be idle, as determined by
 * alt_qspi_is_idle().
 *
 * \param       single_type_sz
 *              The number of bytes for each DMA single type request. Value must
 *              be a power of 2 between 4 and 32768.
 *
 * \param       burst_type_sz
 *              The number of bytes for each DMA burst type request. Value must
 *              be a power of 2 between 4 and 32768. Bursts must be equal or
 *              larger than single requests.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_qspi_dma_config_set(const uint32_t single_type_sz,
                                        const uint32_t burst_type_sz);


/*! @} */

/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_QSPI_H__ */
