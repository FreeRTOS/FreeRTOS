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
 *  Altera - SPI Flash Controller Module
 */

#ifndef __ALT_SPI_H__
#define __ALT_SPI_H__

#include "hwlib.h"
#include "alt_clock_manager.h"
#include "socal/alt_spis.h"
#include "socal/alt_spim.h"
#include "socal/alt_sysmgr.h"
#include "socal/hps.h"
#include "socal/socal.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/******************************************************************************/
/*! \addtogroup ALT_SPI SPI Flash Controller Module
 *
 * This module defines an API for configuring and managing the HPS serial
 * peripheral interface (SPI) master and slave controller instances.
 *
 * The hard processor system (HPS) provides two SPI masters and two SPI
 * slaves. The SPI masters and slaves are instances of the Synopsys DesignWare
 * Synchronous Serial Interface (SSI) controller.
 *
 * @{
 */

/*!
 * This type enumerates the HPS SPI controller instances.
 */
typedef enum ALT_SPI_CTLR_e
{
    ALT_SPI_SPIS0   = (int32_t)ALT_SPIS0_OFST,      /*!< SPI Slave Controller 0 instance */
    ALT_SPI_SPIS1   = (int32_t)ALT_SPIS1_OFST,      /*!< SPI Slave Controller 1 instance */
    ALT_SPI_SPIM0   = (int32_t)ALT_SPIM0_OFST,      /*!< SPI Master Controller 0 instance */
    ALT_SPI_SPIM1   = (int32_t)ALT_SPIM1_OFST       /*!< SPI Master Controller 1 instance */
} ALT_SPI_CTLR_t;

/*!
 * This type enumerates the serial protocol frame formats supported by the SPI
 * controller.
 *
 * See: <em>Functional Description of the SPI Controller</em> section of
 *      <em>Chapter 19. SPI Controller</em> in the <em>Cyclone V Device Handbook
 *      Volume 3: Hard Processor System Technical Reference Manual</em> for a full
 *      description of the supported protocols.
 */
typedef enum ALT_SPI_FRF_e
{
    ALT_SPI_FRF_SPI         = 0, /*!< Motorola SPI protocol - A four-wire, full-duplex
                                  *  serial protocol from Motorola.
                                  */
    ALT_SPI_FRF_SSP         = 1, /*!< Texas Instruments Serial Protocol (SSP) - A
                                  *   four-wire, full-duplex serial protocol.
                                  */
    ALT_SPI_FRF_MICROWIRE   = 2  /*!< National Semiconductor Microwire - A half-duplex
                                  *   serial protocol, which uses a control word
                                  *   transmitted from the serial master to the target
                                  *   serial slave.
                                  */
} ALT_SPI_FRF_t;

/*!
 * This type enumerates the SPI serial clock polarity choices. Only valid when the
 * frame format is set to Motorola SPI. Used to select the polarity of the
 * inactive serial clock, which is held inactive when the SPI controller master is
 * not actively transferring data on the serial bus.
 */
typedef enum ALT_SPI_SCPOL_e
{
    ALT_SPI_SCPOL_INACTIVE_LOW  = 0,    /*!< Inactive state of serial clock is low */
    ALT_SPI_SCPOL_INACTIVE_HIGH = 1     /*!< Inactive state of serial clock is high */
} ALT_SPI_SCPOL_t;

/*!
 * This type enumerates the SPI serial clock phase choices. Only valid when the
 * frame format is set to Motorola SPI. The serial clock phase selects the
 * relationship of the serial clock with the slave select signal.  When
 * ALT_SPI_SCPH_TOGGLE_MIDDLE, data are captured on the first edge of the serial
 * clock. When ALT_SPI_SCPH_TOGGLE_START, the serial clock starts toggling one
 * cycle after the slave select line is activated, and data are captured on the
 * second edge of the serial clock.
 */
typedef enum ALT_SPI_SCPH_e
{
    ALT_SPI_SCPH_TOGGLE_MIDDLE  = 0,    /*!< Serial clock toggles in middle of first data bit. */
    ALT_SPI_SCPH_TOGGLE_START   = 1     /*!< Serial clock toggles at start of first data bit. */
} ALT_SPI_SCPH_t;

/*!
 * This type enumerates the SPI available frame size. Specifies the frame size of
 * transfer for serial communication.
 */
typedef enum ALT_SPI_DFS_e
{
    ALT_SPI_DFS_4BIT    = 3,        /*!< 4-bit serial data transfer */
    ALT_SPI_DFS_5BIT    = 4,        /*!< 5-bit serial data transfer */
    ALT_SPI_DFS_6BIT    = 5,        /*!< 6-bit serial data transfer */
    ALT_SPI_DFS_7BIT    = 6,        /*!< 7-bit serial data transfer */
    ALT_SPI_DFS_8BIT    = 7,        /*!< 8-bit serial data transfer */
    ALT_SPI_DFS_9BIT    = 8,        /*!< 9-bit serial data transfer */
    ALT_SPI_DFS_10BIT   = 9,        /*!< 10-bit serial data transfer */
    ALT_SPI_DFS_11BIT   = 10,       /*!< 11-bit serial data transfer */
    ALT_SPI_DFS_12BIT   = 11,       /*!< 12-bit serial data transfer */
    ALT_SPI_DFS_13BIT   = 12,       /*!< 13-bit serial data transfer */
    ALT_SPI_DFS_14BIT   = 13,       /*!< 14-bit serial data transfer */
    ALT_SPI_DFS_15BIT   = 14,       /*!< 15-bit serial data transfer */
    ALT_SPI_DFS_16BIT   = 15        /*!< 16-bit serial data transfer */
} ALT_SPI_DFS_t;

/*!
 * This type enumerates the SPI transfer mode choices. Specifies the mode of
 * transfer for serial communication.
 */
typedef enum ALT_SPI_TMOD_e
{
    ALT_SPI_TMOD_TXRX    = 0,        /*!< Transmit & Receive */
    ALT_SPI_TMOD_TX      = 1,        /*!< Transmit Only */
    ALT_SPI_TMOD_RX      = 2,        /*!< Receive Only */
    ALT_SPI_TMOD_EEPROM  = 3,        /*!< EEPROM Read */
} ALT_SPI_TMOD_t;

/*! 
 * This type enumerates the HPS SPI controller type mode.
 */
typedef enum ALT_SPI_OP_MODE_e
{
    ALT_SPI_OP_MODE_SLAVE   = 0,      /*!< SPI Slave Controller */
    ALT_SPI_OP_MODE_MASTER  = 1       /*!< SPI Master Controller */
} ALT_SPI_OP_MODE_t;

/*
 * A pointer or handle to the SPI controller device instance. The ALT_SPI_DEV_t is
 * initialized by a call to alt_spi_init() and subsequently used by the other SPI
 * controller API functions as a reference to a specific device.
 *
 * \internal
 * ALT_SPI_DEV_t may be a struct or reference to an opaque data
 * structure. Whatever "internal" type is suited to the needs of the
 * implementation.
 * \endinternal
 */
typedef struct ALT_SPI_DEV_s
{
    void *              location;
                            /*!< HPS address of spi instance*/
    alt_freq_t          clock_freq;
                            /*!< Input clock frequency.  */
    uint32_t            last_slave_mask;
                            /*!< Last issued slave mask. */
    uint32_t            last_transfer_mode;
                            /*!< Last transfer mode. */
    ALT_SPI_OP_MODE_t   op_mode;
                            /*!< HPS SPI operation mode*/
} ALT_SPI_DEV_t;

/*!
 * This type defines a structure for specifying configuration parameters for a SPI
 * controller.
 */
typedef struct ALT_SPI_CONFIG_s
{
    ALT_SPI_DFS_t      frame_size;
                                    /*!< Data Frame Size. Selects the data
                                     *   frame length. When the data frame size is
                                     *   programmed to be less than 16 bits, the
                                     *   receive data are automatically
                                     *   right-justified by the receive logic,
                                     *   with the upper bits of the receive FIFO
                                     *   zero-padded.  You must right-justify
                                     *   transmit data before writing into the
                                     *   transmit FIFO. The transmit logic ignores
                                     *   the upper unused bits when transmitting
                                     *   the data. Valid range 4..16.
                                     */
    ALT_SPI_FRF_t   frame_format;
                                    /*!< Frame Format. Selects which serial
                                     *   protocol transfers the data.
                                     */
    ALT_SPI_SCPH_t  clk_phase;
                                    /*!< Serial Clock Phase. Valid when the frame
                                     *   format (FRF) is set to Motorola SPI. The
                                     *   serial clock phase selects the
                                     *   relationship of the serial clock with the
                                     *   slave select signal.
                                     */
    ALT_SPI_SCPOL_t clk_polarity;
                                    /*!< Serial Clock Polarity. Only valid when
                                     *   the frame format (FRF) is set to Motorola
                                     *   SPI. Used to select the polarity of the
                                     *   inactive serial clock.
                                     */
    ALT_SPI_TMOD_t  transfer_mode;
                                    /*!< Transfer Mode. Selects the mode of
                                     *   transfer for serial communication.
                                     */
    bool            slave_output_enable;
                                    /*!< Slave Output Enable. Relevant only for
                                     *   SPI controller slaves.  This data member
                                     *   has no applicability for SPI controller
                                     *   masters. This data member specifies
                                     *   whether the \b ssi_oe_n output is enabled
                                     *   or disabled from the SPI controller
                                     *   slave.  When \b true, the \b ssi_oe_n
                                     *   output can never be active. When the \b
                                     *   ssi_oe_n output controls the tri-state
                                     *   buffer on the \b txd output from the
                                     *   slave, a high impedance state is always
                                     *   present on the slave \b txd output when
                                     *   \e slv_oe = \b true. This is useful when
                                     *   the master transmits in broadcast mode.
                                     *   Only one slave may respond with data on
                                     *   the master \b rxd line. This data member
                                     *   is enabled after reset and must be
                                     *   disabled by software (when broadcast mode
                                     *   is used), if you do not want this device
                                     *   to respond with data.
                                     */
    bool            loopback_mode;
                                    /*!< Used for testing purposes only. When \b
                                     *   true, creates an internal loopback by
                                     *   connecting the transmit shift register
                                     *   output to the receive shift register
                                     *   input. Can be used in both serial- slave
                                     *   and serial-master modes. For SPI
                                     *   controller slaves in loopback mode, the
                                     *   \b ss_in_n and \b ssi_clk signals must be
                                     *   provided by an external source. In this
                                     *   mode, the slave cannot generate these
                                     *   signals because there is nothing to which
                                     *   to loop back. For normal operation this
                                     *   data member should be set to \b false.
                                     */
} ALT_SPI_CONFIG_t;

/*!
 * This type enumerates the Microwire transfer mode choices. Specifies whether the
 * Microwire transfer is sequential or non-sequential. When sequential mode is
 * used, only one control word is needed to transmit or receive a block of data
 * words. When non-sequential mode is used, there must be a control word for each
 * data word that is transmitted or received.
 */
typedef enum ALT_SPI_MW_MODE_e
{
    ALT_SPI_MW_NON_SEQUENTIAL   = 0,    /*!< Non-Sequential Transfer */
    ALT_SPI_MW_SEQUENTIAL       = 1     /*!< Sequential Transfer */
} ALT_SPI_MW_MODE_t;

/*!
 * This type enumerates the slave select output lines for SPI controller modules
 * configured as masters.
 */
typedef enum ALT_SPI_SS_e
{
    ALT_SPI_SS0 = 1UL << 0,     /*!< Slave select 0 output \b ss_0_n */
    ALT_SPI_SS1 = 1UL << 1,     /*!< Slave select 1 output \b ss_1_n */
    ALT_SPI_SS2 = 1UL << 2,     /*!< Slave select 2 output \b ss_2_n */
    ALT_SPI_SS3 = 1UL << 3      /*!< Slave select 3 output \b ss_3_n */
} ALT_SPI_SS_t;

/*!
 * This type enumerates the Microwire direction control choices. The enumerations
 * specify the direction of the data word when the Microwire serial protocol is
 * used.
 */
typedef enum ALT_SPI_MW_DIR_e
{
    ALT_SPI_MW_DIR_RX   = 0,        /*!< The data word is received by the
                                     *   controller from an external serial
                                     *   device.
                                     */
    ALT_SPI_MW_DIR_TX   = 1         /*!< The data word is transmitted from the
                                     *   controller to an external serial device.
                                     */
} ALT_SPI_MW_DIR_t;

/*!
 * This definition specifies the largest possible control frame size.
 */
#define ALT_SPI_MW_CTL_FRAME_SIZE_MAX   (16)

/*!
 * This type defines a structure for configuration of the SPI controller when
 * using the Microwire serial protocol.
 */
typedef struct ALT_SPI_MW_CONFIG_s
{
    uint32_t            ctl_frame_size;
                                    /*!< Control Frame Size. Selects the length of
                                     *   the control word for the Microwire frame
                                     *   format. Valid range 0 <= \e n <= 16 where
                                     *   \e n sets the bit field to \e n - 1.
                                     */
    ALT_SPI_MW_MODE_t   mode;
                                    /*!< Transfer Mode. Specifies whether the
                                     *   Microwire transfer is sequential or
                                     *   non-sequential.
                                     */
    ALT_SPI_MW_DIR_t    dir;
                                    /*!< Direction.  This setting controls the
                                     *   direction of the data word for the
                                     *   half-duplex Microwire serial protocol.
                                     */
    bool                handshake_enabled;
                                    /*!< Microwire handshaking enable
                                     *   flag. Relevant only when the SPI
                                     *   controller is a master. Used to enable
                                     *   and disable the "busy/ready" handshaking
                                     *   interface for the Microwire
                                     *   protocol. When enabled (\e true), the SPI
                                     *   controller checks for a ready status from
                                     *   the target slave, after the transfer of
                                     *   the last data/control bit, before
                                     *   clearing the controller busy status.
                                     */
} ALT_SPI_MW_CONFIG_t;

/*!
 * Initialize the specified SPI controller instance for use and return a device
 * handle referencing it.
 *
 * \param       spi
 *              The HPS SPI controller instance to initialize.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * Initialization process:
 * * Initialize internal driver state
 * * Check clock setup
 *   - spi_m_clk (ALT_CLK_SPI_M) for master instances
 *   - l4_main_clk (ALT_CLK_L4_MAIN) for slave instances
 * * Take SPI module instance out of reset (System Manager)
 *   - RSTMGR.PERMODRST.SPIM[01] for master instances
 *   - RSTMGR.PERMODRST.SPIS[01] for slave instances
 * * Disable and clear all interrupts and status conditions
 * * Setup and initialize any expected initial SPI controller state
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_init(const ALT_SPI_CTLR_t spi, ALT_SPI_DEV_t *spi_dev);

/*!
 * Reset the specified SPI controller instance for use.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * Reset process:
 * * Disable controller
 * * Initialize internal driver state
 * * Take SPI instance out of reset (System Manager)
 * * Disable and clear all interrupts and status conditions
 * * Enable controller
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_reset(ALT_SPI_DEV_t * spi_dev);

/*!
 * Uninitialize the SPI controller referenced by the \e spi_dev handle.
 *
 * This function attempts to gracefully shutdown the SPI controller by waiting for
 * any incomplete transactions to finish and then putting the SPI controller into
 * reset.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * * Put SPI module instance into reset (System Manager)
 *   - RSTMGR.PERMODRST.SPIM[01] for master instances
 *   - RSTMGR.PERMODRST.SPIS[01] for slave instances
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_uninit(ALT_SPI_DEV_t *spi_dev);

/*!
 * Disables the SPI controller.
 *
 * When the SPI controller is disabled, the following occurs:
 * * All transfers are halted immediately.
 * * The TX FIFO and RX FIFO are cleared.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * SSIENR.SSI_EN = 0
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_disable(ALT_SPI_DEV_t *spi_dev);

/*!
 * Enables the SPI controller.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * SSIENR.SSI_EN = 1
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_enable(ALT_SPI_DEV_t *spi_dev);

/*!
 * Returns ALT_E_TRUE if the SPI controller is enabled.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_BAD_ARG   Details about error status code
 * \retval      ALT_E_TRUE      SPI controller is enabled.
 * \retval      ALT_E_FALSE     SPI controller is not enabled.
 *
 * \internal
 * SSIENR.SSI_EN == 1
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_is_enabled(ALT_SPI_DEV_t *spi_dev);

/*!
 * Returns ALT_E_TRUE if the SPI controller is busy. The SPI controller is busy if
 * a serial transfer is in progress. If ALT_E_FALSE is returned, then the SPI
 * controller is idle or disabled.
 *
 * NOTE: A busy status is not indicated when data is written into the transmit
 *       FIFO. The busy status only is set only when the target slave has been
 *       selected and the actual transfer is underway.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * SR.BUSY == 1
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_is_busy(ALT_SPI_DEV_t *spi_dev);

/*!
 * Gets the current configuration of the SPI controller.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       cfg
 *              [out] Pointer to a ALT_SPI_CONFIG_t structure for holding the
 *              returned SPI controller configuration parameters.
 *
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_config_get(ALT_SPI_DEV_t *spi_dev, ALT_SPI_CONFIG_t *cfg);

/*!
 * Sets the configuration of the SPI controller.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       cfg
 *              Pointer to a ALT_SPI_CONFIG_t structure holding the desired SPI
 *              controller configuration parameters.
 *
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_config_set(ALT_SPI_DEV_t *spi_dev, const ALT_SPI_CONFIG_t *cfg);

/*!
 * Gets the current Microwire specific configuration parameters of the SPI
 * controller.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       cfg
 *              [out] Pointer to a ALT_SPI_MW_CONFIG_t structure for holding the
 *              returned SPI controller Microwire specific configuration
 *              parameters.
 *
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_mw_config_get(ALT_SPI_DEV_t *spi_dev, ALT_SPI_MW_CONFIG_t *cfg);

/*!
 * Sets the Microwire specific configuration parameters of the SPI controller.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       cfg
 *              Pointer to a ALT_SPI_MW_CONFIG_t structure holding the desired SPI
 *              controller Microwire specific configuration parameters.
 *
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_mw_config_set(ALT_SPI_DEV_t *spi_dev, const ALT_SPI_MW_CONFIG_t *cfg);

/*!
 * This definition specifies a mask that applies to all slaves.
 */
#define ALT_SPI_SLAVE_MASK_ALL 0xF

/*!
 * Disable the specified SPI controller slave select output lines.
 * 
 * This function is only valid for SPI controllers configured as masters.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       mask
 *              Specifies the slave select output signal line(s) to disable. \e
 *              mask is a mask of logically OR'ed \ref ALT_SPI_SS_t values that
 *              designate the slave select outputs to disable.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * SER
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_slave_select_disable(ALT_SPI_DEV_t *spi_dev,
                                             const uint32_t mask);

/*!
 * Enable the specified SPI controller slave select output lines.
 * 
 * Normally, unless operating in broadcast mode, only one slave select output
 * should be specified in \e mask.
 *
 * This function is only valid for SPI controllers configured as masters.
 *
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       mask
 *              Specifies the slave select output signal line(s) to enable.  \e
 *              mask is a mask of logically OR'ed \ref ALT_SPI_SS_t values that
 *              designate the slave select outputs to enable.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * SER
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_slave_select_enable(ALT_SPI_DEV_t *spi_dev,
                                            const uint32_t mask);

/*!
 * Gets the speed of the SPI master, which is calculated from divider value and
 * the SPI controller internal clock.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       speed_in_hz
 *              Speed (Hz) of the SPI bus.
 *
 * \param       div
 *              Clock divider.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_speed_get(ALT_SPI_DEV_t * spi_dev, 
                                  uint32_t * speed_in_hz);


/*!
 * Set the baud rate divider to configure the generated \b sclk_out frequency.
 *
 * The generated \b sclk_out frequency is defined by the formula:
 *
 * <b>F<sub>sclk_out</sub> = F<sub>spi_m_clk</sub> / DIV</b>
 *
 * Where:
 * * <b>F<sub>sclk_out</sub></b> is the generated frequency of \b sclk_out.
 * * <b>F<sub>spi_m_clk</sub></b> is the input clock frequency to the SPI master
 *   peripheral module.
 * * <b>DIV</b> is the baud rate divider value.
 *   
 * This function is only valid for SPI master controllers.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       div
 *              The clock divider value. Valid clock divider values must be an
 *              even value in the range 2 to 65,534. If \e div is 0, then \b
 *              sclk_out is disabled.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * BAUDR
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_divider_set(ALT_SPI_DEV_t *spi_dev, const uint32_t div);



/*!
 * Get the configured baud rate divider value for the specified SPI controller.
 * 
 * This function is only valid for SPI master controllers.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       div
 *              [out] The configured clock divider value. A returned value of 0
 *              indicates that \b sclk_out is disabled.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * BAUDR
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_baud_rate_get(ALT_SPI_DEV_t *spi_dev, uint32_t *div);

/*!
 * Set the baud rate divider to configure the generated \b sclk_out frequency.
 *
 * The generated \b sclk_out frequency is defined by the formula:
 *
 * <b>F<sub>sclk_out</sub> = F<sub>spi_m_clk</sub> / DIV</b>
 *
 * Where:
 * * <b>F<sub>sclk_out</sub></b> is the generated frequency of \b sclk_out.
 * * <b>F<sub>spi_m_clk</sub></b> is the input clock frequency to the SPI master
 *   peripheral module.
 * * <b>DIV</b> is the baud rate divider value.
 *   
 * This function is only valid for SPI master controllers.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       div
 *              The clock divider value. Valid clock divider values must be an
 *              even value in the range 2 to 65,534. If \e div is 0, then \b
 *              sclk_out is disabled.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * BAUDR
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_baud_rate_set(ALT_SPI_DEV_t *spi_dev, const uint32_t div);

/*!
 * Gets the speed of the SPI master, which is calculated from divider value and
 * the SPI controller internal clock.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       speed_in_hz
 *              Speed (Hz) of the SPI bus.
 *
 * \param       div
 *              Clock divider.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_speed_get(ALT_SPI_DEV_t * spi_dev, 
                                  uint32_t * speed_in_hz);

/*!
 * Attempts to sets the speed of the SPI master to the requested speed by
 * calculating and setting the most suitable divider value.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       speed_in_hz
 *              Speed (Hz) of the SPI bus.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_speed_set(ALT_SPI_DEV_t * spi_dev, 
                                  uint32_t speed_in_hz);


/*!
 * Gets the speed of the SPI master, which is calculated from divider value and
 * the SPI controller internal clock.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       speed_in_hz
 *              Speed (Hz) of the SPI bus.
 *
 * \param       div
 *              Clock divider.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_speed_to_divider(ALT_SPI_DEV_t * spi_dev, 
                                        uint32_t speed_in_hz, 
                                        uint32_t * div);

/*!
 * Attempts to sets the speed of the SPI master to the requested speed by
 * calculating and setting the most suitable divider value.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       speed_in_hz
 *              Speed (Hz) of the SPI bus.
 *
 * \param       div
 *              A pointer to the clock divider.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_divider_to_speed(ALT_SPI_DEV_t * spi_dev, 
                                        uint32_t * speed_in_hz, 
                                        const uint32_t * div);

/*!
 * Get the current number of data frames configured for the SPI controller.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       num_data_frames
 *              [out] The current number of data frames parameter configured for
 *              the SPI controller.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * *num_data_frames = CTRLR1.NDF + 1
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_num_data_frames_get(ALT_SPI_DEV_t *spi_dev, uint32_t *num_data_frames);

/*!
 * Set the number of data frames configured for the SPI controller.
 *
 * Sets the number of data frames to be continuously received by the SPI
 * controller. The SPI controller continues to receive serial data until the
 * number of data frames received is equal to this parameter, which enables you to
 * receive up to 64 KiB of data in a continuous transfer.
 *
 * This function is only valid for SPI master controller instances.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       num_data_frames
 *              The desired number of data frames for the SPI controller to
 *              receive. valid range: 1 to 65536.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * assert( alt_spi_is_enabled() == false )
 * assert( CRTLR0.TMOD == ALT_SPI_TMOD_RX or CRTLR0.TMOD == ALT_SPI_TMOD_EEPROM )
 * CTRLR1.NDF = num_data_frames - 1
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_num_data_frames_set(ALT_SPI_DEV_t *spi_dev, const uint32_t num_data_frames);

/******************************************************************************/
/*! \addtogroup ALT_SPI_INT Interrupt Status Conditions
 *
 * The SPI controller supports combined interrupt requests, which can be
 * masked. The combined interrupt request is the ORed result of all other SPI
 * interrupts after masking. All SPI interrupts have active-high polarity
 * level. The SPI interrupts are described as follows:
 *
 * * <b>Transmit FIFO Empty Interrupt</b> - Set when the transmit FIFO is equal to
 *   or below its threshold value and requires service to prevent an
 *   under-run. The threshold value determines the level of transmit FIFO entries
 *   at which an interrupt is generated. This interrupt is cleared by hardware
 *   when data are written into the transmit FIFO buffer, bringing it over the
 *   threshold level.
 *
 * * <b>Transmit FIFO Overflow Interrupt</b> - Set when the host attempts to write
 *   into the transmit FIFO after it has been completely filled. When set, data
 *   written from the host is discarded.  This interrupt remains set until you
 *   call alt_spi_int_clear() with ALT_SPI_STATUS_TXOI in the mask.
 *
 * * <b>Receive FIFO Full Interrupt</b> - Set when the receive FIFO is equal to or
 *   above its threshold value plus 1 and requires service to prevent an
 *   overflow. The threshold value determines the level of receive FIFO entries at
 *   which an interrupt is generated. This interrupt is cleared by hardware when
 *   data are read from the receive FIFO buffer, bringing it below the threshold
 *   level.
 *
 * * <b>Receive FIFO Overflow Interrupt</b> - Set when the receive logic attempts
 *   to place data into the receive FIFO after it has been completely filled. When
 *   set, newly received data are discarded. This interrupt remains set until you
 *   call alt_spi_int_clear() with ALT_SPI_STATUS_RXOI in the mask.
 *
 * * <b>Receive FIFO Underflow Interrupt</b> - Set when the host attempts to read
 *   from the receive FIFO when it is empty.  When set, zeros are read back from
 *   the receive FIFO. This interrupt remains set until you call
 *   alt_spi_int_clear() with ALT_SPI_STATUS_RXUI in the mask.
 *
 * * <b>Combined Interrupt Request</b> - The OR'ed result of all the previously
 *   discussed interrupt status conditions after masking. Masking all interrupt
 *   status conditions will mask the combined interrupt signal (\b
 *   ALT_INT_INTERRUPT_SPI<em>n</em>_IRQ where \e n is 0-3) generated for the SPI
 *   controller that is sent to the Generic Interrupt Controller (GIC).
 *
 * Interrupt status conditions may be monitored by polling () or setting up an
 * interrupt handler using the \ref INT_LL_ISR "HWLIB Interrupt Manager API".
 *
 * @{
 */

/*!
 * This type enumerates interrupt status conditions for the SPI controller.
 *
 * For any interrupt status condition, a 0 value indicates the interrupt condition
 * is not active and a 1 value indicates the interrupt condition is active.
 */
typedef enum ALT_SPI_STATUS_e
{
    ALT_SPI_STATUS_TXEI         = 1UL << 0, /*!< Transmit FIFO Empty Interrupt Status */
    ALT_SPI_STATUS_TXOI         = 1UL << 1, /*!< Transmit FIFO Overflow Interrupt Status */
    ALT_SPI_STATUS_RXUI         = 1UL << 2, /*!< Receive FIFO Underflow Interrupt Status */
    ALT_SPI_STATUS_RXOI         = 1UL << 3, /*!< Receive FIFO Overflow Interrupt Status */
    ALT_SPI_STATUS_RXFI         = 1UL << 4, /*!< Receive FIFO Full Interrupt Status */
    ALT_SPI_STATUS_ALL          = 0x1f      /*!< All interrupt status conditions */
} ALT_SPI_STATUS_t;

/*!
 * Returns the current SPI controller interrupt status conditions.
 *
 * This function returns the current value of the SPI controller interrupt status
 * register value which reflects the current SPI controller interrupt status
 * conditions that are not disabled (i.e. masked).
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       status
 *              [out] A pointer to a bit mask of the active \ref ALT_SPI_STATUS_t
 *              interrupt and status conditions.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * ISR
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_int_status_get(ALT_SPI_DEV_t *spi_dev,
                                       uint32_t *status);

/*!
 * Returns the SPI controller raw interrupt status conditions irrespective of the
 * interrupt status condition enablement state.
 *
 * This function returns the current value of the SPI controller raw interrupt
 * status register value which reflects the current SPI controller status
 * conditions regardless of whether they are disabled (i.e. masked) or not.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       status
 *              [out] A pointer to a bit mask of the active \ref ALT_SPI_STATUS_t
 *              interrupt and status conditions.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * RISR
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_int_raw_status_get(ALT_SPI_DEV_t *spi_dev,
                                           uint32_t *status);

/*!
 * Clears the specified SPI controller interrupt status conditions identified in
 * the mask.
 *
 * This function clears one or more of the interrupt status conditions that
 * contribute to the combined \b ALT_INT_INTERRUPT_SPI<em>n</em>_IRQ interrupt
 * signal state.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       mask
 *              Specifies the QSPI interrupt status conditions to clear. \e mask
 *              is a mask of logically OR'ed \ref ALT_SPI_STATUS_t values that
 *              designate the status conditions to clear.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * RXOICR
 * TXOICR
 * RXUICR
 * MSTICR
 * ICR
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_int_clear(ALT_SPI_DEV_t *spi_dev, const uint32_t mask);

/*!
 * Disable the specified SPI controller interrupt status conditions identified in
 * the mask.
 *
 * This function disables one or more of the interrupt status conditions that
 * contribute to the combined \b ALT_INT_INTERRUPT_SPI<em>n</em>_IRQ interrupt
 * signal state.
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have
 *       the effect of enabling it as a contributor to the \b
 *       ALT_INT_INTERRUPT_SPI<em>n</em>_IRQ interrupt signal state. The function
 *       alt_spi_int_enable() is used to enable status source conditions.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       mask
 *              Specifies the status conditions to disable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed \ref
 *              ALT_SPI_STATUS_t values that designate the status conditions to
 *              disable.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_int_disable(ALT_SPI_DEV_t *spi_dev, const uint32_t mask);

/*!
 * Enable the specified SPI controller interrupt status conditions identified in
 * the mask.
 *
 * This function enables one or more of the interrupt status conditions that
 * contribute to the combined \b ALT_INT_INTERRUPT_SPI<em>n</em>_IRQ interrupt
 * signal state.
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have
 *       the effect of disabling it as a contributor to the \b
 *       ALT_INT_INTERRUPT_SPI<em>n</em>_IRQ interrupt signal state. The function
 *       alt_spi_int_disable() is used to disable status source conditions.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       mask
 *              Specifies the status conditions to enable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed \ref
 *              ALT_SPI_STATUS_t values that designate the status conditions to
 *              enable.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_int_enable(ALT_SPI_DEV_t *spi_dev, const uint32_t mask);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_SPI_SAMPLE_DELAY RX Sample Delay Configuration
 *
 * SPI master controllers can configure a delay in the sample time of the \b rxd
 * signal in order to increase the maximum achievable frequency on the serial bus.
 *
 * The delay value specifies an additional amount of delay applied to the \b rxd
 * sample, in number of spi_m_clk clock cycles, up to \ref
 * ALT_SPI_RXD_SAMPLE_DELAY_MAX cycles.
 *
 * The functions in this group only apply to SPI master controllers.
 * @{
 */

/*!
 * The maximum number of clock cycles that can be used to delay the sampling of
 * the \b rxd input signal.
 */
#define ALT_SPI_RXD_SAMPLE_DELAY_MAX    4

/*!
 * Get the configured Rx sample delay value.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       delay
 *              [out] The configured Rx sample delay in spi_m_clk clock cycles for
 *              the \b rxd signal.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_rx_sample_delay_get(ALT_SPI_DEV_t *spi_dev, uint32_t *delay);

/*!
 * Set the configured Rx sample delay value.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       delay
 *              The desired Rx sample delay in spi_m_clk clock cycles for the \b
 *              rxd signal.  Must be in the range 0 .. \ref ALT_SPI_RXD_SAMPLE_DELAY_MAX.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_rx_sample_delay_set(ALT_SPI_DEV_t *spi_dev, const uint32_t delay);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_SPI_RX_FIFO RX FIFO Management
 *
 * The receive FIFO has a configurable threshold value that controls the level of
 * entries (or above) that sets the RX_FULL status condition and triggers an
 * interrupt. The valid range is 0..(\ref ALT_SPI_RX_FIFO_NUM_ENTRIES - 1), with the
 * additional restriction that SPI controller does not allow this value to be set to
 * a value larger than the depth of the buffer. If an attempt is made to do that, the
 * actual value set will be the maximum depth of the buffer. A value of 0 sets the
 * threshold for 1 entry, and a value of (\ref ALT_SPI_RX_FIFO_NUM_ENTRIES - 1) sets
 * the threshold for \ref ALT_SPI_RX_FIFO_NUM_ENTRIES entries.
 *
 * @{
 */

/*!
 * The number of entries (depth) of the SPI controller receive FIFO.
 */
#define ALT_SPI_RX_FIFO_NUM_ENTRIES     256

/*!
 * Reads a data frame from the receive (Rx) FIFO.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       data
 *              [out] The data frame read from into the Rx FIFO.  The
 *              \e data parameter type is sized large enough to
 *              contain the widest possible data frame size.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * assert( alt_spi_is_enabled() )
 * DR = data
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_rx_fifo_deq(ALT_SPI_DEV_t *spi_dev, uint16_t *data);

/*!
 * Returns ALT_E_TRUE when the receive FIFO is empty.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * SR.RFNE == 0
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_rx_fifo_is_empty(ALT_SPI_DEV_t *spi_dev);

/*!
 * Returns ALT_E_TRUE when the receive FIFO is completely full.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * SR.RFF == 1
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_rx_fifo_is_full(ALT_SPI_DEV_t *spi_dev);

/*!
 * Returns the number of valid entries in the receive FIFO.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       num_entries
 *              [out] The number of entries in the receive FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_RXFLR.RXFLR
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_rx_fifo_level_get(ALT_SPI_DEV_t *spi_dev,
                                          uint32_t *num_entries);

/*!
 * Gets the current receive FIFO threshold level value.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       threshold
 *              [out] The current threshold value.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_RX_TL.RX_TL
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_rx_fifo_threshold_get(ALT_SPI_DEV_t *spi_dev,
                                              uint8_t *threshold);

/*!
 * Sets the current receive FIFO threshold level value.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       threshold
 *              The threshold value.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_RX_TL.RX_TL = threshold
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_rx_fifo_threshold_set(ALT_SPI_DEV_t *spi_dev,
                                              const uint8_t threshold);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_SPI_TX_FIFO TX FIFO Management
 *
 * The transmit FIFO has a configurable threshold value that controls the level of
 * entries (or below) that sets the TX_EMPTY status condition and triggers an
 * interrupt. The valid range is 0..(\ref ALT_SPI_TX_FIFO_NUM_ENTRIES - 1), with the
 * additional restriction that SPI controller does not allow this value to be set to
 * a value larger than the depth of the buffer. If an attempt is made to do that, the
 * actual value set will be the maximum depth of the buffer. A value of 0 sets the
 * threshold for 0 entries, and a value of (\ref ALT_SPI_TX_FIFO_NUM_ENTRIES - 1)
 * sets the threshold for (\ref ALT_SPI_TX_FIFO_NUM_ENTRIES - 1) entries.
 *
 * @{
 */

/*!
 * The number of entries (depth) of the SPI controller transmit FIFO.
 */
#define ALT_SPI_TX_FIFO_NUM_ENTRIES     256

/*!
 * Writes a data frame to the transmit (Tx) FIFO for transmittal.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       data
 *              The data frame to put into the Tx FIFO.  The \e data
 *              parameter type is sized large enough to contain the
 *              widest possible data frame size. The data in each
 *              frame should be right justified within the \e data
 *              parameter.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * assert( alt_spi_is_enabled() )
 * DR = data
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_tx_fifo_enq(ALT_SPI_DEV_t *spi_dev, const uint16_t data);

/*!
 * Returns ALT_E_TRUE when the transmit FIFO is empty.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * SR.TFE == 1
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_tx_fifo_is_empty(ALT_SPI_DEV_t *spi_dev);

/*!
 * Returns ALT_E_TRUE when the transmit FIFO is completely full.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * SR.TFNF == 0
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_tx_fifo_is_full(ALT_SPI_DEV_t *spi_dev);

/*!
 * Returns the number of valid entries in the transmit FIFO.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       num_entries
 *              [out] The number of entries in the transmit FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_TXFLR.TXFLR
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_tx_fifo_level_get(ALT_SPI_DEV_t *spi_dev,
                                          uint32_t *num_entries);

/*!
 * Gets the current transmit FIFO threshold level value.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       threshold
 *              [out] The current threshold value.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_TX_TL.TX_TL
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_tx_fifo_threshold_get(ALT_SPI_DEV_t *spi_dev,
                                              uint8_t *threshold);

/*!
 * Sets the current transmit FIFO threshold level value.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       threshold
 *              The threshold value.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_TX_TL.TX_TL = threshold
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_tx_fifo_threshold_set(ALT_SPI_DEV_t *spi_dev,
                                              const uint8_t threshold);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_SPI_TRANSFER Transfer Functions
 *
 * The functions in this section provide a high level serial transfer operations.
 *
 * These functions assume that the SPI master or serial controller configuration
 * has already been established by calls to configuration functions like
 * alt_spi_config_set() and alt_spi_baud_rate_set().
 * 
 * The transfer functions in this section modify settings for the SPI controller
 * interrupts and Tx/Rx FIFOs as part of their implementation. No attempt to
 * preserve established settings for interrupts and Tx/Rx FIFOs across calls to
 * the transfer functions in this section is made.
 *
 * \internal 
 * The functions in this section are variations of procedures detailed in chapter 3.
 * of DesignWare DW_apb_ssi Databook.
 *
 * You may implement the transfer functions to internally factor out common steps
 * of the transfer procedure as you deem appropriate.
 * \endinternal
 *
 * @{
 */

/******************************************************************************/
/*! \addtogroup ALT_SPI_TRANSFER_MASTER SPI Master Controller Transfer Functions
 *
 * The transfer functions in this group are for SPI controllers configured as
 * masters.
 *
 * @{
 */

/*!
 * This function performs a master SPI/SSP serial transmit and receive transfer.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       slave_select
 *              A mask of the slave select output signal line(s) to enable.  \e
 *              slave_selects is a mask of logically OR'ed \ref ALT_SPI_SS_t
 *              values that designate the slave select outputs to enable during the
 *              transfer operation.
 *
 * \param       num_frames
 *              The number of data frames involved in the transfer
 *              operation. Valid range: 1 to 65536.
 *
 * \param       tx_buf
 *              A buffer of data frames to transmit. The \e tx_buf element type is
 *              sized large enough to contain the widest possible data frame
 *              size. The data in each frame should be right justified within its
 *              \e tx_buf element. The buffer is expected to contain \e num_frames
 *              data frames for transmittal.
 *
 * \param       rx_buf
 *              [out] An buffer to receive data frames sent from the slave. The
 *              buffer is expected to be at least \e num_frames data frames in
 *              length.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal 
 * Use procedure specified in section 3.6.1.4 of DesignWare DW_apb_ssi
 * Databook. You may use interrupts to handle Tx FIFO, Rx FIFO, and BUSY event
 * conditions.
 * 
 * * Preconditions to calling this function are that the SPI
 *   controller has been configured with calls to:
 *   - alt_spi_config_set()
 *   - alt_spi_baud_rate_set()
 * * CTRLR0.TMOD = ALT_SPI_TMOD_TXRX
 * * Follow steps 3 - 8 of the procedure.
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_master_tx_rx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                              const uint32_t slave_select,
                                              const size_t num_frames,
                                              const uint16_t * tx_buf, 
                                              uint16_t * rx_buf);

/*!
 * This function performs a master SPI/SSP serial transmit only transfer.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       slave_select
 *              A mask of the slave select output signal line(s) to enable.  \e
 *              slave_selects is a mask of logically OR'ed \ref ALT_SPI_SS_t
 *              values that designate the slave select outputs to enable during the
 *              transfer operation.
 *
 * \param       num_frames
 *              The number of data frames involved in the transfer
 *              operation. Valid range: 1 to 65536.
 *
 * \param       tx_buf
 *              A buffer of data frames to transmit. The \e tx_buf element type is
 *              sized large enough to contain the widest possible data frame
 *              size. The data in each frame should be right justified within its
 *              \e tx_buf element. The buffer is expected to contain \e num_frames
 *              data frames for transmittal.
 *
 * \internal 
 * Use procedure specified in section 3.6.1.4 of DesignWare DW_apb_ssi
 * Databook. You may use interrupts to handle Tx FIFO, Rx FIFO, and BUSY event
 * conditions.
 * 
 * * Preconditions to calling this function are that the SPI
 *   controller has been configured with calls to:
 *   - alt_spi_config_set()
 *   - alt_spi_baud_rate_set()
 * * CTRLR0.TMOD = ALT_SPI_TMOD_TX
 * * Follow steps 3 - 8 of the procedure.
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_master_tx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                           const uint32_t slave_select,
                                           const size_t num_frames,
                                           const uint16_t * tx_buf);

/*!
 * This function performs a master SPI/SSP serial receive only transfer.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       slave_select
 *              A mask of the slave select output signal line(s) to enable.  \e
 *              slave_selects is a mask of logically OR'ed \ref ALT_SPI_SS_t
 *              values that designate the slave select outputs to enable during the
 *              transfer operation.
 *
 * \param       num_frames
 *              The number of data frames involved in the transfer
 *              operation. Valid range: 1 to 65536.
 *
 * \param       rx_buf
 *              [out] An buffer to receive data frames sent from the slave. The
 *              buffer is expected to be at least \e num_frames data frames in
 *              length.
 *
 * \internal 
 * Use procedure specified in section 3.6.1.4 of DesignWare DW_apb_ssi
 * Databook. You may use interrupts to handle Tx FIFO, Rx FIFO, and BUSY event
 * conditions.
 * 
 * * Preconditions to calling this function are that the SPI
 *   controller has been configured with calls to:
 *   - alt_spi_config_set()
 *   - alt_spi_baud_rate_set()
 * * CTRLR0.TMOD = ALT_SPI_TMOD_RX
 * * CTRLR1.NDF = num_frames - 1
 * * Follow steps 3 - 8 of the procedure.
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_master_rx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                           const uint32_t slave_select,
                                           const size_t num_frames,
                                           uint16_t * rx_buf);

/*!
 * This function performs a master SPI EEPROM read transfer.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       slave_select
 *              A mask of the slave select output signal line(s) to enable.  \e
 *              slave_selects is a mask of logically OR'ed \ref ALT_SPI_SS_t
 *              values that designate the slave select outputs to enable during the
 *              transfer operation.
 *
 * \param       opcode
 *              The opcode to transmit to the EEPROM device.
 *
 * \param       eeprom_addr
 *              The address transmitted to access the EEPROM device.
 *
 * \param       num_frames
 *              The number of data frames involved in the transfer
 *              operation. Valid range: 1 to 65536.
 *
 * \param       rx_buf
 *              [out] An buffer to receive data frames sent from the slave. The
 *              buffer is expected to be at least \e num_frames data frames in
 *              length.
 *
 * \internal 
 * Use procedure specified in section 3.6.1.4 of DesignWare DW_apb_ssi
 * Databook. You may use interrupts to handle Tx FIFO, Rx FIFO, and BUSY event
 * conditions.
 * 
 * * Preconditions to calling this function are that the SPI
 *   controller has been configured with calls to:
 *   - alt_spi_config_set()
 *   - alt_spi_baud_rate_set()
 * * assert( CTRLR0.FRF == ALT_SPI_FRF_SPI )
 * * CTRLR0.TMOD = ALT_SPI_TMOD_EEPROM
 * * CTRLR1.NDF = num_frames - 1
 * * DR = opcode
 * * DR = (eeprom_addr >> 8) & 0xff
 * * DR = eeprom_addr & 0xff
 * * Follow steps 3 - 8 of the procedure.
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_master_eeprom_transfer(ALT_SPI_DEV_t *spi_dev, 
                                               const uint32_t slave_select,
                                               const uint8_t opcode,
                                               const uint16_t eeprom_addr,
                                               const size_t num_frames,
                                               uint16_t * rx_buf);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_SPI_TRANSFER_SLAVE SPI Slave Controller Transfer Functions
 *
 * The transfer functions in this group are for SPI controllers configured as
 * slaves.
 *
 * @{
 */

/*!
 * This function performs a slave SPI/SSP serial transmit and receive transfer.
 *
 * This API is suitable for being called during an interrupt context. It is the
 * programmer's responsibility to ensure that there is enough space in the TX
 * FIFO and space in the RX FIFO to accomodate the request made.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       tx_buf
 *              A buffer of data frames to transmit. The \e tx_buf element type is
 *              sized large enough to contain the widest possible data frame
 *              size. The data in each frame should be right justified within its
 *              \e tx_buf element.
 *
 * \param       rx_buf
 *              [out] An buffer to receive data frames sent from the master. The
 *              buffer is expected to be at least \e buf_len data frames in
 *              length.
 *
 * \param       buf_len
 *              The length in data frames of the \e tx_buf and \e rx_buf buffers.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal 
 * Use procedure specified in section 3.6.2.1 of DesignWare DW_apb_ssi
 * Databook. You may use interrupts to handle Tx FIFO, Rx FIFO, and BUSY event
 * conditions.
 * 
 * * Preconditions to calling this function are that the SPI
 *   controller has been configured with calls to:
 *   - alt_spi_config_set()
 *   - alt_spi_baud_rate_set()
 * * CTRLR0.TMOD = ALT_SPI_TMOD_TXRX
 * * Follow steps 3 - 8 of the procedure.
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_slave_tx_rx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                             const uint16_t * tx_buf, 
                                             uint16_t * rx_buf,
                                             const size_t buf_len);

/*!
 * This function performs a slave SPI/SSP serial transmit only transfer.
 *
 * This API is suitable for being called during an interrupt context. It is the
 * programmer's responsibility to ensure that there is enough space in the TX
 * FIFO to accomodate the request made.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       tx_buf
 *              A buffer of data frames to transmit. The \e tx_buf element type is
 *              sized large enough to contain the widest possible data frame
 *              size. The data in each frame should be right justified within its
 *              \e tx_buf element.
 *
 * \param       buf_len
 *              The length in data frames of the \e tx_buf buffer.
 *
 * \internal 
 * Use procedure specified in section 3.6.2.1 of DesignWare DW_apb_ssi
 * Databook. You may use interrupts to handle Tx FIFO, Rx FIFO, and BUSY event
 * conditions.
 * 
 * * Preconditions to calling this function are that the SPI
 *   controller has been configured with calls to:
 *   - alt_spi_config_set()
 *   - alt_spi_baud_rate_set()
 * * CTRLR0.TMOD = ALT_SPI_TMOD_TX
 * * Follow steps 3 - 8 of the procedure.
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_slave_tx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                          const uint16_t * tx_buf,
                                          const size_t buf_len);

/*!
 * This function performs a slave SPI/SSP serial receive only transfer.
 *
 * This API is suitable for being called during an interrupt context. It is the
 * programmer's responsibility to ensure that there is enough data in the RX
 * FIFO to accomodate the request made.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       rx_buf
 *              [out] An buffer to receive data frames sent from the master. The
 *              buffer is expected to be at least \e buf_len data frames in
 *              length.
 *
 * \param       buf_len
 *              The length in data frames of the \e rx_buf buffer.
 *
 * \internal 
 * Use procedure specified in section 3.6.2.1 of DesignWare DW_apb_ssi
 * Databook. You may use interrupts to handle Tx FIFO, Rx FIFO, and BUSY event
 * conditions.
 * 
 * * Preconditions to calling this function are that the SPI
 *   controller has been configured with calls to:
 *   - alt_spi_config_set()
 *   - alt_spi_baud_rate_set()
 * * CTRLR0.TMOD = ALT_SPI_TMOD_RX
 * * CTRLR1.NDF = num_frames - 1
 * * Follow steps 3 - 8 of the procedure.
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_slave_rx_transfer(ALT_SPI_DEV_t *spi_dev, 
                                          uint16_t * rx_buf,
                                          const size_t buf_len);

/*! @} */

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_SPI_DMA DMA Interface
 *
 * The functions in this section provide control and accsss to the DMA interface
 * of the SPI controller.
 *
 * The SPI controller supports DMA signaling to indicate when the receive FIFO
 * buffer has data ready to be read or when the transmit FIFO buffer needs
 * data. It requires two DMA channels, one for transmit data and one for receive
 * data. The SPI controller can issue single or burst DMA transfers and accepts
 * burst acknowledges from the DMA. Software can trigger the DMA burst mode by
 * enabling and programming an appropriate threshold value for the DMA
 * interface. The typical setting of the threshold value is half the size of the
 * Tx/Rx FIFO.
 *
 * @{
 */

/*!
 * Disable the transmit (Tx) FIFO DMA channel.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * DMACR.TDMAE = 0
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_dma_tx_disable(ALT_SPI_DEV_t *spi_dev);

/*!
 * Enable and set the transmit data level for the transmit (Tx) FIFO DMA channel.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       level
 *              The transmit data level value at which the DMA request is made by
 *              the SPI controller transmit logic. The DMA request signal is
 *              generated when the number of valid data entries in the Tx FIFO is
 *              equal or below the \e level value. Valid values: 0 <= \e level < 
 *              ALT_SPI_TX_FIFO_NUM_ENTRIES.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * DMATLDLR.DMATDL = level
 * DMACR.TDMAE = 1
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_dma_tx_enable(ALT_SPI_DEV_t *spi_dev, const uint32_t level);

/*!
 * Disable the receive (Rx) FIFO DMA channel.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * DMACR.RDMAE = 0
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_dma_rx_disable(ALT_SPI_DEV_t *spi_dev);

/*!
 * Enable and set the receive data level for the receive (Rx) FIFO DMA channel.
 *
 * \param       spi_dev
 *              A pointer to the SPI controller device block instance.
 *
 * \param       level
 *              The receive data level value at which the DMA request is made by
 *              the SPI controller receive logic. The DMA request signal is
 *              generated when the number of valid data entries in the Rx FIFO is
 *              equal or below the \e level value. Valid values: 0 < \e level <= 
 *              ALT_SPI_RX_FIFO_NUM_ENTRIES.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * DMARDLR.DMARDL = level + 1
 * DMACR.RDMAE = 1
 * \endinternal
 */
ALT_STATUS_CODE alt_spi_dma_rx_enable(ALT_SPI_DEV_t *spi_dev, const uint32_t level);

/*! @} */

/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_SPI_H__ */
