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

#ifndef __ALT_SDMMC_H__
#define __ALT_SDMMC_H__

#include "hwlib.h"

#ifdef __cplusplus
extern "C"
{
#endif /* __cplusplus */

/******************************************************************************/
/*!
 * \addtogroup ALT_SDMMC SD/MMC Controller API
 *
 * This module defines the API for controlling and accessing devices through the
 * HPS SD/MMC Controller.
 *
 * This module provides programmatic access to the SD/MMC host
 * controller functions for:
 * * control and status
 * * card/device interface configuration
 * * command processor interface
 * * internal DMA controller
 * * FIFO
 *
 * The primary purpose of this API is to a provide a general purpose framework
 * that can be used for writing software drivers that interact with a wide range of
 * card and device types that may interface to HPS through the SD/MMC host controller.
 * 
 * Although the HPS SD/MMC Controller supports SD, SDIO, CE-ATA, and MMC card and
 * device types, this driver only supports block read/write data transfers to
 * SD and MMC storage devices.
 *
 * Supported:
 *  * Integrated DMA Controller (IDMAC)
 *  * Host Bus: AHB (32-bit)
 *  * SD/MMC controller may be used by FPGA
 *
 * Unsupported:
 *  * Dual Data Rate (DDR)
 *  * More than one card
 *  * SDR104, SDR50, and DDR5 timing modes
 *
 * Clock Signals:
 *  * l4_mp_clk - AHB/APB Clock, Frequency Range: 0-100MHz, Must be greater than or equal to 1/10 cclk_in
 *  * sdmmc_clk - Card input clock. Both positive and negative edges are used, Frequency Range: 0-200MHz
 *  * sdmmc_cclk_out - Card Clock. Output from internal clock dividers.
 *  * sdmmc_fb_clk_in - Feedback version of cclk_out to compensate for external delays, Frequency Range: 0-50MHz
 *
 * Interface Signals:
 * SD/MMC Controller Interface I/O Pins
 * Signal        Width    Direction     Description
 * ======================================================================
 * sdmmc_cclk_out  1      Out           Clock from controller to the card
 * sdmmc_cmd       1      In/Out        Card command
 * sdmmc_pwren     1      Out           External device power enable
 * sdmmc_data      8      In/Out        Card data
 *
 * Interrupts:
 *  * Three (3) interrupt outputs:
 *    - sdmmc_int
 *      + SDIO card interrupts
 *      + End bit error(read)/no CRC(write)
 *      + Auto command done
 *      + Start bit error
 *      + Hardware locked write error
 *      + FIFO underrun/overrun error
 *      + Data starvation by host timeout
 *      + Data read timeout/boot data start
 *      + Response Timeout/Boot ack received
 *      + Data CRC error
 *      + Response CRC error
 *      + Receive FIFO data request
 *      + Transmit FIFO data request
 *      + Data transfer over
 *      + Command done
 *      + Response error
 *    - sdmmc_sberr, single bit ECC error
 *    - sdmmc_dberr, double bit ECC error
 *
 * References:
 *  * Altera, Cyclone V Device Handbook Volume 3: Hard Processor System
 *    Technical Reference Manual, SD/MMC Controller.
 *  * Synopsys, DesignWare Cores Mobile Storage Host Databook, DWC_mobile_storage
 *
 * Notes:
 *  * To avoid glitches in the card clock outputs (cclk_out), the software should
 *    use the steps outlined in section 7.4 Phase Switching of the databook when
 *    changing the card clock frequency.
 *    
 *  * In order to utilize ECC, follow the embedded RAM initialization procedure in
 *    section 8 Enabling ECC of the data book.
 *
 *  * The SD/MMC controller does not directly support voltage switching, card
 *    interrupts, or back-end power control of eSDIO card devices. However, you can
 *    connect these signals to general-purpose I/Os (GPIOs).
 *
 *  * The SD/MMC controller does not contain a reset output as part of the external
 *    card interface. To reset the flash card device, consider using a general
 *    purpose output pin.
 *
 * Features:
 *  * Block Read/Write support
 *    - Internal DMA used for efficiency
 *  * Command Engine Interface 
 *  * Internal DMA Interface
 *  * Configuration and Status Interface
 *  * Interrupt Status and Control Interface
 * @{
 */

/******************************************************************************/
/*! \addtogroup ALT_SDMMC_CSR General Control and Status Functions
 *
 * The declarations and functions in this group provide general purpose control
 * and status functions for the SD/MMC Controller.
 * @{
 */

/*!
 * This type enumerates the possible card/device type that may be connected to the
 * SD/MMC controller.
 */
typedef enum ALT_SDMMC_CARD_TYPE_e
{
    ALT_SDMMC_CARD_TYPE_NOTDETECT  = 0, /*!< Cart type has not identified yet */
    ALT_SDMMC_CARD_TYPE_MMC        = 1, /*!< MultiMedia Card */
    ALT_SDMMC_CARD_TYPE_SD         = 2, /*!< Secure Digital Memory Card */
    ALT_SDMMC_CARD_TYPE_SDIOIO     = 3, /*!< Secure Digital Input Output */
    ALT_SDMMC_CARD_TYPE_SDIOCOMBO  = 4, /*!< Secure Digital Input Output Combo */
    ALT_SDMMC_CARD_TYPE_SDHC       = 5, /*!< Secure Digital High Capacity */
    ALT_SDMMC_CARD_TYPE_CEATA      = 6, /*!< Serial ATA interface based on the 
                                         *   MultiMediaCard standard
                                         */
} ALT_SDMMC_CARD_TYPE_t;

/*!
 * This type defines a structure to hold identification and type information for a
 * card connected to the SD/MMC controller.
 *
 * \internal
 * See: Card_info declaration in synopmob_bus.h
 * \endinternal
 */
typedef struct ALT_SDMMC_CARD_INFO_s
{
    ALT_SDMMC_CARD_TYPE_t   card_type;          /*!< Type of the card */
    uint32_t                rca;                /*!< Releative Card Address (RCA) */
    uint32_t                xfer_speed;         /*!< The maximum data transfer rate (bit/s) */
    uint32_t                max_r_blkln;        /*!< Max read data block length */
    uint32_t                max_w_blkln;        /*!< Max write data block length */
    bool                    partial_r_allowed;  /*!< Partial blocks for read allowed */
    bool                    partial_w_allowed;  /*!< Partial blocks for write allowed */
} ALT_SDMMC_CARD_INFO_t;

/*!
 * Initialize the SD/MMC controller.
 * 
 * Initializes the SD/MMC controller by gracefully bringing the controller out of
 * reset. This function also initializes the registers, FIFO buffer pointers, DMA
 * interface controls, and state machines in the controller. All interrupts are
 * cleared and disabled (masked) and timeout parameters set to default values.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_sdmmc_init(void);

/*!
 * Uninitializes the SD/MMC controller by stopping any data transfers in progress and
 * putting the controller into reset.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_sdmmc_uninit(void);

/*!
 * Reset the SD/MMC controller by stopping any data transfers in progress and
 * putting the controller into reset and reinit it after reset complete.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_sdmmc_reset(void);

/*!
 * This type enumerates the SDMMC evailable commands. Read specification 
 * to the appropriate card type
 */
typedef enum ALT_SDMMC_CMD_INDEX_e
{
    /* TBD - Standart sdmmc commands... */
    ALT_SDMMC_GO_IDLE_STATE          = 0,
    ALT_SDMMC_ALL_SEND_CID           = 2,
    ALT_SDMMC_SET_RELATIVE_ADDR      = 3,
    ALT_SDMMC_SET_DSR                = 4,
    ALT_SDMMC_SEND_OP_COND           = 5,
    ALT_SDMMC_SWITCH                 = 6,
    ALT_SDMMC_SEL_DES_CARD           = 7,
    ALT_SDMMC_IF_COND                = 8,
    ALT_SDMMC_SEND_EXT_CSD           = 8,
    ALT_SDMMC_SEND_CSD               = 9,
    ALT_SDMMC_SEND_CID               = 10,
    ALT_SDMMC_READ_DAT_UNTIL_STOP    = 11,
    ALT_SDMMC_STOP_TRANSMISSION      = 12,
    ALT_SDMMC_SEND_STATUS            = 13,
    ALT_SDMMC_GO_INACTIVE_STATE      = 15,
    ALT_SDMMC_SET_BLOCKLEN           = 16,
    ALT_SDMMC_READ_SINGLE_BLOCK      = 17,
    ALT_SDMMC_READ_MULTIPLE_BLOCK    = 18,
    ALT_SDMMC_WRITE_DAT_UNTIL_STOP   = 20,
    ALT_SDMMC_WRITE_BLOCK            = 24,
    ALT_SDMMC_WRITE_MULTIPLE_BLOCK   = 25,
    ALT_SDMMC_PROGRAM_CID            = 26,
    ALT_SDMMC_PROGRAM_CSD            = 27,
    ALT_SDMMC_SET_WRITE_PROT         = 28,
    ALT_SDMMC_CLR_WRITE_PROT         = 29,
    ALT_SDMMC_SEND_WRITE_PROT        = 30,
    ALT_SDMMC_TAG_SECTOR_START       = 32,
    ALT_SDMMC_TAG_SECTOR_END         = 33,
    ALT_SDMMC_UNTAG_SECTOR           = 34,
    ALT_SDMMC_TAG_ERASE_GROUP_START  = 35,
    ALT_SDMMC_TAG_ERASE_GROUP_END    = 36,
    ALT_SDMMC_UNTAG_ERASE_GROUP      = 37,
    ALT_SDMMC_ERASE                  = 38,
    ALT_SDMMC_FAST_IO                = 39,
    ALT_SDMMC_GO_IRQ_STATE           = 40,
    ALT_SDMMC_LOCK_UNLOCK            = 42,
    ALT_SDMMC_APP_CMD                = 55,
    ALT_SDMMC_GEN_CMD                = 56,
    ALT_SDMMC_READ_OCR               = 58,
    ALT_SDMMC_CRC_ON_OFF             = 59,
    
    ALT_SDMMC_STANDART_CMD_ALL       = 60,
    
    /* TBD - Commands specific for card type. */
    ALT_SD_SET_BUS_WIDTH             = 6,
    ALT_SD_SEND_OP_COND              = 41,
    ALT_SD_SEND_SCR                  = 51,

    /* TBD - Clock command or command index does not matter... */
    ALT_SDMMC_CLK_INDEX              = -1,

    ALT_SDMMC_CMD_ALL                = ALT_SDMMC_STANDART_CMD_ALL + 1
} ALT_SDMMC_CMD_INDEX_t;

/*!
 * This type defines a structure for command with options.
 */
typedef struct ALT_SDMMC_CMD_CONFIG_s 
{
    uint32_t    cmd_index                       : 6; //0-5
                                /*!< Command index */
    uint32_t    response_expect                 : 1; //6
                                /*!< Response expected from card */
    uint32_t    response_length_long            : 1; //7
                                /*!< Long response expected from card */
    uint32_t    check_response_crc              : 1; //8
                                /*!< Check response CRC */
    uint32_t    data_expected                   : 1; //9
                                /*!< Data transfer expected (read/write) */
    uint32_t    write_active                    : 1; //10
                                /*!< 0 – Read from card 
                                 *   1 – Write to card 
                                 */
    uint32_t    stream_mode_active              : 1; //11
                                /*!< Stream data transfer command */
    uint32_t    send_auto_stop                  : 1; //12
                                /*!< Send stop command at end of data transfer */
    uint32_t    wait_prvdata_complete           : 1; //13
                                /*!< Wait for previous data transfer completion
                                 *   before sending command 
                                 */
    uint32_t    stop_abort_cmd                  : 1; //14
                                /*!< Stop or abort command intended to stop
                                 *   current data transfer in progress.
                                 */
    uint32_t    send_initialization             : 1; //15
                                /*!< Send initialization sequence before 
                                 *   sending this command
                                 */
    uint32_t    card_number                     : 5; //16-20
                                /*!< Card number in use. Represents physical
                                 *   slot number of card being accessed.
                                 */
    uint32_t    update_clock_registers_only     : 1; //21
                                /*!< Do not send commands, just update clock
                                 *   register value into card clock domain
                                 */
    uint32_t    read_ceata_device               : 1; //22
                                /*!< Host is performing read access (RW_REG or RW_BLK)
                                 *   towards CE-ATA device 
                                 */
    uint32_t    ccs_expected                    : 1; //23
                                /*!< Interrupts are enabled in CE-ATA device (nIEN = 0),
                                 *   and RW_BLK command expects command completion
                                 *   signal from CE-ATA device 
                                 */
    uint32_t    enable_boot                     : 1; //24
                                /*!< Enable Boot—this bit should be set only for
                                 *   mandatory boot mode.
                                 */
    uint32_t    expect_boot_ack                 : 1; //25
                                /*!< Expect Boot Acknowledge. When Software sets
                                 *   this bit along with enable_boot, CIU expects a boot
                                 *   acknowledge start pattern of 0-1-0 from the selected card 
                                 */
    uint32_t    disable_boot                    : 1; //26
                                /*!< Disable Boot. */
    uint32_t    boot_mode                       : 1; //27
                                /*!< Boot Mode 
                                 *   0 - Mandatory Boot operation
                                 *   1 - Alternate Boot operation
                                 */
    uint32_t    volt_switch                     : 1; //28
                                /*!< Voltage switching enabled; must be set for CMD11 only */
    uint32_t    use_hold_reg                    : 1; //29
                                /*!< CMD and DATA sent to card through the HOLD Register */
    uint32_t    reserved                        : 1; //30
    uint32_t    start_bit                       : 1; //31
                                /*!< Start command. Once command is taken by CIU, 
                                 *   bit is cleared. When bit is set, host should 
                                 *   not attempt to write to any command registers. 
                                 *   If write is attempted, hardware lock error 
                                 *   is set in raw interrupt register.
                                 */
} ALT_SDMMC_CMD_CONFIG_t;

/*!
 * Send the a command and command argument to the card and optionally return the
 * command response.
 *
 * \param       command
 *              The card command.
 *
 * \param       command_arg
 *              The card command argument.
 *
 * \param       response
 *              [out] A pointer to a 4 (32-bit) word to return the card command
 *              response. If NULL is passed then any card command response is
 *              ignored.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_sdmmc_command_send(ALT_SDMMC_CMD_INDEX_t command,
                                        uint32_t command_arg, uint32_t *response);

/*!
 * This type defines a structure for get long response of last
 * last complete command.
 */
typedef struct ALT_SDMMC_RESPONSE_s
{
    uint32_t     resp0;
    uint32_t     resp1;
    uint32_t     resp2;
    uint32_t     resp3;
 } ALT_SDMMC_RESPONSE_t;

/*!
 * Get the long response of the last compleated command.
 *
 * \param       response
 *              [out] Pointer to a \ref ALT_SDMMC_RESPONSE_t structure to hold
 *              the long response.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_read_long_response(ALT_SDMMC_RESPONSE_t *response);

/*!
 * Returns the SD/MMC controller interrupt status register value which reflects
 * interrupt controller interrupt status conditions before masking.
 *
 * \returns     The raw value of the SD/MMC controller interrupt status register
 *              which reflects the current SD/MMC controller interrupt status
 *              conditions before masking.
 */
uint32_t alt_sdmmc_int_status_get(void);

/*!
 * Returns the SD/MMC controller interrupt mask register value which reflects the
 * enabled (i.e. unmasked) interrupt status conditions.
 *
 * \returns     The aggregate value of the enabled SD/MMC controller interrupt 
 *              status conditions.  A set (1) bit in the corresponding
 *              ALT_SDMMC_INT_STATUS_t position indicates an interrupt that is
 *              enabled. A clear (0) bit the corresponding ALT_SDMMC_INT_STATUS_t
 *              position indicates an interrupt that is masked.
 */
uint32_t alt_sdmmc_int_mask_get(void);

/*!
 * Clears the specified SD/MMC controller interrupt status conditions identified in
 * the mask.
 *
 * This function clears one or more of the status conditions as contributors to the
 * \b ALT_INT_INTERRUPT_SDMMC_IRQ interrupt signal state.
 *
 * \param       mask
 *              Specifies the SD/MMC controller status conditions to clear.  \e mask
 *              is a mask of logically OR'ed \ref ALT_SDMMC_INT_STATUS_t values that
 *              designate the status conditions to clear.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_sdmmc_int_clear(const uint32_t mask);

/*!
 * Disable the specified SD/MMC controller interrupt status conditions identified in
 * the mask.
 *
 * This function disables one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_SDMMC_IRQ interrupt signal state.
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have the
 * effect of enabling it as a contributor to the \b ALT_INT_INTERRUPT_SDMMC_IRQ
 * interrupt signal state. The function alt_sdmmc_int_enable() is used to enable
 * status source conditions.
 *
 * \param       mask
 *              Specifies the status conditions to disable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed \ref
 *              ALT_SDMMC_INT_STATUS_t values that designate the status conditions
 *              to disable.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_sdmmc_int_disable(const uint32_t mask);

/*!
 * Enable the specified SD/MMC controller interrupt status conditions identified in
 * the mask.
 *
 * This function enables one or more of the status conditions as contributors to the
 * \b ALT_INT_INTERRUPT_SDMMC_IRQ interrupt signal state.
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have the
 * effect of disabling it as a contributor to the \b ALT_INT_INTERRUPT_SDMMC_IRQ
 * interrupt signal state. The function alt_sdmmc_int_disable() is used to disable
 * status source conditions.
 *
 * \param       mask
 *              Specifies the status conditions to enable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed \ref
 *              ALT_SDMMC_INT_STATUS_t values that designate the status conditions
 *              to enable.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_sdmmc_int_enable(const uint32_t mask);

/*!
 * This type definition enumerates the interrupt status conditions that contribute
 * to the \b ALT_INT_INTERRUPT_SDMMC_IRQ signal state.
 *
 * NOTE: Both the general purpose interrupt status conditions for the SD/MMC
 * controller (\ref ALT_SDMMC_INT_STATUS_t) and the interrupt status conditions
 * for the internal DMA controller (\ref ALT_SDMMC_DMA_INT_STATUS_t) contribute to
 * the overall \b ALT_INT_INTERRUPT_SDMMC_IRQ signal state
 */
typedef enum ALT_SDMMC_INT_STATUS_e
{
    ALT_SDMMC_INT_STATUS_CD     = (1UL << 0),    /*!< Card Detect (CD) */
    ALT_SDMMC_INT_STATUS_RE     = (1UL << 1),    /*!< Response Error (RE) */
    ALT_SDMMC_INT_STATUS_CMD    = (1UL << 2),    /*!< Command Done (CMD) */
    ALT_SDMMC_INT_STATUS_DTO    = (1UL << 3),    /*!< Data Transfer Over (DTO) */
    ALT_SDMMC_INT_STATUS_TXDR   = (1UL << 4),    /*!< Transmit FIFO Data Request (TXDR) */
    ALT_SDMMC_INT_STATUS_RXDR   = (1UL << 5),    /*!< Receive FIFO Data Request (RXDR) */
    ALT_SDMMC_INT_STATUS_RCRC   = (1UL << 6),    /*!< Response CRC Error (RCRC) */
    ALT_SDMMC_INT_STATUS_DCRC   = (1UL << 7),    /*!< Data CRC Error (DCRC) */
    ALT_SDMMC_INT_STATUS_RTO    = (1UL << 8),    /*!< Response Timeout Boot Ack Received (RTO) */
    ALT_SDMMC_INT_STATUS_DRTO   = (1UL << 9),    /*!< Data Read Timeout Boot Data Start (DRTO) */
    ALT_SDMMC_INT_STATUS_HTO    = (1UL << 10),   /*!< Data Starvation Host Timeout (HTO) / Volt Switch_int */
    ALT_SDMMC_INT_STATUS_FRUN   = (1UL << 11),   /*!< FIFO Underrun Overrun Error (FRUN) */
    ALT_SDMMC_INT_STATUS_HLE    = (1UL << 12),   /*!< Hardware Locked Write Error (HLE) */
    ALT_SDMMC_INT_STATUS_SBE    = (1UL << 13),   /*!< Start-Bit Error (SBE) */
    ALT_SDMMC_INT_STATUS_ACD    = (1UL << 14),   /*!< Auto Command Done (ACD) */
    ALT_SDMMC_INT_STATUS_EBE    = (1UL << 15),   /*!< End-Bit Error (read) / write no CRC (EBE) */
    ALT_SDMMC_INT_STATUS_SDIO_0 = (1UL << 16),    /*!< SDIO Interrupt Card 0 - only one card supported */

    ALT_SDMMC_INT_STATUS_ALL    = 0x1FFFF    /*!< All previous status types*/
} ALT_SDMMC_INT_STATUS_t;

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_SDMMC_CARD_INTFC Card Interface
 *
 * The clock control block provides different clock frequencies required for
 * SD/MMC/CE-ATA cards. The clock control block has one clock divider, which is
 * used to generate different card clock frequencies.
 *
 * The clock divider is used to generate different clock frequencies required for
 * the cards. The division factor for the clock divider can be set by calling the
 * alt_sdmmc_card_clk_div_set() function. The clock divider is an 8-bit value that
 * provides a clock division factor from 1 to 510; a value of 0 represents a
 * clock-divider bypass, a value of 1 represents a divide by 2, a value of 2
 * represents a divide by 4, and so on.
 *
 * @{
 */

/*!
 * This type enumerates the SDMMC evailable bus width.
 */
typedef enum ALT_SDMMC_BUS_WIDTH_e
{
    ALT_SDMMC_BUS_WIDTH_1         = 1,
    ALT_SDMMC_BUS_WIDTH_4         = 4,
    ALT_SDMMC_BUS_WIDTH_8         = 8
}ALT_SDMMC_BUS_WIDTH_t;

/*!
 * This type defines a structure for configuration of miscellaneous interface
 * parameters for an attached card.
 */
typedef struct ALT_SDMMC_CARD_MISC_s
{
    uint32_t                 response_timeout; /*!< Card response timeout period in
                                                *   sdmmc_cclk_out (SD/MMC card clock) ticks.
                                                */
    uint32_t                 data_timeout;     /*!< Card data read timeout period in
                                                *   sdmmc_cclk_out (SD/MMC card clock) ticks.
                                                */
    ALT_SDMMC_BUS_WIDTH_t    card_width;       /*!< Indicates card interface width (1, 4, or
                                                *   8 bits).
                                                */
    uint32_t                 block_size;       /*!< The card block size in bytes. */
    uint32_t                 debounce_count;   /*!< Number of host clock (l4_mp_clk) ticks
                                                *   used to debounce card interface signals.
                                                */
} ALT_SDMMC_CARD_MISC_t;

/*!
 * Get the current card interface configuration values for the miscellaneous set
 * of parameters.
 *
 * \param       card_misc_cfg
 *              [out] Pointer to a \ref ALT_SDMMC_CARD_MISC_t structure to hold
 *              the returned card interface parameters.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_card_misc_get(ALT_SDMMC_CARD_MISC_t *card_misc_cfg);

/*!
 * Set the specified card interface configuration for the miscellaneous set of
 * parameters.
 *
 * \param       card_misc_cfg
 *              Pointer to a \ref ALT_SDMMC_CARD_MISC_t structure holding the card
 *              interface parameters to configure.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_card_misc_set(const ALT_SDMMC_CARD_MISC_t *card_misc_cfg);

/*!
 * Set the bus width appropriate supported by the card, send this parameter to the card.
 *
 * \param       width
 *              Indicates card interface width.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_card_bus_width_set(const ALT_SDMMC_BUS_WIDTH_t width);

/*!
 * Send block size to the card.
 *
 * \param       block_size
 *              The card block size in bytes.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_card_block_size_set(const uint16_t block_size);

/*!
 * Detects and identifies any connected card.
 *
 * Detects any connected card (only one connected card is possible in this
 * implementation) and returns the device identity and properties.
 *
 * \param       card_info
 *              [out] A pointer to a ALT_SDMMC_CARD_INFO_t structure to hold
 *              identification and device property information for any detected
 *              card.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_card_identify(ALT_SDMMC_CARD_INFO_t *card_info);

/*!
 * Gets the configured card clock divider value (\b sdmmc_cclk_out).
 *
 * Returns the card clock divider value. Clock division is a 2 * n value. For
 * example, a value of 0 means divide by 2 * 0 = 0 (no division, effectively a
 * bypass), a value of 1 means divide by 2 * 1 = 2, value of 0xff means divide by 2
 * * 255 = 510. Valid range is 0 to 255.
 * 
 * \returns     The clock divider value.
 */
uint32_t alt_sdmmc_card_clk_div_get(void);

/*!
 * Sets the card clock divider configuration (\b sdmmc_cclk_out).
 *
 * \param       clk_div
 *              Clock divider value. Clock division is 2 * n. For example, a value
 *              of 0 means divide by 2 * 0 = 0 (no division, effectively a bypass),
 *              a value of 1 means divide by 2 * 1 = 2, value of 0xff means divide
 *              by 2 * 255 = 510. Valid range is 0 to 255.
 * 
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 *              
 * \internal
 * The card clock must be diesabled before changing the clk_div value.
 * \endinternal
 */
ALT_STATUS_CODE alt_sdmmc_card_clk_div_set(const uint32_t clk_div);

/*!
 * Gets the configured card data transfer rate in bit/s. The units is
 * compatible with ALT_SDMMC_CARD_INFO_t::tran_speed.
 *
 * \returns     The data transfer rate in bit/s.
 */
uint32_t alt_sdmmc_card_speed_get(void);

/*!
 * Sets the card data transfer rate. The units is compatible with
 * ALT_SDMMC_CARD_INFO_t::tran_speed.
 *
 * \param       Desired data transfer rate in bit/s.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_sdmmc_card_speed_set(uint32_t xfer_speed);

/*!
 * Disables the card clock (\b sdmmc_cclk_out).
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_sdmmc_card_clk_disable(void);

/*!
 * Enables the card clock (\b sdmmc_cclk_out).
 *
 * \param       use_low_pwr_mode
 *              If true then low-power mode is enabled to save card power, the \b
 *              sdmmc_cclk_out signal is disabled when the card is idle for at
 *              least eight card clock cycles. Low-power mode is enabled when a
 *              new command is loaded and the command path goes to a non-idle
 *              state.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_sdmmc_card_clk_enable(const bool use_low_pwr_mode);

/*!
 * Returns true if the card clock (\b sdmmc_cclk_out) is enabled otherwise returns
 * false.
 *
 * \retval      true            The card clock is enabled.
 * \retval      false           The card clock is not enabled.
 */
bool alt_sdmmc_card_clk_is_enabled(void);

/*!
 * Reset the card device.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 *
 * \internal
 * NOT IMPLEMENTED
 * The SD/MMC controller does not contain a reset output as part of the external
 * card interface. To reset the flash card device, consider using a general
 * purpose output pin.
 * \endinternal
 */
ALT_STATUS_CODE alt_sdmmc_card_reset(void);

/*!
 * Returns true if a card presence is detected otherwise returns false.
 *
 * \retval      true            A card is present.
 * \retval      false           A card is not present.
 *              
 * \internal
 * \endinternal
 */
bool alt_sdmmc_card_is_detected(void);

/*!
 * Returns true if card write protection is enabled otherwise returns false.
 *
 * \retval      true            Card is write protected.
 * \retval      false           Card is not write protected.
 *              
 * \internal
 * \endinternal
 */
bool alt_sdmmc_card_is_write_protected(void);

/*!
 * Returns true if power is on (enabled) to the card otherwise returns false.
 *
 * \retval      true            Card power is on (enabled).
 * \retval      false           Card power is off (disabled).
 *              
 * \internal
 * pwren
 * \endinternal
 */
bool alt_sdmmc_card_pwr_is_on(void);

/*!
 * Enable (turn on) power to the card device.
 *
 * This function enables power to the card device allowing for power ramp-up time
 * before returning.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_card_pwr_on(void);

/*!
 * Disable (turn off) power to the card device.
 *
 * This function disables power to the card device.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_card_pwr_off(void);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_SDMMC_DMA SD/MMC Controller Internal DMA
 *
 * The internal DMA controller has a control and status register interface and a
 * single transmit or receive engine, which transfers data from system memory to
 * the card and vice versa. The controller uses a descriptor mechanism to
 * efficiently move data from source to destination with minimal host processor
 * intervention. You can set up the controller to interrupt the host processor in
 * situations such as transmit and receive data transfer completion from the card,
 * as well as other normal or error conditions. The DMA controller and the host
 * driver communicate through a single data structure.
 *
 * The internal DMA controller transfers the data received from the card to the
 * data buffer in the system memory, and transfers transmit data from the data
 * buffer in the memory to the controller's FIFO buffer. Descriptors that reside
 * in the system memory act as pointers to these buffers.
 *
 * A data buffer resides in the physical memory space of the system memory and
 * consists of complete or partial data. The buffer status is maintained in the
 * descriptor. Data chaining refers to data that spans multiple data
 * buffers. However, a single descriptor cannot span multiple data buffers.
 *
 * A single descriptor is used for both reception and transmission. The base
 * address of the list is written into the descriptor list base address
 * register. A descriptor list is forward linked. The last descriptor can point
 * back to the first entry to create a ring structure. The descriptor list resides
 * in the physical memory address space of the host. Each descriptor can point to
 * a maximum of two data buffers.
 *
 * @{
 */

/*!
 * This type definition enumerates the interrupt status conditions from the
 * SD/MMC internal DMA controller that contribute to the \b
 * ALT_INT_INTERRUPT_SDMMC_IRQ signal state.
 *
 * NOTE: Both the general purpose interrupt status conditions for the SD/MMC
 * controller (\ref ALT_SDMMC_INT_STATUS_t) and the interrupt status conditions
 * for the internal DMA controller (\ref ALT_SDMMC_DMA_INT_STATUS_t) contribute to
 * the overall \b ALT_INT_INTERRUPT_SDMMC_IRQ signal state
 */
typedef enum ALT_SDMMC_DMA_INT_STATUS_e
{
    ALT_SDMMC_DMA_INT_STATUS_TI   = (1UL << 0), /*!< Transmit Interrupt Enable */
    ALT_SDMMC_DMA_INT_STATUS_RI   = (1UL << 1), /*!< Receive Interrupt Enable */
    ALT_SDMMC_DMA_INT_STATUS_FBE  = (1UL << 2), /*!< Fatal Bus Error */
    ALT_SDMMC_DMA_INT_STATUS_DU   = (1UL << 4), /*!< Descriptor Unavailable Interrupt */
    ALT_SDMMC_DMA_INT_STATUS_CES  = (1UL << 5), /*!< Card Error Summary Interrupt Enable */
    ALT_SDMMC_DMA_INT_STATUS_NI   = (1UL << 8), /*!< Normal Interrupt Summary Enable */
    ALT_SDMMC_DMA_INT_STATUS_AI   = (1UL << 9), /*!< Abnormal Interrupt Summary Enable. */

    ALT_SDMMC_DMA_INT_STATUS_ALL  = 0x337,
} ALT_SDMMC_DMA_INT_STATUS_t;

/*!
 * This type defines the SD/MMC controller internal DMA controller descriptor
 * structure.
 *
 * The internal DMA controller uses these types of descriptor structures:
 *   * Dual-buffer structure - The distance between two descriptors is determined
 *     by the skip length value written to the descriptor skip length field
 *     of the bus mode register.
 *   * Chain structure - Each descriptor points to a unique buffer, and to the next
 *     descriptor in a linked list.
 */
typedef struct ALT_SDMMC_DMA_BUF_DESC_s
{
  /*! The DES0 field in the internal DMA controller descriptor contains control and
   *  status information.
   */
  union DES0
  {
    /*! Structure for DES0 register data fields. */
    struct
    {
      uint32_t                  :  1;           /*!< Reserved */
      uint32_t  dic             :  1;           /*!< Disable Interrupt on Completion
                                                 *   (DIC). When set to 1, this bit
                                                 *   prevents the setting of the
                                                 *   TI/RI bit of the internal DMA
                                                 *   controller status register
                                                 *   (idsts) for the data that ends
                                                 *   in the buffer pointed to by
                                                 *   this descriptor.
                                                 */
      uint32_t  ld              :  1;           /*!< Last Descriptor (LD). When set
                                                 *   to 1, this bit indicates that
                                                 *   the buffers pointed to by this
                                                 *   descriptor are the last buffers
                                                 *   of the data.
                                                 */
      uint32_t  fs              :  1;           /*!< First Descriptor (FS). When set
                                                 *   to 1, this bit indicates that
                                                 *   this descriptor contains the
                                                 *   first buffer of the data. If
                                                 *   the size of the first buffer is
                                                 *   0, next descriptor contains the
                                                 *   beginning of the data.
                                                 */
      uint32_t  ch              :  1;           /*!< Second Address Chained
                                                 *   (CH). When set to 1, this bit
                                                 *   indicates that the second
                                                 *   address in the descriptor is
                                                 *   the next descriptor address
                                                 *   rather than the second buffer
                                                 *   address. When this bit is set
                                                 *   to 1, BS2 (DES1[25:13]) must be
                                                 *   all zeros.
                                                 */
      uint32_t  er              :  1;           /*!< End of Ring (ER). When set to
                                                 *   1, this bit indicates that the
                                                 *   descriptor list reached its
                                                 *   final descriptor. The internal
                                                 *   DMA controller returns to the
                                                 *   base address of the list,
                                                 *   creating a descriptor ring. ER
                                                 *   is meaningful for only a
                                                 *   dual-buffer descriptor
                                                 *   structure.
                                                 */
      uint32_t  ces             :  1;           /*!< Card Error Summary (CES). The
                                                 *   CES bit indicates whether a
                                                 *   transaction error occurred. The
                                                 *   CES bit is the logical OR of
                                                 *   the following error bits in the
                                                 *   rintsts register.
                                                 *   * End-bit error (ebe) 
                                                 *   * Response timeout (rto)
                                                 *   * Response CRC (rcrc)
                                                 *   * Start-bit error (sbe)
                                                 *   * Data read timeout (drto)
                                                 *   * Data CRC for receive (dcrc)
                                                 *   * Response error (re)
                                                 */
      uint32_t                  : 24;           /*!< Reserved */
      uint32_t  own             :  1;           /*!< When set to 1, this bit
                                                 *   indicates that the descriptor
                                                 *   is owned by the internal DMA
                                                 *   controller. When this bit is
                                                 *   set to 0, it indicates that the
                                                 *   descriptor is owned by the
                                                 *   host. The internal DMA
                                                 *   controller resets this bit to 0
                                                 *   when it completes the data
                                                 *   transfer.
                                                 */
    }         fld;                              /*!< Union data member access to
                                                 *   DES0 fields.
                                                 */
    uint32_t  raw;                              /*!< The DES0 raw register aggregate
                                                 *   value.
                                                 */
  } des0;                                       /*!< The DES0 field in the internal
                                                 *   DMA controller descriptor
                                                 *   contains control and status
                                                 *   information.
                                                 */
  /*! The DES1 descriptor field contains the buffer size. */
  union DES1
  {
    /*! Structure for DES1 register data fields. */
    struct
    {
        uint32_t  bs1             : 13;           /*!< Buffer 1 Size (BS1). Indicates
                                                   *   the data buffer byte size,
                                                   *   which must be a multiple of
                                                   *   four bytes. When the buffer
                                                   *   size is not a multiple of four,
                                                   *   the resulting behavior is
                                                   *   undefined. If this field is 0,
                                                   *   the DMA ignores the buffer and
                                                   *   proceeds to the next descriptor
                                                   *   for a chain structure, or to
                                                   *   the next buffer for a
                                                   *   dual-buffer structure. If there
                                                   *   is only one descriptor and only
                                                   *   one buffer to be programmed,
                                                   *   you need to use only buffer 1
                                                   *   and not buffer 2.
                                                   */
        uint32_t  bs2             : 13;           /*!< Buffer 2 Size (BS2). These bits
                                                   *   indicate the second data buffer
                                                   *   byte size. The buffer size must
                                                   *   be a multiple of four. When the
                                                   *   buffer size is not a multiple
                                                   *   of four, the resulting behavior
                                                   *   is undefined. This field is not
                                                   *   valid if DES0[4] is set to 1.
                                                   */
        uint32_t                  :  6;           /*!< Reserved */

    }         fld;                              /*!< Union data member access to
                                                 *   DES1 fields.
                                                 */
    uint32_t  raw;                              /*!< The DES1 raw register aggregate
                                                 *   value.
                                                 */
  } des1;                                       /*!< The DES1 descriptor field
                                                 *   contains the buffer size.
                                                 */
  /*! The DES2 descriptor field contains the address pointer to the data buffer. */
  union DES2
  {
    /*! Structure for DES2 register data fields. */
    struct
    {
      uint32_t  bap1            : 32;           /*!< Buffer Address Pointer 1
                                                 *   (BAP1). These bits indicate the
                                                 *   physical address of the first
                                                 *   data buffer. The internal DMA
                                                 *   controller ignores DES2 [1:0],
                                                 *   because it only performs
                                                 *   32-bit-aligned accesses.
                                                 */
    }         fld;                              /*!< Union data member access to
                                                 *   DES2 fields.
                                                 */
    uint32_t  raw;                              /*!< The DES2 raw register aggregate
                                                 *   value.
                                                 */
  } des2;                                       /*!< The DES2 descriptor field
                                                 *   contains the address pointer to
                                                 *   the data buffer.
                                                 */
  /*! The DES3 descriptor field contains the address pointer to the next descriptor
   *  if the present descriptor is not the last descriptor in a chained descriptor
   *  structure or the second buffer address for a dual-buffer structure.
   */
  union DES3
  {
    /*! Structure for DES3 register data fields. */
    struct
    {
      uint32_t  bap2_or_next    : 32;           /*!< Buffer Address Pointer 2 (BAP2)
                                                 *   or Next Descriptor
                                                 *   Address. These bits indicate
                                                 *   the physical address of the
                                                 *   second buffer when the
                                                 *   dual-buffer structure is
                                                 *   used. If the Second Address
                                                 *   Chained (DES0[4]) bit is set to
                                                 *   1, this address contains the
                                                 *   pointer to the physical memory
                                                 *   where the next descriptor is
                                                 *   present. If this is not the
                                                 *   last descriptor, the next
                                                 *   descriptor address pointer must
                                                 *   be aligned to 32 bits. Bits 1
                                                 *   and 0 are ignored.
                                                 */
    }         fld;                              /*!< Union data member access to
                                                 *   DES3 fields.
                                                 */
    uint32_t  raw;                              /*!< The DES3 raw register aggregate
                                                 *   value.
                                                 */
  } des3;                                       /*!< The DES3 descriptor field
                                                 *   contains the address pointer to
                                                 *   the next descriptor if the
                                                 *   present descriptor is not the
                                                 *   last descriptor in a chained
                                                 *   descriptor structure or the
                                                 *   second buffer address for a
                                                 *   dual-buffer structure.
                                                 */

} ALT_SDMMC_DMA_BUF_DESC_t;

/*!
 * Resets the SD/MMC internal DMA controller.
 *
 * This function resets the SD/MMC controller DMA interface control logic and all
 * internal registers of the DMA controller.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 *
 * \internal
 * ctrl.dma_reset
 * bmod.swr
 * What's the difference if the effect of these two controls?
 * \endinternal
 */
ALT_STATUS_CODE alt_sdmmc_dma_reset(void);

/*!
 * Disables use of the SD/MMC controller internal DMA for data transfers.
 *
 * This function disables use of the SD/MMC controller internal DMA for data
 * transfers and requires the host to conduct data transfers through the slave
 * interface.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 *
 * \internal
 * ctrl.use_internal_dmac
 * bmod.de
 * What's the difference if the effect of these two controls?
 * \endinternal
 */
ALT_STATUS_CODE alt_sdmmc_dma_disable(void);

/*!
 * Enables use of the SD/MMC controller internal DMA for data transfers.
 *
 * This function enables use of the SD/MMC controller internal DMA for data
 * transfers, otherwise the host must conduct data transfers through the slave
 * interface.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 *
 * \internal
 * ctrl.use_internal_dmac
 * bmod.de
 * What's the difference if the effect of these two controls?
 * \endinternal
 */
ALT_STATUS_CODE alt_sdmmc_dma_enable(void);

/*!
 * This type enumerates the host bus programmable burst length options
 * available to the SD/MMC internal DMA controller.
 */
typedef enum ALT_SDMMC_DMA_PBL_e
{
    ALT_SDMMC_DMA_PBL_1     = 0x0,      /*!< 1 transfer unit    */
    ALT_SDMMC_DMA_PBL_4     = 0x1,      /*!< 4 transfer units   */
    ALT_SDMMC_DMA_PBL_8     = 0x2,      /*!< 8 transfer units   */
    ALT_SDMMC_DMA_PBL_16    = 0x3,      /*!< 16 transfer units  */
    ALT_SDMMC_DMA_PBL_32    = 0x4,      /*!< 32 transfer units  */
    ALT_SDMMC_DMA_PBL_64    = 0x5,      /*!< 64 transfer units  */
    ALT_SDMMC_DMA_PBL_128   = 0x6,      /*!< 128 transfer units */
    ALT_SDMMC_DMA_PBL_256   = 0x7,      /*!< 256 transfer units */
    
} ALT_SDMMC_DMA_PBL_t;

/*!
 * Starts the SD/MMC internal DMA transfer with the specified
 * descriptor an bus mode transfer configuration.
 *
 * \param       buf_desc_list
 *              Pointer to the beginning of a SD/MMC internal DMA buffer
 *              descriptor list.
 *
 * \param       desc_skip_len
 *              Descriptor Skip Length. Specifies the number of
 *              half/full/double words (depending on 16/32/64-bit bus)
 *              to skip between two unchained descriptors. Only
 *              applicable for dual buffer structures otherwise
 *              ignored.
 *
 * \param       burst_len
 *              Programmable Burst Length. Specifies the maximum
 *              number of beats to be performed in one DMA
 *              transaction. The DMA will always attempt to burst as
 *              specified each time it starts a burst transfer on the
 *              host bus.
 *
 * \param       use_fixed_burst
 *              Fixed Burst. Controls whether the AHB Master interface
 *              performs fixed burst transfers or not. When set, the
 *              AHB will use only SINGLE, INCR4, INCR8 or INCR16
 *              during start of normal burst transfers. When reset,
 *              the AHB will use SINGLE and INCR burst transfer
 *              operations.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_dma_start(ALT_SDMMC_DMA_BUF_DESC_t *buf_desc_list, 
                                    const uint32_t desc_skip_len,
                                    const ALT_SDMMC_DMA_PBL_t burst_len,
                                    const bool use_fixed_burst);

/*!
 * Sets any value for the IDMAC FSM to resume normal descriptor
 * fetch operation.
 *
 * \param       value
 *              This value will write for the IDMAC FSM.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_sdmmc_poll_demand_set(const uint32_t value);

/*!
 * Returns the SD/MMC internal DMA controller status register value which
 * reflects current DMA interrupt status conditions.
 *
 * \returns     The value of the SD/MMC internal DMA status register which
 *              reflects the current SD/MMC internal DMA interrupt status
 *              conditions.
 */
uint32_t alt_sdmmc_dma_int_status_get(void);

/*!
 * Returns the SD/MMC internal DMA controller interrupt mask value which
 * reflects the enabled internal DMA controller interrupt status conditions.
 *
 * \returns     The aggregate value of the enabled SD/MMC internal DMA
 *              controller interrupt status conditions.  A set (1) bit in the
 *              corresponding ALT_SDMMC_DMA_INT_STATUS_t position indicates an
 *              interrupt that is enabled. A clear (0) bit the corresponding
 *              ALT_SDMMC_DMA_INT_STATUS_t position indicates an interrupt that
 *              is masked.
 */
uint32_t alt_sdmmc_dma_int_mask_get(void);

/*!
 * Clears the specified SD/MMC internal DMA controller interrupt status
 * conditions identified in the mask.
 *
 * This function clears one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_SDMMC_IRQ interrupt signal state.
 *
 * \param       mask
 *              Specifies the SD/MMC internal DMA controller status conditions
 *              to clear.  \e mask is a mask of logically OR'ed \ref
 *              ALT_SDMMC_DMA_INT_STATUS_t values that designate the status
 *              conditions to clear.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_sdmmc_dma_int_clear(const uint32_t mask);

/*!
 * Disable the specified SD/MMC internal DMA controller interrupt status
 * conditions identified in the mask.
 *
 * This function disables one or more of the status conditions as contributors
 * to the \b ALT_INT_INTERRUPT_SDMMC_IRQ interrupt signal state.
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have
 * the effect of enabling it as a contributor to the \b
 * ALT_INT_INTERRUPT_SDMMC_IRQ interrupt signal state. The function
 * alt_sdmmc_dma_int_enable() is used to enable status source conditions.
 *
 * \param       mask
 *              Specifies the status conditions to disable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed \ref
 *              ALT_SDMMC_DMA_INT_STATUS_t values that designate the status
 *              conditions to disable.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_sdmmc_dma_int_disable(const uint32_t mask);

/*!
 * Enable the specified SD/MMC internal DMA controller interrupt status conditions
 * identified in the mask.
 *
 * This function enables one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_SDMMC_IRQ interrupt signal state.
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have
 * the effect of disabling it as a contributor to the \b
 * ALT_INT_INTERRUPT_SDMMC_IRQ interrupt signal state. The function
 * alt_sdmmc_dma_int_disable() is used to disable status source conditions.
 *
 * \param       mask
 *              Specifies the status conditions to enable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed \ref
 *              ALT_SDMMC_DMA_INT_STATUS_t values that designate the status
 *              conditions to enable.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_sdmmc_dma_int_enable(const uint32_t mask);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_SDMMC_FIFO SD/MMC Controller FIFO
 *
 *
 * @{
 */

/*!
 * The number of entries (depth) of the SDMMC controller FIFO.
 */
#define ALT_SDMMC_FIFO_NUM_ENTRIES     1024

/*!
 * Resets the SD/MMC controller FIFO.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * 
 * \internal
 * ctrl.fifo_reset - write 1 to reset FIFO
 * \endinternal
 */
ALT_STATUS_CODE alt_sdmmc_fifo_reset(void);

/*!
 * This type enumerates the burst size of multiple transaction
 * available to the SD/MMC internal DMA controller.
 */
typedef enum ALT_SDMMC_MULT_TRANS_e
{
    ALT_SDMMC_MULT_TRANS_TXMSIZE1     = 0x0,      /*!< Msize 1 and TX_WMARK 1-1023 */
    ALT_SDMMC_MULT_TRANS_TXMSIZE4     = 0x1,      /*!< Msize 1 and TX_WMARK 1-1023 */
    ALT_SDMMC_MULT_TRANS_TXMSIZEK8    = 0x2,      /*!< Msize 4 and TX_WMARK 256    */
    ALT_SDMMC_MULT_TRANS_TXMSIZEK16   = 0x3,      /*!< Msize 16 and TX_WMARK 64    */
    ALT_SDMMC_MULT_TRANS_RXMSIZEK1    = 0x5,      /*!< Msize 1 and RX_WMARK 512    */
    ALT_SDMMC_MULT_TRANS_RXMSIZEK4    = 0x6,      /*!< Msize 1 and RX_WMARK 512    */
    ALT_SDMMC_MULT_TRANS_RXMSIZE8     = 0x7,      /*!< Msize 8 and RX_WMARK 64     */
} ALT_SDMMC_MULT_TRANS_t;

/*!
 * Gets the configured FIFO operational parameter values.
 *
 * This function returns the FIFO configuration parameter set for the receive and
 * transmit watermark threshold values and the DMA multiple transaction size.
 *
 * \param       rx_wtrmk
 *              [out] FIFO threshold watermark value when receiving data to card.
 *
 * \param       tx_wtrmk
 *              [out] FIFO threshold watermark value when transmitting data to card.
 *
 * \param       mult_trans_size
 *              [out] Burst size of multiple transaction.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */

ALT_STATUS_CODE alt_sdmmc_fifo_param_get(uint32_t *rx_wtrmk, uint32_t *tx_wtrmk,
                                                ALT_SDMMC_MULT_TRANS_t *mult_trans_size);

/*!
 * Sets the configured FIFO operational parameter values.
 *
 * This function sets the FIFO configuration parameter for the receive and
 * transmit watermark threshold values and the DMA multiple transaction size.
 *
 * \param       rx_wtrmk
 *              FIFO threshold watermark value when receiving data to card.
 *
 * \param       tx_wtrmk
 *              FIFO threshold watermark value when transmitting data to card.
 *
 * \param       mult_trans_size
 *              Burst size of multiple transaction.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_sdmmc_fifo_param_set(uint32_t rx_wtrmk, uint32_t tx_wtrmk, ALT_SDMMC_MULT_TRANS_t mult_trans_size);

/*!
 * Returns true if SD/MMC controller FIFO has reached the receive watermark level
 * otherwise returns false.
 *
 * \retval      true            The FIFO has reached the receive watermark level.
 * \retval      false           The FIFO has not reached the receive watermark level.
 *              
 * \internal
 * \endinternal
 */
bool alt_sdmmc_fifo_is_rx_wtrmk_reached(void);

/*!
 * Returns true if SD/MMC controller FIFO has reached the transmit watermark level
 * otherwise returns false.
 *
 * \retval      true            The FIFO has reached the transmit watermark level.
 * \retval      false           The FIFO has not reached the transmit watermark level.
 *              
 * \internal
 * \endinternal
 */
bool alt_sdmmc_fifo_is_tx_wtrmk_reached(void);

/*!
 * Returns true if SD/MMC controller FIFO is empty otherwise returns false.
 *
 * \retval      true            The FIFO is empty.
 * \retval      false           The FIFO is not empty.
 *              
 * \internal
 * \endinternal
 */
bool alt_sdmmc_fifo_is_empty(void);

/*!
 * Returns true if SD/MMC controller FIFO is full otherwise returns false.
 *
 * \retval      true            The FIFO is full.
 * \retval      false           The FIFO is not full.
 *              
 * \internal
 * \endinternal
 */
bool alt_sdmmc_fifo_is_full(void);

/*!
 * Returns the number of filled FIFO locations.
 *
 * \returns     The number of filled FIFO locations.
 */
int32_t alt_sdmmc_fifo_count(void);

/*!
 * Read data from the SD/MMC controller FIFO.
 *
 * Reads the requested number of bytes (rounded up to nearest whole 32-bit word)
 * from the FIFO. The function returns when the requested number of bytes has been
 * read from the FIFO or if an error occurs.
 *
 * \param       dest
 *              A pointer to a user supplied destination buffer for the data read
 *              from the FIFO. The buffer must be as large the requested number of
 *              bytes rounded up to the nearest 32-bit word size.
 *
 * \param       size
 *              The requested number of bytes to read from the FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_fifo_read(void *dest, const size_t size);

/*!
 * Writes data to the SD/MMC controller FIFO.
 *
 * Writes the requested number of bytes (rounded up to nearest whole 32-bit word)
 * to the FIFO. The function returns when the requested number of bytes has been
 * written to the FIFO or if an error occurs.
 *
 * \param       src
 *              A pointer to 
 *              A pointer to the source buffer containing the data to be written to the
 *              FIFO. The buffer must be as large the requested number of
 *              bytes rounded up to the nearest 32-bit word size.
 *
 * \param       size
 *              The number of bytes to write to the FIFO. If size is not a
 *              multiple of 4 then the number of bytes is rounded up to the next
 *              32-but word size and the byte difference padded with zeroes.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_sdmmc_fifo_write(const void *src, const size_t size);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_SDMMC_BLKIO General Purpose Block I/O
 *
 * The functions in this group provide general purpose block read and write flash
 * functions.
 *
 * @{
 */

/*!
 * Reads a block of data from the SD/MMC flash card.
 *
 * Reads a block of \e size data bytes from the SD/MMC flash \e src address into the
 * user supplied \e dest buffer.
 *
 * \param       dest
 *              The address of a caller supplied destination buffer in system
 *              memory large enough to contain the requested block of flash data.
 *
 * \param       src
 *              The flash memory address to begin reading data from.
 *
 * \param       size
 *              The requested number of data bytes to read from the flash device.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_sdmmc_read(void *dest, void *src, const size_t size);

/*!
 * Write a block of data to the SD/MMC flash card.
 *
 * Writes a block of \e size data bytes to the SD/MMC flash \e dest address from the
 * designated \e src buffer. The actual number of bytes written to the flash card is
 * \e size bytes rounded up to the next whole multiple flash card block size. That
 * is: 
 * \e actual_bytes_written = ((\e size / \e flash_block_size) + 1) * \e flash_block_size
 *
 *
 * \param       dest
 *              The destination flash memory address to begin writing data to.
 *
 * \param       src
 *              The source address in system memory to begin writing data from.
 *
 * \param       size
 *              The requested number of data bytes to write to the flash device.
 *
 * \retval      ALT_E_SUCCESS   Indicates successful completion.
 * \retval      ALT_E_ERROR     Indicates an error occurred.
 */
ALT_STATUS_CODE alt_sdmmc_write(void *dest, void *src, const size_t size);

/*! @} */

/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */

#endif  /* __ALT_SDMMC_H__ */
