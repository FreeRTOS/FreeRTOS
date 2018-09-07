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
 *  Altera - I2C Controller API
 */

#ifndef __ALT_I2C_H__
#define __ALT_I2C_H__

#include "hwlib.h"
#include "alt_clock_manager.h"
#include "socal/alt_i2c.h"
#include "socal/alt_rstmgr.h"
#include "socal/hps.h"
#include "socal/socal.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/******************************************************************************/
/*! \addtogroup ALT_I2C I2C Controller API
 *
 * This module defines an API for configuring and managing the HPS I2C controllers.
 *
 * The I2C controller provides support for a communication link between integrated
 * circuits on a board. It is a simple two-wire bus which consists of a serial
 * data line (SDA) and a serial clock (SCL) for use in applications such as
 * temperature sensors and voltage level translators to EEPROMs, A/D and D/A
 * converters, CODECs, and many types of microprocessors.
 *
 * The Hard Processor System (HPS) provides four I2C controllers to enable system
 * software to communicate serially with I2C buses. Each I2C controller can
 * operate in master or slave mode, and support standard mode of up to 100
 * kilobits per second (Kbps) or fast mode of up to 400 Kbps. These I2C
 * controllers are instances of the Synopsys DesignWare APB I2C (DW_apb_i2c)
 * controller.
 * 
 * NOTE: Each I2C controller must be programmed to operate in either master or
 *       slave mode only. Operating as a master and slave simultaneously is not
 *       supported.
 *
 * Features of the I2C Controller:
 *  * Support both 100 KBps and 400 KBps modes
 *  * One of the following I2C operations: master or slave
 *  * Support both 7-bit and 10-bit addressing modes
 *  * Mixed read and write combined-format transactions
 *  * Bulk transmit mode
 *  * DMA handshaking interface
 *
 * For a complete details on the configuration and operation of I2C controller,
 * consult the following references:
 *  * <em>Cyclone V Device Handbook Volume 3: Hard Processor System Technical
 *    Reference Manual, Chapter 20. I2C Controller (cv_54020-1.2)</em>
 *  * <em>Synopsys DesignWare DW_apb_i2c Databook DW_apb_i2c, Version 1.15a</em>
 *  * <em>The I2C-Bus Specification Version 2.1</em>
 *
 * @{
 */

/******************************************************************************/
/*!
 * This type definition enumerates the operational state of I2C by
 * transfer operation.
 */
typedef enum ALT_I2C_TRANSFER_TYPE_e
{
    ALT_I2C_TRANSFER_NONE     = 0, /*!< No transfer operation */
    ALT_I2C_TRANSFER_START    = 1, /*!< Start detect */
    ALT_I2C_TRANSFER_COMPLETE = 2, /*!< All operations done */
    ALT_I2C_TRANSFER_READ     = 3, /*!< Read operation is active */
    ALT_I2C_TRANSFER_WRITE    = 4, /*!< Write operation is active */
}
ALT_I2C_TRANSFER_TYPE_t;


/*
 * A pointer or handle to the I2C controller device instance. The ALT_I2C_DEV_t is
 * initialized by a call to alt_i2c_init() and subsequently used by the other I2C
 * controller API functions as a reference to a specific device.
 *
 * \internal
 * ALT_I2C_DEV_t may be a struct or reference to an opaque data
 * structure. Whatever "internal" type is suited to the needs of the
 * implementation.
 * \endinternal
 */
typedef struct ALT_I2C_DEV_s
{
    void *                  location;    /*!< HPS address of I2C instance. */
    alt_freq_t              clock_freq;  /*!< Input clock frequency. */
    uint32_t                last_target; /*!< Last issued target address. */
}
ALT_I2C_DEV_t;

/*!
 * This type enumerates the HPS I2C controller instances.
 */
typedef enum ALT_I2C_CTLR_e
{
    ALT_I2C_I2C0        = (int)ALT_I2C0_OFST,  /*!< I2C0 instance. */
    ALT_I2C_I2C1        = (int)ALT_I2C1_OFST,  /*!< I2C1 instance. */
    ALT_I2C_I2C2        = (int)ALT_I2C2_OFST,  /*!< I2C2 instance. */
    ALT_I2C_I2C3        = (int)ALT_I2C3_OFST,  /*!< I2C3 instance. */
} ALT_I2C_CTLR_t;

/*!
 * This type enumerates the modes that the I2C controller may operate in.
 *
 * NOTE: Each I2C controller must be programmed to operate in either master or
 *       slave mode only. Operating as a master and slave simultaneously is not
 *       supported.
 */
typedef enum ALT_I2C_MODE_e
{
    ALT_I2C_MODE_SLAVE     = ALT_I2C_CON_MST_MOD_E_DIS,  /*!< Slave Mode  */
    ALT_I2C_MODE_MASTER    = ALT_I2C_CON_MST_MOD_E_EN    /*!< Master Mode */
} ALT_I2C_MODE_t;

/*!
 * This type enumerates the I2C controller operational speed modes.
 *
 * The I2C controller can operate in standard mode (with data rates 0 to 100 Kbps)
 * or fast mode (with data rates less than or equal to 400 Kbps). Additionally,
 * fast mode devices are downward compatible. For instance, fast mode devices can
 * communicate with standard mode devices in 0 to 100 Kbps I2C bus
 * system. However, standard mode devices are not upward compatible and should not
 * be incorporated in a fast-mode I2C bus system as they cannot follow the higher
 * transfer rate and therefore unpredictable states would occur.
 *
 * This setting is relevant only if one is operating the I2C in master mode.
 */
typedef enum ALT_I2C_SPEED_e
{
    ALT_I2C_SPEED_STANDARD   = ALT_I2C_CON_SPEED_E_STANDARD,
                                    /*!< Standard mode (0 to 100 Kbps) */
    ALT_I2C_SPEED_FAST       = ALT_I2C_CON_SPEED_E_FAST
                                    /*!< Fast mode (<= 400 Kbps)       */
} ALT_I2C_SPEED_t;

/*!
 * This type enumerates the two addressing modes formats supported by the I2C
 * controller.
 *
 * The I2C controller does not support mixed address format - that is, a 7-bit
 * address transaction followed by a 10-bit address transaction or vice versa -
 * combined format transactions.
 */
typedef enum ALT_I2C_ADDR_MODE_e
{
    ALT_I2C_ADDR_MODE_7_BIT     = ALT_I2C_TAR_IC_10BITADDR_MST_E_START7,
                                    /*!< 7-Bit Address Format  */
    ALT_I2C_ADDR_MODE_10_BIT    = ALT_I2C_TAR_IC_10BITADDR_MST_E_START10
                                    /*!< 10-Bit Address Format */
} ALT_I2C_ADDR_MODE_t;

/*!
 * This type enumerates interrupt status conditions for the I2C controller.
 */
typedef enum ALT_I2C_STATUS_e
{
    ALT_I2C_STATUS_RX_UNDER     = 1UL << 0,
                                /*!< Set if the processor attempts to read the
                                 *   receive buffer when it is empty. If the I2C
                                 *   controller is disabled, this status keeps
                                 *   maintains its state until the master or slave
                                 *   state machines go into idle, then this
                                 *   interrupt is cleared.
                                 */
    ALT_I2C_STATUS_RX_OVER      = 1UL << 1,
                                /*!< Set if the receive buffer is completely
                                 *   filled to capacity and an additional byte is
                                 *   received from an external I2C device. The I2C
                                 *   controller acknowledges this, but any data
                                 *   bytes received after the FIFO is full are
                                 *   discarded. If the I2C controller is disabled,
                                 *   this status maintains its statue until the
                                 *   master or slave state machines go into idle,
                                 *   then this interrupt is cleared.
                                 */
    ALT_I2C_STATUS_RX_FULL      = 1UL << 2,
                                /*!< Set when the receive buffer reaches or goes
                                 *   above the RX_TL threshold. It is
                                 *   automatically cleared by hardware when buffer
                                 *   level goes below the threshold. If the I2C
                                 *   controller is disabled, the RX FIFO is
                                 *   flushed and held in reset; therefore the RX
                                 *   FIFO is not full. So this bit is cleared once
                                 *   the I2C controller is disabled, regardless of
                                 *   the activity that continues.
                                 */
    ALT_I2C_STATUS_TX_OVER     = 1UL << 3,
                                /*!< Set during transmit if the transmit buffer is
                                 *   filled to capacity and the processor attempts
                                 *   to issue another I2C command. When the I2C
                                 *   controller is disabled, this bit maintains
                                 *   its state until the master or slave state
                                 *   machines go into idle, then this interrupt is
                                 *   cleared.
                                 */
    ALT_I2C_STATUS_TX_EMPTY     = 1UL << 4,
                                /*!< This bit is set to 1 when the transmit buffer
                                 *   is at or below the configured threshold
                                 *   value. It is automatically cleared by
                                 *   hardware when the buffer level goes above the
                                 *   threshold. When the I2C controller is
                                 *   disabled, the TX FIFO is flushed and held in
                                 *   reset. The TX FIFO appears as if it has no
                                 *   data in it, so this bit is set to 1, provided
                                 *   there is activity in the master or slave
                                 *   state machines. When there is no longer
                                 *   activity, then this bit is set to 0.
                                 *
                                 */
    ALT_I2C_STATUS_RD_REQ       = 1UL << 5,
                                /*!< This bit is set to 1 when I2C is acting as a
                                 *   slave and another I2C master is attempting to
                                 *   read data from the I2C. The I2C holds the bus
                                 *   in a wait state until this interrupt is
                                 *   serviced, which means that the slave has been
                                 *   addressed by a remote master that is asking
                                 *   for data to be transferred. The processor
                                 *   must respond to this interrupt and then write
                                 *   the requested data. This bit is set to 0 just
                                 *   after the processor by calling
                                 *   alt_i2c_int_clear() with
                                 *   ALT_I2C_STATUS_RD_REQ in the mask..
                                 */
    ALT_I2C_STATUS_TX_ABORT     = 1UL << 6,
                                /*!< This bit indicates if I2C, as an I2C
                                 *   transmitter, is unable to complete the
                                 *   intended actions on the contents of the
                                 *   transmit FIFO. This situation can occur both
                                 *   as an I2C master or an I2C slave, and is
                                 *   referred to as a 'transmit abort'. When this
                                 *   bit is set to 1, the IC_TX_ABRT_SOURCE
                                 *   register indicates the reason why the
                                 *   transmit abort takes places.
                                 *
                                 *   NOTE: The I2C flushes/resets/empties the TX
                                 *   FIFO whenever this bit is set. The TX FIFO
                                 *   remains in this flushed state until the
                                 *   register alt_i2c_int_clear() with
                                 *   ALT_I2C_STATUS_TX_ABORT in the mask is
                                 *   called. Once this happens, the TX FIFO is
                                 *   then ready to accept more data bytes from the
                                 *   APB interface.
                                 */
    ALT_I2C_STATUS_RX_DONE      = 1UL << 7,
                                /*!< When the I2C is acting as a
                                 *   slave-transmitter, this bit is set to 1 if
                                 *   the master does not acknowledge a transmitted
                                 *   byte. This occurs on the last byte of the
                                 *   transmission, indicating that the
                                 *   transmission is done.
                                 */
    ALT_I2C_STATUS_ACTIVITY     = 1UL << 8,
                                /*!< This bit captures I2C activity and stays set
                                 *   until it is cleared. There are four ways to
                                 *   clear it:
                                 *   * Disabling the I2C controller
                                 *   * Calling alt_i2c_int_clear() with
                                 *     ALT_I2C_STATUS_ACTIVITY in the mask.
                                 *   * Calling alt_i2c_int_clear() with
                                 *     ALT_I2C_STATUS_ALL in the mask.
                                 *   * System reset
                                 * 
                                 *   Once this bit is set, it stays set unless one
                                 *   of the four methods is used to clear it. Even
                                 *   if the I2C module is idle, this bit remains
                                 *   set until cleared, indicating that there was
                                 *   activity on the bus.
                                 */
    ALT_I2C_STATUS_STOP_DET     = 1UL << 9,
                                /*!< Indicates whether a STOP condition has
                                 *   occurred on the I2C interface regardless of
                                 *   whether I2C is operating in slave or master
                                 *   mode.
                                 */
    ALT_I2C_STATUS_START_DET    = 1UL << 10,
                                /*!< Indicates whether a START or RESTART
                                 *   condition has occurred on the I2C interface
                                 *   regardless of whether I2C is operating in
                                 *   slave or master mode.
                                 */
    ALT_I2C_STATUS_INT_CALL     = 1UL << 11,
                                /*!< Set only when a General Call address is
                                 *   received and it is acknowledged. It stays set
                                 *   until it is cleared either by disabling I2C
                                 *   or when alt_i2c_int_clear() with
                                 *   ALT_I2C_STATUS_CALL in the mask is
                                 *   called. I2C stores the received data in the
                                 *   Rx buffer.
                                 */
    ALT_I2C_STATUS_INT_ALL      = 0xFFF,
                                /*!< All Combined and Individual Interrupts. This
                                 *   enumeration value can be used to clear,
                                 *   disable, and enable the combined interrupt
                                 *   and all individual interrupt status
                                 *   conditions. As a side effect, when passed to
                                 *   alt_i2c_int_clear(), clears the source causes
                                 *   (\ref ALT_I2C_TX_ABORT_CAUSE_t) of the
                                 *   ALT_I2C_STATUS_TX_ABORT condition.
                                 */
} ALT_I2C_STATUS_t;

/*!
 * This type enumerates the source causes of a ALT_I2C_STATUS_TX_ABORT condition.
 *
 * The active ALT_I2C_TX_ABORT_CAUSE_t source conditions are cleared when
 * alt_i2c_int_clear() with is called ALT_I2C_STATUS_TX_ABORT in the mask or
 * alt_i2c_int_clear() is called with ALT_I2C_STATUS_ALL in the mask.
 *
 * \internal
 * Discuss special handling of abrt_sbyte_norstrt TX_ABRT source required in ???() function.
 * \endinternal
 */
typedef enum ALT_I2C_TX_ABORT_CAUSE_e
{
    ALT_I2C_TX_ABORT_CAUSE_7B_ADDR_NOACK        = 1UL << 0,
                                /*!< Master Abort 7 Bit Address - If set (1),
                                 *   Master is in 7-bit addressing mode and the
                                 *   address sent was not acknowledged by any
                                 *   slave.
                                 *   
                                 *   Role of I2C: Master-Transmitter or
                                 *   Master-Receiver
                                 */
    ALT_I2C_TX_ABORT_CAUSE_10ADDR1_NOACK        = 1UL << 1,
                                /*!< Master Abort 10 Bit Address Byte 1 - If set
                                 *   (1), Master is in 10-bit address mode and the
                                 *   first 10-bit address byte was not
                                 *   acknowledged by any slave.
                                 *   
                                 *   Role of I2C: Master-Transmitter or
                                 *   Master-Receiver
                                 */
    ALT_I2C_TX_ABORT_CAUSE_10ADDR2_NOACK        = 1UL << 2,
                                /*!< Master Abort 10 Bit Address Byte 2 - If set
                                 *   (1), Master is in 10-bit address mode and the
                                 *   second address byte of the 10-bit address was
                                 *   not acknowledged by any slave
                                 *   
                                 *   Role of I2C: Master-Transmitter or
                                 *   Master-Receiver
                                 */
    ALT_I2C_TX_ABORT_CAUSE_TXDATA_NOACK         = 1UL << 3,
                                /*!< Master Abort TX NOACK Bit - If set (1),
                                 *   Master has received an acknowledgement for
                                 *   the address, but when it sent data byte(s)
                                 *   following the address, it did not receive an
                                 *   acknowledge from the remote slave(s). This is
                                 *   a master-mode only bit.
                                 *   
                                 *   Role of I2C: Master-Transmitter.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_GCALL_NOACK          = 1UL << 4,
                                /*!< Master Abort GC Noack Bit - If set (1), I2C
                                 *   controller in master mode sent a General Call
                                 *   and no slave on the bus acknowledged the
                                 *   General Call.
                                 *   
                                 *   Role of I2C: Master-Transmitter.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_GCALL_RD             = 1UL << 5,
                                /*!< Master Abort GC Read Bit - If set (1), I2C
                                 *   controller in master mode sent a General Call
                                 *   but the user programmed the byte following
                                 *   the General Call to be a read from the bus
                                 *   (IC_DATA_CMD[9] is set to 1).
                                 *   
                                 *   Role of I2C: Master-Transmitter.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_HS_ACKDET            = 1UL << 6,
                                /*!< Master HS MC Ack - If set (1), Master is in
                                 *   High Speed mode and the High Speed Master
                                 *   code was acknowledged (wrong behavior).
                                 *   
                                 *   Role of I2C: Master.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_SBYTE_ACKDET         = 1UL << 7,
                                /*!< Master Abort START Byte - If set (1), Master
                                 *   has sent a START Byte and the START Byte was
                                 *   acknowledged (wrong behavior).
                                 *   
                                 *   Role of I2C: Master.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_HS_NORSTRT           = 1UL << 8,
                                /*!< Master HS Restart Disabled - If set (1), the
                                 *   restart is disabled (IC_RESTART_EN bit
                                 *   (IC_CON[5]) = 0) and the user is trying to
                                 *   use the master to transfer data in High Speed
                                 *   mode.
                                 *   
                                 *   Role of I2C: Master-Transmitter or
                                 *   Master-Receiver
                                 */
    ALT_I2C_TX_ABORT_CAUSE_SBYTE_NORSTRT        = 1UL << 9,
                                /*!< Master Abort START No Restart - To clear, the
                                 *   source of the ABRT_SBYTE_NORSTRT must be
                                 *   fixed first; restart must be enabled
                                 *   (IC_CON[5]=1), the SPECIAL bit must be
                                 *   cleared (IC_TAR[11]), or the GC_OR_START bit
                                 *   must be cleared (IC_TAR[10]). Once the source
                                 *   of the ABRT_SBYTE_NORSTRT is fixed, then this
                                 *   bit can be cleared in the same manner as
                                 *   other bits in this register. If the source of
                                 *   the ABRT_SBYTE_NORSTRT is not fixed before
                                 *   attempting to clear this bit, bit 9 clears
                                 *   for one cycle and then gets re-asserted.
                                 *
                                 *   If set (1), the restart is disabled
                                 *   (IC_RESTART_EN bit (IC_CON[5]) = 0) and the
                                 *   user is trying to send a START Byte.
                                 *   
                                 *   Role of I2C: Master.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_10B_RD_NORSTRT       = 1UL << 10,
                                /*!< Master Abort 10 Bit No Restart - If set (1),
                                 *   the restart is disabled (IC_RESTART_EN bit
                                 *   (IC_CON[5]) = 0) and the master sends a read
                                 *   command in 10-bit addressing mode.
                                 *   
                                 *   Role of I2C: Master Receiver.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_MST_DIS              = 1UL << 11,
                                /*!< Master Operation with Master Disabled - If set
                                 *   (1), user tries to initiate a Master
                                 *   operation with the Master mode disabled.
                                 *   
                                 *   Role of I2C: Master or Slave-Receiver.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_ARB_LOST             = 1UL << 12,
                                /*!< Master Abort Arbitration Lost - If set (1),
                                 *   master has lost arbitration, or if
                                 *   IC_TX_ABRT_SOURCE[14] is also set, then the
                                 *   slave transmitter has lost arbitration. Note:
                                 *   I2C can be both master and slave at the same
                                 *   time.
                                 *   
                                 *   Role of I2C: Master or Slave-Transmitter.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_SLVFLUSH_TXFIFO      = 1UL << 13,
                                /*!< Slave Abort Flush TXFIFO - If set (1), Slave
                                 *   has received a read command and some data
                                 *   exists in the TX FIFO so the slave issues a
                                 *   TX_ABRT interrupt to flush old data in TX
                                 *   FIFO.
                                 *
                                 *   Role of I2C: Slave-Transmitter.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_SLV_ARBLOST          = 1UL << 14,
                                /*!< Slave Abort Arbitration Lost - If set (1),
                                 *   Slave lost the bus while transmitting data to
                                 *   a remote master. IC_TX_ABRT_SOURCE[12] is set
                                 *   at the same time.
                                 *  
                                 *   Note: Even though the slave never owns the
                                 *   bus, something could go wrong on the
                                 *   bus. This is a fail safe check. For instance,
                                 *   during a data transmission at the low-to-high
                                 *   transition of SCL, if what is on the data bus
                                 *   is not what is supposed to be transmitted,
                                 *   then DW_apb_i2c no longer own the bus.
                                 *
                                 *   Role of I2C: Slave-Transmitter.
                                 */
    ALT_I2C_TX_ABORT_CAUSE_SLVRD_INTX           = 1UL << 15
                                /*!< Slave Abort Read TX - If set (1), 
                                 *   when the processor side responds to a
                                 *   slave mode request for data to be transmitted
                                 *   to a remote master and user writes a 1 in CMD
                                 *   (bit 8) of IC_DATA_CMD register.
                                 *
                                 *   Role of I2C: Slave-Transmitter.
                                 */
} ALT_I2C_TX_ABORT_CAUSE_t;

/*!
 * This type defines a structure for configuration of the SCL high and low counts
 * to ensure proper I/O timing with the device interface.
 *      
 * The SCL count values are only relevant if the I2C controller is enabled to as
 * an I2C master. The SCL count values are ignored when the I2C controller is
 * enabled as an I2C slave.
 *
 * See: Clock Frequency Configuration section of <em>Chapter 20. I2C
 *      Controller</em> in the <em>Cyclone V Device Handbook Volume 3: Hard
 *      Processor System Technical Reference Manual</em> for a complete discussion
 *      of calculation of the proper SCL clock high and low times.
 */
typedef struct ALT_I2C_MASTER_CONFIG_s
{
    ALT_I2C_ADDR_MODE_t addr_mode;
                                    /*!< The address mode (7 or 10 bit) when
                                     *   acting as a master.
                                     */
    bool                restart_enable;
                                    /*!< This setting determines whether RESTART
                                     *   conditions may be sent when acting as a
                                     *   master. When the \e restart_enable is
                                     *   false, the I2C controller master is
                                     *   incapable of performing the following
                                     *   functions:
                                     *   * Sending a START BYTE
                                     *   * Performing any high-speed mode
                                     *     operation
                                     *   * Performing direction changes in
                                     *     combined format mode
                                     *   * Performing a read operation with a
                                     *     10-bit address
                                     */
    ALT_I2C_SPEED_t     speed_mode;
                                    /*!< The speed mode of the I2C operation.
                                     */
    uint16_t            ss_scl_hcnt;
                                    /*!< The SCL clock high-period count for
                                     *   standard speed.
                                     */
    uint16_t            ss_scl_lcnt;    
                                    /*!< The SCL clock low-period count for
                                     *   standard speed.
                                     */
    uint16_t            fs_scl_hcnt;    
                                    /*!< The SCL clock high-period count for fast
                                     *   speed.
                                     */
    uint16_t            fs_scl_lcnt;    
                                    /*!< The SCL clock low-period count for fast
                                     *   speed.
                                     */
    uint8_t             fs_spklen;
                                    /*!< The duration, measured in ic_clk cycles,
                                     *   of the longest spike that is filtered out
                                     *   by the spike suppression logic when the
                                     *   component is operating in SS or FS modes.
                                     */
} ALT_I2C_MASTER_CONFIG_t;

/*!
 * This type defines a structure for configuration of the I2C controller when it
 * is operating in slave mode.
 */
typedef struct ALT_I2C_SLAVE_CONFIG_s
{
    ALT_I2C_ADDR_MODE_t addr_mode;      /*!< The address mode (7 or 10 bit) when
                                         *   acting as a slave.
                                         */
    uint32_t            addr;           /*!< The slave address to which the I2C
                                         *   controller responds when acting as a
                                         *   slave.
                                         */
    bool                nack_enable;    /*!< Enable generation of a NACK. when the
                                         *   I2C controller is a
                                         *   slave-receiver. If \b true, it can
                                         *   only generate a NACK after a data
                                         *   byte is received; hence, the data
                                         *   transfer is aborted and the data
                                         *   received is not pushed onto the
                                         *   receive buffer. When \b false, it
                                         *   generates NACK/ACK, depending on
                                         *   normal criteria.
                                         *   * \b true = generate NACK after data 
                                         *               byte received
                                         *   * \b false = generate NACK/ACK normally
                                         */
} ALT_I2C_SLAVE_CONFIG_t;

/*!
 * Initialize the specified I2C controller instance for use and return a device
 * handle referencing it.
 *
 * \param       i2c
 *              The HPS I2C controller instance to initialize.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * Initialization process:
 * * Initialize internal driver state
 * * Check clock setup (ALT_CLK_L4_SP)
 * * Take I2C instance out of reset (System Manager)
 * * Disable and clear all interrupts and status conditions
 * * Setup and initialize any expected initial I2C controller state
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_init(const ALT_I2C_CTLR_t i2c, ALT_I2C_DEV_t *i2c_dev);

/*!
 * Reset the specified I2C controller instance for use.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * Reset process:
 *  * Disable controller
 *  * Initialize internal driver state
 *  * Check clock setup (ALT_CLK_L4_SP)
 *  * Take I2C instance out of reset (System Manager)
 *  * Disable and clear all interrupts and status conditions
 *  * Setup and initialize any expected initial I2C controller state
 *  * Enable controller
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_reset(ALT_I2C_DEV_t * i2c_dev);

/*!
 * Uninitialize the I2C controller referenced by the \e i2c_dev handle.
 *
 * This function attempts to gracefully shutdown the I2C controller by waiting for
 * any inpcomplete transactions to finish and then putting the I2C controller into
 * reset.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_uninit(ALT_I2C_DEV_t *i2c_dev);

/*!
 * Disables the I2C controller.
 *
 * When the I2C controller is disabled, the following occurs:
 * * The TX FIFO and RX FIFO get flushed.
 * * The I2C interrupt status conditions remain active until the I2C controller
 *   goes into IDLE state.
 *
 * If the controller is transmitting, it stops as well as deletes the contents of
 * the transmit buffer after the current transfer is complete. If the module is
 * receiving, the controller stops the current transfer at the end of the current
 * byte and does not acknowledge the transfer.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_ENABLE.ENABLE = 0
 * Follow the procedure in section 3.8.3 Disabling DW_apb_i2c of the DW Databook.
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_disable(ALT_I2C_DEV_t *i2c_dev);

/*!
 * Enables the I2C controller.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_ENABLE.ENABLE = 1
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_enable(ALT_I2C_DEV_t *i2c_dev);

/*!
 * Returns ALT_E_TRUE if the I2C controller is enabled.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_ENABLE.ENABLE == 1
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_is_enabled(ALT_I2C_DEV_t *i2c_dev);

/*!
 * Gets the current configuration of the I2C controller when operating in master
 * mode.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       cfg
 *              [out] Pointer to a ALT_I2C_MASTER_CONFIG_t structure for holding
 *              the returned I2C master mode configuration parameters.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_master_config_get(ALT_I2C_DEV_t *i2c_dev,
                                          ALT_I2C_MASTER_CONFIG_t* cfg);

/*!
 * Sets the configuration of the I2C controller with operational parameters for
 * operating in master mode.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       cfg
 *              Pointer to a ALT_I2C_MASTER_CONFIG_t structure holding the desired
 *              I2C master mode operational parameters.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_master_config_set(ALT_I2C_DEV_t *i2c_dev,
                                          const ALT_I2C_MASTER_CONFIG_t* cfg);

/*!
 * This is a utility function that returns the speed based on parameters of the
 * I2C master configuration.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       cfg
 *              A pointer to the master confugurations.
 *
 * \param       speed_in_hz
 *              [out] Speed (Hz) of the I2C bus currently configured at.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_i2c_master_config_speed_get(ALT_I2C_DEV_t *i2c_dev,
                                                const ALT_I2C_MASTER_CONFIG_t* cfg,
                                                uint32_t * speed_in_hz);

/*!
 * This is a utility function that computes parameters for the I2C master
 * configuration that best matches the speed requested.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       cfg
 *              A pointer to the master confugurations.
 *
 * \param       speed_in_hz
 *              Speed (Hz) of the I2C bus to configure.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_master_config_speed_set(ALT_I2C_DEV_t *i2c_dev,
                                                ALT_I2C_MASTER_CONFIG_t * cfg,
                                                uint32_t speed_in_hz);

/*!
 * Definition included for backwards compatibility.
 */
#define alt_i2c_cfg_to_speed(i2c_dev, speed_in_hz, cfg) alt_i2c_master_config_speed_get((i2c_dev), (cfg), (speed_in_hz))

/*!
 * Definition included for backwards compatibility.
 */
#define alt_i2c_speed_to_cfg(i2c_dev, speed_in_hz, cfg) alt_i2c_master_config_speed_set((i2c_dev), (cfg), (speed_in_hz))

/*!
 * Gets the current configuration of the I2C controller when operating in slave
 * mode.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       cfg
 *              [out] Pointer to a ALT_I2C_SLAVE_CONFIG_t structure for holding
 *              the returned I2C slave mode configuration parameters.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_slave_config_get(ALT_I2C_DEV_t *i2c_dev,
                                         ALT_I2C_SLAVE_CONFIG_t* cfg);

/*!
 * Sets the configuration of the I2C controller with operational parameters for
 * operating in slave mode.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       cfg
 *              Pointer to a ALT_I2C_SLAVE_CONFIG_t structure holding the desired
 *              I2C slave mode operational parameters.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_slave_config_set(ALT_I2C_DEV_t *i2c_dev,
                                         const ALT_I2C_SLAVE_CONFIG_t* cfg);

/*! \addtogroup ALT_I2C_SDA_HOLD SDA Hold Time Configuration
 *
 * The I2C protocol specification requires 300ns of hold time on the SDA signal in
 * standard and fast speed modes. Board delays on the SCL and SDA signals can mean
 * that the hold-time requirement is met at the I2C master, but not at the I2C
 * slave (or vice-versa). Because each system may encounter differing board signal
 * delays, the I2C controller provides the capability to adjust of the SDA
 * hold-time.
 *
 * The functions in this section provide software configuration of SDA hold time
 * for the I2C controller.
 *
 * @{
 */

/*!
 * Gets the currently configured value for the SDA hold time in I2C controller
 * clock (\ref ALT_CLK_L4_SP) clock ticks.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       hold_time
 *              [out] The configured SDA hold time in \ref ALT_CLK_L4_SP clock
 *              ticks.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_sda_hold_time_get(ALT_I2C_DEV_t *i2c_dev, 
                                          uint16_t *hold_time);

/*!
 * Sets the configured value for the SDA hold time in terms of I2C controller
 * clock (\ref ALT_CLK_L4_SP) clock ticks.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       hold_time
 *              The SDA hold time in \ref ALT_CLK_L4_SP clock ticks.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_SDA_HOLD is 16 bits wide. hold_time must be in range 0..65535.
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_sda_hold_time_set(ALT_I2C_DEV_t *i2c_dev, 
                                          const uint16_t hold_time);

/*! @} */

/*!
 * Gets the current operational mode of the I2C controller.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       mode
 *              [out] The current operational mode enabled for the I2C
 *              controller.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_op_mode_get(ALT_I2C_DEV_t *i2c_dev,
                                    ALT_I2C_MODE_t* mode);

/*!
 * Sets the operational mode of the I2C controller.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       mode
 *              The operational mode to enable for the I2C controller.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_op_mode_set(ALT_I2C_DEV_t *i2c_dev,
                                    const ALT_I2C_MODE_t mode);
  
/*!
 * Returns ALT_E_TRUE if the I2C controller is busy. The I2C controller is busy if
 * either the Slave Finite State Machine (FSM) is not in the IDLE state or the
 * Master Finite State Machine (FSM) is not in the IDLE state.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_STATUS.ACTIVITY == 1
 * NOTE: IC_STATUS[0] that is, the ACTIVITY bit is the OR of SLV_ACTIVITY and
 * MST_ACTIVITY bits.
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_is_busy(ALT_I2C_DEV_t *i2c_dev);

/*!
 * This function reads a single data byte from the receive FIFO.
 *
 * This function is used to perform low level access to the data bytes
 * received by the I2C controller and buffered in the receive FIFO. It
 * may be used by master-receivers or slave receivers.
 *
 * This function does not check for valid data in the receive FIFO
 * beforehand and may cause an underflow if improperly used. It is
 * meant to be called from a context where preconditions have been
 * previously asserted such as in the implementation of the
 * alt_i2c_slave_receive() or alt_i2c_master_receive() function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       val
 *              [out] The single data byte read from the receive FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_read(ALT_I2C_DEV_t *i2c_dev, uint8_t *val);

/*!
 * This function writes a single data byte to the transmit FIFO.
 *
 * This function is used to perform low level writes of data to the
 * transmit FIFO for transmission by the I2C controller. It may be
 * used by slave receivers.
 *
 * This function does not check whether the transmit FIFO is full or
 * not beforehand and may cause an overflow if improperly used. It is
 * meant to be called from a context where preconditions have been
 * previously asserted such as in the implementation of the
 * alt_i2c_slave_transmit() function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       val
 *              The data byte to write to the transmission FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_write(ALT_I2C_DEV_t *i2c_dev, const uint8_t val);

/*!
 * This function acts in the role of a slave-receiver by receiving a single data
 * byte from the I2C bus in response to a write command from the master.
 *
 * This API is suitable for being called during an interrupt context. It is the
 * programmer's responsibility to ensure that there is data in the RX FIFO to
 * accomodate the request made.
 *
 * The I2C controller must be in slave mode before calling this function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       data
 *              [out] A pointer to a buffer to contain the received data byte.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_slave_receive(ALT_I2C_DEV_t *i2c_dev,
                                      uint8_t *data);

/*!
 * This function acts in the role of a slave-transmitter by transmitting a single
 * data byte to the I2C bus in response to a read request from the master.
 *
 * This API is suitable for being called during an interrupt context. It is the
 * programmer's responsibility to ensure that there is enough space in the TX
 * FIFO to accomodate the request made.
 *
 * The I2C controller must be in slave mode before calling this function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       data
 *              The data byte to transmit.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_slave_transmit(ALT_I2C_DEV_t *i2c_dev,
                                       const uint8_t data);

/*!
 * This function acts in the role of a slave-transmitter by transmitting data in
 * bulk to the I2C bus in response to a series of read requests from a master.
 *
 * In the standard I2C protocol, all transactions are single byte transactions and
 * the slave responds to a remote master read request by writing one byte into the
 * slave's TX FIFO. When a slave (slave-transmitter) is issued with a read request
 * from the remote master (master-receiver), at a minimum there should be at least
 * one entry placed into the slave-transmitter's TX FIFO. The I2C controller is
 * capable of handling more data in the TX FIFO so that subsequent read requests
 * can receive that data without raising an interrupt or software having to poll
 * to request more data. This eliminates overhead latencies from being incurred by
 * servicing the interrupt or polling for data requests each time had there been a
 * restriction of having only one entry placed in the TX FIFO.
 *
 * If the remote master acknowledges the data sent by the slave-transmitter and
 * there is no data in the slave's TX FIFO, the I2C controller raises the read
 * request interrupt and waits for data to be written into the TX FIFO before it
 * can be sent to the remote master.
 *
 * If the programmer knows in advance that the master is requesting a packet of \e
 * n bytes, then when another master request for data is received, the TX FIFO
 * could be written with \e n number bytes and the master receives it as a
 * continuous stream of data. For example, the slave continues to send data to the
 * master as long as the master is acknowledging the data sent and there is data
 * available in the TX FIFO. There is no need to hold the SCL line low or to issue
 * READ request again.
 *
 * If the remote master is to receive \e n bytes from the slave but the programmer
 * wrote a number of bytes larger than \e n to the TX FIFO, then when the slave
 * finishes sending the requested \e n bytes, it clears the TX FIFO and ignores
 * any excess bytes.
 *
 * This API is suitable for being called during an interrupt context. It is the
 * programmer's responsibility to ensure that there is enough space in the TX
 * FIFO to accomodate the request made.
 *
 * The I2C controller must be in slave mode before calling this function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       data
 *              A pointer to the data buffer to transmit.
 *
 * \param       size
 *              The size of the data buffer in bytes to place in the TX FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * See: Section <em>Slave-Transfer Operation for Bulk Transfers</em> of the DW
 * Databook for details of implementation and error conditions that may occur.
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_slave_bulk_transmit(ALT_I2C_DEV_t *i2c_dev,
                                            const void * data,
                                            const size_t size);

/*!
 * This function returns the current target address.
 *
 * The I2C controller must be in master mode before calling this function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       target_addr
 *              [out] The 7 or 10 bit slave target address.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code.
 */
ALT_STATUS_CODE alt_i2c_master_target_get(ALT_I2C_DEV_t * i2c_dev, uint32_t * target_addr);

/*!
 * This function updates the target slave address for any upcoming I2C bus IO.
 *
 * This API is not suitlabe for being called in an interrupt context as it
 * will wait for the TX FIFO to flush before applying the changes. If the TX
 * FIFO is known to be empty and the controller idle, then it can be safely
 * called.
 *
 * The I2C controller must be in master mode before calling this function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       target_addr
 *              The 7 or 10 bit slave target address.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code.
 */
ALT_STATUS_CODE alt_i2c_master_target_set(ALT_I2C_DEV_t * i2c_dev, uint32_t target_addr);

/*!
 * This function acts in the role of a master-transmitter by issuing a write
 * command and transmitting data to the I2C bus.
 *
 * This API is not suitable for being called in an interrupt context as it may
 * wait for certain controller states before completing.
 *
 * The I2C controller must be in master mode before calling this function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       data
 *              A pointer to a data buffer to transmit
 *
 * \param       size
 *              The size of the data buffer in bytes to place in the TX FIFO.
 *
 * \param       issue_restart
 *              This parameter controls whether a RESTART is issued before the
 *              byte is sent or received. If:
 *              * \b true - if \e restart_enabled in \ref ALT_I2C_MASTER_CONFIG_t
 *                is \b true, a RESTART is issued before the data is sent/received
 *                (according to the value of CMD), regardless of whether or not
 *                the transfer direction is changing from the previous command; if
 *                \e restart_enabled is \b false, a STOP followed by a START is
 *                issued instead.
 *              * \b false - If \e restart_enabled in \ref ALT_I2C_MASTER_CONFIG_t
 *                is \b true, a RESTART is issued only if the transfer direction
 *                is changing from the previous command; if \e restart_enabled is
 *                \b false, a STOP followed by a START is issued instead.
 *              
 * \param       issue_stop
 *              This parameter controls whether a STOP is issued after the byte is
 *              sent or received. If:
 *              * \b true - STOP is issued after this byte, regardless of whether or
 *                not the Tx FIFO is empty. If the Tx FIFO is not empty, the
 *                master immediately tries to start a new transfer by issuing a
 *                START and arbitrating for the bus.
 *              * \b false - STOP is not issued after this byte, regardless of
 *                whether or not the Tx FIFO is empty. If the Tx FIFO is not
 *                empty, the master continues the current transfer by
 *                sending/receiving data bytes according to the value of the CMD
 *                bit. If the Tx FIFO is empty, the master holds the SCL line low
 *                and stalls the bus until a new command is available in the Tx
 *                FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_master_transmit(ALT_I2C_DEV_t *i2c_dev,
                                        const void * data,
                                        const size_t size,
                                        const bool issue_restart,
                                        const bool issue_stop);

/*!
 * This function acts in the role of a master-receiver by receiving one or more
 * data bytes transmitted from a slave in response to read requests issued from
 * this master.
 *
 * This function causes the master to issue the required number of read requests
 * to the slave and read the received data bytes from the Rx FIFO.
 *
 * The \e issue_restart and \e issue_stop parameters apply to the final read
 * request transaction in the \e num_data_entries sequence required to fulfill the
 * aggregate receive request.
 *
 * This API is not suitable for being called in an interrupt context as it may
 * wait for certain controller states before completing.
 *
 * The I2C controller must be in master mode before calling this function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       data
 *              [out] The data buffer to receive the requested \e size bytes.
 *
 * \param       size
 *              The size of the data buffer to read from the RX FIFO.
 *
 * \param       issue_restart
 *              This parameter controls whether a RESTART is issued before the
 *              byte is sent or received. If:
 *              * \b true - if \e restart_enabled in \ref ALT_I2C_MASTER_CONFIG_t
 *                is \b true, a RESTART is issued before the data is sent/received
 *                (according to the value of CMD), regardless of whether or not
 *                the transfer direction is changing from the previous command; if
 *                \e restart_enabled is \b false, a STOP followed by a START is
 *                issued instead.
 *              * \b false - If \e restart_enabled in \ref ALT_I2C_MASTER_CONFIG_t
 *                is \b true, a RESTART is issued only if the transfer direction
 *                is changing from the previous command; if \e restart_enabled is
 *                \b false, a STOP followed by a START is issued instead.
 *              
 * \param       issue_stop
 *              This parameter controls whether a STOP is issued after the byte is
 *              sent or received. If:
 *              * \b true - STOP is issued after this byte, regardless of whether or
 *                not the Tx FIFO is empty. If the Tx FIFO is not empty, the
 *                master immediately tries to start a new transfer by issuing a
 *                START and arbitrating for the bus.
 *              * \b false - STOP is not issued after this byte, regardless of
 *                whether or not the Tx FIFO is empty. If the Tx FIFO is not
 *                empty, the master continues the current transfer by
 *                sending/receiving data bytes according to the value of the CMD
 *                bit. If the Tx FIFO is empty, the master holds the SCL line low
 *                and stalls the bus until a new command is available in the Tx
 *                FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_master_receive(ALT_I2C_DEV_t *i2c_dev,
                                       void * data,
                                       const size_t size,
                                       const bool issue_restart,
                                       const bool issue_stop);

/*!
 * This function causes the I2C controller master to issue a READ request on the
 * bus. This function is typically used during master-receiver transfers.
 *
 * The I2C controller must be in master mode before calling this function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       issue_restart
 *              This parameter controls whether a RESTART is issued before the
 *              byte is sent or received. If:
 *              * \b true - if \e restart_enabled in \ref ALT_I2C_MASTER_CONFIG_t
 *                is \b true, a RESTART is issued before the data is sent/received
 *                (according to the value of CMD), regardless of whether or not
 *                the transfer direction is changing from the previous command; if
 *                \e restart_enabled is \b false, a STOP followed by a START is
 *                issued instead.
 *              * \b false - If \e restart_enabled in \ref ALT_I2C_MASTER_CONFIG_t
 *                is \b true, a RESTART is issued only if the transfer direction
 *                is changing from the previous command; if \e restart_enabled is
 *                \b false, a STOP followed by a START is issued instead.
 *              
 * \param       issue_stop
 *              This parameter controls whether a STOP is issued after the byte is
 *              sent or received. If:
 *              * \b true - STOP is issued after this byte, regardless of whether or
 *                not the Tx FIFO is empty. If the Tx FIFO is not empty, the
 *                master immediately tries to start a new transfer by issuing a
 *                START and arbitrating for the bus.
 *              * \b false - STOP is not issued after this byte, regardless of
 *                whether or not the Tx FIFO is empty. If the Tx FIFO is not
 *                empty, the master continues the current transfer by
 *                sending/receiving data bytes according to the value of the CMD
 *                bit. If the Tx FIFO is empty, the master holds the SCL line low
 *                and stalls the bus until a new command is available in the Tx
 *                FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * Write IC_DATA_CMD.CMD = 1 (read request). IC_DATA_CMD.DAT is
 * written with "don't care" values as these bits are ignored by the
 * I2C controller .
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_issue_read(ALT_I2C_DEV_t *i2c_dev,
                                   const bool issue_restart,
                                   const bool issue_stop);

/*!
 * This function causes the I2C controller master to issue a send byte on the
 * bus. This function is typically used during master-transmitter/slave-transmitter
 * transfers.
 *
 * The I2C controller must be in master mode before calling this function.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       value
 *              The data item to be transmitted.
 *
 * \param       issue_restart
 *              This parameter controls whether a RESTART is issued before the
 *              byte is sent or received. If:
 *              * \b true - if \e restart_enabled in \ref ALT_I2C_MASTER_CONFIG_t
 *                is \b true, a RESTART is issued before the data is sent/received
 *                (according to the value of CMD), regardless of whether or not
 *                the transfer direction is changing from the previous command; if
 *                \e restart_enabled is \b false, a STOP followed by a START is
 *                issued instead.
 *              * \b false - If \e restart_enabled in \ref ALT_I2C_MASTER_CONFIG_t
 *                is \b true, a RESTART is issued only if the transfer direction
 *                is changing from the previous command; if \e restart_enabled is
 *                \b false, a STOP followed by a START is issued instead.
 *              
 * \param       issue_stop
 *              This parameter controls whether a STOP is issued after the byte is
 *              sent or received. If:
 *              * \b true - STOP is issued after this byte, regardless of whether or
 *                not the Tx FIFO is empty. If the Tx FIFO is not empty, the
 *                master immediately tries to start a new transfer by issuing a
 *                START and arbitrating for the bus.
 *              * \b false - STOP is not issued after this byte, regardless of
 *                whether or not the Tx FIFO is empty. If the Tx FIFO is not
 *                empty, the master continues the current transfer by
 *                sending/receiving data bytes according to the value of the CMD
 *                bit. If the Tx FIFO is empty, the master holds the SCL line low
 *                and stalls the bus until a new command is available in the Tx
 *                FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * Write IC_DATA_CMD.CMD = 0 (write request). 
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_issue_write(ALT_I2C_DEV_t *i2c_dev,
                                    const uint8_t value,
                                    const bool issue_restart,
                                    const bool issue_stop);

/******************************************************************************/
/*! \addtogroup ALT_I2C_GEN_CALL General Call
 *
 * The functions in this group support General Call addresses.
 * 
 * The general call address is for addressing every device connected to the I2C
 * bus at the same time. However, if a device does not need any of the data
 * supplied within the general call structure, it can ignore this address by not
 * issuing an acknowledgment. If a device does require data from a general call
 * address, it acknowledges this address and behaves as a slave-receiver. The
 * master does not actually know how many devices acknowledged if one or more
 * devices respond. The second and following bytes are acknowledged by every
 * slave-receiver capable of handling this data. A slave who cannot process one of
 * these bytes must ignore it by not-acknowledging. If one or more slaves
 * acknowledge, the not-acknowledge will not be seen by the master.
 *
 * The functions in this group do not provide any general call functional command
 * interpretation or implementation (e.g. software reset).
 *
 * @{
 */

/*!
 * This function acts in the role of a master-transmitter by issuing a general
 * call command to all devices connected to the I2C bus.
 *
 * The \e issue_restart and \e issue_stop parameters apply to the final write
 * transaction in the \e num_data_entries byte transmission sequence.
 *
 * The I2C controller must be in master mode before calling this function.
 *
 * The target slave address will be modified by this function. Call
 * alt_i2c_master_target_set() to reset the slave target address for
 * subsequent IO.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       data
 *              An array of data byte(s) to transmit.
 *
 * \param       num_data_entries
 *              The number of entries (bytes) in \e data to place in the TX FIFO.
 *
 * \param       issue_restart
 *              This parameter controls whether a RESTART is issued before the
 *              byte is sent or received. If:
 *              * \b true - if \e restart_enabled in \ref ALT_I2C_MASTER_CONFIG_t
 *                is \b true, a RESTART is issued before the data is sent/received
 *                (according to the value of CMD), regardless of whether or not
 *                the transfer direction is changing from the previous command; if
 *                \e restart_enabled is \b false, a STOP followed by a START is
 *                issued instead.
 *              * \b false - If \e restart_enabled in \ref ALT_I2C_MASTER_CONFIG_t
 *                is \b true, a RESTART is issued only if the transfer direction
 *                is changing from the previous command; if \e restart_enabled is
 *                \b false, a STOP followed by a START is issued instead.
 *              
 * \param       issue_stop
 *              This parameter controls whether a STOP is issued after the byte is
 *              sent or received. If:
 *              * \b true - STOP is issued after this byte, regardless of whether or
 *                not the Tx FIFO is empty. If the Tx FIFO is not empty, the
 *                master immediately tries to start a new transfer by issuing a
 *                START and arbitrating for the bus.
 *              * \b false - STOP is not issued after this byte, regardless of
 *                whether or not the Tx FIFO is empty. If the Tx FIFO is not
 *                empty, the master continues the current transfer by
 *                sending/receiving data bytes according to the value of the CMD
 *                bit. If the Tx FIFO is empty, the master holds the SCL line low
 *                and stalls the bus until a new command is available in the Tx
 *                FIFO.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_master_general_call(ALT_I2C_DEV_t *i2c_dev,
                                            const void * data,
                                            const size_t size,
                                            const bool issue_restart,
                                            const bool issue_stop);

/*!
 * Disables the I2C controller from responding to a General Call address. The
 * controller will respond with a NACK and no General Call status conditions or
 * interrupts are generated.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_ACK_GENERAL_CALL.ACK_GEN_CALL = 0
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_general_call_ack_disable(ALT_I2C_DEV_t *i2c_dev);

/*!
 * Enables the I2C controller to respond with an ACK when it receives a General
 * Call address.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_ACK_GENERAL_CALL.ACK_GEN_CALL = 1
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_general_call_ack_enable(ALT_I2C_DEV_t *i2c_dev);

/*!
 * Returns ALT_E_TRUE if the I2C controller is enabled to respond to General Call
 * addresses.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_ACK_GENERAL_CALL.ACK_GEN_CALL == 1
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_general_call_ack_is_enabled(ALT_I2C_DEV_t *i2c_dev);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_I2C_INT Interrupt and Status Conditions
 *
 * The functions in this group provide management for the I2C controller status
 * conditions and interrupts.
 *
 * Each I2C controller has a single combined interrupt output (\b
 * ALT_INT_INTERRUPT_I2C<em>n</em>_IRQ). The following events can generate an
 * interrupt:
 * * General Call Address Received
 * * Start or Restart Condition Occurred
 * * Stop Condition Occurred
 * * I2C Controller Activity
 * * Receive Done
 * * Transmit Abort
 * * Read Request
 * * Transmit Buffer Empty
 * * Transmit Overflow
 * * Receive Buffer Full
 * * Receive Overflow
 * * Receive Underflow
 *
 * These interrupt status conditions may be monitored either by polling their
 * status or by configuring interrupt handlers using the HWLIB Interrupt
 * Controller API.
 *
 * Functions to get the current status, enable or disable (i.e. mass or unmask),
 * and clear interrupt status conditions for the I2C controller are defined in
 * this section.
 *
 * @{
 */

/*!
 * Returns the current I2C controller interrupt status conditions.
 *
 * This function returns the current value of the I2C controller interrupt status
 * register value which reflects the current I2C controller status conditions that
 * are not disabled (i.e. masked).
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       status
 *              [out] A pointer to a bit mask of the active \ref ALT_I2C_STATUS_t
 *              interrupt and status conditions.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_INTR_STAT
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_int_status_get(ALT_I2C_DEV_t *i2c_dev,
                                       uint32_t *status);

/*!
 * Returns the I2C controller raw interrupt status conditions irrespective of
 * the interrupt status condition enablement state.
 *
 * This function returns the current value of the I2C controller raw interrupt
 * status register value which reflects the current I2C controller status
 * conditions regardless of whether they are disabled (i.e. masked) or not.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       status
 *              [out] A pointer to a bit mask of the active \ref ALT_I2C_STATUS_t
 *              interrupt and status conditions.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_INTR_STAT
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_int_raw_status_get(ALT_I2C_DEV_t *i2c_dev,
                                           uint32_t *status);

/*!
 * Clears the specified I2C controller interrupt status conditions identified
 * in the mask.
 *
 * This function clears one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_I2C<em>n</em>_IRQ interrupt signal state.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       mask
 *              Specifies the QSPI interrupt status conditions to clear. \e mask
 *              is a mask of logically OR'ed \ref ALT_I2C_STATUS_t values that
 *              designate the status conditions to clear.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_int_clear(ALT_I2C_DEV_t *i2c_dev, const uint32_t mask);

/*!
 * Disable the specified I2C controller interrupt status conditions identified in
 * the mask.
 *
 * This function disables one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_I2C<em>n</em>_IRQ interrupt signal state.
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have
 *       the effect of enabling it as a contributor to the \b
 *       ALT_INT_INTERRUPT_I2C<em>n</em>_IRQ interrupt signal state. The function
 *       alt_i2c_int_enable() is used to enable status source conditions.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       mask
 *              Specifies the status conditions to disable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed \ref
 *              ALT_I2C_STATUS_t values that designate the status conditions to
 *              disable.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_int_disable(ALT_I2C_DEV_t *i2c_dev, const uint32_t mask);

/*!
 * Enable the specified I2C controller interrupt status conditions identified in
 * the mask.
 *
 * This function enables one or more of the status conditions as contributors to
 * the \b ALT_INT_INTERRUPT_I2C<em>n</em>_IRQ interrupt signal state.
 *
 * NOTE: A cleared bit for any status condition in the mask value does not have
 *       the effect of disabling it as a contributor to the \b
 *       ALT_INT_INTERRUPT_I2C<em>n</em>_IRQ interrupt signal state. The function
 *       alt_i2c_int_disable() is used to disable status source conditions.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       mask
 *              Specifies the status conditions to enable as interrupt source
 *              contributors. \e mask is a mask of logically OR'ed \ref
 *              ALT_I2C_STATUS_t values that designate the status conditions to
 *              enable.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_int_enable(ALT_I2C_DEV_t *i2c_dev, const uint32_t mask);

/*!
 * Gets the cause of I2C transmission abort. A I2C transmission abort indicates
 * that the I2C transmitter is unable to complete the intended actions on the
 * contents of the transmit FIFO. This situation can occur both as an I2C master
 * or an I2C slave, and is referred to as a "transmit abort".
 *
 * The returned value of this function is the value of the IC_TX_ABRT_SOURCE
 * register which indicates the cause why the transmit abort occurred.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       cause
 *              [out] A pointer to a bit mask of the \ref ALT_I2C_TX_ABORT_CAUSE_t
 *              causes of the transmission abort.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_TX_ABRT_SOURCE
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_tx_abort_cause_get(ALT_I2C_DEV_t *i2c_dev,
                                           ALT_I2C_TX_ABORT_CAUSE_t *cause);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_I2C_RX_FIFO RX FIFO Management
 *
 * The receive FIFO has a configurable threshold value that controls the level of
 * entries (or above) that sets the RX_FULL status condition and triggers an
 * interrupt. The valid range is 0 - (ALT_I2C_RX_FIFO_NUM_ENTRIES-1), with the
 * additional restriction that I2C controller does not allow this value to be set
 * to a value larger than the depth of the buffer. If an attempt is made to do
 * that, the actual value set will be the maximum depth of the buffer. A value of
 * 0 sets the threshold for 1 entry, and a value of (ALT_I2C_RX_FIFO_NUM_ENTRIES-1)
 * sets the threshold for ALT_I2C_RX_FIFO_NUM_ENTRIES entries.
 *
 * @{
 */

/*!
 * The number of entries (depth) of the I2C controller receive FIFO.
 */
#define ALT_I2C_RX_FIFO_NUM_ENTRIES     64

/*!
 * Returns ALT_E_TRUE when the receive FIFO is empty.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_STATUS.RFNE == 0
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_rx_fifo_is_empty(ALT_I2C_DEV_t *i2c_dev);

/*!
 * Returns ALT_E_TRUE when the receive FIFO is completely full.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_STATUS.RFF == 1
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_rx_fifo_is_full(ALT_I2C_DEV_t *i2c_dev);

/*!
 * Returns the number of valid entries in the receive FIFO.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
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
ALT_STATUS_CODE alt_i2c_rx_fifo_level_get(ALT_I2C_DEV_t *i2c_dev,
                                          uint32_t *num_entries);

/*!
 * Gets the current receive FIFO threshold level value.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
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
ALT_STATUS_CODE alt_i2c_rx_fifo_threshold_get(ALT_I2C_DEV_t *i2c_dev,
                                              uint8_t *threshold);

/*!
 * Sets the current receive FIFO threshold level value.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
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
ALT_STATUS_CODE alt_i2c_rx_fifo_threshold_set(ALT_I2C_DEV_t *i2c_dev,
                                              const uint8_t threshold);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_I2C_TX_FIFO TX FIFO Management
 *
 * The transmit FIFO has a configurable threshold value that controls the level of
 * entries (or below) that sets the TX_EMPTY status condition and triggers an
 * interrupt. The valid range is 0 - (ALT_I2C_TX_FIFO_NUM_ENTRIES-1), with the
 * additional restriction that I2C controller does not allow this value to be set
 * to a value larger than the depth of the buffer. If an attempt is made to do
 * that, the actual value set will be the maximum depth of the buffer. A value of
 * 0 sets the threshold for 0 entries, and a value of (ALT_I2C_TX_FIFO_NUM_ENTRIES-1)
 * sets the threshold for (ALT_I2C_TX_FIFO_NUM_ENTRIES-1) entries.
 *
 * @{
 */

/*!
 * The number of entries (depth) of the I2C controller transmit FIFO.
 */
#define ALT_I2C_TX_FIFO_NUM_ENTRIES     64

/*!
 * Returns ALT_E_TRUE when the transmit FIFO is empty.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_STATUS.TFE == 1
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_tx_fifo_is_empty(ALT_I2C_DEV_t *i2c_dev);

/*!
 * Returns ALT_E_TRUE when the transmit FIFO is completely full.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 *
 * \internal
 * IC_STATUS.TFNF == 0
 * \endinternal
 */
ALT_STATUS_CODE alt_i2c_tx_fifo_is_full(ALT_I2C_DEV_t *i2c_dev);

/*!
 * Returns the number of valid entries in the transmit FIFO.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
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
ALT_STATUS_CODE alt_i2c_tx_fifo_level_get(ALT_I2C_DEV_t *i2c_dev,
                                          uint32_t *num_entries);

/*!
 * Gets the current transmit FIFO threshold level value.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
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
ALT_STATUS_CODE alt_i2c_tx_fifo_threshold_get(ALT_I2C_DEV_t *i2c_dev,
                                              uint8_t *threshold);

/*!
 * Sets the current transmit FIFO threshold level value.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
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
ALT_STATUS_CODE alt_i2c_tx_fifo_threshold_set(ALT_I2C_DEV_t *i2c_dev,
                                              const uint8_t threshold);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_I2C_DMA DMA Interface
 *
 * The DMA interface has a configurable threshold value that controls the
 * level of entries that triggers the burst handshaking request used for DMA
 * integration.
 *
 * For the TX threshold, if the number of entries in the TX FIFO is at or
 * below the set threshold, a DMA handshaking request will be made. The valid
 * range for the TX threshold is 0 - (ALT_I2C_TX_FIFO_NUM_ENTRIES - 1).
 *
 * For the RX threshold, if the number of entries in the RX FIFO is above the
 * set threshold, a DMA handshaking request will be made. The valid range for
 * the RX treshold is 0 - (ALT_I2C_TX_FIFO_NUM_ENTRIES - 1).
 *
 * Having a higher threshold can improve the AXI bus utilization at the
 * expense of the likelyhoold of overflow / underflow conditions.
 * @{
 */

/*!
 * Gets the current RX DMA threshold level value.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       threshold
 *              [out] The threshold value.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_i2c_rx_dma_threshold_get(ALT_I2C_DEV_t * i2c_dev, uint8_t * threshold);

/*!
 * Sets the current RX DMA threshold level value.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       threshold
 *              The threshold value.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_i2c_rx_dma_threshold_set(ALT_I2C_DEV_t * i2c_dev, uint8_t threshold);

/*!
 * Gets the current TX DMA threshold level value.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       threshold
 *              [out] The threshold value.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_i2c_tx_dma_threshold_get(ALT_I2C_DEV_t * i2c_dev, uint8_t * threshold);

/*!
 * Sets the current TX DMA threshold level value.
 *
 * \param       i2c_dev
 *              A pointer to the I2C controller device block instance.
 *
 * \param       threshold
 *              The threshold value.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_i2c_tx_dma_threshold_set(ALT_I2C_DEV_t * i2c_dev, uint8_t threshold);

/*! @} */

/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_I2C_H__ */
