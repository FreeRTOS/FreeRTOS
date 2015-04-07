/*! \file
 *  Contains definitions for the Altera Hardware Libraries Clock Manager
 *  Application Programming Interface
 */

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

#ifndef __ALT_CLK_MGR_H__
#define __ALT_CLK_MGR_H__

#include "hwlib.h"
#include "alt_clock_group.h"

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*! \addtogroup CLK_MGR The Clock Manager API
 *
 * This module defines the Clock Manager API for accessing, configuring, and
 * controlling the HPS clock resources.
 *
 * @{
 */

/******************************************************************************/
/*!
 * This type definition is an opaque type definition for clock frequency values
 * in Hz.
 */
typedef uint32_t    alt_freq_t;

/******************************************************************************/
/*!
 * This type definition enumerates the names of the clock and PLL resources
 * managed by the Clock Manager.
 */
typedef enum ALT_CLK_e
{
    /* Clock Input Pins */
    ALT_CLK_IN_PIN_OSC1,
                                        /*!< \b OSC_CLK_1_HPS
                                         *   External oscillator input:
                                         *   * Input Pin
                                         *   * Clock source to Main PLL
                                         *   * Clock source to SDRAM PLL
                                         *     and Peripheral PLL if selected via
                                         *     register write
                                         *   * Clock source for clock in safe mode
                                         */

    ALT_CLK_IN_PIN_OSC2,
                                        /*!< \b OSC_CLK_2_HPS
                                         *   External Oscillator input:
                                         *   * Input Pin
                                         *   * Optional clock source to SDRAM PLL
                                         *     and Peripheral PLL if selected
                                         *   * Typically used for Ethernet
                                         *     reference clock
                                         */


    /* FPGA Clock Sources External to HPS */
    ALT_CLK_F2H_PERIPH_REF,
                                        /*<! Alternate clock source from FPGA
                                         * for HPS Peripheral PLL. */

    ALT_CLK_F2H_SDRAM_REF,
                                        /*<! Alternate clock source from FPGA
                                         * for HPS SDRAM PLL. */


    /* Other Clock Sources External to HPS */
    ALT_CLK_IN_PIN_JTAG,
                                        /*!< \b JTAG_TCK_HPS
                                         *   * Input Pin
                                         *   * External HPS JTAG clock input.
                                         */

    ALT_CLK_IN_PIN_ULPI0,
                                        /*!< \b ULPI0_CLK
                                         *   ULPI Clock provided by external USB0
                                         *   PHY
                                         *   * Input Pin
                                         */

    ALT_CLK_IN_PIN_ULPI1,
                                        /*!< \b ULPI1_CLK
                                         *   ULPI Clock provided by external USB1
                                         *   PHY
                                         *   * Input Pin
                                         */

    ALT_CLK_IN_PIN_EMAC0_RX,
                                        /*!< \b EMAC0:RX_CLK
                                         *   Rx Reference Clock for EMAC0
                                         *   * Input Pin
                                         */

    ALT_CLK_IN_PIN_EMAC1_RX,
                                        /*!< \b EMAC1:RX_CLK
                                         *   Rx Reference Clock for EMAC1
                                         *   * Input Pin
                                         */


    /* PLLs */
    ALT_CLK_MAIN_PLL,
                                        /*!< \b main_pll_ref_clkin
                                         *   Main PLL input reference clock,
                                         *   used to designate the Main PLL in
                                         *   PLL clock selections.
                                         */

    ALT_CLK_PERIPHERAL_PLL,
                                        /*!< \b periph_pll_ref_clkin
                                         *   Peripheral PLL input reference
                                         *   clock, used to designate the
                                         *   Peripheral PLL in PLL clock
                                         *   selections.
                                         */

    ALT_CLK_SDRAM_PLL,
                                        /*!< \b sdram_pll_ref_clkin
                                         *   SDRAM PLL input reference clock,
                                         *   used to designate the SDRAM PLL in
                                         *   PLL clock selections.
                                         */

    /* OSC1 Clock Group - The OSC1 clock group contains those clocks which are derived
     * directly from the osc_clk_1_HPS pin */
    ALT_CLK_OSC1,
                                        /*!< \b osc1_clk
                                         *   OSC1 Clock Group - The
                                         *   OSC1 clock group contains
                                         *   those clocks which are
                                         *   derived directly from the
                                         *   osc_clk_1_HPS pin.
                                         *   * alias for ALT_CLK_IN_PIN_OSC1
                                         */

    /* Main Clock Group - The following clocks are derived from the Main PLL. */
    ALT_CLK_MAIN_PLL_C0,
                                        /*!< \b Main PLL C0 Output */

    ALT_CLK_MAIN_PLL_C1,
                                        /*!< \b Main PLL C1 Output */

    ALT_CLK_MAIN_PLL_C2,
                                        /*!< \b Main PLL C2 Output */

    ALT_CLK_MAIN_PLL_C3,
                                        /*!< \b Main PLL C3 Output */

    ALT_CLK_MAIN_PLL_C4,
                                        /*!< \b Main PLL C4 Output */

    ALT_CLK_MAIN_PLL_C5,
                                        /*!< \b Main PLL C5 Output */

    ALT_CLK_MPU,
                                        /*!< \b mpu_clk
                                         *   Main PLL C0 Output. Clock for MPU
                                         *   subsystem, including CPU0 and CPU1.
                                         *   * Alias for \e ALT_CLK_MAIN_PLL_C0
                                         */

    ALT_CLK_MPU_L2_RAM,
                                        /*!< \b mpu_l2_ram_clk
                                         *   Clock for MPU level 2 (L2) RAM
                                         */

    ALT_CLK_MPU_PERIPH,
                                        /*!< \b mpu_periph_clk
                                         *   Clock for MPU snoop control unit
                                         *   (SCU) peripherals, such as the
                                         *   general interrupt controller (GIC)
                                         */

    ALT_CLK_L3_MAIN,
                                        /*!< \b main_clk
                                         *   Main PLL C1 Output
                                         *   * Alias for \e ALT_CLK_MAIN_PLL_C1
                                         */

    ALT_CLK_L3_MP,
                                        /*!< \b l3_mp_clk
                                         *   Clock for L3 Master Peripheral Switch
                                         */

    ALT_CLK_L3_SP,
                                        /*!< \b l3_sp_clk
                                         *   Clock for L3 Slave Peripheral Switch
                                         */

    ALT_CLK_L4_MAIN,
                                        /*!< \b l4_main_clk
                                         *   Clock for L4 main bus
                                         *   * Clock for DMA
                                         *   * Clock for SPI masters
                                         */

    ALT_CLK_L4_MP,
                                        /*!< \b l4_mp_clk
                                         *   Clock for L4 master peripherals (MP) bus
                                         */

    ALT_CLK_L4_SP,
                                        /*!< \b l4_sp_clk
                                         *   Clock for L4 slave peripherals (SP) bus
                                         */

    ALT_CLK_DBG_BASE,
                                        /*!< \b dbg_base_clk
                                         *   Main PLL C2 Output
                                         *   * Alias for \e ALT_CLK_MAIN_PLL_C2
                                         */

    ALT_CLK_DBG_AT,
                                        /*!< \b dbg_at_clk
                                         *   Clock for CoreSight debug Advanced
                                         *   Microcontroller Bus Architecture
                                         *   (AMBA) Trace Bus (ATB)
                                         */

    ALT_CLK_DBG_TRACE,
                                        /*!< \b dbg_trace_clk
                                         *   Clock for CoreSight debug Trace
                                         *   Port Interface Unit (TPIU)
                                         */

    ALT_CLK_DBG_TIMER,
                                        /*!< \b dbg_timer_clk
                                         *   Clock for the trace timestamp
                                         *   generator
                                         */

    ALT_CLK_DBG,
                                        /*!< \b dbg_clk
                                         *   Clock for Debug Access Port (DAP)
                                         *   and debug Advanced Peripheral Bus
                                         *   (APB)
                                         */

    ALT_CLK_MAIN_QSPI,
                                        /*!< \b main_qspi_clk
                                         *   Main PLL C3 Output. Quad SPI flash
                                         *   internal logic clock.
                                         *   * Alias for \e ALT_CLK_MAIN_PLL_C3
                                         */

    ALT_CLK_MAIN_NAND_SDMMC,
                                        /*!< \b main_nand_sdmmc_clk
                                         *   Main PLL C4 Output. Input clock to
                                         *   flash controller clocks block.
                                         *   * Alias for \e ALT_CLK_MAIN_PLL_C4
                                         */

    ALT_CLK_CFG,
                                        /*!< \b cfg_clk
                                         *   FPGA manager configuration clock.
                                         */

    ALT_CLK_H2F_USER0,
                                        /*!< \b h2f_user0_clock
                                         *   Clock to FPGA fabric
                                         */


    /* Peripherals Clock Group - The following clocks are derived from the Peripheral PLL */
    ALT_CLK_PERIPHERAL_PLL_C0,
                                        /*!< \b Peripheral PLL C0 Output */

    ALT_CLK_PERIPHERAL_PLL_C1,
                                        /*!< \b Peripheral PLL C1 Output */

    ALT_CLK_PERIPHERAL_PLL_C2,
                                        /*!< \b Peripheral PLL C2 Output */

    ALT_CLK_PERIPHERAL_PLL_C3,
                                        /*!< \b Peripheral PLL C3 Output */

    ALT_CLK_PERIPHERAL_PLL_C4,
                                        /*!< \b Peripheral PLL C4 Output */

    ALT_CLK_PERIPHERAL_PLL_C5,
                                        /*!< \b Peripheral PLL C5 Output */

    ALT_CLK_USB_MP,
                                        /*!< \b usb_mp_clk
                                         *   Clock for USB
                                         */

    ALT_CLK_SPI_M,
                                        /*!< \b spi_m_clk
                                         *   Clock for L4 SPI master bus
                                         */

    ALT_CLK_QSPI,
                                        /*!< \b qspi_clk
                                         *   Clock for Quad SPI
                                         */

    ALT_CLK_NAND_X,
                                        /*!< \b nand_x_clk
                                         *   NAND flash controller master and
                                         *   slave clock
                                         */

    ALT_CLK_NAND,
                                        /*!< \b nand_clk
                                         *   Main clock for NAND flash
                                         *   controller
                                         */

    ALT_CLK_SDMMC,
                                        /*!< \b sdmmc_clk
                                         *   Clock for SD/MMC logic input clock
                                         */

    ALT_CLK_EMAC0,
                                        /*!< \b emac0_clk
                                         *   EMAC 0 clock - Peripheral PLL C0
                                         *   Output
                                         *   * Alias for \e ALT_CLK_PERIPHERAL_PLL_C0
                                         */

    ALT_CLK_EMAC1,
                                        /*!< \b emac1_clk
                                         *   EMAC 1 clock - Peripheral PLL C1
                                         *   Output
                                         *   * Alias for \e ALT_CLK_PERIPHERAL_PLL_C1
                                         */

    ALT_CLK_CAN0,
                                        /*!< \b can0_clk
                                         *   Controller area network (CAN)
                                         *   controller 0 clock
                                         */

    ALT_CLK_CAN1,
                                        /*!< \b can1_clk
                                         *   Controller area network (CAN)
                                         *   controller 1 clock
                                         */

    ALT_CLK_GPIO_DB,
                                        /*!< \b gpio_db_clk
                                         *   Debounce clock for GPIO0, GPIO1,
                                         *   and GPIO2
                                         */

    ALT_CLK_H2F_USER1,
                                        /*!< \b h2f_user1_clock
                                         *   Clock to FPGA fabric - Peripheral
                                         *   PLL C5 Output
                                         *   * Alias for \e ALT_CLK_PERIPHERAL_PLL_C5
                                         */


    /* SDRAM Clock Group - The following clocks are derived from the SDRAM PLL */
    ALT_CLK_SDRAM_PLL_C0,
                                        /*!< \b SDRAM PLL C0 Output */

    ALT_CLK_SDRAM_PLL_C1,
                                        /*!< \b SDRAM PLL C1 Output */

    ALT_CLK_SDRAM_PLL_C2,
                                        /*!< \b SDRAM PLL C2 Output */

    ALT_CLK_SDRAM_PLL_C3,
                                        /*!< \b SDRAM PLL C3 Output */

    ALT_CLK_SDRAM_PLL_C4,
                                        /*!< \b SDRAM PLL C4 Output */

    ALT_CLK_SDRAM_PLL_C5,
                                        /*!< \b SDRAM PLL C5 Output */

    ALT_CLK_DDR_DQS,
                                        /*!< \b ddr_dqs_clk
                                         *   Clock for MPFE, single-port
                                         *   controller, CSR access, and PHY -
                                         *   SDRAM PLL C0 Output
                                         *   * Alias for \e ALT_CLK_SDRAM_PLL_C0
                                         */

    ALT_CLK_DDR_2X_DQS,
                                        /*!< \b ddr_2x_dqs_clk
                                         *    Clock for PHY - SDRAM PLL C1 Output
                                         *   * Alias for \e ALT_CLK_SDRAM_PLL_C1
                                         */

    ALT_CLK_DDR_DQ,
                                        /*!< \b ddr_dq_clk
                                         *   Clock for PHY - SDRAM PLL C2 Output
                                         *   * Alias for \e ALT_CLK_SDRAM_PLL_C2
                                         */

    ALT_CLK_H2F_USER2,
                                        /*!< \b h2f_user2_clock
                                         *   Clock to FPGA fabric - SDRAM PLL C5
                                         *   Output
                                         *   * Alias for \e ALT_CLK_SDRAM_PLL_C5
                                         */

    /* Clock Output Pins */
    ALT_CLK_OUT_PIN_EMAC0_TX,
                                       /*!< \b EMAC0:TX_CLK
                                        *   Tx Reference Clock for EMAC0
                                        *   * Output Pin
                                        */

    ALT_CLK_OUT_PIN_EMAC1_TX,
                                       /*!< \b EMAC1:TX_CLK
                                        *   Tx Reference Clock for EMAC1
                                        *   * Output Pin
                                        */

    ALT_CLK_OUT_PIN_SDMMC,
                                       /*!< \b SDMMC:CLK
                                        *   SD/MMC Card Clock
                                        *   * Output Pin
                                        */

    ALT_CLK_OUT_PIN_I2C0_SCL,
                                       /*!< \b I2C0:SCL
                                        *   I2C Clock for I2C0
                                        *   * Output Pin
                                        */

    ALT_CLK_OUT_PIN_I2C1_SCL,
                                       /*!< \b I2C1:SCL
                                        *   I2C Clock for I2C1
                                        *   * Output Pin
                                        */

    ALT_CLK_OUT_PIN_I2C2_SCL,
                                       /*!< \b I2C2:SCL
                                        *   I2C Clock for I2C2/2 wire
                                        *   * Output Pin
                                        */

    ALT_CLK_OUT_PIN_I2C3_SCL,
                                       /*!< \b I2C3:SCL
                                        *   I2C Clock for I2C1/2 wire
                                        *   * Output Pin
                                        */

    ALT_CLK_OUT_PIN_SPIM0,
                                       /*!< \b SPIM0:CLK
                                        *   SPI Clock
                                        *   * Output Pin
                                        */

    ALT_CLK_OUT_PIN_SPIM1,
                                       /*!< \b SPIM1:CLK
                                        *   SPI Clock
                                        *   * Output Pin
                                        */

    ALT_CLK_OUT_PIN_QSPI,
                                       /*!< \b QSPI:CLK
                                        *   QSPI Flash Clock
                                        *   * Output Pin
                                        */

    ALT_CLK_UNKNOWN
} ALT_CLK_t;

/******************************************************************************/
/*! \addtogroup CLK_MGR_STATUS Clock Manager Status
 *
 * This functional group provides status information on various aspects and
 * properties of the Clock Manager state.
 *
 * @{
 */
/******************************************************************************/
/*!
 * This type definition defines the lock condition status codes for each of the
 * PLLs. If the PLL lock status condition is enabled (See: alt_clk_irq_enable())
 * then it contributes to the overall \b clkmgr_IRQ signal assertion state.
 */
typedef enum ALT_CLK_PLL_LOCK_STATUS_e
{
    ALT_MAIN_PLL_LOCK_ACHV    = 0x00000001, /*!< This condition is set if the Main
                                             *   PLL has achieved lock at least once
                                             *   since this condition was last
                                             *   cleared.
                                             */
    ALT_PERIPH_PLL_LOCK_ACHV  = 0x00000002, /*!< This condition is set if the Peripheral
                                             *   PLL has achieved lock at least once
                                             *   since this condition was last
                                             *   cleared.
                                             */
    ALT_SDR_PLL_LOCK_ACHV     = 0x00000004, /*!< This condition is set if the SDRAM
                                             *   PLL has achieved lock at least once
                                             *   since this condition was last
                                             *   cleared.
                                             */
    ALT_MAIN_PLL_LOCK_LOST    = 0x00000008, /*!< This condition is set if the Main
                                             *   PLL has lost lock at least once
                                             *   since this condition was last
                                             *   cleared.
                                             */
    ALT_PERIPH_PLL_LOCK_LOST  = 0x00000010, /*!< This condition is set if the Peripheral
                                             *   PLL has lost lock at least once
                                             *   since this condition was last
                                             *   cleared.
                                             */
    ALT_SDR_PLL_LOCK_LOST     = 0x00000020  /*!< This condition is set if the SDRAM
                                             *   PLL has lost lock at least once
                                             *   since this condition was last
                                             *   cleared.
                                             */
} ALT_CLK_PLL_LOCK_STATUS_t;

/******************************************************************************/
/*!
 * Clear the selected PLL lock status conditions.
 *
 * This function clears assertions of one or more of the PLL lock status
 * conditions.
 *
 * NOTE: This function is used to clear \b clkmgr_IRQ interrupt signal source
 * assertion conditions.
 *
 * \param       lock_stat_mask
 *              Specifies the PLL lock status conditions to clear. \e lock_stat_mask
 *              is a mask of logically OR'ed \ref ALT_CLK_PLL_LOCK_STATUS_t
 *              values designating the PLL lock conditions to clear.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_BAD_ARG   The \e lock_stat_mask argument contains an
 *                              unknown condition value.
 */
ALT_STATUS_CODE alt_clk_lock_status_clear(ALT_CLK_PLL_LOCK_STATUS_t lock_stat_mask);

/******************************************************************************/
/*!
 * Returns the PLL lock status condition values.
 *
 * This function returns the value of the PLL lock status conditions.
 *
 * \returns The current values of the PLL lock status conditions as defined by
 * the \ref ALT_CLK_PLL_LOCK_STATUS_t mask bits. If the corresponding bit is set
 * then the condition is asserted.
 */
uint32_t alt_clk_lock_status_get(void);

/******************************************************************************/
/*!
 * Returns ALT_E_TRUE if the designated PLL is currently locked and ALT_E_FALSE
 * otherwise.
 *
 * \param       pll
 *              The PLL to return the lock status of.
 *
 * \retval      ALT_E_TRUE      The specified PLL is currently locked.
 * \retval      ALT_E_FALSE     The specified PLL is currently not locked.
 * \retval      ALT_E_BAD_ARG   The \e pll argument designates a non PLL clock
 *                              value.
 * \internal
 * NOTE: This function uses the
 *       * \b hps::clkmgr::inter::mainplllocked
 *       * \b hps::clkmgr::inter::perplllocked,
 *       * \b hps::clkmgr::inter::sdrplllocked
 *
 *       bits to determine if the PLL is locked or not.
 * \endinternal
 */
ALT_STATUS_CODE alt_clk_pll_is_locked(ALT_CLK_t pll);

/*! @} */

/******************************************************************************/
/*! \addtogroup CLK_MGR_SAFE_MODE Safe Mode Options
 *
 * When safe mode is enabled, clocks in the HPS are directly generated from the
 * \b osc1_clk clock. Safe mode is enabled by the assertion of a safe mode
 * request from the reset manager or by a cold reset. Assertion of the safe mode
 * request from the reset manager sets the safe mode bit in the clock manager
 * control register. No other control register bits are affected by the safe
 * mode request from the reset manager.
 *
 * While in safe mode, clock manager register settings which control clock
 * behavior are not changed. However, the output of the registers which control
 * the clock manager state are forced to the safe mode values such that the
 * following conditions occur:
 * * All PLLs are bypassed to the \b osc1_clk clock, including their counters.
 * * Clock dividers select their default reset values.
 * * The flash controllers source clock selections are set to the peripheral
 *   PLL.
 * * All clocks are enabled.
 * * Safe mode is optionally applied to debug clocks.
 *
 * A write by software is the only way to clear the safe mode bit. All registers
 * and clocks need to be configured correctly and all software-managed clocks
 * need to be gated off before clearing safe mode. Software can then gate clocks
 * on as required.
 *
 * On cold reset, all clocks are put in safe mode.
 *
 * On warm reset, safe mode is optionally and independently applied to debug
 * clocks and normal (i.e.non-debug) clocks based on clock manager register
 * settings. The default response for warm reset is to put all clocks in safe
 * mode.
 *
 * The APIs in this group provide control of the Clock Manager safe mode warm
 * reset response behavior.
 * @{
 */

/******************************************************************************/
/*!
 * This type definition enumerates the safe mode clock domains under control of
 * the Clock Manager.
 */
typedef enum ALT_CLK_SAFE_DOMAIN_e
{
    /*!
     * This enumeration literal specifies the normal safe mode domain. The
     * normal domain consists of all clocks except debug clocks.
     */
    ALT_CLK_DOMAIN_NORMAL,
    /*!
     * This enumeration literal specifies the debug safe mode domain. The debug
     * domain consists of all debug clocks.
     */
    ALT_CLK_DOMAIN_DEBUG
} ALT_CLK_SAFE_DOMAIN_t;

/******************************************************************************/
/*!
 * Clear the safe mode status of the Clock Manager following a reset.
 *
 * NOTE: Safe mode should only be cleared once clocks have been correctly
 * configured.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_clk_safe_mode_clear(void);

/******************************************************************************/
/*!
 * Return whether the specified safe mode clock domain is in safe mode or not.
 *
 * \param       clk_domain
 *              The safe mode clock domain to check whether in safe mode or not.
 *
 * \retval      TRUE            The safe mode clock domain is in safe mode.
 * \retval      FALSE           The safe mode clock domain is not in safe mode.
 */
bool alt_clk_is_in_safe_mode(ALT_CLK_SAFE_DOMAIN_t clk_domain);

/*! @} */

/******************************************************************************/
/*! \addtogroup CLK_MGR_BYPASS PLL Bypass Control
 *
 * When a PLL is in bypass, the PLL clock logic is kept in reset. In this
 * manner, the PLL clock can be free running while it stabilizes and achieves
 * lock. The bypass logic isolates PLL configuration registers from the clock
 * while changes are made to the PLL settings.
 *
 * The bypass controls are used by software to change the source clock input
 * reference (for Peripheral and SDRAM PLLs) and is recommended when changing
 * settings that may affect the ability of the VCO to maintain lock.  When a PLL
 * is taken in or out of bypass the PLL output clocks will pause momentarily
 * while the clocks are in transition, There will be no glitches or clocks
 * shorter than the either the old or the new clock period.
 *
 * In summary, the PLL bypass controls permit:
 * * Each PLL to be individually bypassed.
 * * Bypass of all PLL clock outputs to \b osc1_clk or alternatively the PLLs
 *   reference clock input source reference clock selection.
 * * Isolation of a the PLL VCO frequency registers (multiplier and divider),
     phase shift registers (negative phase) , and post scale counters.
 * * Glitch free clock transitions.
 * @{
 */
/******************************************************************************/
/*!
 * Disable bypass mode for the specified PLL. This operation takes the PLL out
 * of bypass mode.
 *
 * \param       pll
 *              The PLL to take out of bypass mode.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The \e pll argument specified a non PLL clock
 *                              value.
 */
ALT_STATUS_CODE alt_clk_pll_bypass_disable(ALT_CLK_t pll);

/******************************************************************************/
/*!
 * Enable bypass mode for the specified PLL.
 *
 * \param       pll
 *              The PLL to put into bypass mode.
 *
 * \param       use_input_mux
 *              If TRUE then use the PLLs reference clock input source selection
 *              to directly drive the bypass clock. If FALSE then use bypass
 *              clock directly driven by the \b osc1_clk.
 *
 * \retval      ALT_E_SUCCESS       The operation was succesful.
 * \retval      ALT_E_ERROR         The operation failed.
 * \retval      ALT_E_BAD_ARG       The \e pll argument specified a non PLL
 *                                  clock value.
 * \retval      ALT_E_INV_OPTION    TRUE is an invalid option for
 *                                  \e use_input_mux with the \e pll selection.
 */
ALT_STATUS_CODE alt_clk_pll_bypass_enable(ALT_CLK_t pll,
                                          bool use_input_mux);

/******************************************************************************/
/*!
 * Return whether the specified PLL is in bypass or not.
 *
 * \internal
 * This function must also test the \b clkmgr.ctrl.safemode bit in
 * addition to the PLLs bypass bit to tell whether the bypass mode is
 * effect or not.
 * \endinternal
 *
 * \param       pll
 *              The PLL to check whether in bypass mode or not.
 *
 * \retval      ALT_E_TRUE      The PLL is in bypass mode.
 * \retval      ALT_E_FALSE     The PLL is not in bypass mode.
 * \retval      ALT_E_BAD_ARG   The \e pll argument designates a non PLL clock
 *                              value.
 */
ALT_STATUS_CODE alt_clk_pll_is_bypassed(ALT_CLK_t pll);

/*! @} */

/******************************************************************************/
/*! \addtogroup CLK_MGR_GATE Clock Gating Control
 *
 * This functional group provides gating control of selected clock signals.
 *
 * When a clock is enabled, then its clock signal propogates to its respective
 * clocked IP block(s).  When a clock is disabled, then its clock signal is
 * prevented from propogating to its respective clocked IP block(s).
 *
 * The following clocks may be gated:
 *
 * * Main PLL Group
 *   - l4_main_clk
 *   - l3_mp_clk
 *   - l4_mp_clk
 *   - l4_sp_clk
 *   - dbg_at_clk
 *   - dbg_clk
 *   - dbg_trace_clk
 *   - dbg_timer_clk
 *   - cfg_clk
 *   - s2f_user0_clk
 *
 * * SDRAM PLL Group
 *   - ddr_dqs_clk
 *   - ddr_2x_clk
 *   - ddr_dq_clk
 *   - s2f_user2_clk
 *
 * * Peripheral PLL Group
 *   - emac0_clk
 *   - emac1_clk
 *   - usb_mp_clk
 *   - spi_m_clk
 *   - can0_clk
 *   - can1_clk
 *   - gpio_db_clk
 *   - s2f_user1_clk
 *   - sdmmc_clk
 *   - nand_clk
 *   - nand_x_clk
 *   - qspi_clk
 *
 * @{
 */
/******************************************************************************/
/*!
 * Disable the specified clock. Once the clock is disabled, its clock signal does
 * not propogate to its clocked elements.
 *
 * \param       clk
 *              The clock to disable.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The \e clk argument designates a non gated clock
 *                              value.
 */
ALT_STATUS_CODE alt_clk_clock_disable(ALT_CLK_t clk);

/******************************************************************************/
/*!
 * Enable the specified clock. Once the clock is enabled, its clock signal
 * propogates to its elements.
 *
 * \param       clk
 *              The clock to enable.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   The \e clk argument designates a non gated clock
 *                              value.
 */
ALT_STATUS_CODE alt_clk_clock_enable(ALT_CLK_t clk);

/******************************************************************************/
/*!
 * Return whether the specified clock is enabled or not.
 *
 * \param       clk
 *              The clock to check whether enabled or not.
 *
 * \retval      ALT_E_TRUE      The clock is enabled.
 * \retval      ALT_E_FALSE     The clock is not enabled.
 * \retval      ALT_E_BAD_ARG   The \e clk argument designates a non gated clock
 *                              value.
 */
ALT_STATUS_CODE alt_clk_is_enabled(ALT_CLK_t clk);

/*! @} */

/******************************************************************************/
/*! \addtogroup CLK_MGR_CLK_SEL Clock Source Selection
 *
 * This API group provide access and control to the input reference clock source
 * selection for a clock or PLL.
 *
 * \internal
 * These are the clocks that have software configurable input reference clock
 * source selection available. Each clock below is listed with its valid
 * input reference clock source selections.
 *
 * + Valid reference clock input selections for \b sdram_pll_ref_clkin
 *   - osc_clk_1
 *   - osc_clk_2
 *   - f2h_sdram_ref_clk
 *
 * + Valid reference clock input selections for \b periph_pll_ref_clkin
 *   - osc_clk_1
 *   - osc_clk_2,
 *   - f2h_periph_ref_clk
 *
 * + Valid reference clock input selections for \b l4_mp_clk
 *   - periph_base_clk
 *   - main_clk
 *
 * + Valid reference clock input selections for \b l4_sp_clk
 *   - periph_base_clk
 *   - main_clk
 *
 * + Valid reference clock input selections for \b sdmmc_clk
 *   - f2h_periph_ref_clk
 *   - main_nand_sdmmc_clk
 *   - periph_nand_sdmmc_clk
 *
 * + Valid reference clock input selections for \b nand_clk
 *   - f2h_periph_ref_clk
 *   - main_nand_sdmmc_clk
 *   - periph_nand_sdmmc_clk
 *
 * + Valid reference clock input selections for \b qspi_clk
 *   - f2h_periph_ref_clk
 *   - main_qspi_clk
 *   - periph_qspi_clk
 *
 * \endinternal
 * @{
 */
/******************************************************************************/
/*!
 * Get the input reference clock source selection value for the specified clock
 * or PLL.
 *
 * NOTE: This function returns a clock value even though \e clk may specify a
 *       clock that does not have a selectable input reference clock source. In
 *       this case, the clock value returned is the static clock source for the
 *       specified clock. For example calling alt_clk_source_get() with \e clk
 *       set to \ref ALT_CLK_MAIN_PLL will return \ref ALT_CLK_OSC1.
 *
 * \param       clk
 *              The clock or PLL to retrieve the input reference clock source
 *              selection value for.
 *
 * \returns     The clock's currently selected input reference clock source.
 */
ALT_CLK_t alt_clk_source_get(ALT_CLK_t clk);

/******************************************************************************/
/*!
 * Set the specified clock's input reference clock source selection.
 *
 * \param       clk
 *              The clock or PLL to set the input reference clock source
 *              selection for.
 *
 * \param       ref_clk
 *              The input reference clock source selection value.
 *
 * \retval      ALT_E_SUCCESS       The operation was succesful.
 * \retval      ALT_E_ERROR         The operation failed.
 * \retval      ALT_E_BAD_ARG       The \e clk argument designates a clock that
 *                                  does not have a selectable input reference
 *                                  clock source.
 * \retval      ALT_E_INV_OPTION    The \e ref_clk argument designates a clock that
 *                                  is an invalid reference clock source for the
 *                                  specified clock.
 */
ALT_STATUS_CODE alt_clk_source_set(ALT_CLK_t clk,
                                   ALT_CLK_t ref_clk);

/*! @} */

/******************************************************************************/
/*! \addtogroup CLK_MGR_FREQ Clock Frequency Control
 *
 * This API group provides access and control of the output frequency of a clock
 * or PLL.
 *
 * @{
 */

/******************************************************************************/
/*!
 * Set the external clock frequency value.
 *
 * The function is used to specify the frequency of the external clock source as
 * a measure of Hz. The supplied frequency should be within the Fmin and Fmax
 * values allowed for the external clock source.
 *
 * \param       clk
 *              The external clock source. Valid external clocks are
 *              * \e ALT_CLK_OSC1
 *              * \e ALT_CLK_OSC2
 *              * \e ALT_CLK_F2H_PERIPH_REF
 *              * \e ALT_CLK_F2H_SDRAM_REF
 *
 * \param       freq
 *              The frequency of the external clock in Hz.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   A bad argument value was passed. Either the \e clk
 *                              argument is bad or not a valid external clock
 *                              source
 * \retval      ALT_E_ARG_RANGE The frequency value violates the range constraints
 *                              for the specified clock.

 */
ALT_STATUS_CODE alt_clk_ext_clk_freq_set(ALT_CLK_t clk,
                                         alt_freq_t freq);

/******************************************************************************/
/*!
 * Get the external clock frequency value.
 *
 * This function returns the frequency of the external clock source as
 * a measure of Hz.
 *
 * \param       clk
 *              The external clock source. Valid external clocks are
 *              * \e ALT_CLK_OSC1
 *              * \e ALT_CLK_OSC2
 *              * \e ALT_CLK_F2H_PERIPH_REF
 *              * \e ALT_CLK_F2H_SDRAM_REF
 *
 * \retval      freq
 *              The frequency of the external clock in Hz.
 *
 */
alt_freq_t alt_clk_ext_clk_freq_get(ALT_CLK_t clk);

/******************************************************************************/
/*!
 * This type definition defines a structure to contain the generalized
 * configuration settings for a PLL.
 */
typedef struct ALT_CLK_PLL_CFG_s
{
    ALT_CLK_t           ref_clk;        /*!< PLL Reference Clock Source */
    uint32_t            mult;           /*!< VCO Frequency Configuration -
                                         *   Multiplier (M) value, range 1 to 4096
                                         */
    uint32_t            div;            /*!< VCO Frequency Configuration -
                                         *   Divider (N) value, range 1 to 64
                                         */
    uint32_t            cntrs[6];       /*!< Post-Scale Counters (C0 - C5) -
                                         *   range 1 to 512
                                         */
    uint32_t            pshift[6];      /*!< Phase Shift - 1/8 (45 degrees) of
                                         *   negative phase shift per increment,
                                         *   range 0 to 4096
                                         */
} ALT_CLK_PLL_CFG_t;

/******************************************************************************/
/*!
 * Get the current PLL configuration.
 *
 * \param       pll
 *              The PLL to get the configuration from.
 *
 * \param       pll_cfg
 *              [out] Pointer to an output parameter variable for the returned
 *              PLL configuration.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_clk_pll_cfg_get(ALT_CLK_t pll,
                                    ALT_CLK_PLL_CFG_t* pll_cfg);

/******************************************************************************/
/*!
 * Set the PLL configuration using the configuration parameters specified in
 * \e pll_cfg.
 *
 * \param       pll
 *              The PLL to set the configuration for.
 *
 * \param       pll_cfg
 *              Pointer to a ALT_CLK_PLL_CFG_t structure specifying the desired
 *              PLL configuration.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_clk_pll_cfg_set(ALT_CLK_t pll,
                                    const ALT_CLK_PLL_CFG_t* pll_cfg);

/******************************************************************************/
/*!
 * Get the current PLL VCO frequency configuration.
 *
 * \param       pll
 *              The PLL to get the VCO frequency configuration for.
 *
 * \param       mult
 *              [out] Pointer to an output variable for the returned
 *              configured PLL VCO multiplier (M) value.
 *
 * \param       div
 *              [out] Pointer to an output variable for the returned
 *              configured PLL VCO divider (N) value.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_clk_pll_vco_cfg_get(ALT_CLK_t pll,
                                        uint32_t* mult,
                                        uint32_t* div);

/******************************************************************************/
/*!
 * Set the PLL VCO frequency configuration using the supplied multiplier and
 * divider arguments.
 *
 * \param       pll
 *              The PLL to set the VCO frequency configuration for.
 *
 * \param       mult
 *              The PLL VCO multiplier (M). Expected argument range 1 to 4096.
 *
 * \param       div
 *              The PLL VCO divider (N). Expected argument range 1 to 64.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_clk_pll_vco_cfg_set(ALT_CLK_t pll,
                                        uint32_t mult,
                                        uint32_t div);

/******************************************************************************/
/*!
 * Get the VCO frequency of the specified PLL.
 *
 * \param       pll
 *              The PLL to retrieve the VCO frequency from.
 *
 * \param       freq
 *              [out] Pointer to the an output parameter variable to return the
 *              PLL VCO frequency value. The frequency value is returned as a
 *              measures of Hz.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   A bad argument value was passed. Either
 *                              the \e pll argument is invalid or a bad
 *                              \e freq pointer value was passed.
 */
ALT_STATUS_CODE alt_clk_pll_vco_freq_get(ALT_CLK_t pll,
                                         alt_freq_t* freq);

/******************************************************************************/
/*!
 * Get the PLL frequency guard band value.
 *
 * \param       pll
 *              The PLL from which to return the current guard band value.
 *
 * \returns     The current guard band range in effect for the PLL.
 */
uint32_t alt_clk_pll_guard_band_get(ALT_CLK_t pll);

/******************************************************************************/
/*!
 * Set the PLL frequency guard band value.
 *
 * Once a PLL has achieved lock, any changes to the PLL VCO frequency that are
 * within a specific guard band range (default value 20%) of the reference
 * period should not cause the PLL to lose lock.
 *
 * Programmatic changes to the PLL frequency within this guard band range are
 * permitted to be made without the risk of breaking lock during the transition
 * to the new frequency.
 *
 * The clk_mgr_pll_guard_band_set() function changes the guard band from its
 * current value to permit a more lenient or stringent policy to be in effect in
 * the implementation of the functions configuring PLL VCO frequency. The
 * rationale for changing the default guard band value might be to accommodate
 * unexpected environmental conditions (noise, temperature, and other
 * instability factors) that may affect the PLLs ability to maintain lock during
 * a frequency change.
 *
 * \param       pll
 *              The PLL to set the guard band value for.
 *
 * \param       guard_band
 *              The guard band value. Value should be 0 <= \e guard_band <= 100.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_ARG_RANGE The guard band value violates its range constraint.
 */
ALT_STATUS_CODE alt_clk_pll_guard_band_set(ALT_CLK_t pll,
                                           uint32_t guard_band);

/******************************************************************************/
/*!
 * Get the configured divider value for the specified clock.
 *
 * This function is used to get the configured values of both internal and
 * external clock dividers.  The internal divider (PLL counters C0-C5) values
 * are retrieved by specifying the clock name that is the divider output
 * (e.g. ALT_CLK_MPU is used to get the Main PLL C0 counter value). \n
 * It returns the actual divider value, not the encoded bitfield stored
 * in the register, due to the variety of different encodings.
 *
 * \param       clk
 *              The clock divider to get the value from.
 *
 * \param       div
 *              [out] Pointer to an output variable for the returned clock
 *              divider value.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   An invalid clock argument was specified or a
 *                              clock that does not have a divider.
 */
ALT_STATUS_CODE alt_clk_divider_get(ALT_CLK_t clk,
                                    uint32_t* div);

/******************************************************************************/
/*!
 * Set the divider value for the specified clock.
 *
 * This function is used to set the values of both internal and external clock
 * dividers.  The internal divider (PLL counters C0-C5) values are set by
 * specifying the clock name that is the divider output (e.g. ALT_CLK_MPU is
 * used to set the Main PLL C0 counter value).
 *
 * \param       clk
 *              The clock divider to set the value for.
 *
 * \param       div
 *              The clock divider value. NOTE: The valid range of clock divider
 *              values depends on the clock being configured. This is the
 *              real divisor ratio, not how the divisor is coded into the
 *              register, and is always one or greater.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   An invalid clock argument was specified or a
 *                              clock that does not have a divider.
 * \retval      ALT_E_ARG_RANGE The divider value violates the range constraints
 *                              for the clock divider.
 */
ALT_STATUS_CODE alt_clk_divider_set(ALT_CLK_t clk,
                                    uint32_t div);

/******************************************************************************/
/*!
 * Get the output frequency of the specified clock.
 *
 * \param       clk
 *              The clock to retrieve the output frequency from.
 *
 * \param       freq
 *              [out] Pointer to the an output parameter variable to return the
 *              clock output frequency value. The frequency value is returned as
 *              a measures of Hz.
 *
 * \retval      ALT_E_SUCCESS   The operation was succesful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   A bad argument value was passed. Either
 *                              the \e clk argument is invalid or a bad
 *                              \e freq pointer value was passed.
 */
ALT_STATUS_CODE alt_clk_freq_get(ALT_CLK_t clk,
                                 alt_freq_t* freq);

/*! @} */

/******************************************************************************/
/*! \addtogroup CLK_MGR_INT Clock Manager Interrupt Management
 *
 * The functions in this group provide management of interrupts originating from
 * the Clock Manager.
 *
 * The following interrupt request (IRQ) signals are sourced from the Clock
 * Manager:
 *
 * * \b clkmgr_IRQ - Clock Manager lock status interrupt output.  The PLL lock
 *                   status interrupt is the logical \e OR of six interrupt
 *                   sources defining the loss or achievement of lock status for
 *                   each PLL. The six PLL lock status conditions are:
 *                   - Main PLL Achieved Lock
 *                   - Main PLL Lost Lock
 *                   - Peripheral PLL Achieved Lock
 *                   - Peripheral PLL Lost Lock
 *                   - SDRAM PLL Achieved Lock
 *                   - SDRAM PLL Lost Lock
 *
 *                   They are enumeratated by the type \ref ALT_CLK_PLL_LOCK_STATUS_t.
 *
 *                   Each PLL lock condition may be individually disabled/enabled
 *                   as a contributor to the determination of the \b clkmgr_IRQ
 *                   assertion status.
 *
 *                   The alt_clk_lock_status_clear() function is used to clear
 *                   the PLL lock conditions causing the \b clkmgr_IRQ
 *                   assertion.
 *
 * * \b mpuwakeup_IRQ - MPU wakeup interrupt output. This interrupt notifies the
 *                      MPU to "wake up" after a transition of the Main PLL into
 *                      or out of bypass mode has been safely achieved. The need
 *                      for the "wake up" notification is because the PLL clocks
 *                      pause for a short number of clock cycles during bypass
 *                      state transition. ARM recommeds that the CPUs are placed
 *                      in standby if the clocks are ever paused.
 *
 * NOTE: \b mpuwakeup_IRQ appears to be an Altera private interrupt and may not
 *        be part of the public API although clearly it has important utility in
 *        implementing safe changes to PLL settings and transitions into and out
 *        of bypass mode.
 * @{
 */

/******************************************************************************/
/*!
 * Disable the \b clkmgr_IRQ interrupt signal source lock status condition(s).
 *
 * This function disables one or more of the lock status conditions as
 * contributors to the \b clkmgr_IRQ interrupt signal state.
 *
 * NOTE: A set bit for a PLL lock status condition in the mask value does not
 * have the effect of enabling it as a contributor to the \b clkmgr_IRQ
 * interrupt signal state. The function alt_clk_irq_enable is used to enable PLL
 * lock status source condition(s).
 *
 * \param       lock_stat_mask
 *              Specifies the PLL lock status conditions to disable as interrupt
 *              source contributors. \e lock_stat_mask is a mask of logically
 *              OR'ed ALT_CLK_PLL_LOCK_STATUS_t values that designate the PLL lock
 *              conditions to disable.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_BAD_ARG   The \e lock_stat_mask argument contains an
 *                              unknown condition value.
 */
ALT_STATUS_CODE alt_clk_irq_disable(ALT_CLK_PLL_LOCK_STATUS_t lock_stat_mask);

/******************************************************************************/
/*!
 * Enable the \b clkmgr_IRQ interrupt signal source lock status condition(s).
 *
 * This function enables one or more of the lock status conditions as
 * contributors to the \b clkmgr_IRQ interrupt signal state.
 *
 * NOTE: A cleared bit for any PLL lock status condition in the mask value does
 * not have the effect of disabling it as a contributor to the \b clkmgr_IRQ
 * interrupt signal state. The function alt_clk_irq_disable is used to disable
 * PLL lock status source condition(s).
 *
 * \param       lock_stat_mask
 *              Specifies the PLL lock status conditions to enable as interrupt
 *              source contributors. \e lock_stat_mask is a mask of logically
 *              OR'ed ALT_CLK_PLL_LOCK_STATUS_t values that designate the PLL lock
 *              conditions to enable.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_BAD_ARG   The \e lock_stat_mask argument contains an
 *                              unknown condition value.
 */
ALT_STATUS_CODE alt_clk_irq_enable(ALT_CLK_PLL_LOCK_STATUS_t lock_stat_mask);

/*! @} */

/******************************************************************************/
/*! \addtogroup CLK_MGR_GROUP_CFG Clock Group Configuration
 *
 * This API provides the ability to safely set the configuration of a clock
 * group with a single function call.
 *
 * A clock group is defined as set of clocks and signals generated from a common
 * PLL VCO. The PLL and its derived clocks are treated as a single clock
 * group. The clocks sourced directly or indirectly from the PLL may or may not
 * have these features:
 * * Clock Gates
 * * Clock Dividers
 * * Clock Source Selection Options
 *
 * The use case for application of the Clock Group Configuration functions is the
 * ability to safely configure an entire clock group from a known good clock
 * group configuration using the run-time function alt_clk_group_cfg_raw_set().
 *
 * A known good clock group configuration may be generated by one of the
 * following methods:
 *
 * * As static design information generated by an ACDS clock configuration tool
 *   and passed to embedded software for dynamic loading.
 *
 * * By calling alt_clk_group_cfg_raw_get() at run-time from an SoC FPGA that has
 *   programmatically established a known good clock group configuration using
 *   the clock manager API configuration functions.
 *
 * @{
 */

/******************************************************************************/
/*!
 * Get the raw configuration state of the designated clock group.
 *
 * This function is used to capture the configuration state of the specified
 * clock group in a private (raw) data structure.  The raw data structure may be
 * saved and used later to restore the clock group configuration using
 * alt_clk_group_cfg_raw_get().
 *
 * \param       clk_group
 *              The clock group configuration to capture.
 *
 * \param       clk_group_raw_cfg
 *              [out] A pointer to a private (raw) data structure to store the
 *              captured clock group configuration.
 *
 * \retval      ALT_E_SUCCESS   Successful status.
 * \retval      ALT_E_ERROR     Details about error status code
 */
ALT_STATUS_CODE alt_clk_group_cfg_raw_get(ALT_CLK_GRP_t clk_group,
                                          ALT_CLK_GROUP_RAW_CFG_t* clk_group_raw_cfg);

/******************************************************************************/
/*!
 * Set the clock group configuration.
 *
 * This function is used to safely set the configuration state of a clock
 * group from a raw clock group configuration specification.  The raw clock
 * group configuration specification may be a configuration previously
 * captured with alt_clk_group_cfg_raw_get() or a group clock configuration
 * generated by an external utility.
 *
 * \param       clk_group_raw_cfg
 *              A pointer to the specification to use in the configuration of
 *              the clock group.
 *
 * \retval      ALT_E_SUCCESS       Successful status.
 * \retval      ALT_E_ERROR         Details about error status code
 * \retval      ALT_E_BAD_VERSION   The clock group configuration specification is
 *                                  invalid for this device.
 */
ALT_STATUS_CODE alt_clk_group_cfg_raw_set(const ALT_CLK_GROUP_RAW_CFG_t* clk_group_raw_cfg);

ALT_STATUS_CODE alt_clk_clkmgr_init(void);

/*! @} */

/*! @} */
#ifdef __cplusplus
}

#endif  /* __cplusplus */
#endif  /* __ALT_CLK_MGR_H__ */
