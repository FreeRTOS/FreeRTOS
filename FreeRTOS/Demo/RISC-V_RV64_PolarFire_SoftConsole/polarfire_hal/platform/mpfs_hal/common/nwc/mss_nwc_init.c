/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_nwc_init.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief north west corner, calls required startup code
 *
 */

#include <string.h>
#include <stdio.h>
#include "mpfs_hal/mss_hal.h"
#include "mss_nwc_init.h"
#include "simulation.h"

#ifdef DEBUG_DDR_INIT
#include "drivers/mss/mss_mmuart/mss_uart.h"
extern mss_uart_instance_t *g_debug_uart ;
uint32_t setup_ddr_debug_port(mss_uart_instance_t * uart);
#endif

/*******************************************************************************
 * Local Defines
 */
CFG_DDR_SGMII_PHY_TypeDef       * const CFG_DDR_SGMII_PHY   =  ((CFG_DDR_SGMII_PHY_TypeDef *) CFG_DDR_SGMII_PHY_BASE);
DDR_CSR_APB_TypeDef             * const DDRCFG              = ((DDR_CSR_APB_TypeDef *)       DDRCFG_BASE);
IOSCBCFG_TypeDef                * const SCBCFG_REGS         =  (IOSCBCFG_TypeDef            *)IOSCBCFG_BASE ;
g5_mss_top_scb_regs_TypeDef     * const SCB_REGS            = (g5_mss_top_scb_regs_TypeDef *) SYSREGSCB_BASE;

/*******************************************************************************
 * Local functions
 */
void delay(uint32_t n);

/*******************************************************************************
 * extern defined functions
 */
#ifdef DEBUG_DDR_INIT
uint32_t setup_ddr_debug_port(mss_uart_instance_t * uart);
#endif

/******************************************************************************
 * Public Functions - API
 ******************************************************************************/

/**
 * MSS_DDR_init_simulation(void)
 * Flow when running through full chip simulation
 *
 * @return
 */
uint8_t mss_nwc_init(void)
{
    uint8_t error = 0U;

#ifndef SIFIVE_HIFIVE_UNLEASHED

#ifdef SIMULATION_TEST_FEEDBACK
    /*
     * set the test version- this is read in Simulation environment
     * x.y.z
     * byte[0] = z
     * byte[1] = y
     * byte[2] = x
     */
    SIM_FEEDBACK0(0x33333333);
    SYSREG->TEMP0 = (0U << 16U) | (3U << 8U) | 3U;
    SYSREG->TEMP0 = 0x44444444U;
    SIM_FEEDBACK0(1);
    SIM_FEEDBACK0(0x55555555);
    SIM_FEEDBACK0(1);
#endif
    /*
     * Assumptions:
     *  1. We enter here shortly after start-up of E51 code by  the system
     *  controller.
     *  2. We are running on the E51 and all other cores  are in wfi.
     *  3. The MSS PLL will be set to use default internal clock of 80MH
     *  4. MSS peripherals including the I/O are in the default power on state
     *
     *
     *   The following implements setting of
     *          external clock reference
     *          MSS PLL, SHMII PLL, SGMII PLL, MSS Mux's
     *          IO settings and IO MUX
     *          HSIO IO calibration options
     *          SGMII configuration
     *          DDR configuration
     *              Including SEG regs
     *          MPU setup
     *          PMP setup
     *          ABP Peripheral address setup (High/Low)
     *
     */

    /*
     * Set based on reference clock
     */
    set_RTC_divisor();

    /*
     * SCB access settings
     * Bits 15:8 Sets how long SCB request is held active after SCB bus granted.
     * Allows SCB bus master-ship to maintained across multiple SCB access
     * cycles
     * Bits 7:0 Set the timeout for an SCB access in CPU cycles.
     */
    SCBCFG_REGS->TIMER.TIMER = MSS_SCB_ACCESS_CONFIG;

    /*
     * Release APB reset & turn on dfi clock
     *
     * reserved bit 31:2
     * reset    bit 1   Asserts the APB reset to the MSS corner, is asserted at
     *                  MSS reset.
     * clock_on bit 0   Turns on the APB clock to the MSS Corner, is off at
     *                  reset. Once corner blocks is configured the firmware
     *                  may turn off the clock, but periodically should turn
     *                  back on to allow refresh of TMR registers inside
     *                  the corner block.
     *
     */
    SYSREG->DFIAPB_CR = 0x00000001U;

    /*
     * Dynamic APB enables for slaves
     * APB  dynamic enables determine if we can write to the associated APB
     * registers.
     * ACB dynamic enables determine if we can write to the associated SCB
     * registers.
     *
     * bit 31:22 Reserved
     * bit 21   DYNEN_APB_DECODER_PRESETS
     * bit 20   DYNEN_APB_BANKCNTL
     * bit 19   DYNEN_APB_IO_CALIB
     * bit 18   DYNEN_APB_CFM
     * bit 17   DYNEN_APB_PLL1
     * bit 16   DYNEN_APB_PLL0
     * bit 15:13 Reserved
     * bit 12   DYNEN_SCB_BANKCNTL
     * bit 11   DYNEN_SCB_IO_CALIB
     * bit 10   DYNEN_SCB_CFM
     * bit 9    DYNEN_SCB_PLL1
     * bit 8    DYNEN_SCB_PLL0
     * bit 7:5 Reserved
     * bit 4    Persist_DATA
     * bit 3    CLKOUT
     * bit 2    PERSIST_ADD_CMD
     * bit 1    DATA_Lockdn
     * bit 0    ADD_CMD_Lockdn
     */
    CFG_DDR_SGMII_PHY->DDRPHY_STARTUP.DDRPHY_STARTUP =\
            (0x3FU << 16U) | (0x1FU << 8U);
    /* Enable all dynamic enables
       When in dynamic enable more, this allows:
       1. writing directly using SCB
       2. setting using RPC on a soft reset
     */
    CFG_DDR_SGMII_PHY->DYN_CNTL.DYN_CNTL = (0x01U<< 10U) | (0x7FU<<0U);

    /*
     * Configure IOMUX and I/O settings for bank 2 and 4
     */
    {
#ifdef MSSIO_SUPPORT
        error |= mssio_setup();
#endif
    }

    /*************************************************************************/

    /*
     *
     *  In this step we enter Dynamic Enable mode.
     *  This is done by using the following sequence:
     *
     *  Please note all dynamic enables must be enabled.
     *  If dynamic enables are not enabled, when flash valid is asserted, value
     *  of SCB registers will be immediately written to with default values
     *  rather than the RPC values.
     *
     *  Dynamic Enable mode:
     *      Step 1:
     *          Make sure SCB dynamic enable bit is high
     *      step 2: Assert MSS core_up
     *          followed by delay
     *      step 3: Change dce[0,1,2] to 0x00
     *          followed by delay
     *      step 4: Assert flash valid
     *          followed by delay
     *      step 5: make sure all RPC registers are set to desired values
     *              (using mode and direct RPC writes to RPC)
     *      step 6: soft reset IP so SCB registers are written with RPC values.
     *          note: We will carry out step 5/6 later, once we have modified any
     *          RPC registers directly that may need tweaking or are not
     *          included in the mode write state machine, carried out in a
     *          previous step.
     *
     *          Note 1: The SCB bus can be used to update/write new values to
     *          the SCB registers through the SCB bus interface while in Dynamic
     *          enable mode
     *          Note 2: The MSS top block assertion of core_up and flash_valid
     *          have no effect in themselves if MSS custom SCB register values
     *          if the custom SCB slaves are not being reset at the same time.
     *          If the custom SCB slaves are reset whilst core_up and
     *          flash_valid are high, then the SCB registers get asynchronously
     *          loaded with the values of their corresponding RPC bits. These
     *          values remain even after negation of reset but may be
     *          subsequently overwritten by SCB writes.
     *
     *  reg MSS_LOW_POWER_CR
     *
     *      bit 12 flash_valid          Sets the value driven out on
     *                                  mss_flash_valid_out
     *      bit 11 core_up              Sets the value driven out on
     *                                  mss_core_up_out
     *      bit 10:8  dce   S           Sets the value driven out on mss_dce_out
     *                                  unless G5C asserts its overrides
     *      bit 7 lp_stop_clocks_in     Read back of lp_stop_clocks input
     *      bit 6 lp_stop_clocks_out    Direct control of MSS Corner LP state
     *                                  control
     *      bit 5 p_pll_locked          Direct control of MSS Corner
     *                                  LP state control
     *      bit 4 lp_state_bypass       Direct control of MSS Corner LP
     *                                  state control
     *      bit 3 lp_state_persist
     *      bit 2 lp_state_op
     *      bit 1 lp_state_ip
     *      bit 0 lp_state_mss
     *
     *      In order to re-flash/update the APB RPC register values into the
     *      registers of a specific SCB slave,the following sequence must be
     *      followed:
     *      1)  Embedded software running on E51 must force the mss_core_up and
     *          mss_flash valid must be high
     *      2)  Then do a soft reset of the specific SCB slave that will be
     *          re-flashed/updated.
     *
     *      The APB RPC registers are used in the following ways to configure
     *      the MSS periphery
     *      1)  Load values to SCB registers.
     *          core_up" and "flash_valid" determines if the SCB registers get
     *          either:
     *               a.  Reset to their hardware default
     *                   (when core_up/flash_valis low)
     *              b.  Loaded with the APB RPC register.
     *                   (when core_up/flash_valid high)
     *      2)  IO configuration settings
     *          These are fed directly to the static configuration of IOA cells
     *          within the IOG lanes of the DDR and SGMII PHYs, as long as
     *          "core_up" and "flash_valid" are high.
     *          a.  To avoid unwanted/intermediate states on IOs, the "core_up"
     *          and "flash_valid" should be initially 0 on MSS reset. This will
     *          select the safe hardware defaults. The RPC registers are written
     *          in the background and then simultaneously "flashed" as the new
     *          IO configuration by assertion of "core_up" and "flash_valid"
     *          being asserted.
     *      3)  Training IP settings
     *          These allow the direct control of the training IP via the APB
     *          registers.
     *
     *      Notes:
     *      1)  When the MSS is reset, the SCB slaves won't take on the RPC
     *      values. They will be reset to their hardware default values.
     *
     *      2)  Although RPC registers are writable in APB space,
     *      they only take effect on the SCB registers whenever there is a
     *      "virtual re-flash" operation, which involves performing
     *      a soft reset of an SCB slave (i.e. writing to the NV_MAP register
     *      bit in the SOFT_RESET register in the SCB slave).
     *      This mechanism would only be used if a full new configuration is to
     *      be applied to the full SCB slave and wouldn't be used, for example
     *      to change just a clock mux configuration.
     *
     *      3)  To make configuration changes to individual registers, without
     *      "re-flashing" all registers in an MSS custom SCB slave, it is
     *      necessary to write directly to the SCB registers (via SCB space) in
     *      that slave, rather than writing RPC registers via APB space
     *
     */

    /*
       lp_state_mss         :1;
       lp_state_ip_mss      :1;
       lp_state_op_mss      :1;
       lp_state_persist_mss :1;
       lp_state_bypass_mss  :1;
       lp_pll_locked_mss    :1;
       lp_stop_clocks_out_mss :1;
       lp_stop_clocks_in_mss :1;
       mss_dce              :3;
       mss_core_up          :1;
       mss_flash_valid      :1;
       mss_io_en            :1;
    */
     /* DCE:111, CORE_UP:1, FLASH_VALID:0, mss_io_en:0 */
    SCB_REGS->MSSIO_CONTROL_CR.MSSIO_CONTROL_CR =\
            (0x07U<<8U)|(0x01U<<11U)|(0x00U<<12U)|(0x00U<<13U);
    delay((uint32_t) 10U);
    /* DCE:000, CORE_UP:1, FLASH_VALID:0, mss_io_en:0 */
    SCB_REGS->MSSIO_CONTROL_CR.MSSIO_CONTROL_CR =\
            (0x00U<<8U)|(0x01U<<11U)|(0x00U<<12U)|(0x00U<<13U);
    delay((uint32_t) 10U);
    /* DCE:000, CORE_UP:1, FLASH_VALID:1, mss_io_en:0 */
    SCB_REGS->MSSIO_CONTROL_CR.MSSIO_CONTROL_CR =\
            (0x00U<<8U)|(0x01U<<11U)|(0x01U<<12U)|(0x00U<<13U);
    delay((uint32_t) 10U);
    /* DCE:000, CORE_UP:1, FLASH_VALID:1, mss_io_en:1  */
    SCB_REGS->MSSIO_CONTROL_CR.MSSIO_CONTROL_CR =\
            (0x00U<<8U)|(0x01U<<11U)|(0x01U<<12U)|(0x01U<<13U);

    /*
     * Setup SGMII
     * The SGMII set-upset configures the external clock reference so this must
     * be called before configuring the MSS PLL
     */
    SIM_FEEDBACK0(2);
    sgmii_setup();

    /*
     * Setup the MSS PLL
     */
    SIM_FEEDBACK0(3);
    mss_pll_config();

    {
#ifdef DDR_SUPPORT
#ifdef DEBUG_DDR_INIT
        {
            (void)setup_ddr_debug_port(g_debug_uart);
        }
#endif

        uint32_t  ddr_status;
        ddr_status = ddr_state_machine(DDR_SS__INIT);

        while((ddr_status & DDR_SETUP_DONE) != DDR_SETUP_DONE)
        {
            ddr_status = ddr_state_machine(DDR_SS_MONITOR);
        }
        if ((ddr_status & DDR_SETUP_FAIL) == DDR_SETUP_FAIL)
        {
            error |= (0x1U << 2U);
        }
        //todo: remove, just for sim test ddr_recalib_io_test();
#endif
    }

#endif /* end of !define SIFIVE_HIFIVE_UNLEASHED */
    SIM_FEEDBACK0(0x12345678U);
    SIM_FEEDBACK0(error);
    SIM_FEEDBACK0(0x87654321U);
    return error;
}


/*-------------------------------------------------------------------------*//**
 * delay()
 * Not absolute. Dependency on current clk rate
 * @param n Number of iterations to wait.
 */
void delay(uint32_t n)
{
    volatile uint32_t count = n;
    while(count!=0U)
    {
        count--;
    }
}

/*-------------------------------------------------------------------------*//**
 * mtime_delay()
 * waits x microseconds
 * Assumption 1 is we have ensured clock is 1MHz
 * Assumption 2 is we have not setup tick timer when using this function. It is
 * only used by the startup code
 * @param microseconds microseconds to delay
 */

void mtime_delay(uint32_t microseconds)
{
    CLINT->MTIME = 0ULL;
    volatile uint32_t count = 0ULL;

    while(CLINT->MTIME < microseconds)
    {
        count++;
    }
    return;
}
