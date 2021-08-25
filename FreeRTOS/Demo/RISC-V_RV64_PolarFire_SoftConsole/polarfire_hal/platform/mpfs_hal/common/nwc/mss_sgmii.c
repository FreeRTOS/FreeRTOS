/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_sgmii.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief sgmii related functions
 *
 */

#include <string.h>
#include <stdio.h>
#include "mpfs_hal/mss_hal.h"
#include "simulation.h"

#ifdef  MPFS_HAL_HW_CONFIG

static PART_TYPE silicon_variant = PART_NOT_DETERMINED;

/*
 * local functions
 */
static void setup_sgmii_rpc_per_config(void);
#ifdef SGMII_SUPPORT
static uint32_t sgmii_channel_setup(void);
#endif

/*
 * local variable
 */
static uint32_t sro_dll_90_code;

/*
 * local functions
 */
static void set_early_late_thresholds(uint8_t n_late_threshold, uint8_t p_early_threshold);

/*
 * extern functions
 */
extern void sgmii_mux_config(uint8_t option);


uint32_t sgmii_setup(void)
{
#ifdef SGMII_SUPPORT
    /*
     * Check if any tx/Rx channels enabled
     */
    if((LIBERO_SETTING_SGMII_MODE & (TX_RX_CH_EN_MASK<<TX_RX_CH_EN_OFFSET)) != 0U)
    {
        while (sgmii_channel_setup() != 0)
        {

        }
    }
    else
    {
        sgmii_off_mode();
        sgmii_mux_config(RPC_REG_UPDATE);
    }
#else
    {
        sgmii_off_mode();
        sgmii_mux_config(RPC_REG_UPDATE);
    }
#endif
    return(0UL);
}


/**
 *
 * @param sgmii_instruction
 * @return
 */
#ifdef SGMII_SUPPORT
static uint32_t sgmii_channel_setup(void)
{
    static SGMII_TRAINING_SM sgmii_training_state = SGMII_SETUP_INIT;
    static uint32_t status = SGMII_IN_SETUP;
    static uint32_t timer_out;

    /*
     * Initialise NWC
     *      Clocks
     *      SGMII
     *      DDR
     *      IOMUX
     */

    switch(sgmii_training_state)
    {
        case SGMII_SETUP_INIT:
            status = SGMII_IN_SETUP;
            CFG_DDR_SGMII_PHY->SOFT_RESET_SGMII.SOFT_RESET_SGMII = \
                    (0x01 << 8U) | 1U; /* PERIPH   soft reset */
            CFG_DDR_SGMII_PHY->SOFT_RESET_SGMII.SOFT_RESET_SGMII = 1U;
            setup_sgmii_rpc_per_config();         /* load RPC SGMII_MODE register ext */

            /* Enable the Bank controller */
            /*
             * Set soft reset on IP to load RPC to SCB regs (dynamic mode)
             * Bring the sgmii bank controller out of reset =- ioscb_bank_ctrl_sgmii
             */
            IOSCB_BANK_CNTL_SGMII->soft_reset = 1U;  /* DPC_BITS NV_MAP  reset */
            sgmii_training_state = SGMII_IO_EN;
            break;

        case SGMII_IO_EN:
            /*
             * Check the IO_EN signal here.
             * This is an output from the bank controller power detector, which are
             * turned on using MSS_IO_EN
             */
            /* aro_ioen_bnk  - PVT calibrator IOEN  */
            timer_out++;
            if((CFG_DDR_SGMII_PHY->PVT_STAT.PVT_STAT & (0x01U<<6U)) != 0U)
            {
                timer_out=0U;
                sgmii_training_state = SGMII_RAMP_TIMER;
            }
            break;

        case SGMII_RAMP_TIMER:
            /*
             * IO power ramp wait time
             * After IOEN is received from power detectors DDR and SGMii, extra time
             * required for voltage to ramp.
             * This time will come from the user- Dependent on ramp time of power
             * supply
             * Approximately - Bank power timer (from ioen_in to ioen_out = 10uS)?
             *
             */
            timer_out++;
            if(timer_out >= 0xFU)
            {
                timer_out=0U;
                sgmii_training_state = SGMII_IO_SETUP;
            }
            break;

        case SGMII_IO_SETUP:
            /*
             * fixme- not sure if we should be setting this register
             * From regmap detail:
             * bit 8 of MSS_RESET_CR
             * Asserts a reset the SGMII block containing the MSS reference clock
             * input.
             * Warning that setting this bit causes the external reference clock
             * input to the
             * MSS PLL to disappear.
             * It is advisable to use the SGMII channel soft resets in the PHY
             * instead of this bit.
             * However if E51 software wants to set this bit, the MSS clock source
             * should be switched over to the standby source in advance.
             */
            SCB_REGS->MSS_RESET_CR.MSS_RESET_CR = 0;

            /*
             * I ran the sim past the place where we set the nvmap_reset in the
             * SOFT_RESET_SGMII register and it did not result in any
             * change from the DLL default bits.
             * But I traced the 'flashing' signal on one of these regs back to
             * 'dll0_soft_reset_nv_map' (not 'pll0_soft_reset_periph').
             * Now the only place I can find 'dll0_soft_reset_nv_map' is in SCB
             * space...ie 0x3e10_0000 SOFT_RESET register.
             *
             */
            /*
             * so we have to use scb register to reset as no APB register available
             * to soft reset the IP
             * ioscb_dll_sgmii
             * */
            IOSCB_DLL_SGMII->soft_reset = (0x01U << 0x00U);  /*  reset sgmii DLL */

            /*
              * I have discovered the problem with the tx channels (soft reset issue)
              * So we require the:
              *
              * sgmiiphy_lane 01 soft-reset register (0x3650_0000) to be written to
              * with 0x1 (to set the nv_map bit[0] =1 (self clears))
              * same for sgmiiphy_lane 23 soft-reset register (0x3651_0000).
              *
              * This will result in the rpc bits for the Lane controls to get loaded.
              * Not happening currently.
              *
              * The soft_reset_sgmii occurs in the mss_ddr.c line 436, so I suppose
              * we put the 2 new soft reset writes after that.
              *
              */
            {
                /* sgmiiphy_lane 01 soft-reset register (0x3650_0000) */
                SGMIIPHY_LANE01->soft_reset = 0x000000001U;
                /* sgmiiphy_lane 23 soft-reset register (0x3650_0000) */
                SGMIIPHY_LANE23->soft_reset = 0x000000001U;
            }

            /*
             * Kick-off calibration, by taking calibration IP out of reset
             */
            /*
             * Soft reset
             */
            {
                /* PVT soft reset - APB*/
                /* reg_pvt_soft_reset_periph  */
                CFG_DDR_SGMII_PHY->DYN_CNTL.DYN_CNTL        = (0x01U<< 10U) | (0x7FU<<0U);
                /* reg_pvt_soft_reset_periph  */
                CFG_DDR_SGMII_PHY->DYN_CNTL.DYN_CNTL        = (0x7FU<<0U);
                /* PVT soft reset - SCB */
                /* make sure out of reset */
                IOSCB_IO_CALIB_SGMII->SOFT_RESET_IOCALIB    = 0x1U;
                /* make sure out of reset */
                IOSCB_IO_CALIB_SGMII->SOFT_RESET_IOCALIB    = 0x0U;
            }
            sgmii_training_state = SGMII_WAIT_FOR_CALIB_COMPLETE;
            break;

        case SGMII_WAIT_FOR_CALIB_COMPLETE:
            /*
             * Verify calibration
             * Bank 5 PVT calibrator can be controlled by MSS firmware through APB
             * registers to do initial calibration and re-calibration. During startup,
             * the initial calibration can be started by default when MSS releases SGMII
             * reset. Re-calibration is enabled by default with reg_pvt_calib_start/lock
             * bits being set to 1 before startup, and MSS firmware can start
             * re-calibration after startup by toggling  pvt_calib_start/lock bits per
             * PVT calibrator spec.
             *
             */
            if((CFG_DDR_SGMII_PHY->PVT_STAT.PVT_STAT & (1U << 14U)) == (1U << 14U))
            {
                sgmii_training_state = SGMII_ASSERT_CALIB_LOCK;
            }
            break;

        case SGMII_ASSERT_CALIB_LOCK:
            /*
             * now assert calib lock
             *    calibrated pcode and ncode will be written.
             * */

            CFG_DDR_SGMII_PHY->PVT_STAT.PVT_STAT |= 0x40000000UL;
            IOSCB_IO_CALIB_SGMII->IOC_REG0       |= (0x01U<<14U);
            sgmii_training_state = SGMII_SET_UP_PLL;
            break;

        case SGMII_SET_UP_PLL:
            /*
              * SGMii Step 3)   Wait for PLL and DLL lock
              * Delay codes generated
              */

            /* 0U => configure using scb, 1U => NVMAP reset */
            sgmii_mux_config(RPC_REG_UPDATE);
            /* 0U => configure using scb, 1U => NVMAP reset */
            sgmii_pll_config_scb(RPC_REG_UPDATE);

            timer_out=0U;
            sgmii_training_state = SGMII_WAIT_FOR_MSS_LOCK;
            break;

        case SGMII_WAIT_FOR_MSS_LOCK:
            if (CFG_DDR_SGMII_PHY->PLL_CNTL.PLL_CNTL & (1U<<7U))
            {
                sgmii_training_state = SGMII_WAIT_FOR_DLL_LOCK;
            }
            break;

        case SGMII_WAIT_FOR_DLL_LOCK:
            if (CFG_DDR_SGMII_PHY->RECAL_CNTL.RECAL_CNTL & (1U<<23U))
            {
                sgmii_training_state = SGMII_TURN_ON_MACS;
            }
            break;

        case SGMII_TURN_ON_MACS:
            /*
             * Provide mac clocks
             * The nw_config register for mac0 (0x2011_0004): I am forcing 'gigabit' and
             * 'tbi' bits = 11.
             * The same for Mac1.
             * This starts up the tx_mac_clocks for the 2 macs.
             *
             */
            /* the mac clocks need to be turned on when setting up the sgmii */
            (void)mss_config_clk_rst(MSS_PERIPH_MAC0, (uint8_t) MPFS_HAL_FIRST_HART, PERIPHERAL_ON);
            (void)mss_config_clk_rst(MSS_PERIPH_MAC0, (uint8_t) MPFS_HAL_FIRST_HART, PERIPHERAL_ON);
            GEM_A_LO->network_config |= (0x01U << 10U) | (0x01U << 11U);   /* GEM0 */
            GEM_B_LO->network_config |= (0x01U << 10U) | (0x01U << 11U);   /* GEM1 */
            sgmii_training_state = SGMII_DETERMINE_SILICON_VARIANT;
            break;

        case SGMII_DETERMINE_SILICON_VARIANT:
            /*
             * Determine Silicon variant from generated dll generated sro_dll_90_code
             */
            sro_dll_90_code = ((CFG_DDR_SGMII_PHY->RECAL_CNTL.RECAL_CNTL >> 16U) & 0x7FU);

            if(CFG_DDR_SGMII_PHY->SPARE_STAT.SPARE_STAT & (01U<<31U)) /* bit31 == 1 => post rev B silicon */
            {
                silicon_variant = PART_REVC_OR_LATER;
                set_early_late_thresholds(LATE_EYE_WIDTH_PART_REVC_OR_LATER_PRE_TEST, EARLY_EYE_WIDTH_PART_REVC_OR_LATER_PRE_TEST);
            }
            else
            {
                /*
                 * SS  part expect  < 13
                 * typical-typical  or FF expect  > 13
                 */
                if(sro_dll_90_code < MIN_DLL_90_CODE_VALUE_INDICATING_TT_PART_REVB) /* SS part */
                {
                    silicon_variant = SS_PART_REVB;
                    set_early_late_thresholds(LATE_EYE_WIDTH_SS_PART_REVB, EARLY_EYE_WIDTH_SS_PART_REVB);
                }
                else
                {
                    silicon_variant = TT_PART_REVB;
                    set_early_late_thresholds(LATE_TT_PART_REVB, EARLY_TT_PART_REVB);
                }
            }
            sgmii_training_state = SGMII_RESET_CHANNELS;
            break;

        case SGMII_RESET_CHANNELS:
            /*
             * DLL soft reset                   - Already configured
             * PVT soft reset                   - Already configured
             * Bank controller soft reset       - Already configured
             * CLKMUX soft reset                - Already configured
             * Lane0 soft reset                 - must be soft reset here
             * Lane1 soft reset                 - must be soft reset here
             *
             *      __IO  uint32_t               reg_lane0_soft_reset_periph :1;  bit 13
             *      __IO  uint32_t               reg_lane1_soft_reset_periph :1;  bit 14
             */
            CFG_DDR_SGMII_PHY->DYN_CNTL.DYN_CNTL  = (1U << 14U)|(1U << 13U)|(0x7FU<<0U);
            CFG_DDR_SGMII_PHY->DYN_CNTL.DYN_CNTL  = (0U << 14U)|(0U << 13U)|(0x7FU<<0U);
            if(silicon_variant == PART_REVC_OR_LATER)
            {
                timer_out=0U;
                sgmii_training_state = SGMII_WAIT_10MS;
            }
            else
            {
                sgmii_training_state = SGMII_CHANNELS_UP;
            }
            break;

        case SGMII_WAIT_10MS:
            timer_out++;
            if(timer_out >= 0xFFFU)
            {
                timer_out=0U;
                sgmii_training_state = SGMII_CHECK_REVC_RESULT;
            }
            break;

        case SGMII_CHECK_REVC_RESULT:
            if ( (CFG_DDR_SGMII_PHY->SPARE_STAT.SPARE_STAT & ARO_REF_PCODE_MASK) > ARO_REF_PCODE_REVC_THRESHOLD )
            {
                /* OK, we are good */
                sgmii_training_state = SGMII_CHANNELS_UP;
            }
            else
            {
                /* need to adjust eye values */
                set_early_late_thresholds(LATE_EYE_WIDTH_PART_REVC_OR_LATER, EARLY_EYE_WIDTH_PART_REVC_OR_LATER);
                /*
                 * Now reset the channels
                 */
                CFG_DDR_SGMII_PHY->DYN_CNTL.DYN_CNTL  = (1U << 14U)|(1U << 13U)|(0x7FU<<0U);
                CFG_DDR_SGMII_PHY->DYN_CNTL.DYN_CNTL  = (0U << 14U)|(0U << 13U)|(0x7FU<<0U);
                /* OK, we are good */
                sgmii_training_state = SGMII_CHANNELS_UP;
            }
            break;

        case SGMII_CHANNELS_UP:
            /*
             * SGMii Step 4)    Monitor the DLL codes for Voltage and Temp variation
             * MSS E51 software sets the magnitude value of variation to flag.
             * MSS E51 software can poll this flag.
             * Re-calibration, if needed, is controlled by E51 software if needed.
             * ML step 4- This is a monitoring step- to be run constantly in the back
             * ground
             */
            status = SGMII_FINISHED_SETUP;
            break;
    } /* end of switch statement */

    return(status);
}
#endif

/**
 * setup_sgmii_rpc_per_config
 * Configures SGMII RPC TIP registers
 */
static void setup_sgmii_rpc_per_config(void)
{
    CFG_DDR_SGMII_PHY->SGMII_MODE.SGMII_MODE    = (LIBERO_SETTING_SGMII_MODE & ~REG_CDR_MOVE_STEP);
    CFG_DDR_SGMII_PHY->CH0_CNTL.CH0_CNTL        = LIBERO_SETTING_CH0_CNTL;
    CFG_DDR_SGMII_PHY->CH1_CNTL.CH1_CNTL        = LIBERO_SETTING_CH1_CNTL;
    CFG_DDR_SGMII_PHY->RECAL_CNTL.RECAL_CNTL    = LIBERO_SETTING_RECAL_CNTL;
    CFG_DDR_SGMII_PHY->CLK_CNTL.CLK_CNTL        = LIBERO_SETTING_CLK_CNTL;
    /* ibuffmx_p and _n rx1, bit 22 and 23 , rx0, bit 20 and 21 */
    CFG_DDR_SGMII_PHY->SPARE_CNTL.SPARE_CNTL    = LIBERO_SETTING_SPARE_CNTL;
    CFG_DDR_SGMII_PHY->PLL_CNTL.PLL_CNTL        = LIBERO_SETTING_PLL_CNTL;
}

/**
 * SGMII Off mode
 */
void sgmii_off_mode(void)
{
    /*
     * do soft reset of SGMII TIP
     */
    CFG_DDR_SGMII_PHY->SOFT_RESET_SGMII.SOFT_RESET_SGMII = (0x01 << 8U) | 1U;
    CFG_DDR_SGMII_PHY->SOFT_RESET_SGMII.SOFT_RESET_SGMII = 1U;

    /*
     *
     */
    setup_sgmii_rpc_per_config();

    /*
     * Resetting the SCB register only required in already in dynamic mode. If
     * not reset, IO will not be configured.
     */
    IOSCB_DLL_SGMII->soft_reset = (0x01U << 0x00U);         /*  reset sgmii */

}

/**
 *
 */
void ddr_pvt_calibration(void)
{
    /*
     * R3.1
     * PVT calibration
     * Wait for IOEN from power detectors DDR and SGMII - IO enable signal from
     * System Control powers on
     *
     * From DDR phy SAC spec:
     *      MSS processor releases dce bus to send RPC bits to IO buffer,
     *      setting each to it's programmed mode and then asserts
     *      ioen high at end of this state.
     *
     *
     *      Following verification required for MSS IO Calibration (DDRPHY,
     *      SGMII and MSSIO)
     *          Auto-calibration supply ramp time settings
     *          Calibration in reset until ioen_bnk goes high, timer complete
     *          and setup of bits complete
     *              scbclk divider setting (/1)
     *              calibration clkdiv setting
     *              VS bit settings
     *          Initial non-calibrated codes to IOs (functional max codes)
     *          Calibration signal transitions
     *              pvt_calib_status ,        r in reg     DYN_CNTL
     *              reg_calib_reset,        w/r in reg     IOC_REG6
     *              calib_clkdiv,           w/r in reg     IOC_REG6
     *              soft_reset_periph_b,
     *              calib_lock,             w/r in reg     IOC_REG0
     *              calib_start,            w/r in reg     IOC_REG0
     *              calib_intrpt              r in reg
     *          Final calibration codes
     *          Lane latching of codes
     *          IO Glitching
     */
    volatile uint32_t timer_out=0U;

    #ifndef RENODE_DEBUG
    /* sro_ioen_out  */
    while((CFG_DDR_SGMII_PHY->IOC_REG1.IOC_REG1 & (1U<<4U)) == 0U)
    {
        timer_out++;
        /*todo: add a fail break */
    }
    #endif

    /*
     * R3.2  Trigger timer and wait for completion
     * PVT calibration
     * After IOEN is received from power detectors DDR and SGMII, extra time
     * required for voltage to ramp.
     * This time will come from the user- Dependent on ramp time of power supply
     * Approximately - Bank power timer (from ioen_in to ioen_out = 10uS)?
     *
     */
    /*todo: implement proper timer- user will supply ramp time */
    timer_out=0U;
    while(timer_out < 0xFU)
    {
        timer_out++;
    }

    /*
     * R3.2 Initiate calibration:
     *
     * IOC_REG6
     *  bit 2:1 reg_calib_clkdiv
     *  bit 0  reg_calib_reset
     *
     *      DDRIO:  calib_reset: 1 -> 0
     *      mss_write(0x20007000 + 0x21C,0x00000004);
     *      DDRIO: calib_rst_b: 0 -> 1
     *      mss_write(0x20007000 + 0x220,0x00000000);
     *      SGMII: calib_rst_b: 0 -> 1
     *      mss_write(0x20007000 + 0xC1C,0x00000000);
     *
     */
    /*
     * Soft reset
     */
    /* PVT soft reset - APB*/
    /* DDRIO:  calib_reset: 1 -> 0, clk divider changed - from 2 - to 3 */
    CFG_DDR_SGMII_PHY->IOC_REG6.IOC_REG6               =    0x00000006U;

    /* PVT soft nv reset - SCB, should load from RPC */
    IOSCB_IO_CALIB_DDR->SOFT_RESET_IOCALIB       = 0x1U; /* make sure reset */
    IOSCB_IO_CALIB_DDR->SOFT_RESET_IOCALIB       = 0x0U; /* make sure reset */

    /*
     * R3.4 Wait for PVT calibration to complete
     * Check:
     * bit 2 sro_calib_status
     *
     * The G5 Memory controller needs to see that the IO calibration has
     * completed before kicking off DDR training.
     * It uses the calib_status signal as a flag for this.
     */
    timer_out=0U;
    #ifndef RENODE_DEBUG
    {
        /* PVT I/O - sro_calib_status -  wait for calibration to complete */
        while((IOSCB_IO_CALIB_DDR->IOC_REG1 & 0x00000004U) == 0U)
        {
            timer_out++;
        }
        /* PVT I/O - sro_calib_status -  wait for calibration to complete */
        while((CFG_DDR_SGMII_PHY->IOC_REG1.IOC_REG1 & 0x00000004U) == 0U)
        {
            timer_out++;
        }
    }
    #endif
    /*
     * now assert calib lock
     *
     * */
    {
        CFG_DDR_SGMII_PHY->IOC_REG0.IOC_REG0    &= ~(0x01U<<14U);
        IOSCB_IO_CALIB_DDR->IOC_REG0            &= ~(0x01U<<14U);
        CFG_DDR_SGMII_PHY->IOC_REG0.IOC_REG0    |= (0x01U<<14U);
        IOSCB_IO_CALIB_DDR->IOC_REG0            |= (0x01U<<14U);
    }
}


/**
 *
 */
void ddr_pvt_recalibration(void)
{
    volatile uint32_t timer_out=0U;

    /*
     * now assert calib start
     *
     * */
    {
        CFG_DDR_SGMII_PHY->IOC_REG0.IOC_REG0    &= ~(0x01U<<13U);
        IOSCB_IO_CALIB_DDR->IOC_REG0            &= ~(0x01U<<13U);
        CFG_DDR_SGMII_PHY->IOC_REG0.IOC_REG0    |= (0x01U<<13U);
        IOSCB_IO_CALIB_DDR->IOC_REG0            |= (0x01U<<13U);
    }

    /*
     * R3.4 Wait for PVT calibration to complete
     * Check:
     * bit 2 sro_calib_status
     *
     * The G5 Memory controller needs to see that the IO calibration has
     * completed before kicking off DDR training.
     * It uses the calib_status signal as a flag for this.
     */
    timer_out=0U;
    #ifndef RENODE_DEBUG
    {
        /* PVT I/O - sro_calib_status -  wait for calibration to complete */
        while((IOSCB_IO_CALIB_DDR->IOC_REG1 & 0x00000004U) == 0U)
        {
            timer_out++;
        }
        /* PVT I/O - sro_calib_status -  wait for calibration to complete */
        while((CFG_DDR_SGMII_PHY->IOC_REG1.IOC_REG1 & 0x00000004U) == 0U)
        {
            timer_out++;
        }
    }
    #endif
    /*
     * now assert calib lock
     *
     * */
    {
#if 0   /*
         * fixme: this appears to cause wite calibration to fail, investigating
         */
        CFG_DDR_SGMII_PHY->IOC_REG0.IOC_REG0    &= ~(0x01U<<14U);
        IOSCB_IO_CALIB_DDR->IOC_REG0            &= ~(0x01U<<14U);
        CFG_DDR_SGMII_PHY->IOC_REG0.IOC_REG0    |= (0x01U<<14U);
        IOSCB_IO_CALIB_DDR->IOC_REG0            |= (0x01U<<14U);
#endif
    }
}

/**
 * Set eye thresholds
 * @param n_late_threshold
 * @param p_early_threshold
 */
static void set_early_late_thresholds(uint8_t n_late_threshold, uint8_t p_early_threshold)
{
    uint32_t n_eye_values;
    uint32_t p_eye_value;

    /*
     * Set the N eye width value
     * bits 31:29 for CH1, bits 28:26  for CH0 in spare control (N eye width value)
     */
    n_eye_values = (n_late_threshold << SHIFT_TO_CH0_N_EYE_VALUE);
    n_eye_values |= (n_late_threshold << SHIFT_TO_CH1_N_EYE_VALUE);

    CFG_DDR_SGMII_PHY->SPARE_CNTL.SPARE_CNTL    = (LIBERO_SETTING_SPARE_CNTL & N_EYE_MASK) | n_eye_values;

    /*
     * Set P values
     */
    p_eye_value = (p_early_threshold << SHIFT_TO_REG_RX0_EYEWIDTH);
    CFG_DDR_SGMII_PHY->CH0_CNTL.CH0_CNTL        = ((LIBERO_SETTING_CH0_CNTL & REG_RX0_EYEWIDTH_P_MASK) | p_eye_value) | REG_RX0_EN_FLAG_N;
    CFG_DDR_SGMII_PHY->CH1_CNTL.CH1_CNTL        = ((LIBERO_SETTING_CH1_CNTL & REG_RX0_EYEWIDTH_P_MASK) | p_eye_value) | REG_RX1_EN_FLAG_N;

}

#endif
