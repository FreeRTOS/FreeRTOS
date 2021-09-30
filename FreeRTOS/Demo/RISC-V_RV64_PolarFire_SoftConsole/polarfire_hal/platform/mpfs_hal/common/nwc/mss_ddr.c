/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_ddr.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief DDR related code
 *
 */
#include <string.h>
#include <stdio.h>
#include "mpfs_hal/mss_hal.h"
#ifdef DDR_SUPPORT
#include "mss_ddr_debug.h"
#include "simulation.h"
#ifdef FABRIC_NOISE_TEST
#include "drivers/mss_gpio/mss_gpio.h"
#endif

/*******************************************************************************
 * Local Defines
 */
/* This string is updated if any change to ddr driver */
#define DDR_DRIVER_VERSION_STRING   "0.2.003"
/* Version     |  Comment                                                     */
/* 0.2.003     |  Updated SEG setup to match Libero 12.7, Removed warnings,   */
/*             |  shortened timeout in mtc_test                               */
/* 0.2.002     |  MTC_test() update -added more tests                         */
/* 0.2.001     |  Reverted ADDCMD training command                            */
/* 0.2.000     |  RPC166 now does short retrain by default                    */
/* 0.1.009     |  Removed AXI overrides. Agreed better placed in              */
/*             |  mss_sw_config.h util until corrected in configurator v3.0   */
/* 0.1.008     |  Added manual addcmd traing for all variants                 */
/* 0.1.007     |  Added some updates from SVG and DCT. Also overrides AXI     */
/*             |  ranges if incorrectly set (Liber0 v12.5 and Liber0 v12.6    */
/* 0.1.006     |  Added tuning for rpc166, read lane FIFO alignement          */
/* 0.1.005     |  Added parameter to modify rpc166, lane out of sync on read  */
/* 0.1.004     |  Corrected default RPC220 setting so dq/dqs window centred   */
/* 0.1.003     |  refclk_phase correctly masked during bclk sclk sw training  */
/* 0.1.002     |  Reset modified- corrects softreset on retry issue  (1.8.x)  */
/* 0.1.001     |  Reset modified- corrects softreset on retry issue  (1.7.2)  */
/* 0.0.016     |  Added #define DDR_FULL_32BIT_NC_CHECK_EN to mss_ddr.h       */
/* 0.0.016     |  updated mss_ddr_debug.c with additio of 32-bit write test   */
/* 0.0.015     |  DDR3L - Use Software Bclk Sclk training                     */
/* 0.0.014     |  DDR3 and DDR update to sync with SVG proven golden version  */
/* 0.0.013     |  Added code to turn off DM if DDR4 and using ECC             */
/* 0.0.012     |  Added support for turning off unused I/O from Libero        */

/*
 * Calibration data records calculated write calibration values during training
 */
mss_ddr_calibration calib_data;

/* rx lane FIFO used for tuning  */
#if (TUNE_RPC_166_VALUE == 1)
static uint32_t rpc_166_fifo_offset;
#endif

/*
 * This string is used as a quick sanity check of write/read to DDR.
 * The memory test core is used for more comprehensive testing during and
 * post calibration
 */
#ifdef DDR_SANITY_CHECKS_EN
static const uint32_t test_string[] = {
        0x12345678,23211234,0x35675678,0x4456789,0x56789123,0x65432198,\
        0x45673214,0xABCD1234,0x99999999,0xaaaaaaaa,0xbbbbbbbb,0xcccccccc,\
        0xdddddddd,0xeeeeeeee,0x12121212,0x12345678};
#endif

/*******************************************************************************
 * external functions
 */
#ifdef DEBUG_DDR_INIT
extern mss_uart_instance_t *g_debug_uart;
extern uint32_t tip_register_status (mss_uart_instance_t *g_mss_uart_debug_pt);
#endif

/* Use to record instance of errors during calibration */
static uint32_t ddr_error_count;
#ifdef SWEEP_ENABLED
uint8_t sweep_results[MAX_NUMBER_DPC_VS_GEN_SWEEPS]\
                     [MAX_NUMBER_DPC_H_GEN_SWEEPS]\
                     [MAX_NUMBER_DPC_V_GEN_SWEEPS]\
                     [MAX_NUMBER__BCLK_SCLK_OFFSET_SWEEPS]\
                     [MAX_NUMBER_ADDR_CMD_OFFSET_SWEEPS];
#define TOTAL_SWEEPS (MAX_NUMBER_DPC_H_GEN_SWEEPS*MAX_NUMBER_DPC_H_GEN_SWEEPS*\
        MAX_NUMBER_DPC_V_GEN_SWEEPS*MAX_NUMBER__BCLK_SCLK_OFFSET_SWEEPS*\
        MAX_NUMBER_ADDR_CMD_OFFSET_SWEEPS)
#endif

/*******************************************************************************
 * Local function declarations
 */
static uint32_t ddr_setup(void);
static void init_ddrc(void);
static uint8_t write_calibration_using_mtc(uint8_t num_of_lanes_to_calibrate);
/*static uint8_t mode_register_write(uint32_t MR_ADDR, uint32_t MR_DATA);*/
static uint8_t MTC_test(uint8_t mask, uint64_t start_address, uint32_t size, MTC_PATTERN pattern, MTC_ADD_PATTERN add_pattern, uint32_t *error);
#ifdef VREFDQ_CALIB
static uint8_t FPGA_VREFDQ_calibration_using_mtc(void);
static uint8_t VREFDQ_calibration_using_mtc(void);
#endif
#ifdef DDR_SANITY_CHECKS_EN
static uint8_t rw_sanity_chk(uint64_t * address, uint32_t count);
static uint8_t mtc_sanity_check(uint64_t start_address);
#endif
#ifdef SET_VREF_LPDDR4_MODE_REGS
static uint8_t mode_register_write(uint32_t MR_ADDR, uint32_t MR_DATA);
#endif
#ifdef DDR_SANITY_CHECKS_EN
static uint8_t memory_tests(void);
#endif
static void ddr_off_mode(void);
static void set_ddr_mode_reg_and_vs_bits(uint32_t dpc_bits);
static void set_ddr_rpc_regs(DDR_TYPE ddr_type);
static uint8_t get_num_lanes(void);
static void load_dq(uint8_t lane);
static uint8_t use_software_bclk_sclk_training(DDR_TYPE ddr_type);
static void config_ddr_io_pull_up_downs_rpc_bits(DDR_TYPE ddr_type);
#ifdef SWEEP_ENABLED
static uint8_t get_best_sweep(sweep_index *good_index);
#endif
#ifdef MANUAL_ADDCMD_TRAINIG
static uint8_t ddr_manual_addcmd_refclk_offset(DDR_TYPE ddr_type, uint8_t * refclk_sweep_index);
#endif

/*******************************************************************************
 * External function declarations
 */
extern void delay(uint32_t n);

#ifdef DEBUG_DDR_INIT
extern mss_uart_instance_t *g_debug_uart;
#ifdef DEBUG_DDR_DDRCFG
void debug_read_ddrcfg(void);
#endif
#endif

#ifdef FABRIC_NOISE_TEST
uint32_t fabric_noise_en = 1;
uint32_t fabric_noise_en_log = 1;
uint32_t num_of_noise_blocks_en = 3; /* do not set less than 1 */
uint32_t noise_ena = 0x0;
#endif

/*******************************************************************************
 * Instance definitions
 */

/*******************************************************************************
 * Public Functions - API
 ******************************************************************************/


/***************************************************************************//**
 * ddr_state_machine(DDR_SS_COMMAND)
 * call this routine if you do not require the state machine
 *
 * @param ddr_type
 */
uint32_t  ddr_state_machine(DDR_SS_COMMAND command)
{
    static DDR_SM_STATES ddr_state;
    static uint32_t return_status;
    if (command == DDR_SS__INIT)
    {
        ddr_state = DDR_STATE_INIT;
    }
    SIM_FEEDBACK0(100U + ddr_state);
    SIM_FEEDBACK1(ddr_state);
    switch (ddr_state)
    {
        default:
        case DDR_STATE_INIT:
            ddr_state = DDR_STATE_TRAINING;
            return_status = 0U;
            break;

        case DDR_STATE_TRAINING:
            /*
             * We stay in this state until finished training/fail training
             */
            return_status = ddr_setup();
            break;

        case DDR_STATE_MONITOR:
            /*
             * 1. Periodically check DDR access
             * 2. Run any tests, as directed
             */
//            return_status = ddr_monitor();
            break;
    }
    SIM_FEEDBACK1(0xFF000000UL + return_status);
    return (return_status);
}


/***************************************************************************//**
 * ddr_setup(DDR_TYPE ddr_type)
 * call this routine if you do not require the state machine
 *
 * @param ddr_type
 */
static uint32_t ddr_setup(void)
{
    static DDR_TRAINING_SM ddr_training_state = DDR_TRAINING_INIT;
    static uint32_t error;
    static uint32_t timeout;
#ifdef DEBUG_DDR_INIT
    static uint32_t addr_cmd_value;
    static uint32_t bclk_sclk_offset_value;
    static uint32_t dpc_vrgen_v_value;
    static uint32_t dpc_vrgen_h_value;
    static uint32_t dpc_vrgen_vs_value;
#endif
#ifdef SWEEP_ENABLED
    static SWEEP_STATES sweep_state = INIT_SWEEP;
#endif
    static uint32_t retry_count;
    static uint32_t write_latency;
    static uint32_t tip_cfg_params;
    static uint32_t dpc_bits;
    static uint8_t last_sweep_status;
#if (TUNE_RPC_166_VALUE == 1)
    static uint8_t num_rpc_166_retires = 0U;
#endif
#ifdef MANUAL_ADDCMD_TRAINIG
    static uint8_t refclk_offset;
    static  uint8_t refclk_sweep_index =0xFU;
#endif
    static uint32_t bclk_answer = 0U;
    DDR_TYPE ddr_type;
    uint32_t ret_status = 0U;
    uint8_t number_of_lanes_to_calibrate;

    ddr_type = LIBERO_SETTING_DDRPHY_MODE & DDRPHY_MODE_MASK;

    SIM_FEEDBACK0(200U + ddr_training_state);
    SIM_FEEDBACK1(0U);

    switch (ddr_training_state)
    {
        case DDR_TRAINING_INIT:
            tip_cfg_params = LIBERO_SETTING_TIP_CFG_PARAMS;
            dpc_bits = LIBERO_SETTING_DPC_BITS ;
            write_latency = LIBERO_SETTING_CFG_WRITE_LATENCY_SET;
#if (TUNE_RPC_166_VALUE == 1)
            rpc_166_fifo_offset = DEFAULT_RPC_166_VALUE;
#endif
#ifdef MANUAL_ADDCMD_TRAINIG
            refclk_offset = LIBERO_SETTING_MAX_MANUAL_REF_CLK_PHASE_OFFSET + 1U;
#endif
#ifdef SWEEP_ENABLED
            sweep_state = INIT_SWEEP;
#endif
            ddr_error_count = 0U;
            error = 0U;
            memfill((uint8_t *)&calib_data,0U,sizeof(calib_data));
            retry_count = 0U;
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r Start training. TIP_CFG_PARAMS:"\
                    , LIBERO_SETTING_TIP_CFG_PARAMS);
#endif
#ifdef SWEEP_ENABLED
            addr_cmd_value = LIBERO_SETTING_TIP_CFG_PARAMS\
                                         & ADDRESS_CMD_OFFSETT_MASK;
            bclk_sclk_offset_value = (LIBERO_SETTING_TIP_CFG_PARAMS\
                   & BCLK_SCLK_OFFSET_MASK)>>BCLK_SCLK_OFFSET_SHIFT;
            dpc_vrgen_v_value = (LIBERO_SETTING_DPC_BITS & \
                    BCLK_DPC_VRGEN_V_MASK)>>BCLK_DPC_VRGEN_V_SHIFT;
            dpc_vrgen_h_value = (LIBERO_SETTING_DPC_BITS & \
                    BCLK_DPC_VRGEN_H_MASK)>>BCLK_DPC_VRGEN_H_SHIFT;
            dpc_vrgen_vs_value = (LIBERO_SETTING_DPC_BITS & \
                    BCLK_DPC_VRGEN_VS_MASK)>>BCLK_DPC_VRGEN_VS_SHIFT;
#endif
            ddr_training_state = DDR_TRAINING_CHECK_FOR_OFFMODE;
            break;
        case DDR_TRAINING_FAIL_SM2_VERIFY:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r SM2_VERIFY: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_SM_VERIFY:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r SM_VERIFY: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_SM_DQ_DQS:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r SM_DQ_DQS: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_SM_RDGATE:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r SM_RDGATE: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_SM_WRLVL:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r SM_WRLVL: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_SM_ADDCMD:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r SM_ADDCMD: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_SM_BCLKSCLK:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r BCLKSCLK_SWY: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_BCLKSCLK_SW:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r BCLKSCLK_SW: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_FULL_32BIT_NC_CHECK:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r 32BIT_NC_CHECK: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_32BIT_CACHE_CHECK:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r 32BIT_CACHE_CHECK: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_MIN_LATENCY:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r MIN_LATENCY: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_START_CHECK:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r START_CHECK: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_PLL_LOCK:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r PLL LOCK FAIL: ",addr_cmd_value);
#endif
            ddr_training_state = DDR_TRAINING_FAIL;
            break;
        case DDR_TRAINING_FAIL_DDR_SANITY_CHECKS:
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r DDR_SANITY_CHECKS FAIL: ",\
                                                                addr_cmd_value);
            ddr_training_state = DDR_TRAINING_FAIL;
#endif
            break;
        case DDR_SWEEP_AGAIN:
            retry_count++;
            last_sweep_status = CALIBRATION_PASSED;
    #ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r\n\r DDR_SWEEP_AGAIN: ",\
                                        ddr_training_state);
    #endif
            ddr_training_state = DDR_CHECK_TRAINING_SWEEP;
            break;
        case DDR_TRAINING_FAIL:
#ifdef DEBUG_DDR_INIT
            {
                tip_register_status (g_debug_uart);
                (void)uprint32(g_debug_uart, "\n\r ****************************************************", 0U);

            }
#endif
            retry_count++;
            if(last_sweep_status != CALIBRATION_SUCCESS)
            {
                last_sweep_status = CALIBRATION_FAILED;
            }
    #ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r\n\r DDR_TRAINING_FAIL: ",\
                        ddr_training_state);
            (void)uprint32(g_debug_uart, "\n\r Retry Count: ", retry_count);
    #endif
            ddr_training_state = DDR_CHECK_TRAINING_SWEEP;
            break;

        case DDR_CHECK_TRAINING_SWEEP:
            {
#ifdef SWEEP_ENABLED
                /* first check if we are finished */
                if(last_sweep_status == CALIBRATION_SUCCESS)
                {
                    /*
                     * Try again with calculated values
                     */
                    ddr_training_state = DDR_TRAINING_CHECK_FOR_OFFMODE;
                }
                else if(retry_count == TOTAL_SWEEPS)
                {
                    sweep_index index;
#ifdef DEBUG_DDR_INIT
                    sweep_status(g_debug_uart);
#endif
                    /*
                     * Choose the best index
                     */
                    if (get_best_sweep(&index) == 0U)
                    {
#ifdef DEBUG_DDR_INIT
                        (void)uprint32(g_debug_uart, "\n\r sweep success: ",\
                                                                tip_cfg_params);
#endif
                        last_sweep_status = CALIBRATION_SUCCESS;
                        /*
                         * Use obtained settings
                         */
                        addr_cmd_value = index.cmd_index +\
                                LIBERO_SETTING_MIN_ADDRESS_CMD_OFFSET;
                        bclk_sclk_offset_value = index.bclk_sclk_index +\
                                LIBERO_SETTING_MIN_ADDRESS_BCLK_SCLK_OFFSET;
                        dpc_vrgen_v_value = index.dpc_vgen_index +\
                                LIBERO_SETTING_MIN_DPC_V_GEN;
                        dpc_vrgen_h_value = index.dpc_vgen_h_index +\
                                LIBERO_SETTING_MIN_DPC_H_GEN;
                        dpc_vrgen_vs_value = index.dpc_vgen_vs_index +\
                                LIBERO_SETTING_MIN_DPC_VS_GEN;

                        tip_cfg_params = ((tip_cfg_params &\
                            (~BCLK_SCLK_OFFSET_MASK))|\
                             (bclk_sclk_offset_value<<BCLK_SCLK_OFFSET_SHIFT));
                        tip_cfg_params = ((tip_cfg_params &\
                                 (~ADDRESS_CMD_OFFSETT_MASK))|(addr_cmd_value));
                        dpc_bits = ((dpc_bits &\
                                 (~BCLK_DPC_VRGEN_V_MASK))|\
                                   (dpc_vrgen_v_value<<BCLK_DPC_VRGEN_V_SHIFT));
                        dpc_bits = ((dpc_bits &\
                                 (~BCLK_DPC_VRGEN_H_MASK))|\
                                   (dpc_vrgen_h_value<<BCLK_DPC_VRGEN_H_SHIFT));
                        dpc_bits = ((dpc_bits &\
                                 (~BCLK_DPC_VRGEN_VS_MASK))|\
                                 (dpc_vrgen_vs_value<<BCLK_DPC_VRGEN_VS_SHIFT));
                        ddr_training_state = DDR_TRAINING_CHECK_FOR_OFFMODE;
                    }
                    else
                    {
#ifdef SWEEP_ENABLED
                        sweep_state = INIT_SWEEP;
#endif
                        retry_count = 0U;
                        ddr_training_state = DDR_TRAINING_SWEEP;
                    }
                }
                else
                {
                    ddr_training_state = DDR_TRAINING_SWEEP;
                }
                ddr_error_count = 0U;
                error = 0U;
                memfill((uint8_t *)&calib_data,0U,sizeof(calib_data));
                DDRCFG->DFI.PHY_DFI_INIT_START.PHY_DFI_INIT_START   = 0x0U;
                /* reset controller */
                DDRCFG->MC_BASE2.CTRLR_INIT.CTRLR_INIT = 0x0U;
                CFG_DDR_SGMII_PHY->training_start.training_start = 0x0U;
            }
#else       /* we are not SWEEP_ENABLED */
            ddr_error_count = 0U;
            error = 0U;
            memfill((uint8_t *)&calib_data,0U,sizeof(calib_data));
            DDRCFG->DFI.PHY_DFI_INIT_START.PHY_DFI_INIT_START   = 0x0U;
            /* reset controller */
            DDRCFG->MC_BASE2.CTRLR_INIT.CTRLR_INIT = 0x0U;
            CFG_DDR_SGMII_PHY->training_start.training_start = 0x0U;

            ddr_training_state = DDR_TRAINING_CHECK_FOR_OFFMODE;
            }
#endif
            break;

        case DDR_TRAINING_SWEEP:
#ifdef SWEEP_ENABLED
            {
                static uint32_t sweep_count_cmd_offset;
                static uint32_t sweep_count_bck_sclk;
                static uint32_t sweep_count_dpc_v_bits;
                static uint32_t sweep_count_dpc_h_bits;
                static uint32_t sweep_count_dpc_vs_bits;

                switch(sweep_state)
                {
                    case INIT_SWEEP:
                        /*
                         * Parameter values
                         */
                        addr_cmd_value = LIBERO_SETTING_MIN_ADDRESS_CMD_OFFSET;
                        bclk_sclk_offset_value =\
                                LIBERO_SETTING_MIN_ADDRESS_BCLK_SCLK_OFFSET;
                        dpc_vrgen_v_value = LIBERO_SETTING_MIN_DPC_V_GEN;
                        dpc_vrgen_h_value = LIBERO_SETTING_MIN_DPC_H_GEN;
                        dpc_vrgen_vs_value = LIBERO_SETTING_MIN_DPC_VS_GEN;
                        /*
                         * state counts
                         */
                        sweep_count_cmd_offset = 0U;
                        sweep_count_bck_sclk = 0U;
                        sweep_count_dpc_v_bits = 0U;
                        sweep_count_dpc_h_bits = 0U;
                        sweep_count_dpc_vs_bits = 0U;
                        sweep_state = ADDR_CMD_OFFSET_SWEEP;
                        __attribute__((fallthrough)); /* deliberately fall through */
                    case ADDR_CMD_OFFSET_SWEEP:
                        /*
                         * Record sweep result
                         */
                        sweep_results[sweep_count_dpc_vs_bits][sweep_count_dpc_h_bits][sweep_count_dpc_v_bits]\
                            [sweep_count_bck_sclk]\
                                [sweep_count_cmd_offset] = last_sweep_status;
                        /*
                         * sweep:  ADDR_CMD OFFSET
                         */
                        addr_cmd_value++;
                        if (addr_cmd_value > \
                                LIBERO_SETTING_MAX_ADDRESS_CMD_OFFSET)
                        {
                            addr_cmd_value = \
                                    LIBERO_SETTING_MIN_ADDRESS_CMD_OFFSET;
                        }

                        tip_cfg_params = ((tip_cfg_params &\
                                 (~ADDRESS_CMD_OFFSETT_MASK))|(addr_cmd_value));
                        sweep_count_cmd_offset++;
                        if(sweep_count_cmd_offset > MAX_NUMBER_ADDR_CMD_OFFSET_SWEEPS)
                        {
                            sweep_count_cmd_offset = 0U;
                            sweep_state = BCLK_SCLK_OFFSET_SWEEP;
                        }
                        else
                        {
                            /*
                             * Now do a sweep
                             */
                            ddr_error_count = 0U;
                            error = 0U;
                            memfill((uint8_t *)&calib_data,0U,sizeof(calib_data));
                            DDRCFG->DFI.PHY_DFI_INIT_START.PHY_DFI_INIT_START   = 0x00000000U;
                            /* reset controller */
                            DDRCFG->MC_BASE2.CTRLR_INIT.CTRLR_INIT = 0x00000000U;
                            CFG_DDR_SGMII_PHY->training_start.training_start    = 0x00000000U;
                            ddr_training_state = DDR_TRAINING_CHECK_FOR_OFFMODE;
                        }
                        break;
                    case BCLK_SCLK_OFFSET_SWEEP:
                        /*
                         * sweep:  BCLK_SCLK
                         */
                        bclk_sclk_offset_value++;
                        if (bclk_sclk_offset_value > \
                                LIBERO_SETTING_MAX_ADDRESS_BCLK_SCLK_OFFSET)
                        {
                            bclk_sclk_offset_value = \
                                    LIBERO_SETTING_MIN_ADDRESS_BCLK_SCLK_OFFSET;
                        }
                        tip_cfg_params = ((tip_cfg_params &\
                             (~BCLK_SCLK_OFFSET_MASK))|\
                                 (bclk_sclk_offset_value<<BCLK_SCLK_OFFSET_SHIFT));
                        sweep_count_bck_sclk++;
                        if(sweep_count_bck_sclk > MAX_NUMBER__BCLK_SCLK_OFFSET_SWEEPS)
                        {
                            sweep_count_bck_sclk = 0U;
                            sweep_state = DPC_VRGEN_V_SWEEP;
                        }
                        else
                        {
                            sweep_state = ADDR_CMD_OFFSET_SWEEP;
                        }
                        break;
                    case DPC_VRGEN_V_SWEEP:
                        /*
                         * sweep:  DPC_VRGEN_V [4:6]
                         * LIBERO_SETTING_DPC_BITS
                         */
                        dpc_vrgen_v_value++;
                        if (dpc_vrgen_v_value > \
                                    LIBERO_SETTING_MAX_DPC_V_GEN)
                        {
                            dpc_vrgen_v_value = \
                                    LIBERO_SETTING_MIN_DPC_V_GEN;
                        }
                        dpc_bits = ((dpc_bits &\
                             (~BCLK_DPC_VRGEN_V_MASK))|\
                                 (dpc_vrgen_v_value<<BCLK_DPC_VRGEN_V_SHIFT));
                        sweep_count_dpc_v_bits++;
                        if(sweep_count_dpc_v_bits > MAX_NUMBER_DPC_V_GEN_SWEEPS)
                        {
                            sweep_count_dpc_v_bits = 0U;
                            sweep_state = DPC_VRGEN_H_SWEEP;
                        }
                        else
                        {
                            sweep_state = BCLK_SCLK_OFFSET_SWEEP;
                        }
                        break;
                    case DPC_VRGEN_H_SWEEP:
                        /*
                         * sweep:  DPC_VRGEN_V [4:6]
                         * LIBERO_SETTING_DPC_BITS
                         */
                        dpc_vrgen_h_value++;
                        if (dpc_vrgen_h_value > \
                                    LIBERO_SETTING_MAX_DPC_H_GEN)
                        {
                            dpc_vrgen_h_value = \
                                    LIBERO_SETTING_MIN_DPC_H_GEN;
                        }
                        dpc_bits = ((dpc_bits &\
                             (~BCLK_DPC_VRGEN_H_MASK))|\
                                 (dpc_vrgen_h_value<<BCLK_DPC_VRGEN_H_SHIFT));
                        sweep_count_dpc_h_bits++;
                        if(sweep_count_dpc_h_bits > MAX_NUMBER_DPC_H_GEN_SWEEPS)
                        {
                            sweep_count_dpc_h_bits = 0U;
                            sweep_state = DPC_VRGEN_VS_SWEEP;
                        }
                        else
                        {
                            sweep_state = DPC_VRGEN_V_SWEEP;
                        }
                        break;
                    case DPC_VRGEN_VS_SWEEP:
                        /*
                         * sweep:  DPC_VRGEN_V [4:6]
                         * LIBERO_SETTING_DPC_BITS
                         */
                        dpc_vrgen_vs_value++;
                        if (dpc_vrgen_vs_value > \
                                    LIBERO_SETTING_MAX_DPC_VS_GEN)
                        {
                            dpc_vrgen_vs_value = \
                                    LIBERO_SETTING_MIN_DPC_VS_GEN;
                        }
                        dpc_bits = ((dpc_bits &\
                             (~BCLK_DPC_VRGEN_VS_MASK))|\
                                 (dpc_vrgen_vs_value<<BCLK_DPC_VRGEN_VS_SHIFT));
                        sweep_count_dpc_vs_bits++;
                        if(sweep_count_dpc_vs_bits > MAX_NUMBER_DPC_VS_GEN_SWEEPS)
                        {
                            sweep_count_dpc_vs_bits = 0U;
                        }
                        sweep_state = DPC_VRGEN_H_SWEEP;
                        break;
                    case FINISHED_SWEEP:
                        break;
                    default:
                        break;
                }
            }
#endif /* SWEEP_ENABLED */
            break;

        case DDR_TRAINING_CHECK_FOR_OFFMODE:
            /*
             * check if we are in off mode
             */
            if (ddr_type == DDR_OFF_MODE)
            {
                ddr_off_mode();
                ret_status |= DDR_SETUP_DONE;
                return (ret_status);
            }
            else
            {
                /*
                 * set initial conditions
                 */
                /* enable fabric noise */
#ifdef FABRIC_NOISE_TEST
               if(fabric_noise_en)
               {
                    SYSREG->SOFT_RESET_CR &= 0x00U;
                    SYSREG->SUBBLK_CLOCK_CR = 0xffffffffUL;
                    SYSREG->GPIO_INTERRUPT_FAB_CR = 0x00000000UL;
                    PLIC_init();
                    PLIC_SetPriority_Threshold(0);
                    __enable_irq();
                    /* bit0-bit15 used to enable noise logic in steps of 5%
                      bit 16 noise logic reset
                      bit 17 clkmux sel
                      bit 18 pll powerdown
                      bit 19 external io enable for GCLKINT */
                    PLIC_SetPriority(GPIO0_BIT0_or_GPIO2_BIT0_PLIC_0, 4U);
                    PLIC_SetPriority(GPIO0_BIT1_or_GPIO2_BIT1_PLIC_1, 4U);
                    PLIC_SetPriority(GPIO0_BIT2_or_GPIO2_BIT2_PLIC_2, 4U);
                    PLIC_SetPriority(GPIO0_BIT3_or_GPIO2_BIT3_PLIC_3, 4U);
                    PLIC_SetPriority(GPIO0_BIT4_or_GPIO2_BIT4_PLIC_4, 4U);
                    PLIC_SetPriority(GPIO0_BIT5_or_GPIO2_BIT5_PLIC_5, 4U);
                    PLIC_SetPriority(GPIO0_BIT6_or_GPIO2_BIT6_PLIC_6, 4U);
                    PLIC_SetPriority(GPIO0_BIT7_or_GPIO2_BIT7_PLIC_7, 4U);
                    PLIC_SetPriority(GPIO0_BIT8_or_GPIO2_BIT8_PLIC_8, 4U);
                    PLIC_SetPriority(GPIO0_BIT9_or_GPIO2_BIT9_PLIC_9, 4U);
                    PLIC_SetPriority(GPIO0_BIT10_or_GPIO2_BIT10_PLIC_10, 4U);
                    PLIC_SetPriority(GPIO0_BIT11_or_GPIO2_BIT11_PLIC_11, 4U);
                    PLIC_SetPriority(GPIO0_BIT12_or_GPIO2_BIT12_PLIC_12, 4U);
                    PLIC_SetPriority(GPIO0_BIT13_or_GPIO2_BIT13_PLIC_13, 4U);
                    PLIC_SetPriority(GPIO1_BIT0_or_GPIO2_BIT14_PLIC_14, 4U);
                    PLIC_SetPriority(GPIO1_BIT1_or_GPIO2_BIT15_PLIC_15, 4U);
                    PLIC_SetPriority(GPIO1_BIT2_or_GPIO2_BIT16_PLIC_16, 4U);
                    PLIC_SetPriority(GPIO1_BIT3_or_GPIO2_BIT17_PLIC_17, 4U);
                    PLIC_SetPriority(GPIO1_BIT4_or_GPIO2_BIT18_PLIC_18, 4U);
                    PLIC_SetPriority(GPIO1_BIT5_or_GPIO2_BIT19_PLIC_19, 4U);

                    MSS_GPIO_init(GPIO2_LO);
                    MSS_GPIO_config_all(GPIO2_LO, MSS_GPIO_OUTPUT_MODE);
                    MSS_GPIO_set_outputs(GPIO2_LO, 0x00000UL);      /* bits 15:0 - 0, noise logic  disabled */
                    delay(100);
                    /*MSS_GPIO_set_outputs(GPIO2_LO, 0x00FFFUL);*/    /* bits 12:0 - 1,  56% enabled */
                    noise_ena = (1 << num_of_noise_blocks_en) - 1;
                    MSS_GPIO_set_outputs(GPIO2_LO, noise_ena);      /* num_of_noise_blocks_en * 4.72% */
                    fabric_noise_en = 0;
                }
#endif /* FABRIC_NOISE_TEST */
                write_latency = MIN_LATENCY;
                ddr_training_state = DDR_TRAINING_SET_MODE_VS_BITS;
            }
            break;

        case DDR_TRAINING_SET_MODE_VS_BITS:
#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, "\n\r dpc_bits: ",\
                                                                      dpc_bits);
#endif
            /*
             * Set the training mode
             */
            set_ddr_mode_reg_and_vs_bits(dpc_bits);
            ddr_training_state = DDR_TRAINING_FLASH_REGS;
            break;

        case DDR_TRAINING_FLASH_REGS:
            /*
             * flash registers with RPC values
             *   Enable DDR IO decoders
             *   Note :
             *      rpc sequence:
             *          power-up -> mss_boot -> re-flash nv_map -> override
             *      any changes (to fix issues)
             *
             *   SOFT_RESET_  bit 0 == periph soft reset, auto cleared
             */
            CFG_DDR_SGMII_PHY->SOFT_RESET_DECODER_DRIVER.SOFT_RESET_DECODER_DRIVER = 1U;
            CFG_DDR_SGMII_PHY->SOFT_RESET_DECODER_ODT.SOFT_RESET_DECODER_ODT=1U;
            CFG_DDR_SGMII_PHY->SOFT_RESET_DECODER_IO.SOFT_RESET_DECODER_IO = 1U;
            ddr_training_state = DDR_TRAINING_CORRECT_RPC;
            break;

       case DDR_TRAINING_CORRECT_RPC:
            /*
             * correct some rpc registers, which were incorrectly set in mode
             * setting
             */
            set_ddr_rpc_regs(ddr_type);
            ddr_training_state = DDR_TRAINING_SOFT_RESET;
            break;
        case DDR_TRAINING_SOFT_RESET:
            /*
             * Set soft reset on IP to load RPC to SCB regs (dynamic mode)
             * Bring the DDR bank controller out of reset
             */
            IOSCB_BANKCONT_DDR->soft_reset = 1U;  /* DPC_BITS   NV_MAP  reset */
            ddr_training_state = DDR_TRAINING_CALIBRATE_IO;
            break;
        case DDR_TRAINING_CALIBRATE_IO:
            /*
             * Calibrate DDR I/O here, once all RPC settings correct
             */
            ddr_pvt_calibration();
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart,  "\n\r PCODE = ",\
                    (CFG_DDR_SGMII_PHY->IOC_REG2.IOC_REG2 & 0x7FU));
            (void)uprint32(g_debug_uart,  "\n\r NCODE = ", \
                    (((CFG_DDR_SGMII_PHY->IOC_REG2.IOC_REG2) >> 7U) & 0x7FU));
            (void)uprint32(g_debug_uart, "\n\r addr_cmd_value: ",\
                                                addr_cmd_value);
            (void)uprint32(g_debug_uart, "\n\r bclk_sclk_offset_value: ",\
                                                    bclk_sclk_offset_value);
            (void)uprint32(g_debug_uart, "\n\r dpc_vrgen_v_value: ",\
                                               dpc_vrgen_v_value);
            (void)uprint32(g_debug_uart, "\n\r dpc_vrgen_h_value: ",\
                                               dpc_vrgen_h_value);
            (void)uprint32(g_debug_uart, "\n\r dpc_vrgen_vs_value: ",\
                                               dpc_vrgen_vs_value);
#endif
            ddr_training_state = DDR_TRAINING_CONFIG_PLL;
            break;
        case DDR_TRAINING_CONFIG_PLL:
            /*
             *  Configure the DDR PLL
             */
            ddr_pll_config(SCB_UPDATE);
            timeout = 0xFFFF;
            ddr_training_state = DDR_TRAINING_VERIFY_PLL_LOCK;
            break;
        case DDR_TRAINING_VERIFY_PLL_LOCK:
            /*
             *  Verify DDR PLL lock
             */
            if (ddr_pll_lock_scb() == 0U)
            {
                ddr_training_state = DDR_TRAINING_SETUP_SEGS;
            }
            else if(--timeout == 0U)
            {
                ddr_training_state = DDR_TRAINING_FAIL_PLL_LOCK;
            }
            break;
        case DDR_TRAINING_SETUP_SEGS:
            /*
             * Configure Segments- address mapping,  CFG0/CFG1
             */
            setup_ddr_segments(DEFAULT_SEG_SETUP);
            /*
             * enable the  DDRC
             */
            /* Turn on DDRC clock */
            SYSREG->SUBBLK_CLOCK_CR |= SUBBLK_CLOCK_CR_DDRC_MASK;
            /* Remove soft reset */
            SYSREG->SOFT_RESET_CR   &= (uint32_t)~SOFT_RESET_CR_DDRC_MASK;
            ddr_training_state = DDR_TRAINING_SETUP_DDRC;
            break;
        case DDR_TRAINING_SETUP_DDRC:
            /*
             * set-up DDRC
             * Configuration taken from the user.
             */
            {
                init_ddrc();
                ddr_training_state = DDR_TRAINING_RESET;
            }
            break;
        case DDR_TRAINING_RESET:
            /*
             * Assert training reset
             *  reset pin is bit [1]
             * and load skip setting
             */
            /* leave in reset */
/* To verify if separate reset required for DDR4 - believe it is not */
#ifndef SPECIAL_TRAINIG_RESET
            CFG_DDR_SGMII_PHY->training_reset.training_reset    = 0x00000002U;
#ifndef     SOFT_RESET_PRE_TAG_172
            DDRCFG->MC_BASE2.CTRLR_SOFT_RESET_N.CTRLR_SOFT_RESET_N  =\
                                                                                0x00000000U;
            DDRCFG->MC_BASE2.CTRLR_SOFT_RESET_N.CTRLR_SOFT_RESET_N  =\
                                                                                0x00000001U;
#endif      /* !SOFT_RESET_PRE_TAG_172 */
#else
            /* Disable CKE */
            DDRCFG->MC_BASE2.INIT_DISABLE_CKE.INIT_DISABLE_CKE = 0x1;

            /* Assert FORCE_RESET */
            DDRCFG->MC_BASE2.INIT_FORCE_RESET.INIT_FORCE_RESET = 0x1;
            delay(100);
            /* release reset to memory here, set INIT_FORCE_RESET to 0 */
            DDRCFG->MC_BASE2.INIT_FORCE_RESET.INIT_FORCE_RESET = 0x0;
            delay(500000);

            /* Enable CKE */
            DDRCFG->MC_BASE2.INIT_DISABLE_CKE.INIT_DISABLE_CKE = 0x0;
            delay(1000);

            /* reset pin is bit [1] */
            CFG_DDR_SGMII_PHY->training_reset.training_reset    = 0x00000002U;

#endif
            ddr_training_state = DDR_TRAINING_ROTATE_CLK;
            break;
        case DDR_TRAINING_ROTATE_CLK:
        /*
         * Rotate bclk90 by 90 deg
         */
            CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt = 0x00000004U;
            /*expert mode enabling */
            CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0x00000002U;
            /*   */
            CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x7CU; /* loading */
            CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x78U;
            CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x78U;
            CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x7CU;
            CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x4U;
            CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x64U;
            CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x66U; /* increment */
            for (uint32_t d=0;d< \
                LIBERO_SETTING_TIP_CONFIG_PARAMS_BCLK_VCOPHS_OFFSET;d++)
            {
                CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x67U;
                CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x66U;
            }
            CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x64U;
            CFG_DDR_SGMII_PHY->expert_pllcnt.expert_pllcnt= 0x4U;

            /* setting load delay lines */
            CFG_DDR_SGMII_PHY->expert_dlycnt_mv_rd_dly_reg.expert_dlycnt_mv_rd_dly_reg\
                = 0x1FU;
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1=\
                    0xFFFFFFFFU;  /* setting to 1 to load delaylines */
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1=\
                    0x00000000U;

            /* write w DFICFG_REG mv_rd_dly 0x00000000 #
               tip_apb_write(12'h89C, 32'h0);   mv_rd_dly  */
            CFG_DDR_SGMII_PHY->expert_dlycnt_mv_rd_dly_reg.expert_dlycnt_mv_rd_dly_reg \
                = 0x0U;

            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1=\
                    0xFFFFFFFFU;  /* setting to 1 to load delaylines */
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1=\
                    0x00000000U;


            CFG_DDR_SGMII_PHY->expert_dlycnt_pause.expert_dlycnt_pause       =\
                    0x0000003FU;
            CFG_DDR_SGMII_PHY->expert_dlycnt_pause.expert_dlycnt_pause       =\
                    0x00000000U;

            /* DQ */
            /*    dfi_training_complete_shim = 1'b1
                  dfi_wrlvl_en_shim = 1'b1 */
            CFG_DDR_SGMII_PHY->expert_dfi_status_override_to_shim.expert_dfi_status_override_to_shim = 0x6;
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg0.expert_dlycnt_load_reg0=\
                    0xFFFFFFFFU;   /* load output delays */
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1=\
                    0xF;           /* (ECC) - load output delays */
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg0.expert_dlycnt_load_reg0=\
                    0x0;           /* clear */
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1=\
                    0x0;           /* (ECC) clear */

            /* DQS
             * dfi_wrlvl_en_shim = 1'b1 */
            CFG_DDR_SGMII_PHY->expert_dfi_status_override_to_shim.expert_dfi_status_override_to_shim = 0x4;
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg0.expert_dlycnt_load_reg0=\
                    0xFFFFFFFFU;   /* load output delays */
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1=\
                    0xF;           /* (ECC) - load output delays */
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg0.expert_dlycnt_load_reg0=\
                    0x0;           /* clear */
            CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1=\
                    0x0;           /* (ECC) clear */

            CFG_DDR_SGMII_PHY->expert_dfi_status_override_to_shim.expert_dfi_status_override_to_shim = 0x0; /* clear */

            CFG_DDR_SGMII_PHY->expert_dlycnt_pause.expert_dlycnt_pause       =\
                    0x0000003FU;
            CFG_DDR_SGMII_PHY->expert_dlycnt_pause.expert_dlycnt_pause       =\
                    0x00000000U;

            /* expert mode disabling */
            CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en                 =\
                    0x00000000U;
            ddr_training_state = DDR_TRAINING_SET_TRAINING_PARAMETERS;
            break;
        case DDR_TRAINING_SET_TRAINING_PARAMETERS:
            /*
             * SET TRAINING PARAMETERS
             *
             * TIP STATIC PARAMETERS 0
             *
             *  30:22   Number of VCO Phase offsets between BCLK and SCLK
             *  21:13   Number of VCO Phase offsets between BCLK and SCLK
             *  12:6    Number of VCO Phase offsets between BCLK and SCLK
             *  5:3     Number of VCO Phase offsets between BCLK and SCLK
             *  2:0  Number of VCO Phase offsets between REFCLK and ADDCMD bits
             */
            {
#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, "\n\r tip_cfg_params: ",\
                                                                tip_cfg_params);
#endif

                CFG_DDR_SGMII_PHY->tip_cfg_params.tip_cfg_params =\
                                                                tip_cfg_params;
                timeout = 0xFFFF;

                if(use_software_bclk_sclk_training(ddr_type) == 1U)
                {
                    /*
                     * Initiate software training
                     */
#ifdef     SOFT_RESET_PRE_TAG_172
                    DDRCFG->MC_BASE2.CTRLR_SOFT_RESET_N.CTRLR_SOFT_RESET_N  =\
                                                                    0x00000001U;
#endif
                    ddr_training_state = DDR_TRAINING_IP_SM_BCLKSCLK_SW;
                }
                else
                {
                    /*
                     * Initiate IP training and wait for dfi_init_complete
                     */
                    /*asserting training_reset */
                    if (ddr_type != DDR3)
                    {
                        CFG_DDR_SGMII_PHY->training_reset.training_reset =\
                            0x00000000U;
                    }
                    else
                    {
                        DDRCFG->MC_BASE2.CTRLR_SOFT_RESET_N.CTRLR_SOFT_RESET_N  =\
                                                                   0x00000001U;
                    }
                    ddr_training_state = DDR_TRAINING_IP_SM_START;
                }
            }
            break;

        case DDR_TRAINING_IP_SM_BCLKSCLK_SW:
            /*
             * We have chosen to use software bclk sclk sweep instead of IP
             */
            {
                uint32_t bclk_phase, bclk90_phase,refclk_phase;
                bclk_answer = 0U;
                {
                    /*
                     * BEGIN MANUAL BCLKSCLK TRAINING
                     */
                    uint32_t rx_previous=0x3U;
                    uint32_t rx_current=0U;
                    uint32_t answer_count[8U]={0U,0U,0U,0U,0U,0U,0U,0U};
                    uint32_t answer_index=0U;

                    /*UPPER LIMIT MUST BE MULTIPLE OF 8 */
                    for (uint32_t i=0U; i<(8U * 100); i++)
                    {

                        bclk_phase   = ( i    & 0x07UL ) << 8U;
                        bclk90_phase = ((i+2U) & 0x07UL ) << 11U;
                        /*
                         * LOAD BCLK90 PHASE
                         */
                        MSS_SCB_DDR_PLL->PLL_PHADJ = (0x00004003UL | bclk_phase | bclk90_phase);
                        MSS_SCB_DDR_PLL->PLL_PHADJ = (0x00000003UL | bclk_phase | bclk90_phase);
                        MSS_SCB_DDR_PLL->PLL_PHADJ = (0x00004003UL | bclk_phase | bclk90_phase);

                        /*
                        * No pause required, causes an issue
                        */

                        /*
                        * SAMPLE RX_BCLK
                        */
                        rx_current = ((CFG_DDR_SGMII_PHY->expert_addcmd_ln_readback.expert_addcmd_ln_readback) >> 12)& 0x03;
                        /* IF WE FOUND A TRANSITION, BREAK THE LOOP */
                        if ((rx_current & (~rx_previous)) != 0x00000000UL)
                        {
                            answer_index=i&0x07U;
                            /* increment the answer count for this index */
                            answer_count[answer_index]++;
                        }

                        rx_previous = rx_current;
                        uint32_t max=0U;
                        for (uint32_t j=0U;j<8U;j++)
                        {
                            /* sweep through found answers and select the most common */
                            if (answer_count[j] > max)
                            {
                                bclk_answer = j;
                                max=answer_count[j];
                            }
                        }
                    }
                }
                ddr_training_state = DDR_MANUAL_ADDCMD_TRAINING_SW;
                break;

          case DDR_MANUAL_ADDCMD_TRAINING_SW:
                {
                    /*
                     * APPLY OFFSET & LOAD THE PHASE
                     * bclk_sclk_offset_value
                     * BCLK_SCLK_OFFSET_BASE
                     */
                    if(LIBERO_SETTING_TRAINING_SKIP_SETTING & ADDCMD_BIT)
                    {
                        /*
                         * We are skipping add/cmd training so need to set
                         * refclk phase offset manually
                         * We may need to sweep this
                         */
                        refclk_phase = (uint32_t)(((bclk_answer+SW_TRAING_BCLK_SCLK_OFFSET + 5U + LIBERO_SETTING_MANUAL_REF_CLK_PHASE_OFFSET ) & 0x07UL) << 2U);
                        bclk_phase  = ((bclk_answer+SW_TRAING_BCLK_SCLK_OFFSET)    & 0x07UL ) << 8U;
                        bclk90_phase= ((bclk_answer+SW_TRAING_BCLK_SCLK_OFFSET+2U)  & 0x07UL ) << 11U;
                        MSS_SCB_DDR_PLL->PLL_PHADJ      = (0x00004003UL | bclk_phase | bclk90_phase | refclk_phase);
                        MSS_SCB_DDR_PLL->PLL_PHADJ      = (0x00000003UL | bclk_phase | bclk90_phase | refclk_phase);
                        MSS_SCB_DDR_PLL->PLL_PHADJ      = (0x00004003UL | bclk_phase | bclk90_phase | refclk_phase);
                    }
                    else
                    {
                        bclk_phase = ((bclk_answer+SW_TRAING_BCLK_SCLK_OFFSET)    & 0x07UL ) << 8U;
                        bclk90_phase=((bclk_answer+SW_TRAING_BCLK_SCLK_OFFSET+2U)  & 0x07UL ) << 11U;
                        MSS_SCB_DDR_PLL->PLL_PHADJ      = (0x00004003UL | bclk_phase | bclk90_phase);
                        MSS_SCB_DDR_PLL->PLL_PHADJ      = (0x00000003UL | bclk_phase | bclk90_phase);
                        MSS_SCB_DDR_PLL->PLL_PHADJ      = (0x00004003UL | bclk_phase | bclk90_phase);
                    }
                    ddr_training_state = DDR_TRAINING_IP_SM_START;
                    /* END MANUAL BCLKSCLK TRAINING */
                }
            }
            if(--timeout == 0U)
            {
                ddr_training_state = DDR_TRAINING_FAIL_BCLKSCLK_SW;
            }
            break;
        case DDR_TRAINING_IP_SM_START:
            {
                CFG_DDR_SGMII_PHY->training_skip.training_skip      =\
                                        LIBERO_SETTING_TRAINING_SKIP_SETTING;
                if ((ddr_type == DDR3)||(ddr_type == LPDDR4)||(ddr_type == DDR4))
                {
                    /* RX_MD_CLKN */
                    CFG_DDR_SGMII_PHY->rpc168.rpc168 = 0x0U;
                }
#ifdef DDR_TRAINING_IP_SM_START_DELAY
                delay(100);
#endif
                /* release reset to training */
                CFG_DDR_SGMII_PHY->training_reset.training_reset    = 0x00000000U;
#ifdef IP_SM_START_TRAINING_PAUSE
                /* todo: pause removed at Alister's request for test. Will
                 * remove once verified not required after further testing
                 */
                CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0xffU;
                delay(100);
                CFG_DDR_SGMII_PHY->expert_dlycnt_pause.expert_dlycnt_pause = 0x00000000U;
                CFG_DDR_SGMII_PHY->expert_dlycnt_pause.expert_dlycnt_pause = 0x0000003FU;
                CFG_DDR_SGMII_PHY->expert_dlycnt_pause.expert_dlycnt_pause = 0x00000000U;
                delay(100);
                CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0x00U;
                delay(100);
#endif
            }
            {
                DDRCFG->DFI.PHY_DFI_INIT_START.PHY_DFI_INIT_START   =\
                                                                    0x00000000U;
                /* kick off training- DDRC, set dfi_init_start */
                DDRCFG->DFI.PHY_DFI_INIT_START.PHY_DFI_INIT_START   =\
                                                                    0x00000001U;
                DDRCFG->MC_BASE2.CTRLR_INIT.CTRLR_INIT = 0x00000000U;
                DDRCFG->MC_BASE2.CTRLR_INIT.CTRLR_INIT = 0x00000001U;

                timeout = 0xFFFF;
                ddr_training_state = DDR_TRAINING_IP_SM_START_CHECK;
            }
#ifdef DEBUG_DDR_INIT
#ifdef MANUAL_ADDCMD_TRAINIG
            (void)uprint32(g_debug_uart,  "\n\r\n\r ADDCMD_OFFSET ", refclk_offset);
#endif
#endif
            break;
        case DDR_TRAINING_IP_SM_START_CHECK:
#ifndef RENODE_DEBUG
            if((DDRCFG->DFI.STAT_DFI_INIT_COMPLETE.STAT_DFI_INIT_COMPLETE\
                    & 0x01U) == 0x01U)
#endif
            {
#ifdef LANE_ALIGNMENT_RESET_REQUIRED
                CFG_DDR_SGMII_PHY->lane_alignment_fifo_control.lane_alignment_fifo_control = 0x00U;
                CFG_DDR_SGMII_PHY->lane_alignment_fifo_control.lane_alignment_fifo_control = 0x02U;
#endif

#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, \
                        "\n\r\n\r pll_phadj_after_hw_training ",\
                                        MSS_SCB_DDR_PLL->PLL_DIV_2_3);
                (void)uprint32(g_debug_uart, \
                        "\n\r\n\r pll_phadj_after_hw_training ",\
                                        MSS_SCB_DDR_PLL->PLL_DIV_0_1);
#endif

                if(LIBERO_SETTING_TRAINING_SKIP_SETTING & BCLK_SCLK_BIT)
                {
                    ddr_training_state = DDR_TRAINING_IP_SM_ADDCMD;
                }
                else
                {
                    ddr_training_state = DDR_TRAINING_IP_SM_BCLKSCLK;
                }
                timeout = 0xFFFF;
            }
            if(--timeout == 0U)
            {
                ddr_training_state = DDR_TRAINING_FAIL_START_CHECK;
            }
            break;
        case DDR_TRAINING_IP_SM_BCLKSCLK:
            if(CFG_DDR_SGMII_PHY->training_status.training_status & BCLK_SCLK_BIT)
            {
                timeout = 0xFFFF;
                ddr_training_state = DDR_TRAINING_IP_SM_ADDCMD;
            }
            if(--timeout == 0U)
            {
                ddr_training_state = DDR_TRAINING_FAIL_SM_BCLKSCLK;
            }
            break;

        case DDR_TRAINING_IP_SM_ADDCMD:
            if(LIBERO_SETTING_TRAINING_SKIP_SETTING & ADDCMD_BIT)
            {
                timeout = 0xFFFFF;
                ddr_training_state = DDR_TRAINING_IP_SM_WRLVL;
            }
            else if(CFG_DDR_SGMII_PHY->training_status.training_status & ADDCMD_BIT)
            {
                timeout = 0xFFFFF;
                ddr_training_state = DDR_TRAINING_IP_SM_WRLVL;
            }
            if(--timeout == 0U)
            {
                /*
                 * Typically this can fail for two
                 * reasons:
                 * 1. ADD/CMD not being received
                 * We need to sweep:
                 * ADDCMD_OFFSET [0:3]   RW value
                 *  sweep->  0x2 -> 4 -> C -> 0
                 * 2. DQ not received
                 * We need to sweep:
                 * LIBERO_SETTING_DPC_BITS
                 *  DPC_VRGEN_H [4:6]   value= 0x8->0xC
                 *
                 * */
                ddr_training_state = DDR_TRAINING_FAIL_SM_ADDCMD;
            }
            break;
        case DDR_TRAINING_IP_SM_WRLVL:
            if(LIBERO_SETTING_TRAINING_SKIP_SETTING & WRLVL_BIT)
            {
                timeout = 0xFFFF;
                ddr_training_state = DDR_TRAINING_IP_SM_RDGATE;
            }
            else if(CFG_DDR_SGMII_PHY->training_status.training_status & WRLVL_BIT)
            {
                timeout = 0xFFFFF;
                ddr_training_state = DDR_TRAINING_IP_SM_RDGATE;
            }
            if(--timeout == 0U)
            {
                ddr_training_state = DDR_TRAINING_FAIL_SM_WRLVL;
            }
            break;
        case DDR_TRAINING_IP_SM_RDGATE:
            if(LIBERO_SETTING_TRAINING_SKIP_SETTING & RDGATE_BIT)
            {
                timeout = 0xFFFF;
                ddr_training_state = DDR_TRAINING_IP_SM_DQ_DQS;
            }
            else if(CFG_DDR_SGMII_PHY->training_status.training_status & RDGATE_BIT)
            {
                timeout = 0xFFFF;
                ddr_training_state = DDR_TRAINING_IP_SM_DQ_DQS;
            }
            if(--timeout == 0U)
            {
                ddr_training_state = DDR_TRAINING_FAIL_SM_RDGATE;
            }
            break;
        case DDR_TRAINING_IP_SM_DQ_DQS:
            if(LIBERO_SETTING_TRAINING_SKIP_SETTING & DQ_DQS_BIT)
            {
                timeout = 0xFFFF;
                ddr_training_state = DDR_TRAINING_IP_SM_VERIFY;
            }
            else if(CFG_DDR_SGMII_PHY->training_status.training_status & DQ_DQS_BIT)
            {
                timeout = 0xFFFF;
                ddr_training_state = DDR_TRAINING_IP_SM_VERIFY;
            }
            if(--timeout == 0U)
            {
                ddr_training_state = DDR_TRAINING_FAIL_SM_DQ_DQS;
            }
            break;

        case DDR_TRAINING_IP_SM_VERIFY:
            if ((DDRCFG->DFI.STAT_DFI_TRAINING_COMPLETE.STAT_DFI_TRAINING_COMPLETE & 0x01U) == 0x01U)
            {
                 /*
                  * Step 15:
                  * check worked for each lane
                  */
                 uint32_t lane_sel, t_status = 0U;
                 for (lane_sel=0U; lane_sel< \
                            LIBERO_SETTING_DATA_LANES_USED; lane_sel++)
                 {
                     SIM_FEEDBACK1(1000U);
                     delay(10U);
                     SIM_FEEDBACK1(1001U);
                     CFG_DDR_SGMII_PHY->lane_select.lane_select =\
                             lane_sel;
                     delay(10U);
                     /*
                      * verify cmd address results
                      *  rejects if not acceptable
                      * */
                     {
                        uint32_t ca_status[8]= {\
                            ((CFG_DDR_SGMII_PHY->addcmd_status0.addcmd_status0)&0xFFU),\
                            ((CFG_DDR_SGMII_PHY->addcmd_status0.addcmd_status0>>8U)&0xFFU), \
                            ((CFG_DDR_SGMII_PHY->addcmd_status0.addcmd_status0>>16U)&0xFFU),\
                            ((CFG_DDR_SGMII_PHY->addcmd_status0.addcmd_status0>>24U)&0xFFU),\
                            ((CFG_DDR_SGMII_PHY->addcmd_status1.addcmd_status1)&0xFFU),\
                            ((CFG_DDR_SGMII_PHY->addcmd_status1.addcmd_status1>>8U)&0xFFU),\
                            ((CFG_DDR_SGMII_PHY->addcmd_status1.addcmd_status1>>16U)&0xFFU),\
                            ((CFG_DDR_SGMII_PHY->addcmd_status1.addcmd_status1>>24U)&0xFFU)};
                        uint32_t low_ca_dly_count = 0U;
                        uint32_t last = 0U;
                        uint32_t decrease_count = 0U;
                        for(uint32_t i =0U; i<8U;i++)
                        {
                            if(ca_status[i] < 5U)
                            {
                                low_ca_dly_count++;
                            }
                            if(ca_status[i]<=last)
                            {
                                decrease_count++;
                            }
                            last = ca_status[i];
                        }
                        if(ca_status[0]<= ca_status[7U])
                        {
                            decrease_count++;
                        }
                        if((LIBERO_SETTING_TRAINING_SKIP_SETTING & ADDCMD_BIT) != ADDCMD_BIT)
                        {
                            /* Retrain if abnormal CA training result detected */
                            if(low_ca_dly_count > ABNORMAL_RETRAIN_CA_DLY_DECREASE_COUNT)
                            {
                                t_status = t_status | 0x01U;
                            }
                            /* Retrain if abnormal CA training result detected */
                            if(decrease_count > ABNORMAL_RETRAIN_CA_DECREASE_COUNT)
                            {
                                t_status = t_status | 0x01U;
                            }
                        }
                     }
                     /* Check that gate training passed without error  */
                     t_status =t_status |\
                             CFG_DDR_SGMII_PHY->gt_err_comb.gt_err_comb;
                     delay(10U);
                     /* Check that DQ/DQS training passed without error */
                     if(CFG_DDR_SGMII_PHY->dq_dqs_err_done.dq_dqs_err_done != 8U)
                     {
                         t_status = t_status | 0x01U;
                     }
                     /* Check that DQ/DQS calculated window is above 5 taps. */
                     if(CFG_DDR_SGMII_PHY->dqdqs_status1.dqdqs_status1 < \
                                                                        DQ_DQS_NUM_TAPS)
                     {
                         t_status = t_status | 0x01U;
                     }
#ifdef DCT_EXTRA_CHECKS  /* todo: Theses checks was added by DCT */
                     if(((CFG_DDR_SGMII_PHY->gt_txdly.gt_txdly)&0xFFU) == 0U) // Gate training tx_dly check: AL
                     {
                         t_status = t_status | 0x01U;
                     }
                     if(((CFG_DDR_SGMII_PHY->gt_txdly.gt_txdly>>8U)&0xFFU) == 0U)
                     {
                         t_status = t_status | 0x01U;
                     }
                     if(((CFG_DDR_SGMII_PHY->gt_txdly.gt_txdly>>16U)&0xFFU) == 0U)
                     {
                         t_status = t_status | 0x01U;
                      }
                     if(((CFG_DDR_SGMII_PHY->gt_txdly.gt_txdly>>24U)&0xFFU) == 0U)
                     {
                         t_status = t_status | 0x01U;
                     }
#endif
                 }
    #ifdef RENODE_DEBUG
                 t_status = 0U;  /* Dummy success -move on to
                                    next stage */
    #endif
                 if(t_status == 0U)
                 {
                     SIM_FEEDBACK1(21U);
                     /*
                      * We can now set vref on the memory
                      * mode register for lpddr4
                      * May include other modes, and include a sweep
                      * Alister looking into this and will revert.
                      */
                     if (ddr_type == LPDDR4)
                     {
#ifdef SET_VREF_LPDDR4_MODE_REGS
                         mode_register_write(DDR_MODE_REG_VREF,\
                             DDR_MODE_REG_VREF_VALUE);
#endif
                     }
                     ddr_training_state = DDR_TRAINING_SET_FINAL_MODE;
                 }
                 else /* fail, try again */
                 {
                     SIM_FEEDBACK1(20U);
                     ddr_training_state = DDR_TRAINING_FAIL_SM_VERIFY;
                 }
             }
            else
            {
                ddr_training_state = DDR_TRAINING_FAIL_SM2_VERIFY;
            }
            break;


        case DDR_TRAINING_SET_FINAL_MODE:
            /*
             * Set final mode register value.
             */
            CFG_DDR_SGMII_PHY->DDRPHY_MODE.DDRPHY_MODE =\
                LIBERO_SETTING_DDRPHY_MODE;
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r\n\r DDR FINAL_MODE: ",\
                    LIBERO_SETTING_DDRPHY_MODE);
#ifdef DEBUG_DDR_CFG_DDR_SGMII_PHY
            (void)print_reg_array(g_debug_uart ,
                  (uint32_t *)CFG_DDR_SGMII_PHY,\
                          (sizeof(CFG_DDR_SGMII_PHY_TypeDef)/4U));
#endif
#ifdef DEBUG_DDR_DDRCFG
            debug_read_ddrcfg();
#endif
#endif
#ifdef DEBUG_DDR_INIT
            {
                tip_register_status (g_debug_uart);
                (void)uprint32(g_debug_uart, "\n\r ****************************************************", 0U);

            }
#endif
            ddr_training_state = DDR_TRAINING_WRITE_CALIBRATION;
            break;

        case DDR_TRAINING_WRITE_CALIBRATION:
            /*
             * Does the following in the DDRC need to be checked??
             * DDRCFG->DFI.STAT_DFI_TRAINING_COMPLETE.STAT_DFI_TRAINING_COMPLETE;
             *
             */
            number_of_lanes_to_calibrate = get_num_lanes();
            /*
             *  Now start the write calibration as training has been successful
             */
            if(error == 0U)
            {
                if (ddr_type == LPDDR4)
                {
                    uint8_t lane;
                    /* Changed default value to centre dq/dqs on window */
                    CFG_DDR_SGMII_PHY->rpc220.rpc220 = 0xCUL;
                    for(lane = 0U; lane < number_of_lanes_to_calibrate; lane++)
                    {
                        load_dq(lane);
                    }
                    SIM_FEEDBACK1(1U);

#ifdef SW_CONFIG_LPDDR_WR_CALIB_FN
                    error =\
                            write_calibration_lpddr4_using_mtc(\
                                                  number_of_lanes_to_calibrate);
#else
                    error =\
                            write_calibration_using_mtc(\
                                                  number_of_lanes_to_calibrate);
#endif
                }
                else
                {
                    SIM_FEEDBACK1(2U);
                    error =\
                      write_calibration_using_mtc(number_of_lanes_to_calibrate);
                }
                if(error)
                {
                    ddr_error_count++;
                    SIM_FEEDBACK1(106U);
                }
            }
#if (EN_RETRY_ON_FIRST_TRAIN_PASS == 1)
            if((error == 0U)&&(retry_count != 0U))
#else
            if(error == 0U)
#endif
            {
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r\n\r wr calib result ",\
                    calib_data.write_cal.lane_calib_result);
#endif
                ddr_training_state = DDR_SWEEP_CHECK;
            }
            else if(error == MTC_TIMEOUT_ERROR)
            {
                error = 0U;
                ddr_training_state = DDR_TRAINING_FAIL_DDR_SANITY_CHECKS;
            }
            else
            {
                error = 0U;
                ddr_training_state = DDR_TRAINING_WRITE_CALIBRATION_RETRY;
            }
            break;

        case DDR_TRAINING_WRITE_CALIBRATION_RETRY:
            /*
             * Clear write calibration data
             */
            memfill((uint8_t *)&calib_data,0U,sizeof(calib_data));
            /*
             * Try the next offset
             */
            write_latency++;
            if (write_latency > MAX_LATENCY)
            {
                write_latency = MIN_LATENCY;
                ddr_training_state = DDR_TRAINING_FAIL_MIN_LATENCY;
            }
            else
            {
                DDRCFG->DFI.CFG_DFI_T_PHY_WRLAT.CFG_DFI_T_PHY_WRLAT =\
                        write_latency;
#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, "\n\r\n\r wr write latency ",\
                                                                write_latency);
#endif
                ddr_training_state = DDR_TRAINING_WRITE_CALIBRATION;
            }
            break;

        case DDR_SWEEP_CHECK:
#ifdef SWEEP_ENABLED
            if((retry_count != 0U)&&(retry_count < (TOTAL_SWEEPS-1U)))
            {
                ddr_training_state = DDR_SWEEP_AGAIN;
            }
            else
#endif
            {
                ddr_training_state = DDR_SANITY_CHECKS;
            }
            break;

        case DDR_SANITY_CHECKS:
            /*
             *  Now start the write calibration if training successful
             */
#ifdef DEBUG_DDR_INIT
            (void)uprint32(g_debug_uart, "\n\r\n\r DDR SANITY_CHECKS: ",\
                                                                        error);
#endif
            if(error == 0U)
            {
#ifdef DDR_SANITY_CHECKS_EN
                error = memory_tests();
#endif
            }
            if(error == 0U)
            {
                ddr_training_state = DDR_FULL_MTC_CHECK;
            }
            else
            {
                ddr_training_state = DDR_TRAINING_FAIL_DDR_SANITY_CHECKS;
            }
            break;

        case DDR_FULL_MTC_CHECK:
            {
                uint64_t start_address = 0x0000000000000000ULL;
                uint32_t size = ONE_MB_MTC;  /* Number of reads for each iteration 2**size*/
                uint8_t mask;
                if (get_num_lanes() <= 3U)
                {
                    mask = 0x3U;
                }
                else
                {
                    mask = 0xFU;
                }
                error = MTC_test(mask, start_address, size, MTC_COUNTING_PATTERN, MTC_ADD_SEQUENTIAL, &error);
                /* Read using different patterns */
                error = 0U;
                error |= MTC_test(mask, start_address, size, MTC_COUNTING_PATTERN, MTC_ADD_SEQUENTIAL, &error);
                error |= MTC_test(mask, start_address, size, MTC_WALKING_ONE, MTC_ADD_SEQUENTIAL, &error);
                error |= MTC_test(mask, start_address, size, MTC_PSEUDO_RANDOM, MTC_ADD_SEQUENTIAL, &error);
                error |= MTC_test(mask, start_address, size, MTC_NO_REPEATING_PSEUDO_RANDOM, MTC_ADD_SEQUENTIAL, &error);
                error |= MTC_test(mask, start_address, size, MTC_ALT_ONES_ZEROS, MTC_ADD_SEQUENTIAL, &error);
                error |= MTC_test(mask, start_address, size, MTC_ALT_5_A, MTC_ADD_SEQUENTIAL, &error);
                error |= MTC_test(mask, start_address, size, MTC_PSEUDO_RANDOM_16BIT, MTC_ADD_SEQUENTIAL, &error);
                error |= MTC_test(mask, start_address, size, MTC_PSEUDO_RANDOM_8BIT, MTC_ADD_SEQUENTIAL, &error);

                error |= MTC_test(mask, start_address, size, MTC_COUNTING_PATTERN, MTC_ADD_RANDOM, &error);
                error |= MTC_test(mask, start_address, size, MTC_WALKING_ONE, MTC_ADD_RANDOM, &error);
                error |= MTC_test(mask, start_address, size, MTC_PSEUDO_RANDOM, MTC_ADD_RANDOM, &error);
                error |= MTC_test(mask, start_address, size, MTC_NO_REPEATING_PSEUDO_RANDOM, MTC_ADD_RANDOM, &error);
                error |= MTC_test(mask, start_address, size, MTC_ALT_ONES_ZEROS, MTC_ADD_RANDOM, &error);
                error |= MTC_test(mask, start_address, size, MTC_ALT_5_A, MTC_ADD_RANDOM, &error);
                error |= MTC_test(mask, start_address, size, MTC_PSEUDO_RANDOM_16BIT, MTC_ADD_RANDOM, &error);
                error |= MTC_test(mask, start_address, size, MTC_PSEUDO_RANDOM_8BIT, MTC_ADD_RANDOM, &error);
            }
            if(error == 0U)
            {
#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, "\n\r\n\r Passed MTC full check ", error);
#endif
                ddr_training_state = DDR_FULL_32BIT_NC_CHECK;
            }
            else
            {
#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, "\n\r\n\r Failed MTC full check ", error);
#endif
                ddr_training_state = DDR_TRAINING_FAIL;
            }
            break;

        case DDR_FULL_32BIT_NC_CHECK:
            /*
             * write and read back test from drr, non cached access
             */
            {
#if (DDR_FULL_32BIT_NC_CHECK_EN == 1)
                error = ddr_read_write_fn((uint64_t*)LIBERO_SETTING_DDR_32_NON_CACHE,\
                                     SW_CFG_NUM_READS_WRITES,\
                                         SW_CONFIG_PATTERN);
#endif
            }
            if(error == 0U)
            {
                ddr_training_state = DDR_FULL_32BIT_CACHE_CHECK;
            }
            else
            {
                ddr_training_state = DDR_TRAINING_FAIL_FULL_32BIT_NC_CHECK;
            }
            break;
        case DDR_FULL_32BIT_CACHE_CHECK:
#if (DDR_FULL_32BIT_CACHED_CHECK_EN == 1)
            error = ddr_read_write_fn((uint64_t*)LIBERO_SETTING_DDR_32_CACHE,\
                                    SW_CFG_NUM_READS_WRITES,\
                                    SW_CONFIG_PATTERN);
#endif
            if(error == 0U)
            {
#ifdef SKIP_VERIFY_PATTERN_IN_CACHE
                ddr_training_state = DDR_FULL_32BIT_WRC_CHECK;
#else
                ddr_training_state = DDR_LOAD_PATTERN_TO_CACHE;
#endif
            }
            else
            {
                ddr_training_state = DDR_TRAINING_FAIL_32BIT_CACHE_CHECK;
            }
            break;
        case DDR_LOAD_PATTERN_TO_CACHE:
            load_ddr_pattern(LIBERO_SETTING_DDR_32_CACHE, SIZE_OF_PATTERN_TEST, SIZE_OF_PATTERN_OFFSET);
            if(error == 0U)
            {
                ddr_training_state = DDR_VERIFY_PATTERN_IN_CACHE;
            }
            else
            {
                ddr_training_state = DDR_TRAINING_FAIL;
            }
            break;
        case DDR_VERIFY_PATTERN_IN_CACHE:
            error = test_ddr(NO_PATTERN_IN_CACHE_READS, SIZE_OF_PATTERN_TEST);
            if(error == 0U)
            {
#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, "\n\r\n\r wr write latency ",\
                                                                write_latency);
#if (TUNE_RPC_166_VALUE == 1)
                (void)uprint32(g_debug_uart, "\n\r rpc_166_fifo_offset: ",\
                        rpc_166_fifo_offset);
#endif
#endif
                ddr_training_state = DDR_FULL_32BIT_WRC_CHECK;
            }
            else
            {
#if (TUNE_RPC_166_VALUE == 1)

#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, "\n\r rpc_166_fifo_offset: ",\
                                        rpc_166_fifo_offset);
#endif

#ifdef NOT_A_FULL_RETRAIN

                /* this fails post tests */
                if(num_rpc_166_retires < NUM_RPC_166_VALUES)
                {
                    num_rpc_166_retires++;
                    rpc_166_fifo_offset++;
                    if(rpc_166_fifo_offset > MAX_RPC_166_VALUE)
                    {
                        rpc_166_fifo_offset = MIN_RPC_166_VALUE;
                    }
                    /* try again here DDR_LOAD_PATTERN_TO_CACHE */
                }
                else
                {
                    num_rpc_166_retires = 0U;
                    rpc_166_fifo_offset = DEFAULT_RPC_166_VALUE;
                    ddr_training_state = DDR_TRAINING_FAIL;
                }
                CFG_DDR_SGMII_PHY->rpc166.rpc166 = rpc_166_fifo_offset;
                //PAUSE to reset fifo (loads new RXPTR value).
                CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0x1U;
                CFG_DDR_SGMII_PHY->expert_dlycnt_pause.expert_dlycnt_pause =\
                0x0000003EU;
                CFG_DDR_SGMII_PHY->expert_dlycnt_pause.expert_dlycnt_pause =\
                0x00000000U;
                CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0x8U;
                //delay(10);
                //END PAUSE
#else
                if(num_rpc_166_retires < NUM_RPC_166_VALUES)
                {
                    num_rpc_166_retires++;
                    rpc_166_fifo_offset++;
                    if(rpc_166_fifo_offset > MAX_RPC_166_VALUE)
                    {
                        rpc_166_fifo_offset = MIN_RPC_166_VALUE;
                    }
                    /* try again here DDR_LOAD_PATTERN_TO_CACHE */
                }
                else
                {
                    num_rpc_166_retires = 0U;
                    rpc_166_fifo_offset = DEFAULT_RPC_166_VALUE;
                    ddr_training_state = DDR_TRAINING_FAIL;
                }
                ddr_training_state = DDR_TRAINING_FAIL;
#endif
#else       /* (TUNE_RPC_166_VALUE == 0) */
                ddr_training_state = DDR_TRAINING_FAIL;
#endif
            }
            break;
        case DDR_FULL_32BIT_WRC_CHECK:
            if(error == 0U)
            {
                ddr_training_state = DDR_FULL_64BIT_NC_CHECK;
            }
            else
            {
                ddr_training_state = DDR_TRAINING_FAIL;
            }
            break;
        case DDR_FULL_64BIT_NC_CHECK:
            if(error == 0U)
            {
                ddr_training_state = DDR_FULL_64BIT_CACHE_CHECK;
            }
            else
            {
                ddr_training_state = DDR_TRAINING_FAIL;
            }
            break;
        case DDR_FULL_64BIT_CACHE_CHECK:
            if(error == 0U)
            {
                ddr_training_state = DDR_FULL_64BIT_WRC_CHECK;
            }
            else
            {
                ddr_training_state = DDR_TRAINING_FAIL;
            }
            break;
        case DDR_FULL_64BIT_WRC_CHECK:
            if(error == 0U)
            {
                ddr_training_state = DDR_TRAINING_VREFDQ_CALIB;
            }
            else
            {
                ddr_training_state = DDR_TRAINING_FAIL;
            }

            break;

        case DDR_TRAINING_VREFDQ_CALIB:
#ifdef VREFDQ_CALIB
            /*
             * This step is optional
             * todo: Test once initial board verification complete
             */
            error = VREFDQ_calibration_using_mtc();
            if(error != 0U)
            {
                ddr_error_count++;
            }
#endif
            ddr_training_state = DDR_TRAINING_FPGA_VREFDQ_CALIB;
            break;

        case DDR_TRAINING_FPGA_VREFDQ_CALIB:
#ifdef FPGA_VREFDQ_CALIB
            /*
             * This step is optional
             * todo: Test once initial board verification complete
             */
            error = FPGA_VREFDQ_calibration_using_mtc();
            if(error != 0U)
            {
                ddr_error_count++;
            }
#endif
            ddr_training_state = DDR_TRAINING_FINISH_CHECK;
            break;

        case DDR_TRAINING_FINISH_CHECK:
            /*
             *   return status
             */
#ifdef DEBUG_DDR_INIT
            {
                tip_register_status (g_debug_uart);
                (void)uprint32(g_debug_uart, "\n\r\n\r DDR_TRAINING_PASS: ",\
                        ddr_training_state);
                (void)uprint32(g_debug_uart, "\n ****************************************************", 0);

            }
#endif
            if(ddr_error_count > 0)
            {
                ret_status |= DDR_SETUP_FAIL;
            }
            else
            {
                /*
                 * Configure Segments- address mapping,  CFG0/CFG1
                 */
                setup_ddr_segments(LIBERO_SEG_SETUP);
            }
            ret_status |= DDR_SETUP_DONE;
            ddr_training_state = DDR_TRAINING_FINISHED;
            break;

        default:
        case DDR_TRAINING_FINISHED:
              break;
    } /* end of case statement */

    return (ret_status);
}


/**
 * get_num_lanes(void)
 * @return number of lanes used, 2(16 bit), 3(16 bit + ecc), 4(32 bit) or 5
 * Note: Lane 4 always used when ECC enabled, even for x16
 */
static uint8_t get_num_lanes(void)
{
    uint8_t lanes;
    /* Check width, 16bit or 32bit bit supported, 1 => 32 bit */
    if ((LIBERO_SETTING_DDRPHY_MODE & DDRPHY_MODE_BUS_WIDTH_MASK) ==\
            DDRPHY_MODE_BUS_WIDTH_4_LANE)
    {
        lanes = 4U;
    }
    else
    {
        lanes = 2U;
    }
    /* Check if using ECC, add a lane */
    if ((LIBERO_SETTING_DDRPHY_MODE & DDRPHY_MODE_ECC_MASK) ==\
            DDRPHY_MODE_ECC_ON)
    {
        lanes++;
    }
    return lanes;
}



/***************************************************************************//**
 * set_ddr_mode_reg_and_vs_bits()
 *
 */
static void set_ddr_mode_reg_and_vs_bits(uint32_t dpc_bits)
{
    DDR_TYPE ddr_type = LIBERO_SETTING_DDRPHY_MODE & DDRPHY_MODE_MASK;
    /*
     * R1.6
     * Write DDR phy mode reg (eg DDR3)
     * When we write to the mode register, an ip state machine copies default
     * values for the particular mode chosen to RPC registers associated with
     * DDR in the MSS custom block.
     * ( Note: VS bits are not include in the copy so we set below )
     * The RPC register values are transferred to the SCB registers in a
     * subsequent step.
     */
    /*
     * Set VS bits
     * Select VS bits for DDR mode selected  --- set dynamic pc bit settings to
     * allow editing of RPC registers
     * pvt calibration etc
     *
     * [19]         dpc_move_en_v   enable dynamic control of vrgen circuit for
     *              ADDCMD pins
     * [18]         dpc_vrgen_en_v  enable vref generator for ADDCMD pins
     * [17:12]      dpc_vrgen_v     reference voltage ratio setting for ADDCMD
     *              pins
     * [11:11]      dpc_move_en_h   enable dynamic control of vrgen circuit for
     *              DQ/DQS pins
     * [10:10]      dpc_vrgen_en_h  enable vref generator for DQ/DQS pins
     * [9:4]        dpc_vrgen_h     reference voltage ratio setting for DQ/DQS
     *              pins
     * [3:0]        dpc_vs          bank voltage select for pvt calibration
     */
    /*
        DDRPHY_MODE setting from MSS configurator
            DDRMODE              :3;
            ECC                  :1;
            CRC                  :1;
            Bus_width            :3;
            DMI_DBI              :1;
            DQ_drive             :2;
            DQS_drive            :2;
            ADD_CMD_drive        :2;
            Clock_out_drive      :2;
            DQ_termination       :2;
            DQS_termination      :2;
            ADD_CMD_input_pin_termination :2;
            preset_odt_clk       :2;
            Power_down           :1;
            rank                 :1;
            Command_Address_Pipe :2;
    */
    {
        if ((ddr_type == DDR4) &&\
                (LIBERO_SETTING_DDRPHY_MODE & DDRPHY_MODE_ECC_MASK) ==\
                    DDRPHY_MODE_ECC_ON)
        {
            /*
             * For ECC on when DDR4, and data mask on during training, training
             * will not pass
             * This will eventually be handled by the configurator
             * DM will not be allowed for DDR4 with ECC
             */
            CFG_DDR_SGMII_PHY->DDRPHY_MODE.DDRPHY_MODE  =\
                             (LIBERO_SETTING_DDRPHY_MODE  & DMI_DBI_MASK );
        }
        else
        {
            CFG_DDR_SGMII_PHY->DDRPHY_MODE.DDRPHY_MODE  =\
                                                     LIBERO_SETTING_DDRPHY_MODE;
        }
        delay((uint32_t) 100U);
        CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS        = dpc_bits;
    }
}



/***************************************************************************//**
 * set_ddr_rpc_regs()
 * @param ddr_type
 */
static void set_ddr_rpc_regs(DDR_TYPE ddr_type)
{
    /*
     * Write DDR phy mode reg (eg DDR3)
     * When we write to the mode register, an ip state machine copies default
     * values for the particular mode chossen
     * to RPC registers associated with DDR in the MSS custom block.
     * The RPC register values are transferred to the SCB registers in a
     * subsequent step.
     *
     * Question:
     * Select VS bits (eg DDR3 ) (vs bits not included in mode setup - should
     * be??)
     * Small wait while state machine transfer takes place required here.
     * (status bit required?)
     *
     */
    /*
        DDRPHY_MODE setting from MSS configurator
            DDRMODE              :3;
            ECC                  :1;
            CRC                  :1;
            Bus_width            :3;
            DMI_DBI              :1;
            DQ_drive             :2;
            DQS_drive            :2;
            ADD_CMD_drive        :2;
            Clock_out_drive      :2;
            DQ_termination       :2;
            DQS_termination      :2;
            ADD_CMD_input_pin_termination :2;
            preset_odt_clk       :2;
            Power_down           :1;
            rank                 :1;
            Command_Address_Pipe :2;
      */
    {
        switch (ddr_type)
        {
            default:
            case DDR_OFF_MODE:
                /* Below have already been set  */
                /* CFG_DDR_SGMII_PHY->rpc95.rpc95 = 0x07;  */    /* addcmd I/O*/
                /* CFG_DDR_SGMII_PHY->rpc96.rpc96 = 0x07;  */    /* clk */
                /* CFG_DDR_SGMII_PHY->rpc97.rpc97 = 0x07;  */    /* dq */
                /* CFG_DDR_SGMII_PHY->rpc98.rpc98 = 0x07;  */    /* dqs */
                /*
                 *    bits 15:14 connect to ibufmx DQ/DQS/DM
                 *    bits 13:12 connect to ibufmx CA/CK
                 */
                CFG_DDR_SGMII_PHY->UNUSED_SPACE0[0] = 0x0U;
                break;
            case DDR3L:
            case DDR3:
                /* Required when rank x 2 */
                if ((LIBERO_SETTING_DDRPHY_MODE & DDRPHY_MODE_RANK_MASK) ==\
                        DDRPHY_MODE_TWO_RANKS)
                {
                    CFG_DDR_SGMII_PHY->spio253.spio253 = 1U;
                }

                {
                    /*
                     * firmware set this to 3'b100 for all cases except when we
                     * are in OFF mode (DDR3,DDR4,LPDDR3,LPDDR4).
                     */
                    CFG_DDR_SGMII_PHY->rpc98.rpc98 = 0x04U;
                }
                /*
                 *    SAR xxxx
                 *    bits 15:14 connect to ibufmx DQ/DQS/DM
                 *    bits 13:12 connect to ibufmx CA/CK
                 */
                CFG_DDR_SGMII_PHY->UNUSED_SPACE0[0] = 0x0U;
                break;
            case DDR4:
                {
                    /*
                     * Sar 108017
                     * ODT_STATIC setting is wrong for DDR4/LPDDR3, needs to
                     * be overwritten in embedded SW for E51
                     *
                     * ODT_STATIC is set to 001 for DQ/DQS/DBI bits in
                     * DDR3/LPDDR4, this enables termination to VSS.
                     *
                     * This needs to be switched to VDDI termination.
                     *
                     * To do this, we do APB register writes to override
                     * the following PC bits:
                     * odt_static_dq=010
                     * odt_static_dqs=010
                     */
                    CFG_DDR_SGMII_PHY->rpc10_ODT.rpc10_ODT = 2U;
                    CFG_DDR_SGMII_PHY->rpc11_ODT.rpc11_ODT = 2U;
                    /*
                     * SAR 108218
                     * The firmware should set this to 3'b100 for
                     * all cases except when we are in OFF mode (DDR3,DDR4,
                     * LPDDR3,LPDDR4).
                     */
                    CFG_DDR_SGMII_PHY->rpc98.rpc98 = 0x04U;
                    /*
                     *    bits 15:14 connect to ibufmx DQ/DQS/DM
                     *    bits 13:12 connect to ibufmx CA/CK
                     */
                    CFG_DDR_SGMII_PHY->UNUSED_SPACE0[0] =  0x0U;
                }
                break;
            case LPDDR3:
                {
                    /*
                     * Sar 108017
                     * ODT_STATIC setting is wrong for DDR4/LPDDR3, needs to be
                     * overwritten in embedded SW for E51
                     *
                     * ODT_STATIC is set to 001 for DQ/DQS/DBI bits in
                     * DDR3/LPDDR4, this enables termination to VSS.
                     *
                     * This needs to be switched to VDDI termination.
                     *
                     * To do this, we should do APB register writes to override
                     * the following PC bits:
                     * odt_static_dq=010
                     * odt_static_dqs=010
                     */
                    CFG_DDR_SGMII_PHY->rpc10_ODT.rpc10_ODT = 2U;
                    CFG_DDR_SGMII_PHY->rpc11_ODT.rpc11_ODT = 2U;
                    /*
                     * SAR 108218
                     * I've reviewed the results, and the ibufmd bit should be
                     * fixed in firmware for ibufmd_dqs. Malachy please have
                     * the firmware set this to 3'b100 for all cases except
                     * when we are in OFF mode (DDR3,DDR4,LPDDR3,LPDDR4).
                     */
                    CFG_DDR_SGMII_PHY->rpc98.rpc98 = 0x04U;
                    /*
                     *    SAR xxxx
                     *    bits 15:14 connect to ibufmx DQ/DQS/DM
                     *    bits 13:12 connect to ibufmx CA/CK
                     */
                    CFG_DDR_SGMII_PHY->UNUSED_SPACE0[0] = 0x0U;
                }
                break;
            case LPDDR4:
                {
                    /*
                     * We need to be able to implement different physical
                     * configurations of LPDDR4, given the twindie architecture.
                     * These are not fully decoded by the APB decoder (we dont
                     * have all the options).
                     * Basically we want to support:
                     * Hook the CA buses from the 2 die up in parallel on the
                     * same FPGA pins
                     * Hook the CA buses from the 2 die up in parallel using
                     * the mirrored FPGA pins (IE CA_A/CA_B)
                     * Some combination of the 2, ie duplicate the clocks but
                     * not the CA, duplicate the clocks and command, but not
                     * address, etc.
                     */
                    /* OVRT_EN_ADDCMD1 (default 0xF00), register named ovrt11 */
#ifndef LIBERO_SETTING_RPC_EN_ADDCMD0_OVRT9
                    /*
                     * If this define is not present, indicates older
                     * Libero core (pre 2.0.109)
                     * So we run this code
                     */
                    CFG_DDR_SGMII_PHY->ovrt10.ovrt10 =\
                            LIBERO_SETTING_RPC_EN_ADDCMD1_OVRT10;
                    {
                        /* Use pull-ups to set the CMD/ADD ODT */
                        CFG_DDR_SGMII_PHY->rpc245.rpc245 =\
                            0x00000000U;

                        CFG_DDR_SGMII_PHY->rpc237.rpc237 =\
                            0xffffffff;
                    }

                    /* OVRT_EN_ADDCMD2 (default 0xE06U), register named ovrt12 */
                    CFG_DDR_SGMII_PHY->ovrt11.ovrt11 =\
                            LIBERO_SETTING_RPC_EN_ADDCMD2_OVRT11;
#endif
                    /* Required when rank x 2 */
                    if ((LIBERO_SETTING_DDRPHY_MODE & DDRPHY_MODE_RANK_MASK) ==\
                            DDRPHY_MODE_TWO_RANKS)
                    {
                        /* todo: need to verify this setting with verification */
                        CFG_DDR_SGMII_PHY->spio253.spio253 = 1;
                    }

                    {
                        /*
                         * SAR 108218
                         * I've reviewed the results, and the ibufmd bit should be
                         * fixed in firmware for ibufmd_dqs. Malachy please have the
                         * firmware set this to 3'b100 for all cases except when we
                         * are in OFF mode (DDR3,DDR4,LPDDR3,LPDDR4).
                         */
                        CFG_DDR_SGMII_PHY->rpc98.rpc98 = 0x04U;
                    }
                    /*
                     *    SAR xxxx
                     *    bits 15:14 connect to ibufmx DQ/DQS/DM
                     *    bits 13:12 connect to ibufmx CA/CK
                     */
                    CFG_DDR_SGMII_PHY->UNUSED_SPACE0[0] =  0xA000U;

                }

                break;
        }
    }

    {

        /*
         * sar107009 found by Paul in Crevin,
         * This has been fixed in tag g5_mss_ddrphy_apb tag 2.9.130
         * todo: remove this software workaround as no longer required
         *
         * Default of rpc27 should be 2, currently is 0
         * We will set to 2 for the moment with software.
         */
        CFG_DDR_SGMII_PHY->rpc27.rpc27 = 0x2U;
        /*
         * Default of rpc27 Issue see by Paul/Alister 10th June
         * tb_top.duv_wrapper.u_design.mss_custom.gbank6.tip.gapb.\
         *                      MAIN.u_apb_mss_decoder_io.rpc203_spare_iog_dqsn
         */
        CFG_DDR_SGMII_PHY->rpc203.rpc203 = 0U;
    }

    {
        /*
         *
         * We'll have to pass that one in via E51, meaning APB writes to
         * addresses:
         * 0x2000 7384   rpc1_ODT       ODT_CA
         * 0x2000 7388   rpc2_ODT       RPC_ODT_CLK
         * 0x2000 738C   rpc3_ODT       ODT_DQ
         * 0x2000 7390   rpc4_ODT       ODT_DQS
         *
         * todo: replace with Libero settings below, once values verified
         */
        CFG_DDR_SGMII_PHY->rpc1_ODT.rpc1_ODT = LIBERO_SETTING_RPC_ODT_ADDCMD;
        CFG_DDR_SGMII_PHY->rpc2_ODT.rpc2_ODT = LIBERO_SETTING_RPC_ODT_CLK;
        CFG_DDR_SGMII_PHY->rpc3_ODT.rpc3_ODT = LIBERO_SETTING_RPC_ODT_DQ;
        CFG_DDR_SGMII_PHY->rpc4_ODT.rpc4_ODT = LIBERO_SETTING_RPC_ODT_DQS;
    }
    {
        /*
        * bclk_sel_clkn - selects bclk sclk training clock
        */
        CFG_DDR_SGMII_PHY->rpc19.rpc19 = 0x01U;     /* bclk_sel_clkn */
        /*
        * add cmd - selects bclk sclk training clock
        */
        CFG_DDR_SGMII_PHY->rpc20.rpc20 = 0x00U;     /* bclk_sel_clkp */

    }

    {
        /*
          *  Each lane has its own FIFO. This paramater adjusts offset for all lanes.
          */
#if (TUNE_RPC_166_VALUE == 1)
        CFG_DDR_SGMII_PHY->rpc166.rpc166 = rpc_166_fifo_offset;
#endif
    }

    /*
     *  Override RPC bits for weak PU and PD's
     *  Set over-ride bit for unused I/O
     */
    config_ddr_io_pull_up_downs_rpc_bits(ddr_type);
}

/**
  Info on OFF modes:

  OFF MODE from reset- I/O not being used
        MSSIO from reset- non default values
            Needs non default values to completely go completely OFF
            Drive bits and ibuff mode
            Ciaran to define what need to be done
              SAR107676
        DDR - by default put to DDR4 mode so needs active intervention
            Bills sac spec (DDR PHY SAC spec section 6.1)
            Mode register set to 7
            Ibuff mode set to 7 (rx turned off)
            P-Code/ N-code of no relevance as not used
            Disable DDR PLL
               Will be off from reset- no need
            Need to reflash
            DDR APB ( three resets - soft reset bit 0 to 1)
                Drive odt etc
       SGMII - from reset nothing to be done
           See Jeff's spread sheet- default values listed
           Extn clock off also defined in spread sheet
 */


/**
 *  ddr_off_mode(void)
 *  Assumed in Dynamic mode.
 *  i.e.
 *  SCB dynamic enable bit is high
 *  MSS core_up = 1
 *  dce[0,1,2] 0,0,0
 *  flash valid = 1
 *  IP:
 *  DECODER_DRIVER, ODT, IO all out of reset
 *
 *  DDR PHY off mode that I took from version 1.58 of the DDR SAC spec.
 *  1.  DDR PHY OFF mode (not used at all).
 *  1.  Set the DDR_MODE register to 7
 *  This will disable all the drive and ODT to 0, as well as set all WPU bits.
 *  2.  Set the RPC_IBUF_MD_* registers to 7
 *  This will disable all receivers.
 *  3.  Set the REG_POWERDOWN_B register to 0
 *  This will disable the DDR PLL
 *
 */
static void ddr_off_mode(void)
{
    /*
      * DDR PLL is not turn on on reset- so no need to do anything
      */
     /*
      * set the mode register to 7 => off mode
      * From the DDRPHY training firmware spec.:
      * If the DDR interface is unused, the firmware will have to write 3'b111
      * into the APB_DDR_MODE register. This will disable all the DRIVERs, ODT
      * and INPUT  receivers.
      * By default, WPD will be applied to all pads.
      *
      * If a user wants to apply WPU, this will have to be applied through
      * firmware, by changing all RPC_WPU_*=0, and RPC_WPD_*=1, via APB register
      * writes.
      *
      * Unused IO within an interface will automatically be shut off, as unused
      * DQ/DM/DQS/and CA buffers and odt are automatically disabled by the
      * decode, and put into WPD mode.
      * Again, if the user wants to change this to WPU, the will have to write
      * RPC_WPU_*=0 and RPC_WPD_*=1 to override the default.
      *
      */
     /* Note: DMI_DBI [8:1]   needs to be 0 (off) during training */
     CFG_DDR_SGMII_PHY->DDRPHY_MODE.DDRPHY_MODE  =\
             (LIBERO_SETTING_DDRPHY_MODE_OFF /* & DMI_DBI_MASK */);
     /*
      * VS for off mode
      */
     CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS        =\
             LIBERO_SETTING_DPC_BITS_OFF_MODE;

    /*
     * Toggle decoder here
     *  bit 0 == PERIPH   soft reset, auto cleared
     */
     CFG_DDR_SGMII_PHY->SOFT_RESET_DECODER_DRIVER.SOFT_RESET_DECODER_DRIVER= 1U;
     CFG_DDR_SGMII_PHY->SOFT_RESET_DECODER_ODT.SOFT_RESET_DECODER_ODT      = 1U;
     CFG_DDR_SGMII_PHY->SOFT_RESET_DECODER_IO.SOFT_RESET_DECODER_IO        = 1U;

     /*
      * set ibuff mode to 7 in off mode
      *
      */
     CFG_DDR_SGMII_PHY->rpc95.rpc95 = 0x07;     /* addcmd I/O*/
     CFG_DDR_SGMII_PHY->rpc96.rpc96 = 0x07;     /* clk */
     CFG_DDR_SGMII_PHY->rpc97.rpc97 = 0x07;     /* dq */
     CFG_DDR_SGMII_PHY->rpc98.rpc98 = 0x07;     /* dqs */

     /*
      * Default  WPU, modify If user wants Weak Pull Up
      */
     /*
      * UNUSED_SPACE0
      *     bits 15:14 connect to ibufmx DQ/DQS/DM
      *     bits 13:12 connect to ibufmx CA/CK
      *    todo: Do we need to add Pu/PD option for off mode to Libero setting?
      */
     CFG_DDR_SGMII_PHY->UNUSED_SPACE0[0] = 0x0000U;

    /*
     *  REG_POWERDOWN_B on PLL turn-off, in case was turned on.
     */
    ddr_pll_config_scb_turn_off();
    return;
}


/***************************************************************************//**
 * Number of tests which write and read from DDR
 * Tests data path through the cache and through AXI4 switch.
 */
#ifdef DDR_SANITY_CHECKS_EN
static uint8_t memory_tests(void)
{
    uint64_t shift_walking_one = 4U;
    uint64_t start_address = 0x0000000000000000U;
    uint8_t error = 0U;
    SIM_FEEDBACK1(199U);
    /*
     * Verify seg1 reg 2, datapath through AXI4 switch
     */
    while(shift_walking_one <= 28U) /* 28 => 1G, as 2**28 == 256K and this is
                                      mult by (4 lanes) */
    {
        SIM_FEEDBACK1(shift_walking_one);
        start_address = (uint64_t)(0xC0000000U + (0x1U<<shift_walking_one));
        error = rw_sanity_chk((uint64_t *)start_address , (uint32_t)0x5U);

        if(error)
        {
            ddr_error_count++;
            SIM_FEEDBACK1(200U);
        }
        shift_walking_one++;
    }
    SIM_FEEDBACK1(500U);
    /*
     * Verify seg1 reg 3, datapath through AXI4 switch
     */
    shift_walking_one = 4U;
    while(shift_walking_one <= 28U) //28 => 1G
    {
        SIM_FEEDBACK1(shift_walking_one);
        start_address = (uint64_t)(0x1400000000U + (0x1U<<shift_walking_one));
        error = rw_sanity_chk((uint64_t *)start_address , (uint32_t)0x5U);

        if(error)
        {
            ddr_error_count++;
            SIM_FEEDBACK1(208U);
        }

        /* check upper bound */
        if(shift_walking_one >= 4U)
        {
            start_address = (uint64_t)(0x1400000000U + \
                    (((0x1U<<(shift_walking_one +1)) - 1U) -0x0F) );
            error = rw_sanity_chk((uint64_t *)start_address , (uint32_t)0x5U);

            if(error)
            {
                ddr_error_count++;
                SIM_FEEDBACK1(201U);
            }
        }

        shift_walking_one++;
    }
    /*
     * Verify mtc
     */
    SIM_FEEDBACK1(600U);
    shift_walking_one = 4U;
    while(shift_walking_one <= 28U) //28 => 1G
    {
        SIM_FEEDBACK1(shift_walking_one);
        start_address = (uint64_t)(0x1U<<shift_walking_one);
        error = mtc_sanity_check(start_address);

        if(error)
        {
            ddr_error_count++;
            SIM_FEEDBACK1(203U);
        }

        /* check upper bound */
        if(shift_walking_one >= 4U)
        {
             start_address = (uint64_t)((((0x1U<<(shift_walking_one +1)) - 1U)\
                     -0x0F) );
             error = mtc_sanity_check(start_address);

             if(error)
             {
                 ddr_error_count++;
                 SIM_FEEDBACK1(204U);
             }
        }
        shift_walking_one++;
    }

    /*
     * Verify seg0 reg 0, datapath through cache
     */
    SIM_FEEDBACK1(700U);
    shift_walking_one = 4U;
    while(shift_walking_one <= 27U) //28 => 1G
    {
        SIM_FEEDBACK1(shift_walking_one);
        start_address = (uint64_t)(0x80000000U + (0x1U<<shift_walking_one));
        error = rw_sanity_chk((uint64_t *)start_address , (uint32_t)0x5U);

        if(error)
        {
            ddr_error_count++;
            SIM_FEEDBACK1(206U);
        }
        shift_walking_one++;
    }

    /*
     * Verify seg0 reg 1, datapath through cache,
     */
#if 0 /* issue with cache setup for 64 address width, need to checkout */
    SIM_FEEDBACK1(800U);
    shift_walking_one = 4U;
    while(shift_walking_one <= 28U)  //28 => 1G (0x10000000(address) * 4 (32bits wide))
    {
        SIM_FEEDBACK1(shift_walking_one);
        start_address = (uint64_t)(0x1000000000U + (0x1U<<shift_walking_one));
        error = rw_sanity_chk((uint64_t *)start_address , (uint32_t)0x5U);

        if(error)
        {
            ddr_error_count++;
            SIM_FEEDBACK1(207U);
        }

#if 0 /* this check will not work as written, need to look further into flushing
          cache as part of this test */
        /*
         * read back via axi switch datapath to make sure write through on
         * cache occurred
         */
        start_address = (uint64_t)(0x1400000000U + (0x1U<<shift_walking_one));
        error = read_back_sanity_check((uint64_t *)start_address , 0x5UL);

        if(error)
            ddr_error_count++;

        shift_walking_one++;
#endif
    }
#endif

    SIM_FEEDBACK1(299U);
    return (error);
}
#endif

/***************************************************************************//**
 * rw_sanity_chk()
 * writes and verifies reads back from DDR
 * Uses values defined in the test_string[]
 * @param address
 * @param count
 * @return non zero if error
 */
#ifdef DDR_SANITY_CHECKS_EN
static uint8_t rw_sanity_chk(uint64_t * address, uint32_t count)
{
    volatile uint64_t *DDR_word_ptr;
    uint64_t value;
    uint8_t error = 0U;
    /* DDR memory address from E51 - 0xC0000000 is non cache access */
    DDR_word_ptr =  address;

    volatile uint32_t i = 0x0U;

    /*
     * First fill
     */
    while(i < count)
    {
        *DDR_word_ptr = test_string[i & 0xfU];

        value = *DDR_word_ptr;

        if( value != test_string[i & 0xfU])
        {
            value = *DDR_word_ptr;
            if( value != test_string[i & 0xfU])
            {
                ddr_error_count++;
                error = 1;
            }
        }
        ++i;
        DDR_word_ptr = DDR_word_ptr + 1U;
    }
    /*
     * Recheck read, if first read successful
     */
    if(error == 0)
    {
        /* DDR memory address from E51 - 0xC0000000 is non cache access */
        DDR_word_ptr =  address;
        i = 0x0U;
        while(i < count)
        {
            if( *DDR_word_ptr != test_string[i & 0xfU])
            {
                ddr_error_count++;
                error = 1;
            }
            ++i;
            DDR_word_ptr = DDR_word_ptr + 1U;
        }
    }
    return error;
}
#endif

/***************************************************************************//**
 *
 * @param address
 * @param count
 * @return
 */
#if 0  /* todo: review, add in if required */
static uint8_t read_back_sanity_check(uint64_t * address, uint32_t count)
{
    volatile uint64_t *DDR_word_ptr;
    uint8_t error = 0U;
    DDR_word_ptr =  address;   /* DDR memory address from E51 - 0xC0000000 is
                                  non cache access */

    volatile uint32_t i = 0x0U;

    /*
     * Recheck read, if first read successful
     */
    if(error == 0)
    {
        DDR_word_ptr =  address;   /* DDR memory address from E51 - 0xC0000000
                                      is non cache access */
        i = 0x0U;
        while(i < count)
        {
            if( *DDR_word_ptr != test_string[i & 0xfU])
            {
                ddr_error_count++;
                error = 1;
            }
            ++i;
            DDR_word_ptr = DDR_word_ptr + 1U;
        }
    }
    return error;
}
#endif

/***************************************************************************//**
 * Memory test Core sanity check
 * @param start_address
 * @return non zero if error
 */
#ifdef DDR_SANITY_CHECKS_EN
static uint8_t mtc_sanity_check(uint64_t start_address)
{
    uint8_t result;
    uint64_t size = 4U;
    result = MTC_test((0xFU), start_address, size );
    return result;
}
#endif


/***************************************************************************//**
 *
 * load_dq(lane)
 *      set dyn_ovr_dlycnt_dq_load* = 0
 *      set expert_dfi_status_override_to_shim = 0x7
 *      set expert_mode_en = 0x21
 *      set dyn_ovr_dlycnt_dq_load* = 1
 *      set dyn_ovr_dlycnt_dq_load* = 0
 *      set expert_mode_en = 0x8
 *
 * @param lane
 */
static void load_dq(uint8_t lane)
{
    //set dyn_ovr_dlycnt_dq_load* = 0
    if(lane < 4U)
    {
        CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg0.expert_dlycnt_move_reg0 = 0U;
    }
    else
    {
        CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg1.expert_dlycnt_move_reg1 = \
            (CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg1.expert_dlycnt_move_reg1\
                                                & (uint32_t)~0x0FU);
    }
    //set expert_dfi_status_override_to_shim = 0x7
    CFG_DDR_SGMII_PHY->expert_dfi_status_override_to_shim.expert_dfi_status_override_to_shim = 0x07U;
    //set expert_mode_en = 0x21
    CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0x21U;
    //set dyn_ovr_dlycnt_dq_load* = 1
    if(lane < 4U)
    {
        CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg0.expert_dlycnt_load_reg0 =\
                (0xFFU << (lane * 8U));
    }
    else
    {
        CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1 |=\
                0x0FU;
    }
    //set dyn_ovr_dlycnt_dq_load* = 0
    CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg0.expert_dlycnt_load_reg0 = 0U;
    if(lane < 4U)
    {
        CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg0.expert_dlycnt_load_reg0 = 0U;
    }
    else
    {
        CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1 = \
            (CFG_DDR_SGMII_PHY->expert_dlycnt_load_reg1.expert_dlycnt_load_reg1\
                                                             & (uint32_t)~0x0FU);
    }
    //set expert_mode_en = 0x8
    CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0x8U;
}

/***************************************************************************//**
 *  increment_dq()
 *     set dyn_ovr_dlycnt_dq_move* = 0
 *     set dyn_ovr_dlycnt_dq_direction* = 1
 *     set expert_dfi_status_override_to_shim = 0x7
 *     set expert_mode_en = 0x21
 *
 *     #to increment multiple times loop the move=0/1 multiple times
 *     set dyn_ovr_dlycnt_dq_move* = 1
 *     set dyn_ovr_dlycnt_dq_move* = 0
 *     #
 *     set expert_mode_en = 0x8
 * @param lane
 * @param move_count
 */
#ifdef SW_CONFIG_LPDDR_WR_CALIB_FN
static void increment_dq(uint8_t lane, uint32_t move_count)
{
    //set dyn_ovr_dlycnt_dq_move* = 0
    if(lane < 4U)
    {
        CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg0.expert_dlycnt_move_reg0 = 0U;
    }
    else
    {
        CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg1.expert_dlycnt_move_reg1 = \
           (CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg1.expert_dlycnt_move_reg1\
                   & ~0x0FU);
    }
    //set dyn_ovr_dlycnt_dq_direction* = 1
    if(lane < 4U)
    {
        CFG_DDR_SGMII_PHY->expert_dlycnt_direction_reg0.expert_dlycnt_direction_reg0\
            = (0xFFU << (lane * 8U));
    }
    else
    {
        /* only four lines, use 0xFU */
        CFG_DDR_SGMII_PHY->expert_dlycnt_direction_reg1.expert_dlycnt_direction_reg1 |= 0xFU;
    }
    /*   set expert_dfi_status_override_to_shim = 0x7 */
    CFG_DDR_SGMII_PHY->expert_dfi_status_override_to_shim.expert_dfi_status_override_to_shim = 0x07U;
    /*  set expert_mode_en = 0x21 */
    CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0x21U;
    /*  #to increment multiple times loop the move=0/1 multiple times */
    move_count = move_count + move_count + move_count;
    while(move_count)
    {
        //   set dyn_ovr_dlycnt_dq_move* = 1
        if(lane < 4U)
        {
            CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg0.expert_dlycnt_move_reg0\
                = (0xFFU << (lane * 8U));
        }
        else
        {
            CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg1.expert_dlycnt_move_reg1\
                |= 0x0FU;
        }
        //   set dyn_ovr_dlycnt_dq_move* = 0
        CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg0.expert_dlycnt_move_reg0 = 0U;
        if(lane < 4U)
        {
            CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg0.expert_dlycnt_move_reg0\
                = 0U;
        }
        else
        {
            CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg1.expert_dlycnt_move_reg1 = \
                    (CFG_DDR_SGMII_PHY->expert_dlycnt_move_reg1.expert_dlycnt_move_reg1 & ~0x0FU);
        }
        move_count--;
    }
   /* set expert_mode_en = 0x8 */
   CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0x8U;
}
#endif

/***************************************************************************//**
 *
 */
static void set_write_calib(uint8_t user_lanes)
{
    uint32_t temp = 0U;
    uint8_t lane_to_set;
    uint8_t shift = 0U;

    /*
     * Calculate the calibrated value and write back
     */
    calib_data.write_cal.lane_calib_result = 0U;
    for (lane_to_set = 0x00U;\
        lane_to_set<user_lanes /*USER_TOTAL_LANES_USED */; lane_to_set++)
    {
        temp = calib_data.write_cal.lower[lane_to_set];
        calib_data.write_cal.lane_calib_result =   \
                calib_data.write_cal.lane_calib_result | (temp << (shift));
        shift = (uint8_t)(shift + 0x04U);
    }

    /*
     * bit 3  must be set if we want to use the
     * expert_wrcalib
     * register
     */
    CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0x00000008U;

    SIM_FEEDBACK1(0xFF000000);
    SIM_FEEDBACK1(calib_data.write_cal.lane_calib_result);
    SIM_FEEDBACK1(0xFF000000);

    /* set the calibrated value */
    CFG_DDR_SGMII_PHY->expert_wrcalib.expert_wrcalib =\
            calib_data.write_cal.lane_calib_result;
}

/***************************************************************************//**
 *
 * @param lane_to_set
 */
#ifdef SW_CONFIG_LPDDR_WR_CALIB_FN
static void set_calc_dq_delay_offset(uint8_t lane_to_set)
{
    uint32_t move_count;

    load_dq(lane_to_set); /* set to start */

    /* shift by 1 to divide by two */
    move_count = ((calib_data.dq_cal.upper[lane_to_set] -\
            calib_data.dq_cal.lower[lane_to_set]  ) >> 1U) +\
            calib_data.dq_cal.lower[lane_to_set];

    increment_dq(lane_to_set, move_count);

}
#endif

/***************************************************************************//**
 *
 *  @param user_lanes
 */
#ifdef SW_CONFIG_LPDDR_WR_CALIB_FN
static void set_calib_values(uint8_t user_lanes)
{
    uint8_t lane_to_set;
    uint32_t move_count;

    for (lane_to_set = 0x00U;\
        lane_to_set< user_lanes ; lane_to_set++)
    {
        set_calc_dq_delay_offset(lane_to_set);
    }

    /* and set the write calibration calculated */
    set_write_calib(user_lanes);
}
#endif


/***************************************************************************//**
 * write_calibration_using_mtc
 *   Use Memory Test Core plugged in to the front end of the DDR controller to
 *   perform lane-based writes and read backs and increment write calibration
 *   offset for each lane until data match occurs. The Memory Test Core is the
 *   basis for all training.
 *
 * @param number_of_lanes_to_calibrate
 * @return
 */
static uint8_t \
    write_calibration_using_mtc(uint8_t number_of_lanes_to_calibrate)
{
    uint8_t laneToTest;
    uint32_t result = 0U;
    uint32_t cal_data;
    uint64_t start_address = 0x0000000000000000ULL;
    uint32_t size = ONE_MB_MTC;  /* Number of reads for each iteration 2**size*/

    calib_data.write_cal.status_lower = 0U;
    /*
     * bit 3  must be set if we want to use the
     * expert_wrcalib
     * register
     */
    CFG_DDR_SGMII_PHY->expert_mode_en.expert_mode_en = 0x00000008U;

    /*
     * training carried out here- sweeping write calibration offset from 0 to F
     * Explanation: A register, expert_wrcalib, is described in MSS DDR TIP
     * Register Map [1], and its purpose is to delay--by X number of memory clock
     * cycles--the write data, write data mask, and write output enable with the
     * respect to the address and command for each lane.
     */
    for (cal_data=0x00000U;cal_data<0xfffffU;cal_data=cal_data+0x11111U)
    {
#ifdef DEBUG_DDR_INIT
        (void)uprint32(g_debug_uart, "\n\rCalibration offset used:",cal_data &0xFUL);
#endif
        CFG_DDR_SGMII_PHY->expert_wrcalib.expert_wrcalib = cal_data;

        for (laneToTest = 0x00U; laneToTest<number_of_lanes_to_calibrate;\
                                                                laneToTest++)
        {
            /*
             * read once to flush MTC. During write calibration the first MTC read
             * must be discarded as it is unreliable after a series of bad writes.
             */
            uint8_t mask = (uint8_t)(1U<<laneToTest);
            result = MTC_test(mask, start_address, size, MTC_COUNTING_PATTERN, MTC_ADD_SEQUENTIAL, &result);
            /* Read using different patterns */
            result |= MTC_test(mask, start_address, size, MTC_COUNTING_PATTERN, MTC_ADD_SEQUENTIAL, &result);
            result |= MTC_test(mask, start_address, size, MTC_WALKING_ONE, MTC_ADD_SEQUENTIAL, &result);
            result |= MTC_test(mask, start_address, size, MTC_PSEUDO_RANDOM, MTC_ADD_SEQUENTIAL, &result);
            result |= MTC_test(mask, start_address, size, MTC_NO_REPEATING_PSEUDO_RANDOM, MTC_ADD_SEQUENTIAL, &result);
            result |= MTC_test(mask, start_address, size, MTC_ALT_ONES_ZEROS, MTC_ADD_SEQUENTIAL, &result);
            result |= MTC_test(mask, start_address, size, MTC_ALT_5_A, MTC_ADD_SEQUENTIAL, &result);
            result |= MTC_test(mask, start_address, size, MTC_PSEUDO_RANDOM_16BIT, MTC_ADD_SEQUENTIAL, &result);
            result |= MTC_test(mask, start_address, size, MTC_PSEUDO_RANDOM_8BIT, MTC_ADD_SEQUENTIAL, &result);

            if(result == 0U) /* if passed for this lane */
            {
                if((calib_data.write_cal.status_lower & (0x01U<<laneToTest)) \
                                    == 0U) /* Still looking for good value */
                {
                    calib_data.write_cal.lower[laneToTest]  = (cal_data & 0xFU);
                    calib_data.write_cal.status_lower |= (0x01U<<laneToTest);
                }
                /*
                 * Check the result
                 */
#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, "\n\rLane passed:",laneToTest);
                (void)uprint32(g_debug_uart, " All lanes status:",calib_data.write_cal.status_lower);
#endif
                uint32_t laneToCheck;
                for (laneToCheck = 0x00U;\
                    laneToCheck<number_of_lanes_to_calibrate; laneToCheck++)
                {
                    if(((calib_data.write_cal.status_lower) &\
                            (0x01U<<laneToCheck)) == 0U)
                    {
                        result = 1U; /* not finished, still looking */
                        break;
                    }
                }
                if(result == 0U) /* if true, we are good for all lanes, can stop
                                    looking */
                {
                    SIM_FEEDBACK1(0xF7000000);
                    break;
                }
            }
            else
            {
#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, "\n\rLane failed:",laneToTest);
                (void)uprint32(g_debug_uart, " All lanes status:",calib_data.write_cal.status_lower);
#endif
            }

        } /* end laneToTest */
        if(result == 0U) /* if true, we are good for all lanes, can stop */
        {                /* looking */
            SIM_FEEDBACK1(0xF8000000);
            break;
        }
    }  /* end cal_data */

    SIM_FEEDBACK1(0x01000000);
    SIM_FEEDBACK1(calib_data.write_cal.lower[0]);
    SIM_FEEDBACK1(0x02000000);
    SIM_FEEDBACK1(calib_data.write_cal.lower[1]);
    SIM_FEEDBACK1(0x03000000);
    SIM_FEEDBACK1(calib_data.write_cal.lower[2]);
    SIM_FEEDBACK1(0x04000000);
    SIM_FEEDBACK1(calib_data.write_cal.lower[3]);
    SIM_FEEDBACK1(0x05000000);
    SIM_FEEDBACK1(calib_data.write_cal.lower[4]);
    SIM_FEEDBACK1(0x06000000);
    SIM_FEEDBACK1(calib_data.write_cal.lower[5]);
    SIM_FEEDBACK1(0x07000000);

    /* if calibration successful, calculate and set the value */
    if(result == 0U)
    {
        /* and set the write calibration which has been calculated */
        set_write_calib(number_of_lanes_to_calibrate);
    }

    SIM_FEEDBACK1(0x08000000);
    SIM_FEEDBACK1(result);
    SIM_FEEDBACK1(0x08000000);
    return result;
}


/**
 * MODE register write
 * @param MR_ADDR
 * @param MR_DATA
 * @return fail/pass
 */
#ifdef SET_VREF_LPDDR4_MODE_REGS
static uint8_t mode_register_write(uint32_t MR_ADDR, uint32_t MR_DATA)
{
    uint32_t test = 0xFFFFU;
    uint32_t result = 0U;
    /*
    *
    */
    //DDRCFG->MC_BASE2.INIT_MRR_MODE.INIT_MRR_MODE        = 0x01;
    DDRCFG->MC_BASE2.INIT_MR_ADDR.INIT_MR_ADDR          = MR_ADDR ;
    /*
    * next:
    * write desired VREF calibration range (0=Range 1, 1=Range 2) to bit 6
    * of MR6
    * write 0x00 to bits 5:0 of MR6 (base calibration value)
    */
    DDRCFG->MC_BASE2.INIT_MR_WR_DATA.INIT_MR_WR_DATA    = MR_DATA;
    DDRCFG->MC_BASE2.INIT_MR_WR_MASK.INIT_MR_WR_MASK = 0U;

    DDRCFG->MC_BASE2.INIT_MR_W_REQ.INIT_MR_W_REQ    = 0x01U;
    while((DDRCFG->MC_BASE2.INIT_ACK.INIT_ACK & 0x01U) == 0U) /* wait for ack-
                                          to confirm register is written */
    {
       test--;
       if(test-- == 0U)
       {
           result = 1U;
           break;
       }
    }
    return result;
}
#endif

#define VREF_INVALID 0x01U
/***************************************************************************//**
 * FPGA_VREFDQ_calibration_using_mtc(void)
 * vary DQ voltage and set optimum DQ voltage
 * @return
 */
#ifdef VREFDQ_CALIB
            /*
             * This step is optional
             * todo: Test once initial board verification complete
             */
static uint8_t FPGA_VREFDQ_calibration_using_mtc(void)
{
    uint8_t laneToTest, result = 0U;
    uint64_t mask;
    uint32_t vRef;
    uint64_t start_address = 0x0000000000000000ULL;
    uint64_t size = 4U;

    /*
    * Step 2a. FPGA VREF (Local VREF training)
    * Train FPGA VREF using the vrgen_h and vrgen_v registers
    */
    {
    /*
     * To manipulate the FPGA VREF value, firmware must write to the
     * DPC_BITS register, located at physical address 0x2000 7184.
     * Full documentation for this register can be found in
     * DFICFG Register Map [4].
     */
    /*
     * See DPC_BITS definition in .h file
     */
    /* CFG_DDR_SGMII_PHY->DPC_BITS.bitfield.dpc_vrgen_h; */
    /* CFG_DDR_SGMII_PHY->DPC_BITS.bitfield.dpc_vrgen_v; */

    }

    /*
    * training carried out here- sweeping write calibration offset from 0 to F
    * Explanation: A register, expert_wrcalib, is described in MSS DDR TIP
    * Register Map [1], and its purpose is to delay--by X number of memory
    * clock cycles--the write data, write data mask, and write output enable
    * with the respect to the address and command for each lane.
    */
    calib_data.fpga_vref.vref_result = 0U;
    calib_data.fpga_vref.lower = VREF_INVALID;
    calib_data.fpga_vref.upper = VREF_INVALID;
    calib_data.fpga_vref.status_lower = 0x00U;
    calib_data.fpga_vref.status_upper = 0x00U;
    mask = 0xFU;        /* todo: obtain data width from user parameters */
    uint32_t count = 0U;
    /* each bit .25% of VDD ?? */
    for (vRef=(0x1U<<4U);vRef<(0x1fU<<4U);vRef=vRef+(0x1U<<4U))
    {
        /*
            CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS =\
                          (CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS & (~(0x1U<<10U)));
            CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS =\
                  (CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS & (~(0x1fU<<4U))) | vRef;
        */
        /* need to set via the SCB, otherwise reset required. So lines below
         * rather than above used */

        IOSCB_BANKCONT_DDR->dpc_bits = (IOSCB_BANKCONT_DDR->dpc_bits &\
                (~(0x1U<<10U)));
        IOSCB_BANKCONT_DDR->dpc_bits = (IOSCB_BANKCONT_DDR->dpc_bits &\
                (~(0x1fU<<4U))) | vRef;


        /* read one to flush MTC -  this is required */
        result = MTC_test(1U<<laneToTest, start_address, size);
        /* Read twice, two different patterns will be used */
        result = MTC_test(1U<<laneToTest, start_address, size);
        result |= MTC_test(1U<<laneToTest, start_address, size);
        if((result == 0U)&&(calib_data.fpga_vref.lower == VREF_INVALID))
        {
            calib_data.fpga_vref.lower = vRef;
            calib_data.fpga_vref.upper = vRef;
            calib_data.fpga_vref.status_lower = 0x01;
        }
        else if((result == 0U)&&(calib_data.fpga_vref.lower != VREF_INVALID))
        {
            calib_data.fpga_vref.upper = vRef;
            calib_data.fpga_vref.status_upper = 0x01;
        }
        else if(calib_data.fpga_vref.upper != VREF_INVALID)
        {
            break; /* we are finished */
        }
        else
        {
            /* nothing to do */
        }
    }

    if(calib_data.fpga_vref.upper != VREF_INVALID) /* we found lower/upper */
    {
        /*
         * now set vref
         * calculate optimal VREF calibration value =
         *                              (left side + right side) / 2
         * */
        vRef = ((calib_data.fpga_vref.lower + calib_data.fpga_vref.upper)>>1U);
        CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS =\
                (CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS & (0x1fU<<4U)) | vRef;
        /* need to set via the SCB, otherwise reset required. */
        IOSCB_BANKCONT_DDR->dpc_bits = (IOSCB_BANKCONT_DDR->dpc_bits &\
                (0x1fU<<4U)) | vRef;
    }
    else
    {
        result = 1U; /* failed to get good data at any voltage level */
    }

  return result;
}

#endif

#ifdef VREFDQ_CALIB
            /*
             * This step is optional
             * todo: Test once initial board verification complete
             */
#define MEM_VREF_INVALID 0xFFFFFFFFU
/***************************************************************************//**
 *
 * VREFDQ_calibration_using_mtc
 * In order to write to mode registers, the E51 must use the INIT_* interface
 * at the front end of the DDR controller,
 * which is available via a series of control registers described in the DDR
 * CSR APB Register Map.
 *
 * @return
 */
static uint8_t VREFDQ_calibration_using_mtc(void)
{
    uint8_t laneToTest, result = 0U;
    uint64_t mask;
    uint32_t vRef;
    uint64_t start_address = 0x00000000C0000000ULL;
    uint64_t size = 4U;

    /*
    * Step 2a. FPGA VREF (Local VREF training)
    * Train FPGA VREF using the vrgen_h and vrgen_v registers
    */
    {
        /*
         *
         */
        DDRCFG->MC_BASE2.INIT_MRR_MODE.INIT_MRR_MODE    = 0x01U;
        DDRCFG->MC_BASE2.INIT_MR_ADDR.INIT_MR_ADDR      = 6U ;
        /*
         * next:
         * write desired VREF calibration range (0=Range 1, 1=Range 2) to bit 6
         * of MR6
         * write 0x00 to bits 5:0 of MR6 (base calibration value)
         */
        DDRCFG->MC_BASE2.INIT_MR_WR_DATA.INIT_MR_WR_DATA  = 0U;
        DDRCFG->MC_BASE2.INIT_MR_WR_MASK.INIT_MR_WR_MASK = (0x01U <<6U) |\
                (0x3FU) ;

        DDRCFG->MC_BASE2.INIT_MR_W_REQ.INIT_MR_W_REQ   = 0x01U;
        if((DDRCFG->MC_BASE2.INIT_ACK.INIT_ACK & 0x01U) == 0U) /* wait for ack-
                                               to confirm register is written */
        {

        }
    }

    /*
    * training carried out here- sweeping write calibration offset from 0 to F
    * Explanation: A register, expert_wrcalib, is described in MSS DDR TIP
    * Register Map [1], and its purpose is to delay--by X number of memory clock
    * cycles--the write data, write data mask, and write output enable with the
    * respect to the address and command for each lane.
    */
    calib_data.mem_vref.vref_result = 0U;
    calib_data.mem_vref.lower = MEM_VREF_INVALID;
    calib_data.mem_vref.upper = MEM_VREF_INVALID;
    calib_data.mem_vref.status_lower = 0x00U;
    calib_data.mem_vref.status_upper = 0x00U;
    mask = 0xFU;    /* todo: obtain data width from user paramaters */

    for (vRef=(0x1U<<4U);vRef<0x3fU;vRef=(vRef+0x1U))
    {
        /*
        * We change the value in the RPC register, but we will lso need to
        * change SCB as will not be reflected without a soft reset
        */
        CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS =\
            (CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS & (0x1fU<<4U)) | vRef;
        /* need to set via the SCB, otherwise reset required. */
        IOSCB_BANKCONT_DDR->dpc_bits = (IOSCB_BANKCONT_DDR->dpc_bits\
            & (0x1fU<<4U)) | vRef;

        /* read one to flush MTC -  this is required */
        result = MTC_test(1U<<laneToTest, start_address, size);
        /* Read twice, two different patterns will be used */
        result = MTC_test(1U<<laneToTest, start_address, size);
        result |= MTC_test(1U<<laneToTest, start_address, size);
        if((result == 0U)&&(calib_data.mem_vref.lower == MEM_VREF_INVALID))
        {
            calib_data.mem_vref.lower = vRef;
            calib_data.mem_vref.upper = vRef;
            calib_data.mem_vref.status_lower = 0x01;
        }
        else if((result == 0U)&&(calib_data.mem_vref.lower != MEM_VREF_INVALID))
        {
            calib_data.mem_vref.upper = vRef;
            calib_data.mem_vref.status_lower = 0x01;
        }
        else if(calib_data.mem_vref.upper != MEM_VREF_INVALID)
        {
            break; /* we are finished */
        }
        else
        {
            /* continue */
        }

    }

    if(calib_data.mem_vref.upper != MEM_VREF_INVALID) /* we found lower/upper */
    {
        /*
        * now set vref
        * calculate optimal VREF calibration value =
        *                                    (left side + right side) / 2
        * */
        vRef = ((calib_data.mem_vref.lower + calib_data.mem_vref.lower)>1U);
        CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS =\
            (CFG_DDR_SGMII_PHY->DPC_BITS.DPC_BITS & (0x1fU<<4U)) | vRef;
        /* need to set via the SCB, otherwise reset required. */
        IOSCB_BANKCONT_DDR->dpc_bits = (IOSCB_BANKCONT_DDR->dpc_bits & (0x1fU<<4U)) | vRef;
    }
    else
    {
        result = 1U; /* failed to get good data at any voltage level */
    }

    return result;
    }
#endif

/***************************************************************************//**
 * MTC_test
 * test memory using the NWL memory test core
 * There are numerous options
 * todo: Add user input as to option to use?
 * @param laneToTest
 * @param mask0
 * @param mask1   some lane less DQ as only used for parity
 * @param start_address
 * @param size = x, where x is used as power of two 2**x e.g. 256K => x == 18
 * @return pass/fail
 */
static uint8_t MTC_test(uint8_t mask, uint64_t start_address, uint32_t size, MTC_PATTERN data_pattern, MTC_ADD_PATTERN add_pattern, uint32_t *error)
{
    if((*error & MTC_TIMEOUT_ERROR) == MTC_TIMEOUT_ERROR)
    {
        return (uint8_t)*error;
    }
    /* Write Calibration - first configure memory test */
    {
        /*
         *  write calibration
         *  configure common memory test interface by writing registers:
         *  MT_STOP_ON_ERROR, MT_DATA_PATTERN, MT_ADDR_PATTERN, MT_ADDR_BITS
         */
        /* see MTC user guide */
        DDRCFG->MEM_TEST.MT_STOP_ON_ERROR.MT_STOP_ON_ERROR = 0U;
        /* make sure off, will turn on later. */
        DDRCFG->MEM_TEST.MT_EN_SINGLE.MT_EN_SINGLE = 0x00U;
        /*
         * MT_DATA_PATTERN
         *
         * 0x00 => Counting pattern
         * 0x01 => walking 1's
         * 0x02 => pseudo random
         * 0x03 => no repeating pseudo random
         * 0x04 => alt 1's and 0's
         * 0x05 => alt 5's and A's
         * 0x06 => User specified
         * 0x07 => pseudo random 16-bit
         * 0x08 => pseudo random 8-bit
         * 0x09- 0x0f reserved
         *
         */
        {
            /*
            * Added changing pattern so write pattern is different, read back
            * can not pass on previously written data
            */
            DDRCFG->MEM_TEST.MT_DATA_PATTERN.MT_DATA_PATTERN = data_pattern;
        }
        if(add_pattern == MTC_ADD_RANDOM)
        {
            /*
             * MT_ADDR_PATTERN
             * 0x00 => Count in pattern
             * 0x01 => Pseudo Random Pattern
             * 0x02 => Arbiatry Pattern Gen (user defined ) - Using RAMS
             */
            DDRCFG->MEM_TEST.MT_ADDR_PATTERN.MT_ADDR_PATTERN = 1U;
        }
        else
        {
            DDRCFG->MEM_TEST.MT_ADDR_PATTERN.MT_ADDR_PATTERN = 0U;
        }
    }

    if(add_pattern != MTC_ADD_RANDOM)
    {
        /*
         * Set the starting address and number to test
         *
         * MT_START_ADDR
         *   Starting address
         * MT_ADRESS_BITS
         *   Length to test = 2 ** MT_ADRESS_BITS
         */
        DDRCFG->MEM_TEST.MT_START_ADDR_0.MT_START_ADDR_0   =\
                (uint32_t)(start_address & 0xFFFFFFFFUL);
        /* The address here is as see from DDR controller => start at 0x0*/
        DDRCFG->MEM_TEST.MT_START_ADDR_1.MT_START_ADDR_1   =\
                (uint32_t)((start_address >> 32U));
    }
    else
    {
        DDRCFG->MEM_TEST.MT_START_ADDR_0.MT_START_ADDR_0   = 0U;
        DDRCFG->MEM_TEST.MT_START_ADDR_1.MT_START_ADDR_1   = 0U;
    }
    DDRCFG->MEM_TEST.MT_ADDR_BITS.MT_ADDR_BITS        =\
            size; /* 2 power 24 => 256k to do- make user programmable */

    {
    /*
    * FOR each DQ lane
    *  set error mask registers MT_ERROR_MASK_* to mask out
    *    all error bits but the ones for the current DQ lane
    *    WHILE timeout counter is less than a threshold
    *        perform memory test by writing MT_EN or MT_EN_SINGLE
    *        wait for memory test completion by polling MT_DONE_ACK
    *        read back memory test error status from MT_ERROR_STS
    *       IF no error detected
    *          exit loop
    *        ELSE
    *          increment write calibration offset for current DQ lane
    *          by writing EXPERT_WRCALIB
    *    ENDWHILE
    *  ENDFOR
    */
    {
    /*
    * MT_ERROR_MASK
    * All bits set in this field mask corresponding bits in data fields
    * i.e. mt_error and mt_error_hold will not be set for errors in
    * those fields
    *
    * Structure of 144 bits same as DFI bus
    * 36 bits per lane ( 8 physical * 4) + (1ECC * 4) = 36
    *
    * If we wrote out the following pattern from software:
    * 0x12345678
    * 0x87654321
    * 0x56789876
    * 0x43211234
    * We should see:
    *      NNNN_YXXX_XXX3_4YXX_XXXX_76YX_XXXX_X21Y_XXXX_XX78
    *      N: not used
    *      Y:
    */
        DDRCFG->MEM_TEST.MT_ERROR_MASK_0.MT_ERROR_MASK_0 = 0xFFFFFFFFU;
        DDRCFG->MEM_TEST.MT_ERROR_MASK_1.MT_ERROR_MASK_1 = 0xFFFFFFFFU;
        DDRCFG->MEM_TEST.MT_ERROR_MASK_2.MT_ERROR_MASK_2 = 0xFFFFFFFFU;
        DDRCFG->MEM_TEST.MT_ERROR_MASK_3.MT_ERROR_MASK_3 = 0xFFFFFFFFU;
        DDRCFG->MEM_TEST.MT_ERROR_MASK_4.MT_ERROR_MASK_4 = 0xFFFFFFFFU;

        if (mask & 0x1U)
        {
            DDRCFG->MEM_TEST.MT_ERROR_MASK_0.MT_ERROR_MASK_0 &= 0xFFFFFF00U;
                DDRCFG->MEM_TEST.MT_ERROR_MASK_1.MT_ERROR_MASK_1 &= 0xFFFFF00FU;
                DDRCFG->MEM_TEST.MT_ERROR_MASK_2.MT_ERROR_MASK_2 &= 0xFFFF00FFU;
                DDRCFG->MEM_TEST.MT_ERROR_MASK_3.MT_ERROR_MASK_3 &= 0xFFF00FFFU;
                DDRCFG->MEM_TEST.MT_ERROR_MASK_4.MT_ERROR_MASK_4 &= 0xFFFFFFFFU;
        }
        if (mask & 0x2U)
        {
            DDRCFG->MEM_TEST.MT_ERROR_MASK_0.MT_ERROR_MASK_0 &= 0xFFFF00FFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_1.MT_ERROR_MASK_1 &= 0xFFF00FFFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_2.MT_ERROR_MASK_2 &= 0xFF00FFFFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_3.MT_ERROR_MASK_3 &= 0xF00FFFFFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_4.MT_ERROR_MASK_4 &= 0xFFFFFFFFU;
        }
        if (mask & 0x4U)
        {
            DDRCFG->MEM_TEST.MT_ERROR_MASK_0.MT_ERROR_MASK_0 &= 0xFF00FFFFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_1.MT_ERROR_MASK_1 &= 0xF00FFFFFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_2.MT_ERROR_MASK_2 &= 0x00FFFFFFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_3.MT_ERROR_MASK_3 &= 0x0FFFFFFFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_4.MT_ERROR_MASK_4 &= 0xFFFFFFF0U;
        }
        if (mask & 0x8U)
        {
            DDRCFG->MEM_TEST.MT_ERROR_MASK_0.MT_ERROR_MASK_0 &= 0x00FFFFFFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_1.MT_ERROR_MASK_1 &= 0x0FFFFFFFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_2.MT_ERROR_MASK_2 &= 0xFFFFFFF0U;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_3.MT_ERROR_MASK_3 &= 0xFFFFFF00U;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_4.MT_ERROR_MASK_4 &= 0xFFFFF00FU;
        }
        if (mask & 0x10U)
        {
            DDRCFG->MEM_TEST.MT_ERROR_MASK_0.MT_ERROR_MASK_0 &= 0xFFFFFFFFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_1.MT_ERROR_MASK_1 &= 0xFFFFFFF0U;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_2.MT_ERROR_MASK_2 &= 0xFFFFFF0FU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_3.MT_ERROR_MASK_3 &= 0xFFFFF0FFU;
            DDRCFG->MEM_TEST.MT_ERROR_MASK_4.MT_ERROR_MASK_4 &= 0xFFFF0FFFU;
        }

        /*
        * MT_EN
        * Enables memory test
        * If asserted at end of memory test, will keep going
        */
        DDRCFG->MEM_TEST.MT_EN.MT_EN = 0U;
        /*
        * MT_EN_SINGLE
        * Will not repeat if this is set
        */
        DDRCFG->MEM_TEST.MT_EN_SINGLE.MT_EN_SINGLE = 0x00U;
        DDRCFG->MEM_TEST.MT_EN_SINGLE.MT_EN_SINGLE = 0x01U;
        /*
        * MT_DONE_ACK
        * Set when test completes
        */
        volatile uint64_t something_to_do = 0U;
        #ifndef UNITTEST
        while (( DDRCFG->MEM_TEST.MT_DONE_ACK.MT_DONE_ACK & 0x01U) == 0U)
        {
            something_to_do++;
            if(something_to_do > 0xFFFFFFUL)
            {
#ifdef DEBUG_DDR_INIT
                (void)uprint32(g_debug_uart, "\n\rmtc test error:",MTC_TIMEOUT_ERROR);
#endif
                return (MTC_TIMEOUT_ERROR);
            }
            #ifdef RENODE_DEBUG
            break;
            #endif
        }
        #endif
        }
    }
    /*
    * MT_ERROR_STS
    * Return the error status
    * todo:Check NWL data and detail error states here
    */

    return (DDRCFG->MEM_TEST.MT_ERROR_STS.MT_ERROR_STS & 0x01U);

}


/***************************************************************************//**
 * Setup DDRC
 * These settings come from config tool
 *
 */
#define _USE_SETTINGS_USED_IN_DDR3_FULL_CHIP_TEST

static void init_ddrc(void)
{
    DDRCFG->ADDR_MAP.CFG_MANUAL_ADDRESS_MAP.CFG_MANUAL_ADDRESS_MAP =\
        LIBERO_SETTING_CFG_MANUAL_ADDRESS_MAP;
    DDRCFG->ADDR_MAP.CFG_CHIPADDR_MAP.CFG_CHIPADDR_MAP =\
        LIBERO_SETTING_CFG_CHIPADDR_MAP;
    DDRCFG->ADDR_MAP.CFG_CIDADDR_MAP.CFG_CIDADDR_MAP =\
        LIBERO_SETTING_CFG_CIDADDR_MAP;
    DDRCFG->ADDR_MAP.CFG_MB_AUTOPCH_COL_BIT_POS_LOW.CFG_MB_AUTOPCH_COL_BIT_POS_LOW =\
        LIBERO_SETTING_CFG_MB_AUTOPCH_COL_BIT_POS_LOW;
    DDRCFG->ADDR_MAP.CFG_MB_AUTOPCH_COL_BIT_POS_HIGH.CFG_MB_AUTOPCH_COL_BIT_POS_HIGH =\
        LIBERO_SETTING_CFG_MB_AUTOPCH_COL_BIT_POS_HIGH;
    DDRCFG->ADDR_MAP.CFG_BANKADDR_MAP_0.CFG_BANKADDR_MAP_0 =\
        LIBERO_SETTING_CFG_BANKADDR_MAP_0;
    DDRCFG->ADDR_MAP.CFG_BANKADDR_MAP_1.CFG_BANKADDR_MAP_1 =\
        LIBERO_SETTING_CFG_BANKADDR_MAP_1;
    DDRCFG->ADDR_MAP.CFG_ROWADDR_MAP_0.CFG_ROWADDR_MAP_0 =\
        LIBERO_SETTING_CFG_ROWADDR_MAP_0;
    DDRCFG->ADDR_MAP.CFG_ROWADDR_MAP_1.CFG_ROWADDR_MAP_1 =\
        LIBERO_SETTING_CFG_ROWADDR_MAP_1;
    DDRCFG->ADDR_MAP.CFG_ROWADDR_MAP_2.CFG_ROWADDR_MAP_2 =\
        LIBERO_SETTING_CFG_ROWADDR_MAP_2;
    DDRCFG->ADDR_MAP.CFG_ROWADDR_MAP_3.CFG_ROWADDR_MAP_3 =\
        LIBERO_SETTING_CFG_ROWADDR_MAP_3;
    DDRCFG->ADDR_MAP.CFG_COLADDR_MAP_0.CFG_COLADDR_MAP_0 =\
        LIBERO_SETTING_CFG_COLADDR_MAP_0;
    DDRCFG->ADDR_MAP.CFG_COLADDR_MAP_1.CFG_COLADDR_MAP_1 =\
        LIBERO_SETTING_CFG_COLADDR_MAP_1;
    DDRCFG->ADDR_MAP.CFG_COLADDR_MAP_2.CFG_COLADDR_MAP_2 =\
        LIBERO_SETTING_CFG_COLADDR_MAP_2;
    DDRCFG->MC_BASE3.CFG_VRCG_ENABLE.CFG_VRCG_ENABLE =\
        LIBERO_SETTING_CFG_VRCG_ENABLE;
    DDRCFG->MC_BASE3.CFG_VRCG_DISABLE.CFG_VRCG_DISABLE =\
        LIBERO_SETTING_CFG_VRCG_DISABLE;
    DDRCFG->MC_BASE3.CFG_WRITE_LATENCY_SET.CFG_WRITE_LATENCY_SET =\
        LIBERO_SETTING_CFG_WRITE_LATENCY_SET;
    DDRCFG->MC_BASE3.CFG_THERMAL_OFFSET.CFG_THERMAL_OFFSET =\
        LIBERO_SETTING_CFG_THERMAL_OFFSET;
    DDRCFG->MC_BASE3.CFG_SOC_ODT.CFG_SOC_ODT = LIBERO_SETTING_CFG_SOC_ODT;
    DDRCFG->MC_BASE3.CFG_ODTE_CK.CFG_ODTE_CK = LIBERO_SETTING_CFG_ODTE_CK;
    DDRCFG->MC_BASE3.CFG_ODTE_CS.CFG_ODTE_CS = LIBERO_SETTING_CFG_ODTE_CS;
    DDRCFG->MC_BASE3.CFG_ODTD_CA.CFG_ODTD_CA = LIBERO_SETTING_CFG_ODTD_CA;
    DDRCFG->MC_BASE3.CFG_LPDDR4_FSP_OP.CFG_LPDDR4_FSP_OP =\
        LIBERO_SETTING_CFG_LPDDR4_FSP_OP;
    DDRCFG->MC_BASE3.CFG_GENERATE_REFRESH_ON_SRX.CFG_GENERATE_REFRESH_ON_SRX =\
        LIBERO_SETTING_CFG_GENERATE_REFRESH_ON_SRX;
    DDRCFG->MC_BASE3.CFG_DBI_CL.CFG_DBI_CL = LIBERO_SETTING_CFG_DBI_CL;
    DDRCFG->MC_BASE3.CFG_NON_DBI_CL.CFG_NON_DBI_CL =\
        LIBERO_SETTING_CFG_NON_DBI_CL;
    DDRCFG->MC_BASE3.INIT_FORCE_WRITE_DATA_0.INIT_FORCE_WRITE_DATA_0 =\
        LIBERO_SETTING_INIT_FORCE_WRITE_DATA_0;
    DDRCFG->MC_BASE1.CFG_WRITE_CRC.CFG_WRITE_CRC =\
        LIBERO_SETTING_CFG_WRITE_CRC;
    DDRCFG->MC_BASE1.CFG_MPR_READ_FORMAT.CFG_MPR_READ_FORMAT =\
        LIBERO_SETTING_CFG_MPR_READ_FORMAT;
    DDRCFG->MC_BASE1.CFG_WR_CMD_LAT_CRC_DM.CFG_WR_CMD_LAT_CRC_DM =\
        LIBERO_SETTING_CFG_WR_CMD_LAT_CRC_DM;
    DDRCFG->MC_BASE1.CFG_FINE_GRAN_REF_MODE.CFG_FINE_GRAN_REF_MODE =\
        LIBERO_SETTING_CFG_FINE_GRAN_REF_MODE;
    DDRCFG->MC_BASE1.CFG_TEMP_SENSOR_READOUT.CFG_TEMP_SENSOR_READOUT =\
        LIBERO_SETTING_CFG_TEMP_SENSOR_READOUT;
    DDRCFG->MC_BASE1.CFG_PER_DRAM_ADDR_EN.CFG_PER_DRAM_ADDR_EN =\
        LIBERO_SETTING_CFG_PER_DRAM_ADDR_EN;
    DDRCFG->MC_BASE1.CFG_GEARDOWN_MODE.CFG_GEARDOWN_MODE =\
        LIBERO_SETTING_CFG_GEARDOWN_MODE;
    DDRCFG->MC_BASE1.CFG_WR_PREAMBLE.CFG_WR_PREAMBLE =\
        LIBERO_SETTING_CFG_WR_PREAMBLE;
    DDRCFG->MC_BASE1.CFG_RD_PREAMBLE.CFG_RD_PREAMBLE =\
        LIBERO_SETTING_CFG_RD_PREAMBLE;
    DDRCFG->MC_BASE1.CFG_RD_PREAMB_TRN_MODE.CFG_RD_PREAMB_TRN_MODE =\
        LIBERO_SETTING_CFG_RD_PREAMB_TRN_MODE;
    DDRCFG->MC_BASE1.CFG_SR_ABORT.CFG_SR_ABORT = LIBERO_SETTING_CFG_SR_ABORT;
    DDRCFG->MC_BASE1.CFG_CS_TO_CMDADDR_LATENCY.CFG_CS_TO_CMDADDR_LATENCY =\
        LIBERO_SETTING_CFG_CS_TO_CMDADDR_LATENCY;
    DDRCFG->MC_BASE1.CFG_INT_VREF_MON.CFG_INT_VREF_MON =\
        LIBERO_SETTING_CFG_INT_VREF_MON;
    DDRCFG->MC_BASE1.CFG_TEMP_CTRL_REF_MODE.CFG_TEMP_CTRL_REF_MODE =\
        LIBERO_SETTING_CFG_TEMP_CTRL_REF_MODE;
    DDRCFG->MC_BASE1.CFG_TEMP_CTRL_REF_RANGE.CFG_TEMP_CTRL_REF_RANGE =\
        LIBERO_SETTING_CFG_TEMP_CTRL_REF_RANGE;
    DDRCFG->MC_BASE1.CFG_MAX_PWR_DOWN_MODE.CFG_MAX_PWR_DOWN_MODE =\
        LIBERO_SETTING_CFG_MAX_PWR_DOWN_MODE;
    DDRCFG->MC_BASE1.CFG_READ_DBI.CFG_READ_DBI = LIBERO_SETTING_CFG_READ_DBI;
    DDRCFG->MC_BASE1.CFG_WRITE_DBI.CFG_WRITE_DBI =\
        LIBERO_SETTING_CFG_WRITE_DBI;
    DDRCFG->MC_BASE1.CFG_DATA_MASK.CFG_DATA_MASK =\
        LIBERO_SETTING_CFG_DATA_MASK;
    DDRCFG->MC_BASE1.CFG_CA_PARITY_PERSIST_ERR.CFG_CA_PARITY_PERSIST_ERR =\
        LIBERO_SETTING_CFG_CA_PARITY_PERSIST_ERR;
    DDRCFG->MC_BASE1.CFG_RTT_PARK.CFG_RTT_PARK = LIBERO_SETTING_CFG_RTT_PARK;
    DDRCFG->MC_BASE1.CFG_ODT_INBUF_4_PD.CFG_ODT_INBUF_4_PD =\
        LIBERO_SETTING_CFG_ODT_INBUF_4_PD;
    DDRCFG->MC_BASE1.CFG_CA_PARITY_ERR_STATUS.CFG_CA_PARITY_ERR_STATUS =\
        LIBERO_SETTING_CFG_CA_PARITY_ERR_STATUS;
    DDRCFG->MC_BASE1.CFG_CRC_ERROR_CLEAR.CFG_CRC_ERROR_CLEAR =\
        LIBERO_SETTING_CFG_CRC_ERROR_CLEAR;
    DDRCFG->MC_BASE1.CFG_CA_PARITY_LATENCY.CFG_CA_PARITY_LATENCY =\
        LIBERO_SETTING_CFG_CA_PARITY_LATENCY;
    DDRCFG->MC_BASE1.CFG_CCD_S.CFG_CCD_S = LIBERO_SETTING_CFG_CCD_S;
    DDRCFG->MC_BASE1.CFG_CCD_L.CFG_CCD_L = LIBERO_SETTING_CFG_CCD_L;
    DDRCFG->MC_BASE1.CFG_VREFDQ_TRN_ENABLE.CFG_VREFDQ_TRN_ENABLE =\
        LIBERO_SETTING_CFG_VREFDQ_TRN_ENABLE;
    DDRCFG->MC_BASE1.CFG_VREFDQ_TRN_RANGE.CFG_VREFDQ_TRN_RANGE =\
        LIBERO_SETTING_CFG_VREFDQ_TRN_RANGE;
    DDRCFG->MC_BASE1.CFG_VREFDQ_TRN_VALUE.CFG_VREFDQ_TRN_VALUE =\
        LIBERO_SETTING_CFG_VREFDQ_TRN_VALUE;
    DDRCFG->MC_BASE1.CFG_RRD_S.CFG_RRD_S = LIBERO_SETTING_CFG_RRD_S;
    DDRCFG->MC_BASE1.CFG_RRD_L.CFG_RRD_L = LIBERO_SETTING_CFG_RRD_L;
    DDRCFG->MC_BASE1.CFG_WTR_S.CFG_WTR_S = LIBERO_SETTING_CFG_WTR_S;
    DDRCFG->MC_BASE1.CFG_WTR_L.CFG_WTR_L = LIBERO_SETTING_CFG_WTR_L;
    DDRCFG->MC_BASE1.CFG_WTR_S_CRC_DM.CFG_WTR_S_CRC_DM =\
        LIBERO_SETTING_CFG_WTR_S_CRC_DM;
    DDRCFG->MC_BASE1.CFG_WTR_L_CRC_DM.CFG_WTR_L_CRC_DM =\
        LIBERO_SETTING_CFG_WTR_L_CRC_DM;
    DDRCFG->MC_BASE1.CFG_WR_CRC_DM.CFG_WR_CRC_DM =\
        LIBERO_SETTING_CFG_WR_CRC_DM;
    DDRCFG->MC_BASE1.CFG_RFC1.CFG_RFC1 = LIBERO_SETTING_CFG_RFC1;
    DDRCFG->MC_BASE1.CFG_RFC2.CFG_RFC2 = LIBERO_SETTING_CFG_RFC2;
    DDRCFG->MC_BASE1.CFG_RFC4.CFG_RFC4 = LIBERO_SETTING_CFG_RFC4;
    DDRCFG->MC_BASE1.CFG_NIBBLE_DEVICES.CFG_NIBBLE_DEVICES =\
        LIBERO_SETTING_CFG_NIBBLE_DEVICES;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS0_0.CFG_BIT_MAP_INDEX_CS0_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS0_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS0_1.CFG_BIT_MAP_INDEX_CS0_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS0_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS1_0.CFG_BIT_MAP_INDEX_CS1_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS1_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS1_1.CFG_BIT_MAP_INDEX_CS1_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS1_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS2_0.CFG_BIT_MAP_INDEX_CS2_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS2_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS2_1.CFG_BIT_MAP_INDEX_CS2_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS2_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS3_0.CFG_BIT_MAP_INDEX_CS3_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS3_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS3_1.CFG_BIT_MAP_INDEX_CS3_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS3_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS4_0.CFG_BIT_MAP_INDEX_CS4_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS4_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS4_1.CFG_BIT_MAP_INDEX_CS4_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS4_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS5_0.CFG_BIT_MAP_INDEX_CS5_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS5_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS5_1.CFG_BIT_MAP_INDEX_CS5_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS5_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS6_0.CFG_BIT_MAP_INDEX_CS6_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS6_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS6_1.CFG_BIT_MAP_INDEX_CS6_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS6_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS7_0.CFG_BIT_MAP_INDEX_CS7_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS7_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS7_1.CFG_BIT_MAP_INDEX_CS7_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS7_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS8_0.CFG_BIT_MAP_INDEX_CS8_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS8_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS8_1.CFG_BIT_MAP_INDEX_CS8_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS8_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS9_0.CFG_BIT_MAP_INDEX_CS9_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS9_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS9_1.CFG_BIT_MAP_INDEX_CS9_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS9_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS10_0.CFG_BIT_MAP_INDEX_CS10_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS10_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS10_1.CFG_BIT_MAP_INDEX_CS10_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS10_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS11_0.CFG_BIT_MAP_INDEX_CS11_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS11_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS11_1.CFG_BIT_MAP_INDEX_CS11_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS11_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS12_0.CFG_BIT_MAP_INDEX_CS12_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS12_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS12_1.CFG_BIT_MAP_INDEX_CS12_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS12_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS13_0.CFG_BIT_MAP_INDEX_CS13_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS13_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS13_1.CFG_BIT_MAP_INDEX_CS13_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS13_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS14_0.CFG_BIT_MAP_INDEX_CS14_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS14_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS14_1.CFG_BIT_MAP_INDEX_CS14_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS14_1;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS15_0.CFG_BIT_MAP_INDEX_CS15_0 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS15_0;
    DDRCFG->MC_BASE1.CFG_BIT_MAP_INDEX_CS15_1.CFG_BIT_MAP_INDEX_CS15_1 =\
        LIBERO_SETTING_CFG_BIT_MAP_INDEX_CS15_1;
    DDRCFG->MC_BASE1.CFG_NUM_LOGICAL_RANKS_PER_3DS.CFG_NUM_LOGICAL_RANKS_PER_3DS =\
        LIBERO_SETTING_CFG_NUM_LOGICAL_RANKS_PER_3DS;
    DDRCFG->MC_BASE1.CFG_RFC_DLR1.CFG_RFC_DLR1 = LIBERO_SETTING_CFG_RFC_DLR1;
    DDRCFG->MC_BASE1.CFG_RFC_DLR2.CFG_RFC_DLR2 = LIBERO_SETTING_CFG_RFC_DLR2;
    DDRCFG->MC_BASE1.CFG_RFC_DLR4.CFG_RFC_DLR4 = LIBERO_SETTING_CFG_RFC_DLR4;
    DDRCFG->MC_BASE1.CFG_RRD_DLR.CFG_RRD_DLR = LIBERO_SETTING_CFG_RRD_DLR;
    DDRCFG->MC_BASE1.CFG_FAW_DLR.CFG_FAW_DLR = LIBERO_SETTING_CFG_FAW_DLR;
    DDRCFG->MC_BASE1.CFG_ADVANCE_ACTIVATE_READY.CFG_ADVANCE_ACTIVATE_READY =\
        LIBERO_SETTING_CFG_ADVANCE_ACTIVATE_READY;
    DDRCFG->MC_BASE2.CTRLR_SOFT_RESET_N.CTRLR_SOFT_RESET_N =\
        LIBERO_SETTING_CTRLR_SOFT_RESET_N;
    DDRCFG->MC_BASE2.CFG_LOOKAHEAD_PCH.CFG_LOOKAHEAD_PCH =\
        LIBERO_SETTING_CFG_LOOKAHEAD_PCH;
    DDRCFG->MC_BASE2.CFG_LOOKAHEAD_ACT.CFG_LOOKAHEAD_ACT =\
        LIBERO_SETTING_CFG_LOOKAHEAD_ACT;
    DDRCFG->MC_BASE2.INIT_AUTOINIT_DISABLE.INIT_AUTOINIT_DISABLE =\
        LIBERO_SETTING_INIT_AUTOINIT_DISABLE;
    DDRCFG->MC_BASE2.INIT_FORCE_RESET.INIT_FORCE_RESET =\
        LIBERO_SETTING_INIT_FORCE_RESET;
    DDRCFG->MC_BASE2.INIT_GEARDOWN_EN.INIT_GEARDOWN_EN =\
        LIBERO_SETTING_INIT_GEARDOWN_EN;
    DDRCFG->MC_BASE2.INIT_DISABLE_CKE.INIT_DISABLE_CKE =\
        LIBERO_SETTING_INIT_DISABLE_CKE;
    DDRCFG->MC_BASE2.INIT_CS.INIT_CS = LIBERO_SETTING_INIT_CS;
    DDRCFG->MC_BASE2.INIT_PRECHARGE_ALL.INIT_PRECHARGE_ALL =\
        LIBERO_SETTING_INIT_PRECHARGE_ALL;
    DDRCFG->MC_BASE2.INIT_REFRESH.INIT_REFRESH = LIBERO_SETTING_INIT_REFRESH;
    DDRCFG->MC_BASE2.INIT_ZQ_CAL_REQ.INIT_ZQ_CAL_REQ =\
        LIBERO_SETTING_INIT_ZQ_CAL_REQ;
    DDRCFG->MC_BASE2.CFG_BL.CFG_BL = LIBERO_SETTING_CFG_BL;
    DDRCFG->MC_BASE2.CTRLR_INIT.CTRLR_INIT = LIBERO_SETTING_CTRLR_INIT;
    DDRCFG->MC_BASE2.CFG_AUTO_REF_EN.CFG_AUTO_REF_EN =\
        LIBERO_SETTING_CFG_AUTO_REF_EN;
    DDRCFG->MC_BASE2.CFG_RAS.CFG_RAS = LIBERO_SETTING_CFG_RAS;
    DDRCFG->MC_BASE2.CFG_RCD.CFG_RCD = LIBERO_SETTING_CFG_RCD;
    DDRCFG->MC_BASE2.CFG_RRD.CFG_RRD = LIBERO_SETTING_CFG_RRD;
    DDRCFG->MC_BASE2.CFG_RP.CFG_RP = LIBERO_SETTING_CFG_RP;
    DDRCFG->MC_BASE2.CFG_RC.CFG_RC = LIBERO_SETTING_CFG_RC;
    DDRCFG->MC_BASE2.CFG_FAW.CFG_FAW = LIBERO_SETTING_CFG_FAW;
    DDRCFG->MC_BASE2.CFG_RFC.CFG_RFC = LIBERO_SETTING_CFG_RFC;
    DDRCFG->MC_BASE2.CFG_RTP.CFG_RTP = LIBERO_SETTING_CFG_RTP;
    DDRCFG->MC_BASE2.CFG_WR.CFG_WR = LIBERO_SETTING_CFG_WR;
    DDRCFG->MC_BASE2.CFG_WTR.CFG_WTR = LIBERO_SETTING_CFG_WTR;
    DDRCFG->MC_BASE2.CFG_PASR.CFG_PASR = LIBERO_SETTING_CFG_PASR;
    DDRCFG->MC_BASE2.CFG_XP.CFG_XP = LIBERO_SETTING_CFG_XP;
    DDRCFG->MC_BASE2.CFG_XSR.CFG_XSR = LIBERO_SETTING_CFG_XSR;
    DDRCFG->MC_BASE2.CFG_CL.CFG_CL = LIBERO_SETTING_CFG_CL;
    DDRCFG->MC_BASE2.CFG_READ_TO_WRITE.CFG_READ_TO_WRITE =\
        LIBERO_SETTING_CFG_READ_TO_WRITE;
    DDRCFG->MC_BASE2.CFG_WRITE_TO_WRITE.CFG_WRITE_TO_WRITE =\
        LIBERO_SETTING_CFG_WRITE_TO_WRITE;
    DDRCFG->MC_BASE2.CFG_READ_TO_READ.CFG_READ_TO_READ =\
        LIBERO_SETTING_CFG_READ_TO_READ;
    DDRCFG->MC_BASE2.CFG_WRITE_TO_READ.CFG_WRITE_TO_READ =\
        LIBERO_SETTING_CFG_WRITE_TO_READ;
    DDRCFG->MC_BASE2.CFG_READ_TO_WRITE_ODT.CFG_READ_TO_WRITE_ODT =\
        LIBERO_SETTING_CFG_READ_TO_WRITE_ODT;
    DDRCFG->MC_BASE2.CFG_WRITE_TO_WRITE_ODT.CFG_WRITE_TO_WRITE_ODT =\
        LIBERO_SETTING_CFG_WRITE_TO_WRITE_ODT;
    DDRCFG->MC_BASE2.CFG_READ_TO_READ_ODT.CFG_READ_TO_READ_ODT =\
        LIBERO_SETTING_CFG_READ_TO_READ_ODT;
    DDRCFG->MC_BASE2.CFG_WRITE_TO_READ_ODT.CFG_WRITE_TO_READ_ODT =\
        LIBERO_SETTING_CFG_WRITE_TO_READ_ODT;
    DDRCFG->MC_BASE2.CFG_MIN_READ_IDLE.CFG_MIN_READ_IDLE =\
        LIBERO_SETTING_CFG_MIN_READ_IDLE;
    DDRCFG->MC_BASE2.CFG_MRD.CFG_MRD = LIBERO_SETTING_CFG_MRD;
    DDRCFG->MC_BASE2.CFG_BT.CFG_BT = LIBERO_SETTING_CFG_BT;
    DDRCFG->MC_BASE2.CFG_DS.CFG_DS = LIBERO_SETTING_CFG_DS;
    DDRCFG->MC_BASE2.CFG_QOFF.CFG_QOFF = LIBERO_SETTING_CFG_QOFF;
    DDRCFG->MC_BASE2.CFG_RTT.CFG_RTT = LIBERO_SETTING_CFG_RTT;
    DDRCFG->MC_BASE2.CFG_DLL_DISABLE.CFG_DLL_DISABLE =\
        LIBERO_SETTING_CFG_DLL_DISABLE;
    DDRCFG->MC_BASE2.CFG_REF_PER.CFG_REF_PER = LIBERO_SETTING_CFG_REF_PER;
    DDRCFG->MC_BASE2.CFG_STARTUP_DELAY.CFG_STARTUP_DELAY =\
        LIBERO_SETTING_CFG_STARTUP_DELAY;
    DDRCFG->MC_BASE2.CFG_MEM_COLBITS.CFG_MEM_COLBITS =\
        LIBERO_SETTING_CFG_MEM_COLBITS;
    DDRCFG->MC_BASE2.CFG_MEM_ROWBITS.CFG_MEM_ROWBITS =\
        LIBERO_SETTING_CFG_MEM_ROWBITS;
    DDRCFG->MC_BASE2.CFG_MEM_BANKBITS.CFG_MEM_BANKBITS =\
        LIBERO_SETTING_CFG_MEM_BANKBITS;
    DDRCFG->MC_BASE2.CFG_ODT_RD_MAP_CS0.CFG_ODT_RD_MAP_CS0 =\
        LIBERO_SETTING_CFG_ODT_RD_MAP_CS0;
    DDRCFG->MC_BASE2.CFG_ODT_RD_MAP_CS1.CFG_ODT_RD_MAP_CS1 =\
        LIBERO_SETTING_CFG_ODT_RD_MAP_CS1;
    DDRCFG->MC_BASE2.CFG_ODT_RD_MAP_CS2.CFG_ODT_RD_MAP_CS2 =\
        LIBERO_SETTING_CFG_ODT_RD_MAP_CS2;
    DDRCFG->MC_BASE2.CFG_ODT_RD_MAP_CS3.CFG_ODT_RD_MAP_CS3 =\
        LIBERO_SETTING_CFG_ODT_RD_MAP_CS3;
    DDRCFG->MC_BASE2.CFG_ODT_RD_MAP_CS4.CFG_ODT_RD_MAP_CS4 =\
        LIBERO_SETTING_CFG_ODT_RD_MAP_CS4;
    DDRCFG->MC_BASE2.CFG_ODT_RD_MAP_CS5.CFG_ODT_RD_MAP_CS5 =\
        LIBERO_SETTING_CFG_ODT_RD_MAP_CS5;
    DDRCFG->MC_BASE2.CFG_ODT_RD_MAP_CS6.CFG_ODT_RD_MAP_CS6 =\
        LIBERO_SETTING_CFG_ODT_RD_MAP_CS6;
    DDRCFG->MC_BASE2.CFG_ODT_RD_MAP_CS7.CFG_ODT_RD_MAP_CS7 =\
        LIBERO_SETTING_CFG_ODT_RD_MAP_CS7;
    DDRCFG->MC_BASE2.CFG_ODT_WR_MAP_CS0.CFG_ODT_WR_MAP_CS0 =\
        LIBERO_SETTING_CFG_ODT_WR_MAP_CS0;
    DDRCFG->MC_BASE2.CFG_ODT_WR_MAP_CS1.CFG_ODT_WR_MAP_CS1 =\
        LIBERO_SETTING_CFG_ODT_WR_MAP_CS1;
    DDRCFG->MC_BASE2.CFG_ODT_WR_MAP_CS2.CFG_ODT_WR_MAP_CS2 =\
        LIBERO_SETTING_CFG_ODT_WR_MAP_CS2;
    DDRCFG->MC_BASE2.CFG_ODT_WR_MAP_CS3.CFG_ODT_WR_MAP_CS3 =\
        LIBERO_SETTING_CFG_ODT_WR_MAP_CS3;
    DDRCFG->MC_BASE2.CFG_ODT_WR_MAP_CS4.CFG_ODT_WR_MAP_CS4 =\
        LIBERO_SETTING_CFG_ODT_WR_MAP_CS4;
    DDRCFG->MC_BASE2.CFG_ODT_WR_MAP_CS5.CFG_ODT_WR_MAP_CS5 =\
        LIBERO_SETTING_CFG_ODT_WR_MAP_CS5;
    DDRCFG->MC_BASE2.CFG_ODT_WR_MAP_CS6.CFG_ODT_WR_MAP_CS6 =\
        LIBERO_SETTING_CFG_ODT_WR_MAP_CS6;
    DDRCFG->MC_BASE2.CFG_ODT_WR_MAP_CS7.CFG_ODT_WR_MAP_CS7 =\
        LIBERO_SETTING_CFG_ODT_WR_MAP_CS7;
    DDRCFG->MC_BASE2.CFG_ODT_RD_TURN_ON.CFG_ODT_RD_TURN_ON =\
        LIBERO_SETTING_CFG_ODT_RD_TURN_ON;
    DDRCFG->MC_BASE2.CFG_ODT_WR_TURN_ON.CFG_ODT_WR_TURN_ON =\
        LIBERO_SETTING_CFG_ODT_WR_TURN_ON;
    DDRCFG->MC_BASE2.CFG_ODT_RD_TURN_OFF.CFG_ODT_RD_TURN_OFF =\
        LIBERO_SETTING_CFG_ODT_RD_TURN_OFF;
    DDRCFG->MC_BASE2.CFG_ODT_WR_TURN_OFF.CFG_ODT_WR_TURN_OFF =\
        LIBERO_SETTING_CFG_ODT_WR_TURN_OFF;
    DDRCFG->MC_BASE2.CFG_EMR3.CFG_EMR3 = LIBERO_SETTING_CFG_EMR3;
    DDRCFG->MC_BASE2.CFG_TWO_T.CFG_TWO_T = LIBERO_SETTING_CFG_TWO_T;
    DDRCFG->MC_BASE2.CFG_TWO_T_SEL_CYCLE.CFG_TWO_T_SEL_CYCLE =\
        LIBERO_SETTING_CFG_TWO_T_SEL_CYCLE;
    DDRCFG->MC_BASE2.CFG_REGDIMM.CFG_REGDIMM = LIBERO_SETTING_CFG_REGDIMM;
    DDRCFG->MC_BASE2.CFG_MOD.CFG_MOD = LIBERO_SETTING_CFG_MOD;
    DDRCFG->MC_BASE2.CFG_XS.CFG_XS = LIBERO_SETTING_CFG_XS;
    DDRCFG->MC_BASE2.CFG_XSDLL.CFG_XSDLL = LIBERO_SETTING_CFG_XSDLL;
    DDRCFG->MC_BASE2.CFG_XPR.CFG_XPR = LIBERO_SETTING_CFG_XPR;
    DDRCFG->MC_BASE2.CFG_AL_MODE.CFG_AL_MODE = LIBERO_SETTING_CFG_AL_MODE;
    DDRCFG->MC_BASE2.CFG_CWL.CFG_CWL = LIBERO_SETTING_CFG_CWL;
    DDRCFG->MC_BASE2.CFG_BL_MODE.CFG_BL_MODE = LIBERO_SETTING_CFG_BL_MODE;
    DDRCFG->MC_BASE2.CFG_TDQS.CFG_TDQS = LIBERO_SETTING_CFG_TDQS;
    DDRCFG->MC_BASE2.CFG_RTT_WR.CFG_RTT_WR = LIBERO_SETTING_CFG_RTT_WR;
    DDRCFG->MC_BASE2.CFG_LP_ASR.CFG_LP_ASR = LIBERO_SETTING_CFG_LP_ASR;
    DDRCFG->MC_BASE2.CFG_AUTO_SR.CFG_AUTO_SR = LIBERO_SETTING_CFG_AUTO_SR;
    DDRCFG->MC_BASE2.CFG_SRT.CFG_SRT = LIBERO_SETTING_CFG_SRT;
    DDRCFG->MC_BASE2.CFG_ADDR_MIRROR.CFG_ADDR_MIRROR =\
        LIBERO_SETTING_CFG_ADDR_MIRROR;
    DDRCFG->MC_BASE2.CFG_ZQ_CAL_TYPE.CFG_ZQ_CAL_TYPE =\
        LIBERO_SETTING_CFG_ZQ_CAL_TYPE;
    DDRCFG->MC_BASE2.CFG_ZQ_CAL_PER.CFG_ZQ_CAL_PER =\
        LIBERO_SETTING_CFG_ZQ_CAL_PER;
    DDRCFG->MC_BASE2.CFG_AUTO_ZQ_CAL_EN.CFG_AUTO_ZQ_CAL_EN =\
        LIBERO_SETTING_CFG_AUTO_ZQ_CAL_EN;
    DDRCFG->MC_BASE2.CFG_MEMORY_TYPE.CFG_MEMORY_TYPE =\
        LIBERO_SETTING_CFG_MEMORY_TYPE;
    DDRCFG->MC_BASE2.CFG_ONLY_SRANK_CMDS.CFG_ONLY_SRANK_CMDS =\
        LIBERO_SETTING_CFG_ONLY_SRANK_CMDS;
    DDRCFG->MC_BASE2.CFG_NUM_RANKS.CFG_NUM_RANKS =\
        LIBERO_SETTING_CFG_NUM_RANKS;
    DDRCFG->MC_BASE2.CFG_QUAD_RANK.CFG_QUAD_RANK =\
        LIBERO_SETTING_CFG_QUAD_RANK;
    DDRCFG->MC_BASE2.CFG_EARLY_RANK_TO_WR_START.CFG_EARLY_RANK_TO_WR_START =\
        LIBERO_SETTING_CFG_EARLY_RANK_TO_WR_START;
    DDRCFG->MC_BASE2.CFG_EARLY_RANK_TO_RD_START.CFG_EARLY_RANK_TO_RD_START =\
        LIBERO_SETTING_CFG_EARLY_RANK_TO_RD_START;
    DDRCFG->MC_BASE2.CFG_PASR_BANK.CFG_PASR_BANK =\
        LIBERO_SETTING_CFG_PASR_BANK;
    DDRCFG->MC_BASE2.CFG_PASR_SEG.CFG_PASR_SEG = LIBERO_SETTING_CFG_PASR_SEG;
    DDRCFG->MC_BASE2.INIT_MRR_MODE.INIT_MRR_MODE =\
        LIBERO_SETTING_INIT_MRR_MODE;
    DDRCFG->MC_BASE2.INIT_MR_W_REQ.INIT_MR_W_REQ =\
        LIBERO_SETTING_INIT_MR_W_REQ;
    DDRCFG->MC_BASE2.INIT_MR_ADDR.INIT_MR_ADDR = LIBERO_SETTING_INIT_MR_ADDR;
    DDRCFG->MC_BASE2.INIT_MR_WR_DATA.INIT_MR_WR_DATA =\
        LIBERO_SETTING_INIT_MR_WR_DATA;
    DDRCFG->MC_BASE2.INIT_MR_WR_MASK.INIT_MR_WR_MASK =\
        LIBERO_SETTING_INIT_MR_WR_MASK;
    DDRCFG->MC_BASE2.INIT_NOP.INIT_NOP = LIBERO_SETTING_INIT_NOP;
    DDRCFG->MC_BASE2.CFG_INIT_DURATION.CFG_INIT_DURATION =\
        LIBERO_SETTING_CFG_INIT_DURATION;
    DDRCFG->MC_BASE2.CFG_ZQINIT_CAL_DURATION.CFG_ZQINIT_CAL_DURATION =\
        LIBERO_SETTING_CFG_ZQINIT_CAL_DURATION;
    DDRCFG->MC_BASE2.CFG_ZQ_CAL_L_DURATION.CFG_ZQ_CAL_L_DURATION =\
        LIBERO_SETTING_CFG_ZQ_CAL_L_DURATION;
    DDRCFG->MC_BASE2.CFG_ZQ_CAL_S_DURATION.CFG_ZQ_CAL_S_DURATION =\
        LIBERO_SETTING_CFG_ZQ_CAL_S_DURATION;
    DDRCFG->MC_BASE2.CFG_ZQ_CAL_R_DURATION.CFG_ZQ_CAL_R_DURATION =\
        LIBERO_SETTING_CFG_ZQ_CAL_R_DURATION;
    DDRCFG->MC_BASE2.CFG_MRR.CFG_MRR = LIBERO_SETTING_CFG_MRR;
    DDRCFG->MC_BASE2.CFG_MRW.CFG_MRW = LIBERO_SETTING_CFG_MRW;
    DDRCFG->MC_BASE2.CFG_ODT_POWERDOWN.CFG_ODT_POWERDOWN =\
        LIBERO_SETTING_CFG_ODT_POWERDOWN;
    DDRCFG->MC_BASE2.CFG_WL.CFG_WL = LIBERO_SETTING_CFG_WL;
    DDRCFG->MC_BASE2.CFG_RL.CFG_RL = LIBERO_SETTING_CFG_RL;
    DDRCFG->MC_BASE2.CFG_CAL_READ_PERIOD.CFG_CAL_READ_PERIOD =\
        LIBERO_SETTING_CFG_CAL_READ_PERIOD;
    DDRCFG->MC_BASE2.CFG_NUM_CAL_READS.CFG_NUM_CAL_READS =\
        LIBERO_SETTING_CFG_NUM_CAL_READS;
    DDRCFG->MC_BASE2.INIT_SELF_REFRESH.INIT_SELF_REFRESH =\
        LIBERO_SETTING_INIT_SELF_REFRESH;
    DDRCFG->MC_BASE2.INIT_POWER_DOWN.INIT_POWER_DOWN =\
        LIBERO_SETTING_INIT_POWER_DOWN;
    DDRCFG->MC_BASE2.INIT_FORCE_WRITE.INIT_FORCE_WRITE =\
        LIBERO_SETTING_INIT_FORCE_WRITE;
    DDRCFG->MC_BASE2.INIT_FORCE_WRITE_CS.INIT_FORCE_WRITE_CS =\
        LIBERO_SETTING_INIT_FORCE_WRITE_CS;
    DDRCFG->MC_BASE2.CFG_CTRLR_INIT_DISABLE.CFG_CTRLR_INIT_DISABLE =\
        LIBERO_SETTING_CFG_CTRLR_INIT_DISABLE;
    DDRCFG->MC_BASE2.INIT_RDIMM_COMPLETE.INIT_RDIMM_COMPLETE =\
        LIBERO_SETTING_INIT_RDIMM_COMPLETE;
    DDRCFG->MC_BASE2.CFG_RDIMM_LAT.CFG_RDIMM_LAT =\
        LIBERO_SETTING_CFG_RDIMM_LAT;
    DDRCFG->MC_BASE2.CFG_RDIMM_BSIDE_INVERT.CFG_RDIMM_BSIDE_INVERT =\
        LIBERO_SETTING_CFG_RDIMM_BSIDE_INVERT;
    DDRCFG->MC_BASE2.CFG_LRDIMM.CFG_LRDIMM = LIBERO_SETTING_CFG_LRDIMM;
    DDRCFG->MC_BASE2.INIT_MEMORY_RESET_MASK.INIT_MEMORY_RESET_MASK =\
        LIBERO_SETTING_INIT_MEMORY_RESET_MASK;
    DDRCFG->MC_BASE2.CFG_RD_PREAMB_TOGGLE.CFG_RD_PREAMB_TOGGLE =\
        LIBERO_SETTING_CFG_RD_PREAMB_TOGGLE;
    DDRCFG->MC_BASE2.CFG_RD_POSTAMBLE.CFG_RD_POSTAMBLE =\
        LIBERO_SETTING_CFG_RD_POSTAMBLE;
    DDRCFG->MC_BASE2.CFG_PU_CAL.CFG_PU_CAL = LIBERO_SETTING_CFG_PU_CAL;
    DDRCFG->MC_BASE2.CFG_DQ_ODT.CFG_DQ_ODT = LIBERO_SETTING_CFG_DQ_ODT;
    DDRCFG->MC_BASE2.CFG_CA_ODT.CFG_CA_ODT = LIBERO_SETTING_CFG_CA_ODT;
    DDRCFG->MC_BASE2.CFG_ZQLATCH_DURATION.CFG_ZQLATCH_DURATION =\
        LIBERO_SETTING_CFG_ZQLATCH_DURATION;
    DDRCFG->MC_BASE2.INIT_CAL_SELECT.INIT_CAL_SELECT =\
        LIBERO_SETTING_INIT_CAL_SELECT;
    DDRCFG->MC_BASE2.INIT_CAL_L_R_REQ.INIT_CAL_L_R_REQ =\
        LIBERO_SETTING_INIT_CAL_L_R_REQ;
    DDRCFG->MC_BASE2.INIT_CAL_L_B_SIZE.INIT_CAL_L_B_SIZE =\
        LIBERO_SETTING_INIT_CAL_L_B_SIZE;
    DDRCFG->MC_BASE2.INIT_RWFIFO.INIT_RWFIFO = LIBERO_SETTING_INIT_RWFIFO;
    DDRCFG->MC_BASE2.INIT_RD_DQCAL.INIT_RD_DQCAL =\
        LIBERO_SETTING_INIT_RD_DQCAL;
    DDRCFG->MC_BASE2.INIT_START_DQSOSC.INIT_START_DQSOSC =\
        LIBERO_SETTING_INIT_START_DQSOSC;
    DDRCFG->MC_BASE2.INIT_STOP_DQSOSC.INIT_STOP_DQSOSC =\
        LIBERO_SETTING_INIT_STOP_DQSOSC;
    DDRCFG->MC_BASE2.INIT_ZQ_CAL_START.INIT_ZQ_CAL_START =\
        LIBERO_SETTING_INIT_ZQ_CAL_START;
    DDRCFG->MC_BASE2.CFG_WR_POSTAMBLE.CFG_WR_POSTAMBLE =\
        LIBERO_SETTING_CFG_WR_POSTAMBLE;
    DDRCFG->MC_BASE2.INIT_CAL_L_ADDR_0.INIT_CAL_L_ADDR_0 =\
        LIBERO_SETTING_INIT_CAL_L_ADDR_0;
    DDRCFG->MC_BASE2.INIT_CAL_L_ADDR_1.INIT_CAL_L_ADDR_1 =\
        LIBERO_SETTING_INIT_CAL_L_ADDR_1;
    DDRCFG->MC_BASE2.CFG_CTRLUPD_TRIG.CFG_CTRLUPD_TRIG =\
        LIBERO_SETTING_CFG_CTRLUPD_TRIG;
    DDRCFG->MC_BASE2.CFG_CTRLUPD_START_DELAY.CFG_CTRLUPD_START_DELAY =\
        LIBERO_SETTING_CFG_CTRLUPD_START_DELAY;
    DDRCFG->MC_BASE2.CFG_DFI_T_CTRLUPD_MAX.CFG_DFI_T_CTRLUPD_MAX =\
        LIBERO_SETTING_CFG_DFI_T_CTRLUPD_MAX;
    DDRCFG->MC_BASE2.CFG_CTRLR_BUSY_SEL.CFG_CTRLR_BUSY_SEL =\
        LIBERO_SETTING_CFG_CTRLR_BUSY_SEL;
    DDRCFG->MC_BASE2.CFG_CTRLR_BUSY_VALUE.CFG_CTRLR_BUSY_VALUE =\
        LIBERO_SETTING_CFG_CTRLR_BUSY_VALUE;
    DDRCFG->MC_BASE2.CFG_CTRLR_BUSY_TURN_OFF_DELAY.CFG_CTRLR_BUSY_TURN_OFF_DELAY =\
        LIBERO_SETTING_CFG_CTRLR_BUSY_TURN_OFF_DELAY;
    DDRCFG->MC_BASE2.CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW.CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW =\
        LIBERO_SETTING_CFG_CTRLR_BUSY_SLOW_RESTART_WINDOW;
    DDRCFG->MC_BASE2.CFG_CTRLR_BUSY_RESTART_HOLDOFF.CFG_CTRLR_BUSY_RESTART_HOLDOFF =\
        LIBERO_SETTING_CFG_CTRLR_BUSY_RESTART_HOLDOFF;
    DDRCFG->MC_BASE2.CFG_PARITY_RDIMM_DELAY.CFG_PARITY_RDIMM_DELAY =\
        LIBERO_SETTING_CFG_PARITY_RDIMM_DELAY;
    DDRCFG->MC_BASE2.CFG_CTRLR_BUSY_ENABLE.CFG_CTRLR_BUSY_ENABLE =\
        LIBERO_SETTING_CFG_CTRLR_BUSY_ENABLE;
    DDRCFG->MC_BASE2.CFG_ASYNC_ODT.CFG_ASYNC_ODT =\
        LIBERO_SETTING_CFG_ASYNC_ODT;
    DDRCFG->MC_BASE2.CFG_ZQ_CAL_DURATION.CFG_ZQ_CAL_DURATION =\
        LIBERO_SETTING_CFG_ZQ_CAL_DURATION;
    DDRCFG->MC_BASE2.CFG_MRRI.CFG_MRRI = LIBERO_SETTING_CFG_MRRI;
    DDRCFG->MC_BASE2.INIT_ODT_FORCE_EN.INIT_ODT_FORCE_EN =\
        LIBERO_SETTING_INIT_ODT_FORCE_EN;
    DDRCFG->MC_BASE2.INIT_ODT_FORCE_RANK.INIT_ODT_FORCE_RANK =\
        LIBERO_SETTING_INIT_ODT_FORCE_RANK;
    DDRCFG->MC_BASE2.CFG_PHYUPD_ACK_DELAY.CFG_PHYUPD_ACK_DELAY =\
        LIBERO_SETTING_CFG_PHYUPD_ACK_DELAY;
    DDRCFG->MC_BASE2.CFG_MIRROR_X16_BG0_BG1.CFG_MIRROR_X16_BG0_BG1 =\
        LIBERO_SETTING_CFG_MIRROR_X16_BG0_BG1;
    DDRCFG->MC_BASE2.INIT_PDA_MR_W_REQ.INIT_PDA_MR_W_REQ =\
        LIBERO_SETTING_INIT_PDA_MR_W_REQ;
    DDRCFG->MC_BASE2.INIT_PDA_NIBBLE_SELECT.INIT_PDA_NIBBLE_SELECT =\
        LIBERO_SETTING_INIT_PDA_NIBBLE_SELECT;
    DDRCFG->MC_BASE2.CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH.CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH =\
        LIBERO_SETTING_CFG_DRAM_CLK_DISABLE_IN_SELF_REFRESH;
    DDRCFG->MC_BASE2.CFG_CKSRE.CFG_CKSRE = LIBERO_SETTING_CFG_CKSRE;
    DDRCFG->MC_BASE2.CFG_CKSRX.CFG_CKSRX = LIBERO_SETTING_CFG_CKSRX;
    DDRCFG->MC_BASE2.CFG_RCD_STAB.CFG_RCD_STAB = LIBERO_SETTING_CFG_RCD_STAB;
    DDRCFG->MC_BASE2.CFG_DFI_T_CTRL_DELAY.CFG_DFI_T_CTRL_DELAY =\
        LIBERO_SETTING_CFG_DFI_T_CTRL_DELAY;
    DDRCFG->MC_BASE2.CFG_DFI_T_DRAM_CLK_ENABLE.CFG_DFI_T_DRAM_CLK_ENABLE =\
        LIBERO_SETTING_CFG_DFI_T_DRAM_CLK_ENABLE;
    DDRCFG->MC_BASE2.CFG_IDLE_TIME_TO_SELF_REFRESH.CFG_IDLE_TIME_TO_SELF_REFRESH =\
        LIBERO_SETTING_CFG_IDLE_TIME_TO_SELF_REFRESH;
    DDRCFG->MC_BASE2.CFG_IDLE_TIME_TO_POWER_DOWN.CFG_IDLE_TIME_TO_POWER_DOWN =\
        LIBERO_SETTING_CFG_IDLE_TIME_TO_POWER_DOWN;
    DDRCFG->MC_BASE2.CFG_BURST_RW_REFRESH_HOLDOFF.CFG_BURST_RW_REFRESH_HOLDOFF =\
        LIBERO_SETTING_CFG_BURST_RW_REFRESH_HOLDOFF;
    DDRCFG->MC_BASE2.CFG_BG_INTERLEAVE.CFG_BG_INTERLEAVE =\
        LIBERO_SETTING_CFG_BG_INTERLEAVE;
    DDRCFG->MC_BASE2.CFG_REFRESH_DURING_PHY_TRAINING.CFG_REFRESH_DURING_PHY_TRAINING =\
        LIBERO_SETTING_CFG_REFRESH_DURING_PHY_TRAINING;
    DDRCFG->MPFE.CFG_STARVE_TIMEOUT_P0.CFG_STARVE_TIMEOUT_P0 =\
        LIBERO_SETTING_CFG_STARVE_TIMEOUT_P0;
    DDRCFG->MPFE.CFG_STARVE_TIMEOUT_P1.CFG_STARVE_TIMEOUT_P1 =\
        LIBERO_SETTING_CFG_STARVE_TIMEOUT_P1;
    DDRCFG->MPFE.CFG_STARVE_TIMEOUT_P2.CFG_STARVE_TIMEOUT_P2 =\
        LIBERO_SETTING_CFG_STARVE_TIMEOUT_P2;
    DDRCFG->MPFE.CFG_STARVE_TIMEOUT_P3.CFG_STARVE_TIMEOUT_P3 =\
        LIBERO_SETTING_CFG_STARVE_TIMEOUT_P3;
    DDRCFG->MPFE.CFG_STARVE_TIMEOUT_P4.CFG_STARVE_TIMEOUT_P4 =\
        LIBERO_SETTING_CFG_STARVE_TIMEOUT_P4;
    DDRCFG->MPFE.CFG_STARVE_TIMEOUT_P5.CFG_STARVE_TIMEOUT_P5 =\
        LIBERO_SETTING_CFG_STARVE_TIMEOUT_P5;
    DDRCFG->MPFE.CFG_STARVE_TIMEOUT_P6.CFG_STARVE_TIMEOUT_P6 =\
        LIBERO_SETTING_CFG_STARVE_TIMEOUT_P6;
    DDRCFG->MPFE.CFG_STARVE_TIMEOUT_P7.CFG_STARVE_TIMEOUT_P7 =\
        LIBERO_SETTING_CFG_STARVE_TIMEOUT_P7;
    DDRCFG->REORDER.CFG_REORDER_EN.CFG_REORDER_EN =\
        LIBERO_SETTING_CFG_REORDER_EN;
    DDRCFG->REORDER.CFG_REORDER_QUEUE_EN.CFG_REORDER_QUEUE_EN =\
        LIBERO_SETTING_CFG_REORDER_QUEUE_EN;
    DDRCFG->REORDER.CFG_INTRAPORT_REORDER_EN.CFG_INTRAPORT_REORDER_EN =\
        LIBERO_SETTING_CFG_INTRAPORT_REORDER_EN;
    DDRCFG->REORDER.CFG_MAINTAIN_COHERENCY.CFG_MAINTAIN_COHERENCY =\
        LIBERO_SETTING_CFG_MAINTAIN_COHERENCY;
    DDRCFG->REORDER.CFG_Q_AGE_LIMIT.CFG_Q_AGE_LIMIT =\
        LIBERO_SETTING_CFG_Q_AGE_LIMIT;
    DDRCFG->REORDER.CFG_RO_CLOSED_PAGE_POLICY.CFG_RO_CLOSED_PAGE_POLICY =\
        LIBERO_SETTING_CFG_RO_CLOSED_PAGE_POLICY;
    DDRCFG->REORDER.CFG_REORDER_RW_ONLY.CFG_REORDER_RW_ONLY =\
        LIBERO_SETTING_CFG_REORDER_RW_ONLY;
    DDRCFG->REORDER.CFG_RO_PRIORITY_EN.CFG_RO_PRIORITY_EN =\
        LIBERO_SETTING_CFG_RO_PRIORITY_EN;
    DDRCFG->RMW.CFG_DM_EN.CFG_DM_EN = LIBERO_SETTING_CFG_DM_EN;
    DDRCFG->RMW.CFG_RMW_EN.CFG_RMW_EN = LIBERO_SETTING_CFG_RMW_EN;
    DDRCFG->ECC.CFG_ECC_CORRECTION_EN.CFG_ECC_CORRECTION_EN =\
        LIBERO_SETTING_CFG_ECC_CORRECTION_EN;
    DDRCFG->ECC.CFG_ECC_BYPASS.CFG_ECC_BYPASS = LIBERO_SETTING_CFG_ECC_BYPASS;
    DDRCFG->ECC.INIT_WRITE_DATA_1B_ECC_ERROR_GEN.INIT_WRITE_DATA_1B_ECC_ERROR_GEN =\
        LIBERO_SETTING_INIT_WRITE_DATA_1B_ECC_ERROR_GEN;
    DDRCFG->ECC.INIT_WRITE_DATA_2B_ECC_ERROR_GEN.INIT_WRITE_DATA_2B_ECC_ERROR_GEN =\
        LIBERO_SETTING_INIT_WRITE_DATA_2B_ECC_ERROR_GEN;
    DDRCFG->ECC.CFG_ECC_1BIT_INT_THRESH.CFG_ECC_1BIT_INT_THRESH =\
        LIBERO_SETTING_CFG_ECC_1BIT_INT_THRESH;
    DDRCFG->READ_CAPT.INIT_READ_CAPTURE_ADDR.INIT_READ_CAPTURE_ADDR =\
        LIBERO_SETTING_INIT_READ_CAPTURE_ADDR;
    DDRCFG->MTA.CFG_ERROR_GROUP_SEL.CFG_ERROR_GROUP_SEL =\
        LIBERO_SETTING_CFG_ERROR_GROUP_SEL;
    DDRCFG->MTA.CFG_DATA_SEL.CFG_DATA_SEL = LIBERO_SETTING_CFG_DATA_SEL;
    DDRCFG->MTA.CFG_TRIG_MODE.CFG_TRIG_MODE = LIBERO_SETTING_CFG_TRIG_MODE;
    DDRCFG->MTA.CFG_POST_TRIG_CYCS.CFG_POST_TRIG_CYCS =\
        LIBERO_SETTING_CFG_POST_TRIG_CYCS;
    DDRCFG->MTA.CFG_TRIG_MASK.CFG_TRIG_MASK = LIBERO_SETTING_CFG_TRIG_MASK;
    DDRCFG->MTA.CFG_EN_MASK.CFG_EN_MASK = LIBERO_SETTING_CFG_EN_MASK;
    DDRCFG->MTA.MTC_ACQ_ADDR.MTC_ACQ_ADDR = LIBERO_SETTING_MTC_ACQ_ADDR;
    DDRCFG->MTA.CFG_TRIG_MT_ADDR_0.CFG_TRIG_MT_ADDR_0 =\
        LIBERO_SETTING_CFG_TRIG_MT_ADDR_0;
    DDRCFG->MTA.CFG_TRIG_MT_ADDR_1.CFG_TRIG_MT_ADDR_1 =\
        LIBERO_SETTING_CFG_TRIG_MT_ADDR_1;
    DDRCFG->MTA.CFG_TRIG_ERR_MASK_0.CFG_TRIG_ERR_MASK_0 =\
        LIBERO_SETTING_CFG_TRIG_ERR_MASK_0;
    DDRCFG->MTA.CFG_TRIG_ERR_MASK_1.CFG_TRIG_ERR_MASK_1 =\
        LIBERO_SETTING_CFG_TRIG_ERR_MASK_1;
    DDRCFG->MTA.CFG_TRIG_ERR_MASK_2.CFG_TRIG_ERR_MASK_2 =\
        LIBERO_SETTING_CFG_TRIG_ERR_MASK_2;
    DDRCFG->MTA.CFG_TRIG_ERR_MASK_3.CFG_TRIG_ERR_MASK_3 =\
        LIBERO_SETTING_CFG_TRIG_ERR_MASK_3;
    DDRCFG->MTA.CFG_TRIG_ERR_MASK_4.CFG_TRIG_ERR_MASK_4 =\
        LIBERO_SETTING_CFG_TRIG_ERR_MASK_4;
    DDRCFG->MTA.MTC_ACQ_WR_DATA_0.MTC_ACQ_WR_DATA_0 =\
        LIBERO_SETTING_MTC_ACQ_WR_DATA_0;
    DDRCFG->MTA.MTC_ACQ_WR_DATA_1.MTC_ACQ_WR_DATA_1 =\
        LIBERO_SETTING_MTC_ACQ_WR_DATA_1;
    DDRCFG->MTA.MTC_ACQ_WR_DATA_2.MTC_ACQ_WR_DATA_2 =\
        LIBERO_SETTING_MTC_ACQ_WR_DATA_2;
    DDRCFG->MTA.CFG_PRE_TRIG_CYCS.CFG_PRE_TRIG_CYCS =\
        LIBERO_SETTING_CFG_PRE_TRIG_CYCS;
    DDRCFG->MTA.CFG_DATA_SEL_FIRST_ERROR.CFG_DATA_SEL_FIRST_ERROR =\
        LIBERO_SETTING_CFG_DATA_SEL_FIRST_ERROR;
    DDRCFG->DYN_WIDTH_ADJ.CFG_DQ_WIDTH.CFG_DQ_WIDTH =\
        LIBERO_SETTING_CFG_DQ_WIDTH;
    DDRCFG->DYN_WIDTH_ADJ.CFG_ACTIVE_DQ_SEL.CFG_ACTIVE_DQ_SEL =\
        LIBERO_SETTING_CFG_ACTIVE_DQ_SEL;
    DDRCFG->CA_PAR_ERR.INIT_CA_PARITY_ERROR_GEN_REQ.INIT_CA_PARITY_ERROR_GEN_REQ =\
        LIBERO_SETTING_INIT_CA_PARITY_ERROR_GEN_REQ;
    DDRCFG->CA_PAR_ERR.INIT_CA_PARITY_ERROR_GEN_CMD.INIT_CA_PARITY_ERROR_GEN_CMD =\
        LIBERO_SETTING_INIT_CA_PARITY_ERROR_GEN_CMD;
    DDRCFG->DFI.CFG_DFI_T_RDDATA_EN.CFG_DFI_T_RDDATA_EN =\
        LIBERO_SETTING_CFG_DFI_T_RDDATA_EN;
    DDRCFG->DFI.CFG_DFI_T_PHY_RDLAT.CFG_DFI_T_PHY_RDLAT =\
        LIBERO_SETTING_CFG_DFI_T_PHY_RDLAT;
    DDRCFG->DFI.CFG_DFI_T_PHY_WRLAT.CFG_DFI_T_PHY_WRLAT =\
        LIBERO_SETTING_CFG_DFI_T_PHY_WRLAT;
    DDRCFG->DFI.CFG_DFI_PHYUPD_EN.CFG_DFI_PHYUPD_EN =\
        LIBERO_SETTING_CFG_DFI_PHYUPD_EN;
    DDRCFG->DFI.INIT_DFI_LP_DATA_REQ.INIT_DFI_LP_DATA_REQ =\
        LIBERO_SETTING_INIT_DFI_LP_DATA_REQ;
    DDRCFG->DFI.INIT_DFI_LP_CTRL_REQ.INIT_DFI_LP_CTRL_REQ =\
        LIBERO_SETTING_INIT_DFI_LP_CTRL_REQ;
    DDRCFG->DFI.INIT_DFI_LP_WAKEUP.INIT_DFI_LP_WAKEUP =\
        LIBERO_SETTING_INIT_DFI_LP_WAKEUP;
    DDRCFG->DFI.INIT_DFI_DRAM_CLK_DISABLE.INIT_DFI_DRAM_CLK_DISABLE =\
        LIBERO_SETTING_INIT_DFI_DRAM_CLK_DISABLE;
    DDRCFG->DFI.CFG_DFI_DATA_BYTE_DISABLE.CFG_DFI_DATA_BYTE_DISABLE =\
        LIBERO_SETTING_CFG_DFI_DATA_BYTE_DISABLE;
    DDRCFG->DFI.CFG_DFI_LVL_SEL.CFG_DFI_LVL_SEL =\
        LIBERO_SETTING_CFG_DFI_LVL_SEL;
    DDRCFG->DFI.CFG_DFI_LVL_PERIODIC.CFG_DFI_LVL_PERIODIC =\
        LIBERO_SETTING_CFG_DFI_LVL_PERIODIC;
    DDRCFG->DFI.CFG_DFI_LVL_PATTERN.CFG_DFI_LVL_PATTERN =\
        LIBERO_SETTING_CFG_DFI_LVL_PATTERN;
    DDRCFG->DFI.PHY_DFI_INIT_START.PHY_DFI_INIT_START =\
        LIBERO_SETTING_PHY_DFI_INIT_START;
    DDRCFG->AXI_IF.CFG_AXI_START_ADDRESS_AXI1_0.CFG_AXI_START_ADDRESS_AXI1_0 =\
        LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI1_0;
    DDRCFG->AXI_IF.CFG_AXI_START_ADDRESS_AXI1_1.CFG_AXI_START_ADDRESS_AXI1_1 =\
        LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI1_1;
    DDRCFG->AXI_IF.CFG_AXI_START_ADDRESS_AXI2_0.CFG_AXI_START_ADDRESS_AXI2_0 =\
        LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI2_0;
    DDRCFG->AXI_IF.CFG_AXI_START_ADDRESS_AXI2_1.CFG_AXI_START_ADDRESS_AXI2_1 =\
        LIBERO_SETTING_CFG_AXI_START_ADDRESS_AXI2_1;
    DDRCFG->AXI_IF.CFG_AXI_END_ADDRESS_AXI1_0.CFG_AXI_END_ADDRESS_AXI1_0 =\
        LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI1_0;
    DDRCFG->AXI_IF.CFG_AXI_END_ADDRESS_AXI1_1.CFG_AXI_END_ADDRESS_AXI1_1 =\
        LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI1_1;
    DDRCFG->AXI_IF.CFG_AXI_END_ADDRESS_AXI2_0.CFG_AXI_END_ADDRESS_AXI2_0 =\
        LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI2_0;
    DDRCFG->AXI_IF.CFG_AXI_END_ADDRESS_AXI2_1.CFG_AXI_END_ADDRESS_AXI2_1 =\
        LIBERO_SETTING_CFG_AXI_END_ADDRESS_AXI2_1;
    DDRCFG->AXI_IF.CFG_MEM_START_ADDRESS_AXI1_0.CFG_MEM_START_ADDRESS_AXI1_0 =\
        LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI1_0;
    DDRCFG->AXI_IF.CFG_MEM_START_ADDRESS_AXI1_1.CFG_MEM_START_ADDRESS_AXI1_1 =\
        LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI1_1;
    DDRCFG->AXI_IF.CFG_MEM_START_ADDRESS_AXI2_0.CFG_MEM_START_ADDRESS_AXI2_0 =\
        LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI2_0;
    DDRCFG->AXI_IF.CFG_MEM_START_ADDRESS_AXI2_1.CFG_MEM_START_ADDRESS_AXI2_1 =\
        LIBERO_SETTING_CFG_MEM_START_ADDRESS_AXI2_1;
    DDRCFG->AXI_IF.CFG_ENABLE_BUS_HOLD_AXI1.CFG_ENABLE_BUS_HOLD_AXI1 =\
        LIBERO_SETTING_CFG_ENABLE_BUS_HOLD_AXI1;
    DDRCFG->AXI_IF.CFG_ENABLE_BUS_HOLD_AXI2.CFG_ENABLE_BUS_HOLD_AXI2 =\
        LIBERO_SETTING_CFG_ENABLE_BUS_HOLD_AXI2;
    DDRCFG->AXI_IF.CFG_AXI_AUTO_PCH.CFG_AXI_AUTO_PCH =\
        LIBERO_SETTING_CFG_AXI_AUTO_PCH;
    DDRCFG->csr_custom.PHY_RESET_CONTROL.PHY_RESET_CONTROL =\
        LIBERO_SETTING_PHY_RESET_CONTROL;
    DDRCFG->csr_custom.PHY_RESET_CONTROL.PHY_RESET_CONTROL =\
        (LIBERO_SETTING_PHY_RESET_CONTROL & ~0x8000UL);
    DDRCFG->csr_custom.PHY_PC_RANK.PHY_PC_RANK = LIBERO_SETTING_PHY_PC_RANK;
    DDRCFG->csr_custom.PHY_RANKS_TO_TRAIN.PHY_RANKS_TO_TRAIN =\
        LIBERO_SETTING_PHY_RANKS_TO_TRAIN;
    DDRCFG->csr_custom.PHY_WRITE_REQUEST.PHY_WRITE_REQUEST =\
        LIBERO_SETTING_PHY_WRITE_REQUEST;
    DDRCFG->csr_custom.PHY_READ_REQUEST.PHY_READ_REQUEST =\
        LIBERO_SETTING_PHY_READ_REQUEST;
    DDRCFG->csr_custom.PHY_WRITE_LEVEL_DELAY.PHY_WRITE_LEVEL_DELAY =\
        LIBERO_SETTING_PHY_WRITE_LEVEL_DELAY;
    DDRCFG->csr_custom.PHY_GATE_TRAIN_DELAY.PHY_GATE_TRAIN_DELAY =\
        LIBERO_SETTING_PHY_GATE_TRAIN_DELAY;
    DDRCFG->csr_custom.PHY_EYE_TRAIN_DELAY.PHY_EYE_TRAIN_DELAY =\
        LIBERO_SETTING_PHY_EYE_TRAIN_DELAY;
    DDRCFG->csr_custom.PHY_EYE_PAT.PHY_EYE_PAT = LIBERO_SETTING_PHY_EYE_PAT;
    DDRCFG->csr_custom.PHY_START_RECAL.PHY_START_RECAL =\
        LIBERO_SETTING_PHY_START_RECAL;
    DDRCFG->csr_custom.PHY_CLR_DFI_LVL_PERIODIC.PHY_CLR_DFI_LVL_PERIODIC =\
        LIBERO_SETTING_PHY_CLR_DFI_LVL_PERIODIC;
    DDRCFG->csr_custom.PHY_TRAIN_STEP_ENABLE.PHY_TRAIN_STEP_ENABLE =\
        LIBERO_SETTING_PHY_TRAIN_STEP_ENABLE;
    DDRCFG->csr_custom.PHY_LPDDR_DQ_CAL_PAT.PHY_LPDDR_DQ_CAL_PAT =\
        LIBERO_SETTING_PHY_LPDDR_DQ_CAL_PAT;
    DDRCFG->csr_custom.PHY_INDPNDT_TRAINING.PHY_INDPNDT_TRAINING =\
        LIBERO_SETTING_PHY_INDPNDT_TRAINING;
    DDRCFG->csr_custom.PHY_ENCODED_QUAD_CS.PHY_ENCODED_QUAD_CS =\
        LIBERO_SETTING_PHY_ENCODED_QUAD_CS;
    DDRCFG->csr_custom.PHY_HALF_CLK_DLY_ENABLE.PHY_HALF_CLK_DLY_ENABLE =\
        LIBERO_SETTING_PHY_HALF_CLK_DLY_ENABLE;

}


/**
 * setup_ddr_segments(void)
 * setup segment registers- translated DDR address as user requires
 */
void setup_ddr_segments(SEG_SETUP option)
{
    if(option == DEFAULT_SEG_SETUP)
    {
        SEG[0].u[0].raw = (INIT_SETTING_SEG0_0 & 0x7FFFUL);
        SEG[0].u[1].raw = (INIT_SETTING_SEG0_1 & 0x7FFFUL);
        SEG[1].u[2].raw = (INIT_SETTING_SEG1_2 & 0x7FFFUL);
        SEG[1].u[3].raw = (INIT_SETTING_SEG1_3 & 0x7FFFUL);
        SEG[1].u[4].raw = (INIT_SETTING_SEG1_4 & 0x7FFFUL);
        SEG[1].u[5].raw = (INIT_SETTING_SEG1_5 & 0x7FFFUL);
    }
    else
    {
        SEG[0].u[0].raw = (LIBERO_SETTING_SEG0_0 & 0x7FFFUL);
        SEG[0].u[1].raw = (LIBERO_SETTING_SEG0_1 & 0x7FFFUL);
        SEG[1].u[2].raw = (LIBERO_SETTING_SEG1_2 & 0x7FFFUL);
        SEG[1].u[3].raw = (LIBERO_SETTING_SEG1_3 & 0x7FFFUL);
        SEG[1].u[4].raw = (LIBERO_SETTING_SEG1_4 & 0x7FFFUL);
        SEG[1].u[5].raw = (LIBERO_SETTING_SEG1_5 & 0x7FFFUL);
    }
    /*
     * disable ddr blocker
     * Is cleared at reset. When written to '1' disables the blocker function
     * allowing the L2 cache controller to access the DDRC. Once written to '1'
     * the register cannot be written to 0, only an MSS reset will clear the
     * register
     */
    SEG[0].u[7].raw = 0x01U;
}

/**
 * use_software_bclk_sclk_training()
 * @param ddr_type
 * @return returns 1U if required, otherwise 0U
 */
static uint8_t use_software_bclk_sclk_training(DDR_TYPE ddr_type)
{
    uint8_t result = 0U;
    switch (ddr_type)
    {
        default:
        case DDR_OFF_MODE:
            break;
        case DDR3L:
            result = 1U;
            break;
        case DDR3:
            result = 1U;
            break;
        case DDR4:
            result = 1U;
            break;
        case LPDDR3:
            result = 1U;
            break;
        case LPDDR4:
            result = 1U;
            break;
    }
    return(result);
}

/**
 * config_ddr_io_pull_up_downs_rpc_bits()
 *
 * This function overrides the RPC bits related to weak pull up and
 * weak pull downs. It also sets the override bit if the I/O is disabled.
 * The settings come fro m Libero
 *
 * Note: If LIBERO_SETTING_RPC_EN_ADDCMD0_OVRT9 is not present, indicates older
 * Libero core (pre 2.0.109)
 * Post 2.0.109 version of Libero MSS core, weak pull up and pull down
 * settings come from Libero, along with setting unused MSS DDR I/O to
 * override.
 *
 */
static void config_ddr_io_pull_up_downs_rpc_bits(DDR_TYPE ddr_type)
{
    if(ddr_type == LPDDR4) /* we will add other variants here once verified */
    {
#ifdef LIBERO_SETTING_RPC_EN_ADDCMD0_OVRT9
        /* set over-rides (associated bit set to 1 if I/O not being used */
        CFG_DDR_SGMII_PHY->ovrt9.ovrt9   = LIBERO_SETTING_RPC_EN_ADDCMD0_OVRT9;
        CFG_DDR_SGMII_PHY->ovrt10.ovrt10 = LIBERO_SETTING_RPC_EN_ADDCMD1_OVRT10;
        CFG_DDR_SGMII_PHY->ovrt11.ovrt11 = LIBERO_SETTING_RPC_EN_ADDCMD2_OVRT11;
        CFG_DDR_SGMII_PHY->ovrt12.ovrt12 = LIBERO_SETTING_RPC_EN_DATA0_OVRT12;
        CFG_DDR_SGMII_PHY->ovrt13.ovrt13 = LIBERO_SETTING_RPC_EN_DATA1_OVRT13;
        CFG_DDR_SGMII_PHY->ovrt14.ovrt14 = LIBERO_SETTING_RPC_EN_DATA2_OVRT14;
        CFG_DDR_SGMII_PHY->ovrt15.ovrt15 = LIBERO_SETTING_RPC_EN_DATA3_OVRT15;
        CFG_DDR_SGMII_PHY->ovrt16.ovrt16 = LIBERO_SETTING_RPC_EN_ECC_OVRT16;
        /* set the required wpu state- note: associated I/O bit 1=> off, 0=> on */
        CFG_DDR_SGMII_PHY->rpc235.rpc235 = LIBERO_SETTING_RPC235_WPD_ADD_CMD0;
        CFG_DDR_SGMII_PHY->rpc236.rpc236 = LIBERO_SETTING_RPC236_WPD_ADD_CMD1;
        CFG_DDR_SGMII_PHY->rpc237.rpc237 = LIBERO_SETTING_RPC237_WPD_ADD_CMD2;
        CFG_DDR_SGMII_PHY->rpc238.rpc238 = LIBERO_SETTING_RPC238_WPD_DATA0;
        CFG_DDR_SGMII_PHY->rpc239.rpc239 = LIBERO_SETTING_RPC239_WPD_DATA1;
        CFG_DDR_SGMII_PHY->rpc240.rpc240 = LIBERO_SETTING_RPC240_WPD_DATA2;
        CFG_DDR_SGMII_PHY->rpc241.rpc241 = LIBERO_SETTING_RPC241_WPD_DATA3;
        CFG_DDR_SGMII_PHY->rpc242.rpc242 = LIBERO_SETTING_RPC242_WPD_ECC;
        /* set the required wpd state- note: associated I/O bit 1=> off, 0=> on */
        CFG_DDR_SGMII_PHY->rpc243.rpc243 = LIBERO_SETTING_RPC243_WPU_ADD_CMD0;
        CFG_DDR_SGMII_PHY->rpc244.rpc244 = LIBERO_SETTING_RPC244_WPU_ADD_CMD1;
        CFG_DDR_SGMII_PHY->rpc245.rpc245 = LIBERO_SETTING_RPC245_WPU_ADD_CMD2;
        CFG_DDR_SGMII_PHY->rpc246.rpc246 = LIBERO_SETTING_RPC246_WPU_DATA0;
        CFG_DDR_SGMII_PHY->rpc247.rpc247 = LIBERO_SETTING_RPC247_WPU_DATA1;
        CFG_DDR_SGMII_PHY->rpc248.rpc248 = LIBERO_SETTING_RPC248_WPU_DATA2;
        CFG_DDR_SGMII_PHY->rpc249.rpc249 = LIBERO_SETTING_RPC249_WPU_DATA3;
        CFG_DDR_SGMII_PHY->rpc250.rpc250 = LIBERO_SETTING_RPC250_WPU_ECC;
#endif
    }
}


/**
 * get the best sweep value
 * @param good_index
 * @return
 */
#ifdef SWEEP_ENABLED
static uint8_t get_best_sweep(sweep_index *good_index)
{
#ifdef EXTRACT_SWEEP_RESULT
    uint8_t cmd_index;
    uint8_t bclk_sclk_index;
    uint8_t dpc_vgen_index;
    uint8_t dpc_vgen_h_index;
    uint8_t dpc_vgen_vs_index;
    uint8_t good_in_row;

    for (dpc_vgen_vs_index=0U; dpc_vgen_vs_index < MAX_NUMBER_DPC_VS_GEN_SWEEPS; dpc_vgen_vs_index++)
    {
        for (dpc_vgen_h_index=0U; dpc_vgen_h_index < MAX_NUMBER_DPC_H_GEN_SWEEPS; dpc_vgen_h_index++)
        {
            for (dpc_vgen_index=0U; dpc_vgen_index < MAX_NUMBER_DPC_V_GEN_SWEEPS; dpc_vgen_index++)
            {
                for (bclk_sclk_index=0U; bclk_sclk_index < MAX_NUMBER__BCLK_SCLK_OFFSET_SWEEPS; bclk_sclk_index++)
                {
                    good_in_row = 0U;
                    for (cmd_index=0U; cmd_index < MAX_NUMBER_ADDR_CMD_OFFSET_SWEEPS; cmd_index++)
                    {
                        if (sweep_results[dpc_vgen_vs_index][dpc_vgen_h_index][dpc_vgen_index][bclk_sclk_index][cmd_index]\
                                == CALIBRATION_PASSED)
                        {
                            good_in_row++;
                            /*
                             * look for 3 in a row,in x and y direction and pick the
                             * middle one
                             * */
                            if((good_in_row > 2U)&&(bclk_sclk_index>1)&&(bclk_sclk_index<MAX_NUMBER__BCLK_SCLK_OFFSET_SWEEPS-1))
                            {
                                if ((sweep_results[dpc_vgen_vs_index]\
                                        [dpc_vgen_h_index][dpc_vgen_index]\
                                        [bclk_sclk_index-1][cmd_index]\
                                                == CALIBRATION_PASSED)&&\
                                        (sweep_results[dpc_vgen_vs_index]\
                                                [dpc_vgen_h_index]\
                                                [dpc_vgen_index]\
                                                [bclk_sclk_index+1][cmd_index]\
                                                         == CALIBRATION_PASSED))
                                {
                                    good_index->dpc_vgen_vs_index = dpc_vgen_vs_index;
                                    good_index->dpc_vgen_h_index = dpc_vgen_h_index;
                                    good_index->bclk_sclk_index = bclk_sclk_index;
                                    good_index->dpc_vgen_index = dpc_vgen_index;
                                    good_index->cmd_index = cmd_index - 1U;
                                    return(0U);
                                }
                            }
                        }
                        else
                        {
                            good_in_row = 0U;
                        }
                    }
                }
            }
        }
    }
    return(1U);
#else  /* EXTRACT_SWEEP_RESULT */
    good_index->dpc_vgen_vs_index = 0U;
    good_index->dpc_vgen_h_index = 0U;
    good_index->bclk_sclk_index = 0U;
    good_index->dpc_vgen_index = 0U;
    good_index->cmd_index = 0U;
    return(0U);
#endif
}
#endif /* SWEEP_ENABLED */


#ifdef DDR_DIAGNOSTICS /* todo: add support for diagnostics below during board bring-up */

/*-------------------------------------------------------------------------*//**
  The MSS_DDR_status() function is used to return status information to the
  user.

  TODO: Define number of request inputs

   @param option
    This option chooses status data we wish returned

   @param return_data
    Returned data here. This must be within a defined range.
    todo:Detail on the sharing of data will be system dependent.
    AMP/SMU detail to be finalized at time of writing

  @return
    Returns 0 on success.
    TODO: Define error codes.

  Example:
    The call to MSS_DDR_status(DDR_TYPE, return_data) will return 0 if
    successful and the DDR type in the first four bytes of the ret_mem area.
    @code
    MSS_DDR_status( DDR_TYPE, ret_mem );
    @endcode
 */
uint8_t
MSS_DDR_status
(
    uint8_t option, uint32_t *return_data
)
{
  uint8_t error = 0U;

  switch (option)
  {
    case USR_OPTION_tip_register_dump:
        /* todo: WIP
         * add commands here */
      break;

    default:

      break;
  }

  return error;
}


/*-------------------------------------------------------------------------*//**
 * MSS_DDR_user_commands commands from the user
 *
 * @param command
 *   User command
 * @param extra_command_data
 *   extra data from user for particular command
 * @param return_data
 *   data returned via supplied pointer
 * @return
 *   status 0 => success
 *
 *  Example:
      The call to
      MSS_DDR_user_commands(USR_CMD_INC_DELAY_LINE, 0x01 , return_data)
      will return 0 id successful and the
      DDR type in the first four bytes of the ret_mem area.
      @code
      MSS_DDR_user_commands(USR_CMD_INC_DELAY_LINE, 0x01 , return_data);
      @endcode
 */
uint8_t
MSS_DDR_user_commands
(
    uint8_t command, uint32_t *extra_command_data, uint32_t *return_data,  \
        uint32_t return_size
)
{
  uint8_t error = 0U;
  uint32_t *reg_address;

  switch (command)
  {
    case USR_CMD_GET_DDR_STATUS:
      break;
        case USR_CMD_GET_MODE_SETTING:
            break;
        case USR_CMD_GET_W_CALIBRATION:
            config_copy(return_data, &calib_data, sizeof(calib_data));
            break;
        case USR_CMD_GET_GREEN_ZONE:
            /* READ DQ WINDOW MEASUREMENT */
            /* READ DQS WINDOW MEASUREMENT */
            /* READ VREF WINDOW MAX MEASUREMENT */

            break;

        case USR_CMD_GET_REG:
            /*
             * First check if address valid
             */
            config_copy(reg_address, extra_command_data, 4U);
            reg_address = (uint32_t *)((uint32_t)reg_address &\
                (uint32_t)(0xFFFFFFFCUL));
            if ((reg_address >=\
                &CFG_DDR_SGMII_PHY->SOFT_RESET_DDR_PHY.SOFT_RESET_DDR_PHY)\
                && (reg_address < &CFG_DDR_SGMII_PHY->SPARE_STAT.SPARE_STAT))
            {
                config_copy(return_data, reg_address, sizeof(uint32_t));
            }
            else
            {
                error = 1U;
            }
            break;

        /*
         * And set commands
         */
        case USR_CMD_SET_GREEN_ZONE_DQ:
            /* READ DQ WINDOW MEASUREMENT */
            /*
             * This procedure is uses reads/writes & DQ delayline controls, to
             * measure the maximum DQ offset before failure.
             */
            break;
        case USR_CMD_SET_GREEN_ZONE_DQS:
            /* READ DQS WINDOW MEASUREMENT */
            /*
             * This procedure is uses reads/writes & DQS delayline controls, to
             * measure the maximum DQS offset before failure.
             */
            break;
        case USR_CMD_SET_GREEN_ZONE_VREF_MAX:
            /* READ VREF WINDOW MAX MEASUREMENT */
            /*
             * This procedure is uses reads/writes & VREF controller delayline
             * controls, to measure the max VREF level.
             */
            break;
        case USR_CMD_SET_GREEN_ZONE_VREF_MIN:
            /* READ VREF WINDOW MIN MEASUREMENT */
            /*
             * This procedure is uses reads/writes & VREF controller delayline
             * controls, to measure the minimum VREF level.
             */
            break;
        case USR_CMD_SET_RETRAIN:
            /* Incremental, In-System Retraining Procedures */
            /*
             * This procedure adjusts the read window to re-center clock and
             * data.
             * It should be triggered when the DLL code value passes a certain
             * threshold, during a refresh cycle.
             * Added here to allow the user to trigger.
             */
            break;
        case USR_CMD_SET_REG:
            break;

        default:
            error = 1U;
            break;
    }
    return error;
}
#endif

#ifdef DEBUG_DDR_INIT
#ifdef DEBUG_DDR_DDRCFG
void debug_read_ddrcfg(void)
{
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->ADDR_MAP,\
                (sizeof(DDRCFG->ADDR_MAP)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->MC_BASE3,\
                (sizeof(DDRCFG->MC_BASE3)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->MC_BASE1,\
                (sizeof(DDRCFG->MC_BASE1)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->MC_BASE2,\
                (sizeof(DDRCFG->MC_BASE2)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->MPFE,\
                (sizeof(DDRCFG->MPFE)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->REORDER,\
                (sizeof(DDRCFG->REORDER)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->RMW,\
                (sizeof(DDRCFG->RMW)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->ECC,\
                (sizeof(DDRCFG->ECC)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->READ_CAPT,\
                (sizeof(DDRCFG->READ_CAPT)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->MTA,\
                (sizeof(DDRCFG->MTA)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->DYN_WIDTH_ADJ,\
                (sizeof(DDRCFG->DYN_WIDTH_ADJ)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->CA_PAR_ERR,\
                (sizeof(DDRCFG->CA_PAR_ERR)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->DFI,\
                (sizeof(DDRCFG->DFI)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->AXI_IF,\
                (sizeof(DDRCFG->AXI_IF)/4U));
    (void)print_reg_array(g_debug_uart ,
                (uint32_t *)&DDRCFG->csr_custom,\
                (sizeof(DDRCFG->csr_custom)/4U));
    return;
}
#endif
#endif


const uint8_t REFCLK_OFFSETS[][5U] = {
                {LIBERO_SETTING_REFCLK_DDR3_1600_NUM_OFFSETS,
                LIBERO_SETTING_REFCLK_DDR3_1600_OFFSET_0,
                LIBERO_SETTING_REFCLK_DDR3_1600_OFFSET_1,
                LIBERO_SETTING_REFCLK_DDR3_1600_OFFSET_2,
                LIBERO_SETTING_REFCLK_DDR3_1600_OFFSET_3},
                {
                LIBERO_SETTING_REFCLK_DDR3L_1600_NUM_OFFSETS,
                LIBERO_SETTING_REFCLK_DDR3L_1600_OFFSET_0,
                LIBERO_SETTING_REFCLK_DDR3L_1600_OFFSET_1,
                LIBERO_SETTING_REFCLK_DDR3L_1600_OFFSET_2,
                LIBERO_SETTING_REFCLK_DDR3_1600_OFFSET_3},
                {
                LIBERO_SETTING_REFCLK_DDR4_1600_NUM_OFFSETS,
                LIBERO_SETTING_REFCLK_DDR4_1600_OFFSET_0,
                LIBERO_SETTING_REFCLK_DDR4_1600_OFFSET_1,
                LIBERO_SETTING_REFCLK_DDR4_1600_OFFSET_2,
                LIBERO_SETTING_REFCLK_DDR4_1600_OFFSET_3},
                {
                LIBERO_SETTING_REFCLK_LPDDR3_1600_NUM_OFFSETS,
                LIBERO_SETTING_REFCLK_LPDDR3_1600_OFFSET_0,
                LIBERO_SETTING_REFCLK_LPDDR3_1600_OFFSET_1,
                LIBERO_SETTING_REFCLK_LPDDR3_1600_OFFSET_2,
                LIBERO_SETTING_REFCLK_LPDDR3_1600_OFFSET_3},
                {
                LIBERO_SETTING_REFCLK_LPDDR4_1600_NUM_OFFSETS,
                LIBERO_SETTING_REFCLK_LPDDR4_1600_OFFSET_0,
                LIBERO_SETTING_REFCLK_LPDDR4_1600_OFFSET_1,
                LIBERO_SETTING_REFCLK_LPDDR4_1600_OFFSET_2,
                LIBERO_SETTING_REFCLK_LPDDR4_1600_OFFSET_3},

                {LIBERO_SETTING_REFCLK_DDR3_1333_NUM_OFFSETS,
                LIBERO_SETTING_REFCLK_DDR3_1333_OFFSET_0,
                LIBERO_SETTING_REFCLK_DDR3_1333_OFFSET_1,
                LIBERO_SETTING_REFCLK_DDR3_1333_OFFSET_2,
                LIBERO_SETTING_REFCLK_DDR3_1333_OFFSET_3},
                {
                LIBERO_SETTING_REFCLK_DDR3L_1333_NUM_OFFSETS,
                LIBERO_SETTING_REFCLK_DDR3L_1333_OFFSET_0,
                LIBERO_SETTING_REFCLK_DDR3L_1333_OFFSET_1,
                LIBERO_SETTING_REFCLK_DDR3L_1333_OFFSET_2,
                LIBERO_SETTING_REFCLK_DDR3_1333_OFFSET_3},
                {
                LIBERO_SETTING_REFCLK_DDR4_1333_NUM_OFFSETS,
                LIBERO_SETTING_REFCLK_DDR4_1333_OFFSET_0,
                LIBERO_SETTING_REFCLK_DDR4_1333_OFFSET_1,
                LIBERO_SETTING_REFCLK_DDR4_1333_OFFSET_2,
                LIBERO_SETTING_REFCLK_DDR4_1333_OFFSET_3},
                {
                LIBERO_SETTING_REFCLK_LPDDR3_1333_NUM_OFFSETS,
                LIBERO_SETTING_REFCLK_LPDDR3_1333_OFFSET_0,
                LIBERO_SETTING_REFCLK_LPDDR3_1333_OFFSET_1,
                LIBERO_SETTING_REFCLK_LPDDR3_1333_OFFSET_2,
                LIBERO_SETTING_REFCLK_LPDDR3_1333_OFFSET_3},
                {
                LIBERO_SETTING_REFCLK_LPDDR4_1333_NUM_OFFSETS,
                LIBERO_SETTING_REFCLK_LPDDR4_1333_OFFSET_0,
                LIBERO_SETTING_REFCLK_LPDDR4_1333_OFFSET_1,
                LIBERO_SETTING_REFCLK_LPDDR4_1333_OFFSET_2,
                LIBERO_SETTING_REFCLK_LPDDR4_1333_OFFSET_3},
};

/**
 * ddr_manual_addcmd_refclk_offset This function determines current
 * sweep offset based on DDR type
 * @param ddr_type
 * @param refclk_sweep_index
 * @return
 */
#ifdef MANUAL_ADDCMD_TRAINIG
static uint8_t ddr_manual_addcmd_refclk_offset(DDR_TYPE ddr_type, uint8_t * refclk_sweep_index)
{
    uint8_t refclk_offset;
    uint8_t type_array_index;

    type_array_index = (uint8_t)ddr_type;
    if(LIBERO_SETTING_DDR_CLK == DDR_1333_MHZ)
    {
        type_array_index = type_array_index + (uint8_t)LPDDR4;
    }

    if (*refclk_sweep_index >= REFCLK_OFFSETS[type_array_index][0U])
    {
        *refclk_sweep_index = 0U;
    }

    refclk_offset = REFCLK_OFFSETS[type_array_index][*refclk_sweep_index + 1U];

    *refclk_sweep_index = (*refclk_sweep_index + 1U);

    return refclk_offset;
}
#endif


#endif /* DDR_SUPPORT */

