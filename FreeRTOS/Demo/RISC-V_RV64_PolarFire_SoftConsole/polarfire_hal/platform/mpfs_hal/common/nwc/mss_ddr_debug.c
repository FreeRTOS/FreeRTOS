/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_ddr_debug.h
 * @author Microchip FPGA Embedded Systems Solutions
 * @brief DDR write and read test functions
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "mpfs_hal/mss_hal.h"

/*******************************************************************************
 * Local Defines
 */
#define DDR_BASE            0x80000000u
#define DDR_SIZE            0x40000000u

#define PDMA_CHANNEL0_BASE_ADDRESS  0x3000000ULL
#define PDMA_CHANNEL1_BASE_ADDRESS  0x3001000ULL
#define PDMA_CHANNEL2_BASE_ADDRESS  0x3002000ULL
#define PDMA_CHANNEL3_BASE_ADDRESS  0x3003000ULL

const char *progress[3] = {"|\r", "/\r", "-\r"};
typedef void(*pattern_fct_t)(void);
static uint32_t g_test_buffer_cached[765];
static uint32_t g_test_buffer_not_cached[765];

/*******************************************************************************
 * External Defines
 */
#ifdef DEBUG_DDR_INIT
#ifdef SWEEP_ENABLED
extern uint8_t sweep_results[MAX_NUMBER_DPC_VS_GEN_SWEEPS]\
                            [MAX_NUMBER_DPC_H_GEN_SWEEPS]\
                            [MAX_NUMBER_DPC_V_GEN_SWEEPS]\
                            [MAX_NUMBER__BCLK_SCLK_OFFSET_SWEEPS]\
                            [MAX_NUMBER_ADDR_CMD_OFFSET_SWEEPS];
#endif
#endif
extern const uint32_t ddr_test_pattern[768];

/*******************************************************************************
 * External function declarations
 */
extern void delay(uint32_t n);
extern void pdma_transfer(uint64_t destination, uint64_t source, uint64_t size_in_bytes, uint64_t base_address);
extern void pdma_transfer_complete( uint64_t base_address);

/*******************************************************************************
 * Local data declarations
 */
#ifdef DEBUG_DDR_INIT
mss_uart_instance_t *g_debug_uart;
#endif

uint64_t ddr_test;

/*******************************************************************************
 * Local function declarations
 */
static uint32_t ddr_write ( volatile uint64_t *DDR_word_ptr,\
        uint32_t no_of_access, uint8_t data_ptrn, DDR_ACCESS_SIZE data_size );
static uint32_t ddr_read ( volatile uint64_t *DDR_word_ptr,\
        uint32_t no_of_access, uint8_t data_ptrn,  DDR_ACCESS_SIZE data_size );

#ifdef DEBUG_DDR_INIT
/***************************************************************************//**
 * Setup serial port if DDR debug required during start-up
 * @param uart Ref to uart you want to use
 * @return
 */

__attribute__((weak))\
        uint32_t setup_ddr_debug_port(mss_uart_instance_t * uart)
{
#ifdef DEBUG_DDR_INIT
    /* Turn on UART0 clock */
    SYSREG->SUBBLK_CLOCK_CR |= (SUBBLK_CLOCK_CR_MMUART0_MASK);
    /* Remove soft reset */
    SYSREG->SOFT_RESET_CR   &= (uint32_t)(~SUBBLK_CLOCK_CR_MMUART0_MASK);
    MSS_UART_init( uart,
        MSS_UART_115200_BAUD,
            MSS_UART_DATA_8_BITS | MSS_UART_NO_PARITY | MSS_UART_ONE_STOP_BIT);
    return(0U);
#endif
}


/***************************************************************************//**
 * Print in number hex format
 * @param uart
 * @param b
 */

static void dumpbyte(mss_uart_instance_t * uart, uint8_t b)
{
#ifdef DEBUG_DDR_INIT
    const uint8_t hexchrs[] = { '0','1','2','3','4','5','6','7','8','9','A','B',\
            'C','D','E','F' };
    MSS_UART_polled_tx(uart, &hexchrs[b >> 4u] , 1);
    MSS_UART_polled_tx(uart, &hexchrs[b & 0x0fu] , 1);
#endif
}

/***************************************************************************//**
 *
 * @param uart
 * @param msg
 * @param d
 */
__attribute__((weak))\
        void uprint32(mss_uart_instance_t * uart, const char* msg, uint32_t d)
{
    MSS_UART_polled_tx_string(uart, (const uint8_t *)msg);
    for (unsigned i=0; i < 4; i++)
    {
        dumpbyte(uart, (d >> (8*(3-i))) & 0xffu);
    }
}

/***************************************************************************//**
 *
 * @param uart
 * @param msg
 * @param d
 */
__attribute__((weak))\
        void uprint64(mss_uart_instance_t * uart, const char* msg, uint64_t d)
{
    MSS_UART_polled_tx_string(uart, (const uint8_t *)msg);
    for (unsigned i=4; i < 8; i++)
    {
        dumpbyte(uart, (d >> (8*(3-i))) & 0xffu);
    }
    for (unsigned i=0; i < 4; i++)
    {
        dumpbyte(uart, (d >> (8*(3-i))) & 0xffu);
    }
}

/***************************************************************************//**
 *
 * @param uart
 * @param msg
 */
__attribute__((weak))\
        void uprint(mss_uart_instance_t * uart, const char* msg)
{
    MSS_UART_polled_tx_string(uart, (const uint8_t *)msg);
}

/***************************************************************************//**
 * dump a number of 32bit contiguous registers
 * @param uart
 * @param reg_pointer
 * @param no_of_regs
 */
void print_reg_array(mss_uart_instance_t * uart, uint32_t *reg_pointer,\
        uint32_t no_of_regs)
{
#ifdef DEBUG_DDR_INIT
    while(no_of_regs > 0U)
    {
        uprint64(uart, "\n\rRegister, 0x", (uint64_t)reg_pointer);
        uprint32(uart, "  ,Value, 0x", *reg_pointer);
        reg_pointer++;
        no_of_regs--;
    }
#endif
}

#endif

/***************************************************************************//**
 * Write data to DDR
 * @param DDR_word_ptr
 * @param no_of_access
 * @param data_ptrn
 * @return
 */
static uint32_t ddr_write
(
    volatile uint64_t *DDR_word_ptr,
    uint32_t no_of_access,
    uint8_t data_ptrn,
    DDR_ACCESS_SIZE data_size
)
{
    uint32_t i;
    uint64_t DATA;
    uint32_t error_count = 0U;

    uint32_t *DDR_32_ptr = (uint32_t *)DDR_word_ptr;
    uint16_t *DDR_16_ptr = (uint16_t *)DDR_word_ptr;
    uint8_t *DDR_8_ptr   = (uint8_t *)DDR_word_ptr;

    switch (data_ptrn)
    {
        case PATTERN_INCREMENTAL : DATA = 0x00000000; break;
        case PATTERN_WALKING_ONE : DATA = 0x00000001; break;
        case PATTERN_WALKING_ZERO : DATA = 0x01;
                 DATA = ~ DATA; break;
        case PATTERN_RANDOM :
            DATA = (uint64_t)rand ( );
            break;
        case PATTERN_0xCCCCCCCC :
            DATA = 0xCCCCCCCCCCCCCCCC;
            break;
        case PATTERN_0x55555555 :
            DATA = 0x5555555555555555;
            break;
        case PATTERN_ZEROS :
            DATA = 0x00000000;
            break;
        default :
            DATA = 0x00000000;
            break;
    }

    for( i = 0; i< (no_of_access); i++)
    {
        switch(data_size)
        {
            case DDR_8_BIT:
                DATA &= 0xFFUL;
                *DDR_8_ptr = (uint8_t)DATA;
                DDR_8_ptr = DDR_8_ptr + 1;
                break;
            case DDR_16_BIT:
                DATA &= 0xFFFFUL;
                *DDR_16_ptr = (uint16_t)DATA;
                DDR_16_ptr = DDR_16_ptr + 1;
                break;
            case DDR_32_BIT:
                DATA &= 0xFFFFFFFFUL;
                *DDR_32_ptr = (uint32_t)DATA;
                DDR_32_ptr = DDR_32_ptr + 1;
                break;
            default:
            case DDR_64_BIT:
                *DDR_word_ptr = DATA;
                DDR_word_ptr = DDR_word_ptr + 1;
                break;
        }

#ifdef DEBUG_DDR_INIT
        if((i%0x1000000UL) ==0UL)
        {
            MSS_UART_polled_tx(g_debug_uart, (const uint8_t*)"w", (uint32_t)1UL);
        }
#endif
        switch (data_ptrn)
        {
            case PATTERN_INCREMENTAL : DATA = DATA + 0x00000001; break;
            case PATTERN_WALKING_ONE :
                if (DATA == 0x80000000)
                    DATA = 0x00000001;
                else
                    DATA = (DATA << 1);
                break;
            case PATTERN_WALKING_ZERO :
                DATA = ~DATA;
                if (DATA == 0x80000000)
                    DATA = 0x00000001;
                else
                {
                    DATA = (DATA << 1);
                }
                DATA = ~DATA;
                break;
            case PATTERN_RANDOM :
                DATA = (uint64_t)rand ( );
                break;
            case PATTERN_0xCCCCCCCC :
                DATA = 0xCCCCCCCCCCCCCCCC;
                break;
            case PATTERN_0x55555555 :
                DATA = 0x5555555555555555;
                break;
            case PATTERN_ZEROS :
                DATA = 0x00000000;
                break;
            default :
                break;
        }
    }
    return error_count;
}

/***************************************************************************//**
 * Reads and compares with what was written
 * @param DDR_word_ptr
 * @param no_of_access
 * @param data_ptrn
 * @return 0 => read backs all expected value, otherwise error count
 */
uint32_t ddr_read
(
    volatile uint64_t *DDR_word_ptr,
    uint32_t no_of_access,
    uint8_t data_ptrn,
    DDR_ACCESS_SIZE data_size
)
{
    uint32_t i;
    uint64_t DATA;
    uint32_t err_cnt;
    volatile uint64_t ddr_data;
    volatile uint64_t *DDR_word_pt_t, *first_DDR_word_pt_t;
    uint32_t rand_addr_offset;
    uint8_t *DDR_8_pt_t;
    uint16_t *DDR_16_pt_t;
    uint32_t *DDR_32_pt_t;

    err_cnt = 0U;
    first_DDR_word_pt_t = DDR_word_ptr;
    DDR_8_pt_t = (uint8_t *)DDR_word_ptr;
    DDR_16_pt_t = (uint16_t *)DDR_word_ptr;
    DDR_32_pt_t = (uint32_t *)DDR_word_ptr;

    switch (data_ptrn)
    {
        case PATTERN_INCREMENTAL : DATA = 0x00000000; break;
        case PATTERN_WALKING_ONE : DATA = 0x00000001; break;
        case PATTERN_WALKING_ZERO : DATA = 0x01;
            DATA = ~ DATA; break;
        case PATTERN_RANDOM :
            DATA = (uint64_t)rand ( );
            *DDR_word_ptr = DATA;
            *DDR_8_pt_t =  (uint8_t)DATA;
            *DDR_16_pt_t = (uint16_t)DATA;
            *DDR_32_pt_t = (uint32_t)DATA;
            break;
        case PATTERN_0xCCCCCCCC :
            DATA = 0xCCCCCCCCCCCCCCCC;
            break;
        case PATTERN_0x55555555 :
            DATA = 0x5555555555555555;
            break;
        case PATTERN_ZEROS :
            DATA = 0x00000000;
        break;
        default :
           DATA = 0x00000000;
           break;
    }
    if (data_ptrn == '4')
    {
        delay(10);
    }
    for( i = 0; i< (no_of_access); i++)
    {
        switch(data_size)
        {
            case DDR_8_BIT:
                DATA &= 0xFFUL;
                ddr_data = *DDR_8_pt_t;
                break;
            case DDR_16_BIT:
                DATA &= 0xFFFFUL;
                ddr_data = *DDR_16_pt_t;
                break;
            case DDR_32_BIT:
                DATA &= 0xFFFFFFFFUL;
                ddr_data = *DDR_32_pt_t;
                break;
            default:
            case DDR_64_BIT:
                DDR_word_pt_t = DDR_word_ptr;
                ddr_data = *DDR_word_pt_t;
                break;
        }

#ifdef DEBUG_DDR_INIT
        if((i%0x1000000UL) ==0UL)
        {
            MSS_UART_polled_tx(g_debug_uart, (const uint8_t*)"r", (uint32_t)1UL);
        }
#endif

        if (ddr_data != DATA)
        {
#ifdef DEBUG_DDR_INIT
#ifdef DEBUG_DDR_RD_RW_FAIL
            if (err_cnt <=0xF)
            {
                uprint64(g_debug_uart,\
                        "\n\r READ/ WRITE ACCESS FAILED AT ADDR: 0x ",\
                            (uintptr_t)DDR_word_ptr);
                uprint64(g_debug_uart,"\t Expected Data 0x ", DATA);
                uprint64(g_debug_uart,"\t READ DATA: 0x ", ddr_data);
                uprint64(g_debug_uart,"\t READ DATA: 0x ", *DDR_word_ptr);
                uprint64(g_debug_uart,"\t READ DATA: 0x ", *DDR_word_ptr);
            }
#endif
#endif
            err_cnt++;
        }
        else
        {
#ifdef DEBUG_DDR_RD_RW_PASS
            //printf("\n\r READ/ WRITE ACCESS passED AT ADDR: 0x%x expected data = 0x%x, Data read 0x%x",DDR_word_ptr, DATA, *DDR_word_ptr);
            uprint64(g_debug_uart, "\n\r READ/ WRITE ACCESS PASSED AT ADDR: 0x"\
                    , (uintptr_t)DDR_word_ptr);
            uprint64(g_debug_uart,"\t READ DATA: 0x", *DDR_word_ptr);
#endif
        }
        DDR_word_ptr = DDR_word_ptr + 1U;
        DDR_8_pt_t   = DDR_8_pt_t +1U;
        DDR_16_pt_t  = DDR_16_pt_t +1U;
        DDR_32_pt_t  = DDR_32_pt_t +1U;
        switch (data_ptrn)
        {
            case PATTERN_INCREMENTAL : DATA = DATA + 0x01; break;
            case PATTERN_WALKING_ONE :
                if (DATA == 0x80000000)
                    DATA = 0x00000001;
                else
                    DATA = (DATA << 1);
                break;
            case PATTERN_WALKING_ZERO :
                DATA = ~DATA;
                if (DATA == 0x80000000)
                {
                    DATA = 0x00000001;
                }
                else
                {
                    DATA = (DATA << 1);
                }
                DATA = ~DATA;
                break;
            case PATTERN_RANDOM :
                DATA = (uint64_t)rand ( );
                rand_addr_offset = (uint32_t)(rand() & 0xFFFFCUL);
                DDR_word_ptr = first_DDR_word_pt_t + rand_addr_offset;
                DDR_8_pt_t   = (uint8_t *)(first_DDR_word_pt_t + rand_addr_offset);
                DDR_16_pt_t  = (uint16_t *)(first_DDR_word_pt_t + rand_addr_offset);
                DDR_32_pt_t  = (uint32_t *)(first_DDR_word_pt_t + rand_addr_offset);
                *DDR_word_ptr   = DATA;
                *DDR_8_pt_t     = (uint8_t)DATA;
                *DDR_16_pt_t    = (uint16_t)DATA;
                *DDR_32_pt_t    = (uint32_t)DATA;
                break;
            case PATTERN_0xCCCCCCCC :
                DATA = 0xCCCCCCCCCCCCCCCC;
                break;
            case PATTERN_0x55555555 :
                DATA = 0x5555555555555555;
                break;
            case PATTERN_ZEROS :
                DATA = 0x00000000;
                break;
            default :
                break;
          }
    }
    return (err_cnt);
}

/***************************************************************************//**
 *
 * @param DDR_word_ptr  Address
 * @param no_access  Number of addresses
 * @param pattern bit mask with patterns you want to test against
 * @return
 */
uint32_t ddr_read_write_fn (uint64_t* DDR_word_ptr, uint32_t no_access,\
                                                               uint32_t pattern)
{
    uint32_t error_cnt = 0U;
    uint8_t pattern_mask;
    for (unsigned i=0; i < 1; i++)
    {
        for (uint32_t pattern_shift=0U; pattern_shift < MAX_NO_PATTERNS;\
                                                                pattern_shift++)
        {
            pattern_mask = (uint8_t)(0x01U << pattern_shift);
            if(pattern & pattern_mask)
            {
#ifdef DEBUG_DDR_INIT
                uprint32(g_debug_uart,"\n\r\t Pattern: 0x", pattern_shift);
#endif

#if TEST_64BIT_ACCESS == 1
                /* write the pattern */
                error_cnt += ddr_write ((uint64_t *)DDR_word_ptr,\
                        no_access, pattern_mask, DDR_64_BIT);
                /* read back and verifies */
                error_cnt += ddr_read ((uint64_t *)DDR_word_ptr, \
                        no_access, pattern_mask, DDR_64_BIT);
#endif

#if TEST_32BIT_ACCESS == 1
                /* write the pattern */
                error_cnt += ddr_write ((uint64_t *)DDR_word_ptr,\
                        no_access, pattern_mask, DDR_32_BIT);
                /* read back and verifies */
                error_cnt += ddr_read ((uint64_t *)DDR_word_ptr, \
                        no_access, pattern_mask, DDR_32_BIT);
#endif
            }
        }
        DDR_word_ptr++; /* increment the address */
    }
    return error_cnt;
}


/***************************************************************************//**
 *
 * @param error
 * @return
 */
#ifdef DEBUG_DDR_INIT
uint32_t error_status(mss_uart_instance_t *g_mss_uart_debug_pt, uint32_t error)
{
    uprint32(g_mss_uart_debug_pt,  "\n\r ERROR_RESULT: ", error);
    return (0U);
}
#endif

/***************************************************************************//**
 * Calibration status
 * @return
 */
#ifdef DEBUG_DDR_INIT
uint32_t wrcalib_status(mss_uart_instance_t *g_mss_uart_debug_pt)
{
    uprint32(g_mss_uart_debug_pt,  "\n\r WRCALIB_RESULT: ",\
            CFG_DDR_SGMII_PHY->expert_wrcalib.expert_wrcalib);
    return (0U);
}
#endif

#ifdef DEBUG_DDR_INIT
/***************************************************************************//**
 * Prints out DDR status
 * @return
 */
uint32_t tip_register_status (mss_uart_instance_t *g_mss_uart_debug_pt)
{

    uint32_t t_status = 0U;
    uint32_t MSS_DDR_APB_ADDR;
    uint32_t ddr_lane_sel;
    uint32_t dq0_dly = 0U;
    uint32_t dq1_dly = 0U;
    uint32_t dq2_dly = 0U;
    uint32_t dq3_dly = 0U;
    uint32_t dq4_dly = 0U;
    uint32_t dq5_dly = 0U;

    /*  MSS_UART_polled_tx_string(g_mss_uart_debug_pt, "\n\n\r TIP register status \n");
    delay(1000);*/
    uprint32(g_mss_uart_debug_pt,  "\n\r\n\r training status = ",\
                            CFG_DDR_SGMII_PHY->training_status.training_status);
    uprint32(g_mss_uart_debug_pt,  "\n\r PCODE = ",\
                                (CFG_DDR_SGMII_PHY->IOC_REG2.IOC_REG2 & 0x7F));
    uprint32(g_mss_uart_debug_pt,  "\n\r NCODE = ",\
                        (((CFG_DDR_SGMII_PHY->IOC_REG2.IOC_REG2) >> 7) & 0x7F));
    uprint32(g_mss_uart_debug_pt,  "\n\r WRCALIB_RESULT: "\
                            , CFG_DDR_SGMII_PHY->expert_wrcalib.expert_wrcalib);
    uprint32(g_mss_uart_debug_pt,  "\n\r sro_ref_slewr  = ",\
                        (((CFG_DDR_SGMII_PHY->IOC_REG5.IOC_REG5) >> 0) & 0x3F));
    uprint32(g_mss_uart_debug_pt,  "\n\r sro_ref_slewf  = ",\
                       (((CFG_DDR_SGMII_PHY->IOC_REG5.IOC_REG5) >> 6) & 0xFFF));
    uprint32(g_mss_uart_debug_pt,  "\n\r sro_slewr  = ",\
                       (((CFG_DDR_SGMII_PHY->IOC_REG5.IOC_REG5) >> 18) & 0x3F));
    uprint32(g_mss_uart_debug_pt,  "\n\r sro_slewf  = ",\
            (((CFG_DDR_SGMII_PHY->IOC_REG5.IOC_REG5) >> 24) & 0x3F));

    MSS_UART_polled_tx_string(g_mss_uart_debug_pt, \
            (const uint8_t*)"\n\n\r lane_select \t gt_err_comb \t gt_txdly \t gt_steps_180 \t gt_state \t wl_delay_0 \t dqdqs_err_done \t dqdqs_state \t delta0 \t delta1");

    for (ddr_lane_sel=0U; ddr_lane_sel < LIBERO_SETTING_DATA_LANES_USED; ddr_lane_sel++)
    {
        CFG_DDR_SGMII_PHY->lane_select.lane_select = ddr_lane_sel;
        uprint32(g_mss_uart_debug_pt, "\n\r ",\
                CFG_DDR_SGMII_PHY->lane_select.lane_select);
        delay(1000);
        MSS_DDR_APB_ADDR = CFG_DDR_SGMII_PHY->gt_err_comb.gt_err_comb;
        uprint32(g_mss_uart_debug_pt, "\t ", MSS_DDR_APB_ADDR);
        t_status = t_status | MSS_DDR_APB_ADDR;

        MSS_DDR_APB_ADDR = CFG_DDR_SGMII_PHY->gt_txdly.gt_txdly;
        uprint32(g_mss_uart_debug_pt, "\t ", MSS_DDR_APB_ADDR);

        if((MSS_DDR_APB_ADDR & 0xFF) == 0)    t_status = 1;
        if((MSS_DDR_APB_ADDR & 0xFF00) == 0)  t_status = 1;
        if((MSS_DDR_APB_ADDR & 0xFF0000) == 0) t_status = 1;
        if((MSS_DDR_APB_ADDR & 0xFF000000) == 0) t_status = 1;

        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->gt_steps_180.gt_steps_180);
        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->gt_state.gt_state);
        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->wl_delay_0.wl_delay_0);
        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->dq_dqs_err_done.dq_dqs_err_done);
        t_status = t_status | (MSS_DDR_APB_ADDR  != 8);

        uprint32(g_mss_uart_debug_pt, "\t\t ",\
                CFG_DDR_SGMII_PHY->dqdqs_state.dqdqs_state);
        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->delta0.delta0);
        dq0_dly = (MSS_DDR_APB_ADDR & 0xFF);
        dq1_dly = (MSS_DDR_APB_ADDR & 0xFF00) >> 8;
        dq2_dly = (MSS_DDR_APB_ADDR & 0xFF0000) >> 16;
        dq3_dly = (MSS_DDR_APB_ADDR & 0xFF000000) >> 24;
        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->delta1.delta1);
        dq4_dly = (MSS_DDR_APB_ADDR & 0xFF);
        dq5_dly = (MSS_DDR_APB_ADDR & 0xFF00) >> 8;
        dq2_dly = (MSS_DDR_APB_ADDR & 0xFF0000) >> 16;
        dq3_dly = (MSS_DDR_APB_ADDR & 0xFF000000) >> 24;
    }

    MSS_UART_polled_tx_string(g_mss_uart_debug_pt, (const uint8_t*)"\n\r\n\r lane_select\t rdqdqs_status2\t addcmd_status0\t addcmd_status1\t addcmd_answer1\t dqdqs_status1\n\r");
    for (ddr_lane_sel=0U; ddr_lane_sel < LIBERO_SETTING_DATA_LANES_USED;\
                                                                ddr_lane_sel++)
    {
        CFG_DDR_SGMII_PHY->lane_select.lane_select = ddr_lane_sel;
        uprint32(g_mss_uart_debug_pt, "\n\r ",\
                                    CFG_DDR_SGMII_PHY->lane_select.lane_select);
        delay(1000);

        if(dq0_dly > 20) t_status = 1;
        if(dq1_dly > 20) t_status = 1;
        if(dq2_dly > 20) t_status = 1;
        if(dq3_dly > 20) t_status = 1;
        if(dq4_dly > 20) t_status = 1;
        if(dq5_dly > 20) t_status = 1;

        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->dqdqs_status2.dqdqs_status2);

        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->addcmd_status0.addcmd_status0);
        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->addcmd_status1.addcmd_status1);
        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->addcmd_answer.addcmd_answer);
        uprint32(g_mss_uart_debug_pt, "\t ",\
                CFG_DDR_SGMII_PHY->dqdqs_status1.dqdqs_status1);

    }
    return(t_status);
}
#endif

/***************************************************************************//**
 * display sweep results
 *
 * @param g_mss_uart_debug_pt
 */
#ifdef DEBUG_DDR_INIT
#ifdef SWEEP_ENABLED
void sweep_status (mss_uart_instance_t *g_mss_uart_debug_pt)
{

    uint32_t t_status;
    uint8_t cmd_index;
    uint8_t bclk_sclk_index;
    uint8_t dpc_vgen_index;
    uint8_t dpc_vgen_h_index;
    uint8_t dpc_vgen_vs_index;

    MSS_UART_polled_tx_string(g_mss_uart_debug_pt,\
                    "\n\n\r dpc_vgen_vs dpc_vgen_h \t dpc_vgen_v \t bclk_sclk");
    for (cmd_index=0U; cmd_index < MAX_NUMBER_ADDR_CMD_OFFSET_SWEEPS; \
                                                                    cmd_index++)
    {
        uprint32(g_mss_uart_debug_pt, "\t ",\
                cmd_index + LIBERO_SETTING_MIN_ADDRESS_CMD_OFFSET);
    }
    MSS_UART_polled_tx_string(g_mss_uart_debug_pt,\
    "\n\r--------------------------------------------------------------------");

    for (dpc_vgen_vs_index=0U; dpc_vgen_vs_index<MAX_NUMBER_DPC_VS_GEN_SWEEPS;\
                                                            dpc_vgen_vs_index++)
    {
        for (dpc_vgen_h_index=0U; dpc_vgen_h_index < \
                                MAX_NUMBER_DPC_H_GEN_SWEEPS; dpc_vgen_h_index++)
        {
            for (dpc_vgen_index=0U; dpc_vgen_index < \
                                MAX_NUMBER_DPC_V_GEN_SWEEPS; dpc_vgen_index++)
            {
                for (bclk_sclk_index=0U; bclk_sclk_index < \
                        MAX_NUMBER__BCLK_SCLK_OFFSET_SWEEPS; bclk_sclk_index++)
                {
                    uprint32(g_mss_uart_debug_pt, "\n\r ", dpc_vgen_vs_index + \
                                                LIBERO_SETTING_MIN_DPC_VS_GEN);
                    uprint32(g_mss_uart_debug_pt, "\t ", dpc_vgen_h_index + \
                                                  LIBERO_SETTING_MIN_DPC_H_GEN);
                    uprint32(g_mss_uart_debug_pt, "\t ", dpc_vgen_index + \
                                                    LIBERO_SETTING_MIN_DPC_V_GEN);
                    uprint32(g_mss_uart_debug_pt, "\t ", bclk_sclk_index + \
                                    LIBERO_SETTING_MIN_ADDRESS_BCLK_SCLK_OFFSET);
                    for (cmd_index=0U; cmd_index < \
                                MAX_NUMBER_ADDR_CMD_OFFSET_SWEEPS; cmd_index++)
                    {
                        if(sweep_results[dpc_vgen_vs_index][dpc_vgen_h_index]\
                                [dpc_vgen_index][bclk_sclk_index][cmd_index] ==\
                                     CALIBRATION_PASSED)
                        {
                            MSS_UART_polled_tx_string(g_mss_uart_debug_pt,\
                                                                   "\t\t pass");
                        }
                        else
                        {
                            /*
                             * easier to see if not printed
                             * todo: may add detail to fail
                             * */
                            MSS_UART_polled_tx_string(g_mss_uart_debug_pt,\
                                                                      "\t\t F");
                        }

                    }
                }
            }
        }
    }
}
#endif
#endif


/**
 * Load a pattern to DDR
 */
void load_ddr_pattern(uint64_t base, uint32_t size, uint8_t pattern_offset)
{
    int alive = 0;

    uint8_t *p_ddr = (uint8_t *)base;
    uint32_t pattern_length = sizeof(ddr_test_pattern) - pattern_offset ;

#ifdef DEBUG_DDR_INIT
    uprint(g_debug_uart, (const char*)(const uint8_t*)"\r\nLoading test pattern\r\n");
#endif

    while(((uint64_t)p_ddr + pattern_length) <  (base + size))
    {

        switch ( ((uint64_t)p_ddr)%8U )
        {
            case 0:
            case 4:
                pdma_transfer_complete(PDMA_CHANNEL0_BASE_ADDRESS);
                pdma_transfer((uint64_t)p_ddr, (uint64_t)ddr_test_pattern, pattern_length, PDMA_CHANNEL0_BASE_ADDRESS);
                break;
            case 1:
            case 5:
                pdma_transfer_complete(PDMA_CHANNEL1_BASE_ADDRESS);
                pdma_transfer((uint64_t)p_ddr, (uint64_t)ddr_test_pattern, pattern_length, PDMA_CHANNEL1_BASE_ADDRESS);
                break;
            case 2:
            case 6:
                pdma_transfer_complete(PDMA_CHANNEL2_BASE_ADDRESS);
                pdma_transfer((uint64_t)p_ddr, (uint64_t)ddr_test_pattern, pattern_length, PDMA_CHANNEL2_BASE_ADDRESS);
                break;
            case 3:
            case 7:
                pdma_transfer_complete(PDMA_CHANNEL3_BASE_ADDRESS);
                pdma_transfer((uint64_t)p_ddr, (uint64_t)ddr_test_pattern, pattern_length, PDMA_CHANNEL3_BASE_ADDRESS);
                break;
        }

        p_ddr = p_ddr + (pattern_length);
        alive++;
        if (alive > 1000)
        {
            alive = 0;
#ifdef DEBUG_DDR_INIT
            uprint(g_debug_uart, (const char*)".");
#endif
        }
    }
#ifdef DEBUG_DDR_INIT
    uprint(g_debug_uart, (const char*)"\r\nFinished loading test pattern\r\n");
#endif

    pdma_transfer_complete(PDMA_CHANNEL0_BASE_ADDRESS);
    pdma_transfer_complete(PDMA_CHANNEL1_BASE_ADDRESS);
    pdma_transfer_complete(PDMA_CHANNEL2_BASE_ADDRESS);
    pdma_transfer_complete(PDMA_CHANNEL3_BASE_ADDRESS);

}

/**
 * Run from address
 * @param start_addr address to run from.
 */
void execute_ddr_pattern(uint64_t start_addr)
{
    pattern_fct_t p_pattern_fct = (pattern_fct_t)start_addr;

    (*p_pattern_fct)();
}

/**
 * Loads DDR with a pattern that triggers read issues if not enough margin.
 * Used to verify training is successful.
 * @param p_cached_ddr
 * @param p_not_cached_ddr
 * @param length
 */
void load_test_buffers(uint32_t * p_cached_ddr, uint32_t * p_not_cached_ddr, uint64_t length)
{
    (void)length;

    pdma_transfer((uint64_t)g_test_buffer_cached, (uint64_t)p_cached_ddr, length,  PDMA_CHANNEL0_BASE_ADDRESS);
    pdma_transfer((uint64_t)g_test_buffer_not_cached, (uint64_t)p_not_cached_ddr, length,  PDMA_CHANNEL1_BASE_ADDRESS);
    pdma_transfer_complete(PDMA_CHANNEL0_BASE_ADDRESS);
    pdma_transfer_complete(PDMA_CHANNEL1_BASE_ADDRESS);
}

/**
 * test_ddr reads from cached and non cached DDR and compares
 * @param no_of_iterations
 * @param size
 * @return returns 1 if compare fails
 */
uint32_t test_ddr(uint32_t no_of_iterations, uint32_t size)
{
    uint32_t pattern_length = sizeof(ddr_test_pattern) - (3 * sizeof(uint32_t));
    uint32_t * p_ddr_cached = (uint32_t *)0x80000000;
    uint32_t * p_ddr_noncached = (uint32_t *)0x1400000000;
    uint32_t word_offset;
    uint32_t alive = 0;
    uint32_t alive_idx = 0U;
    uint32_t iteration = 0U;
    uint32_t error = 0U;


#ifdef DEBUG_DDR_INIT
    uprint(g_debug_uart, (const char*)"\r\nStarting ddr test\r\n");
#endif
    while(iteration < no_of_iterations)
    {
        int different = 0;

        load_test_buffers(p_ddr_cached, p_ddr_noncached, pattern_length);

        different = memcmp(g_test_buffer_cached, g_test_buffer_not_cached, pattern_length);

        if(different != 0)
        {
            for(word_offset = 0; word_offset < (pattern_length / sizeof(uint32_t)); word_offset++)
            {
                if(g_test_buffer_cached[word_offset] != g_test_buffer_not_cached[word_offset])
                {
#ifdef DEBUG_DDR_INIT
                    uprint64(g_debug_uart, "  Mismatch, 0x", (uint64_t)p_ddr_cached);
                    uprint32(g_debug_uart, "  offset:, 0x", (uint64_t)word_offset);
                    uprint32(g_debug_uart, "  address: 0x", (uint64_t)(p_ddr_cached + word_offset));
                    uprint32(g_debug_uart, "  expected (non-cached): 0x", g_test_buffer_not_cached[word_offset]);
                    uprint32(g_debug_uart, "  found  (cached): 0x", (uint64_t)g_test_buffer_cached[word_offset]);
                    uprint32(g_debug_uart, "  direct cached read: 0x", (uint32_t)*(p_ddr_cached + word_offset));
                    uprint32(g_debug_uart, "  direct non-cached read: 0x", (uint32_t)*(p_ddr_noncached + word_offset));
#endif
                    break;
                }
            }
            error = 1U;
            return error;
        }

        if (((uint64_t)p_ddr_cached + ( 2 * pattern_length)) <  (LIBERO_SETTING_DDR_32_CACHE + size))
        {
            p_ddr_cached += (pattern_length / sizeof(uint32_t));
            p_ddr_noncached += (pattern_length / sizeof(uint32_t));
        }
        else
        {
            p_ddr_cached = (uint32_t *)0x80000000;
            p_ddr_noncached = (uint32_t *)0x1400000000;
            iteration++;
#ifdef DEBUG_DDR_INIT
            uprint32(g_debug_uart, "  Iteration ", (uint64_t)(unsigned int)iteration);
#endif
        }

        alive++;
        if(alive > 10000U)
        {
            alive = 0;
#ifdef DEBUG_DDR_INIT
            uprint(g_debug_uart, (const char*)"\r");
            uprint(g_debug_uart, (const char*)progress[alive_idx]);
#endif
            alive_idx++;
            if(alive_idx >= 3U)
            {
                alive_idx = 0;
            }
            if(ddr_test == 2U)
            {
#ifdef DEBUG_DDR_INIT
            uprint(g_debug_uart, (const char*)"\r\nEnding ddr test. Press 0 to display the menu\r\n");
#endif
                return error;
            }
        }
    }
    return error;
}



