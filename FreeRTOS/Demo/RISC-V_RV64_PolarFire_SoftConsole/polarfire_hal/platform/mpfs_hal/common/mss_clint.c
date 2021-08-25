/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 *
 * @file mss_clint.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief CLINT access data structures and functions.
 *
 */
#include <stdint.h>
#include "mpfs_hal/mss_hal.h"

static uint64_t g_systick_increment[5] = {0ULL,0ULL,0ULL,0ULL,0ULL};

/**
 * call once at startup
 * @return
 */
void reset_mtime(void)
{
#if ROLLOVER_TEST
    CLINT->MTIME = 0xFFFFFFFFFFFFF000ULL;
#else
    CLINT->MTIME = 0ULL;
#endif
}

/**
 * readmtime
 * @return mtime
 */
uint64_t readmtime(void)
{
    return (CLINT->MTIME);
}

/**
 * Configure system tick
 * @return SUCCESS or FAIL
 */
uint32_t SysTick_Config(void)
{
    const uint32_t tick_rate[5] = {HART0_TICK_RATE_MS,    HART1_TICK_RATE_MS    ,HART2_TICK_RATE_MS    ,HART3_TICK_RATE_MS    ,HART4_TICK_RATE_MS};
    volatile uint32_t ret_val = ERROR;

    uint64_t mhart_id = read_csr(mhartid);

    /*
     * We are assuming the tick rate is in milli-seconds
     *
     * convert RTC frequency into milliseconds and multiple by the tick rate
     *
     */

    g_systick_increment[mhart_id] = ((LIBERO_SETTING_MSS_RTC_TOGGLE_CLK/1000U)  * tick_rate[mhart_id]);

    if (g_systick_increment[mhart_id] > 0ULL)
    {

        CLINT->MTIMECMP[mhart_id] = CLINT->MTIME + g_systick_increment[mhart_id];

        set_csr(mie, MIP_MTIP);   /* mie Register - Machine Timer Interrupt Enable */

        __enable_irq();

        ret_val = SUCCESS;
    }

    return (ret_val);
}

/**
 * Disable system tick interrupt
 */
void disable_systick(void)
{
    clear_csr(mie, MIP_MTIP);   /* mie Register - Machine Timer Interrupt Enable */
    return;
}


/*------------------------------------------------------------------------------
 * RISC-V interrupt handler for machine timer interrupts.
 */
void handle_m_timer_interrupt(void)
{

    volatile uint64_t hart_id = read_csr(mhartid);
    volatile uint32_t error_loop;
    clear_csr(mie, MIP_MTIP);

    switch(hart_id)
    {
        case 0U:
            SysTick_Handler_h0_IRQHandler();
            break;
        case 1U:
            SysTick_Handler_h1_IRQHandler();
            break;
        case 2U:
            SysTick_Handler_h2_IRQHandler();
            break;
        case 3U:
            SysTick_Handler_h3_IRQHandler();
            break;
        case 4U:
            SysTick_Handler_h4_IRQHandler();
            break;
        default:
            while (hart_id != 0U)
             {
                 error_loop++;
             }
            break;
    }

    CLINT->MTIMECMP[read_csr(mhartid)] = CLINT->MTIME + g_systick_increment[hart_id];

    set_csr(mie, MIP_MTIP);

}


/**
 *
 */
void handle_m_soft_interrupt(void)
{
    volatile uint64_t hart_id = read_csr(mhartid);
    volatile uint32_t error_loop;

    switch(hart_id)
    {
        case 0U:
            Software_h0_IRQHandler();
            break;
        case 1U:
            Software_h1_IRQHandler();
            break;
        case 2U:
            Software_h2_IRQHandler();
            break;
        case 3U:
            Software_h3_IRQHandler();
            break;
        case 4U:
            Software_h4_IRQHandler();
            break;
        default:
            while (hart_id != 0U)
            {
                error_loop++;
            }
            break;
    }

    /*Clear software interrupt*/
    clear_soft_interrupt();
}

